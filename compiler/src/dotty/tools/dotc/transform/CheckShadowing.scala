package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.transform.MegaPhase
import dotty.tools.dotc.transform.MegaPhase.MiniPhase
import dotty.tools.dotc.report
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Flags.{Param, Local, Synthetic}
import dotty.tools.dotc.util.{Property, SrcPos}
import dotty.tools.dotc.core.Symbols.ClassSymbol
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.core.Flags.EmptyFlags
import dotty.tools.dotc.ast.tpd.TreeTraverser
import dotty.tools.dotc.core.Types.watchList
import dotty.tools.dotc.semanticdb.TypeOps
import dotty.tools.dotc.cc.boxedCaptureSet
import dotty.tools.dotc.core.Symbols.NoSymbol
import dotty.tools.dotc.transform.SymUtils.isParamOrAccessor
import scala.collection.mutable
import dotty.tools.dotc.core.Scopes.Scope
import scala.collection.immutable.HashMap
import dotty.tools.dotc.core.Symbols
import dotty.tools.dotc.typer.ImportInfo


class CheckShadowing extends MiniPhase:
  import CheckShadowing.*
  import ShadowingData.*

  private val _key = Property.Key[ShadowingData]

  private def shadowingDataApply[U](f: ShadowingData => U)(using Context): Context =
    ctx.property(_key).foreach(f)
    ctx

  override def phaseName: String = CheckShadowing.name

  override def description: String = CheckShadowing.description

  override def isRunnable(using Context): Boolean =
    super.isRunnable &&
    ctx.settings.Xlint.value.nonEmpty &&
    !ctx.isJava

  // Setup before the traversal
  override def prepareForUnit(tree: tpd.Tree)(using Context): Context =
    val data = ShadowingData()
    ctx.fresh.setProperty(_key, data)

  // Reporting on traversal's end
  override def transformUnit(tree: tpd.Tree)(using Context): tpd.Tree =
    shadowingDataApply( sd =>
      reportShadowing(sd.getPrivatesShadowing)
    )
    tree

  // MiniPhase traversal work :
  override def prepareForValDef(tree: tpd.ValDef)(using Context): Context =
    shadowingDataApply(sd =>
      sd.registerPrivateShadows(tree)
    )

  override def prepareForTypeDef(tree: tpd.TypeDef)(using Context): Context =
    if tree.symbol.isAliasType then // if alias then traverse to get his first type param
      typeParamTraverser(tree.symbol).traverse(tree.rhs)
    if tree.symbol.is(Param) then // if type param then collect the parameter and
      val owner = tree.symbol.owner
      val parent = if (owner.isConstructor) then owner.owner else owner
      typeParamTraverser(parent).traverse(tree.rhs)(using ctx.outer)
      shadowingDataApply(sd => sd.registerCandidate(parent, tree))
    else
      ctx

  override def transformTypeDef(tree: tpd.TypeDef)(using Context): tpd.Tree =
    if tree.symbol.is(Param) && !tree.symbol.owner.isConstructor then // Do not register for constructors the work is done for the Class owned equivalent TypeDef
      shadowingDataApply(sd => sd.computeTypeParamShadowsFor(tree.symbol.owner)(using ctx.outer))
    if tree.symbol.isAliasType then
      shadowingDataApply(sd => sd.computeTypeParamShadowsFor(tree.symbol)(using ctx)) // No need to start outer here, because the TypeDef reached here it's already the parent
    tree

  // CheckShadowing Helpers :
  private def reportShadowing(res: ShadowingData.ShadowResult)(using Context): Unit =
    import CheckShadowing.WarnTypes
    res.warnings.sortBy(_._1.line)(using Ordering[Int]).foreach { s =>
      s match
        case (t, WarnTypes.PrivateShadowing) =>
          report.warning(s"A private field is shadowing an inherited field", t)
        case (t, WarnTypes.TypeParameterShadowing) =>
          report.warning(s"A type parameter is shadowing a parameter already defined in the scope", t)
        case _ =>
      }

  private def typeParamTraverser(parent: Symbol) = new TreeTraverser:
    import tpd._

    override def traverse(tree: tpd.Tree)(using Context): Unit =
      tree match
        case t:tpd.TypeDef =>
          val newCtx = shadowingDataApply(sd => {
            sd.registerCandidate(parent, t)
          })
          traverseChildren(tree)(using newCtx)
        case _ =>
          traverseChildren(tree)
    end traverse
  end typeParamTraverser

end CheckShadowing


object CheckShadowing:

  val name = "checkShadowing"
  val description = "check for elements shadowing other elements in scope"

  private enum WarnTypes:
    case PrivateShadowing
    case TypeParameterShadowing

  private class ShadowingData:
    import dotty.tools.dotc.transform.CheckShadowing.ShadowingData.ShadowResult
    import dotty.tools.dotc.transform.CheckShadowing.WarnTypes
    import collection.mutable.{Set => MutSet, Map => MutMap, Stack => MutStack}

    private val shadowedPrivateDefs = MutSet[tpd.ValDef]()
    private val shadowedTypeDefs = MutSet[tpd.TypeDef]()

    private val typeParamCandidates = MutMap[Symbol, Seq[tpd.TypeDef]]().withDefaultValue(Seq())

    def printParentToTypeDefs() =
      println(typeParamCandidates.map((sy, seq) => (sy, seq.map(t => t.name))))

    def registerCandidate(parent: Symbol, typeDef: tpd.TypeDef) =
      val actual = typeParamCandidates.getOrElseUpdate(parent, Seq())
      typeParamCandidates.update(parent, actual.+:(typeDef))

    def computeTypeParamShadowsFor(parent: Symbol)(using Context): Unit =
        typeParamCandidates(parent).foreach(typeDef => {
          val matchedSym = lookForShadowedType(typeDef.symbol)
          matchedSym match
            case NoSymbol => None
            case s: Symbol => shadowedTypeDefs += typeDef
        })

    private def lookForShadowedType(symbol: Symbol)(using Context): Symbol =
      if !ctx.owner.exists then
        NoSymbol
      else
        val declarationScope = ctx.effectiveScope
        val res = declarationScope.lookup(symbol.name)
        res match
          case NoSymbol => lookForShadowedType(symbol)(using ctx.outer)
          case s: Symbol => s

    def registerPrivateShadows(valDef: tpd.ValDef)(using Context): Unit =
      if isShadowing(valDef.symbol) then shadowedPrivateDefs += valDef

    private def isShadowing(sym: Symbol)(using Context): Boolean =
      val collectedOverridenSyms = collectOverridenSyms(sym)
      !collectedOverridenSyms.isEmpty

    private def collectOverridenSyms(symDecl: Symbol)(using Context): List[Symbol] =
      if symDecl.isPrivate then
        val symDeclType = symDecl.info
        val bClasses = symDecl.owner.info.baseClasses
        bClasses match
          case _ :: inherited =>
            inherited
              .map(classSymbol => symDecl.denot.matchingDecl(classSymbol, symDeclType))
              .filter(sym => sym.name == symDecl.name)
          case Nil =>
            Nil
      else
        Nil

    def getPrivatesShadowing(using Context): ShadowResult =
      val lsPrivateShadow: List[(SrcPos, WarnTypes)] =
        shadowedPrivateDefs.map(memDef => (memDef.namePos, WarnTypes.PrivateShadowing)).toList
      val lsTypeParamShadow: List[(SrcPos, WarnTypes)] =
        shadowedTypeDefs.map(memDef => (memDef.namePos, WarnTypes.TypeParameterShadowing)).toList
      ShadowResult(lsPrivateShadow ++ lsTypeParamShadow)

  end ShadowingData

  private object ShadowingData:
    /** A container for the results of the shadow elements analysis */
      case class ShadowResult(warnings: List[(SrcPos, WarnTypes)])

end CheckShadowing