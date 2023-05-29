package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.ast.Trees.EmptyTree
import dotty.tools.dotc.transform.MegaPhase
import dotty.tools.dotc.transform.MegaPhase.MiniPhase
import dotty.tools.dotc.report
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Flags.*
import dotty.tools.dotc.util.{Property, SrcPos}
import dotty.tools.dotc.core.Symbols.ClassSymbol
import dotty.tools.dotc.core.Names.Name
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.core.Flags.EmptyFlags
import dotty.tools.dotc.ast.tpd.TreeTraverser
import dotty.tools.dotc.core.Types.watchList
import dotty.tools.dotc.core.Types.NoType
import dotty.tools.dotc.core.Types.Type
import dotty.tools.dotc.core.Types
import dotty.tools.dotc.semanticdb.TypeOps
import dotty.tools.dotc.cc.boxedCaptureSet
import dotty.tools.dotc.core.Symbols.NoSymbol
import dotty.tools.dotc.transform.SymUtils.isParamOrAccessor
import scala.collection.mutable
import dotty.tools.dotc.core.Scopes.Scope
import scala.collection.immutable.HashMap
import dotty.tools.dotc.core.Symbols
import dotty.tools.dotc.typer.ImportInfo
import dotty.tools.dotc.ast.untpd.ImportSelector
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools.dotc.ast.untpd
import dotty.tools.dotc.core.Denotations.SingleDenotation
import dotty.tools.dotc.ast.Trees.Ident
import dotty.tools.dotc.core.Names.TypeName
import dotty.tools.dotc.core.Names.TermName

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
    val fresh = ctx.fresh.setProperty(_key, data)
    shadowingDataApply(sd => sd.registerRootImports())(using fresh)

  // Reporting on traversal's end
  override def transformUnit(tree: tpd.Tree)(using Context): tpd.Tree =
    shadowingDataApply(sd =>
      reportShadowing(sd.getShadowingResult)
    )
    tree

  // MiniPhase traversal work :
  override def prepareForPackageDef(tree: tpd.PackageDef)(using Context): Context =
    shadowingDataApply(sd => sd.inNewScope())
    ctx

  override def prepareForTemplate(tree: tpd.Template)(using Context): Context =
    shadowingDataApply(sd => sd.inNewScope())
    ctx

  override def prepareForBlock(tree: tpd.Block)(using Context): Context =
    shadowingDataApply(sd => sd.inNewScope())
    ctx

  override def prepareForOther(tree: tpd.Tree)(using Context): Context =
    importTraverser(tree.symbol).traverse(tree)
    ctx

  override def prepareForValDef(tree: tpd.ValDef)(using Context): Context =
    shadowingDataApply(sd =>
      sd.registerPrivateShadows(tree)
    )

  override def prepareForTypeDef(tree: tpd.TypeDef)(using Context): Context =
    if tree.symbol.isAliasType then // if alias, the parent is the current symbol
      nestedTypeTraverser(tree.symbol).traverse(tree.rhs)
    if tree.symbol.is(Param) then // if param, the parent is up
      val owner = tree.symbol.owner
      val parent = if (owner.isConstructor) then owner.owner else owner
      nestedTypeTraverser(parent).traverse(tree.rhs)(using ctx.outer)
      shadowingDataApply(sd => sd.registerCandidate(parent, tree))
    else
      ctx


  override def transformPackageDef(tree: tpd.PackageDef)(using Context): tpd.Tree =
    shadowingDataApply(sd => sd.outOfScope())
    tree

  override def transformBlock(tree: tpd.Block)(using Context): tpd.Tree =
    shadowingDataApply(sd => sd.outOfScope())
    tree

  override def transformTemplate(tree: tpd.Template)(using Context): tpd.Tree =
    shadowingDataApply(sd => sd.outOfScope())
    tree

  override def transformTypeDef(tree: tpd.TypeDef)(using Context): tpd.Tree =
    if tree.symbol.is(Param) && !tree.symbol.owner.isConstructor then // Do not register for constructors the work is done for the Class owned equivalent TypeDef
      shadowingDataApply(sd => sd.computeTypeParamShadowsFor(tree.symbol.owner)(using ctx.outer))
    if tree.symbol.isAliasType then // No need to start outer here, because the TypeDef reached here it's already the parent
      shadowingDataApply(sd => sd.computeTypeParamShadowsFor(tree.symbol)(using ctx))
    tree

  // Helpers :

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

  private def nestedTypeTraverser(parent: Symbol) = new TreeTraverser:
    import tpd._

    override def traverse(tree: tpd.Tree)(using Context): Unit =
      tree match
        case t:tpd.TypeDef =>
          val newCtx = shadowingDataApply(sd =>
            sd.registerCandidate(parent, t)
          )
          traverseChildren(tree)(using newCtx)
        case _ =>
          traverseChildren(tree)
    end traverse
  end nestedTypeTraverser

  // To reach the imports during a miniphase traversal
  private def importTraverser(parent: Symbol) = new TreeTraverser:
    import tpd._

    override def traverse(tree: tpd.Tree)(using Context): Unit =
      tree match
        case t:tpd.Import =>
          shadowingDataApply(sd => sd.registerImport(t))
          traverseChildren(tree)
        case _ =>
          traverseChildren(tree)

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

    private val rootImports = MutSet[SingleDenotation]()
    private val explicitsImports = MutStack[MutSet[tpd.Import]]()
    private val renamedImports = MutStack[MutMap[String, Name]]()

    private val typeParamCandidates = MutMap[Symbol, Seq[tpd.TypeDef]]().withDefaultValue(Seq())
    private val shadowedTypeDefs = MutSet[tpd.TypeDef]()


    def inNewScope()(using Context) =
      explicitsImports.push(MutSet())
      renamedImports.push(MutMap())

    def outOfScope()(using Context) =
      explicitsImports.pop()
      renamedImports.pop()

    /** Register the Root imports (at once per compilation unit)*/
    def registerRootImports()(using Context) =
      rootImports.addAll(ctx.definitions.rootImportTypes.flatMap(_.typeMembers))

    /* Register an import encountered in the current scope **/
    def registerImport(imp: tpd.Import)(using Context) =
      val renamedImps = imp.selectors.collect(sel => { sel.renamed match
        case Ident(rename) =>
          (sel.name.toString, rename)
      }).toMap
      explicitsImports.top += imp
      renamedImports.top.addAll(renamedImps)

    /** Register a potential type definition which could shadows a Type already defined */
    def registerCandidate(parent: Symbol, typeDef: tpd.TypeDef) =
      val actual = typeParamCandidates.getOrElseUpdate(parent, Seq())
      typeParamCandidates.update(parent, actual.+:(typeDef))

    /** Compute if there is some TypeParam shadowing and register if it is the case*/
    def computeTypeParamShadowsFor(parent: Symbol)(using Context): Unit =
        typeParamCandidates(parent).foreach(typeDef => {
          val shadowedType =
            lookForRootShadowedType(typeDef.symbol)
              .orElse(lookForImportedShadowedType(typeDef))
              .orElse(lookForUnitShadowedType(typeDef.symbol))
          shadowedType match
            case Some(value) =>
              if !renamedImports.exists(_.contains(value.name.toString())) then
                shadowedTypeDefs += typeDef
            case None =>
        })

    private def lookForImportedShadowedType(typeDef: tpd.TypeDef)(using Context): Option[Symbol] =
      explicitsImports
        .flatMap(_.flatMap(imp => typeDef.symbol.isInImport(imp)))
        .headOption

    private def lookForUnitShadowedType(symbol: Symbol)(using Context): Option[Symbol] =
      if !ctx.owner.exists then
        None
      else
        val declarationScope = ctx.effectiveScope
        val res = declarationScope.lookup(symbol.name)
        res match
          case s: Symbol if s.isType => Some(s)
          case _ => lookForUnitShadowedType(symbol)(using ctx.outer)

    private def lookForRootShadowedType(symbol: Symbol)(using Context): Option[Symbol] =
      if rootImports.exists(p => p.name.toSimpleName == symbol.name.toSimpleName) then Some(symbol) else None

    /** Register a Private Shadows if it is shadowing an inherited field */
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

    /** Get the shadowing analysis's result */
    def getShadowingResult(using Context): ShadowResult =
      val lsPrivateShadow: List[(SrcPos, WarnTypes)] =
        if ctx.settings.XlintHas.privateShadow then
          shadowedPrivateDefs.map(memDef => (memDef.namePos, WarnTypes.PrivateShadowing)).toList
        else
          Nil
      val lsTypeParamShadow: List[(SrcPos, WarnTypes)] =
        if ctx.settings.XlintHas.typeParameterShadow then
          shadowedTypeDefs.map(memDef => (memDef.namePos, WarnTypes.TypeParameterShadowing)).toList
        else
          Nil
      ShadowResult(lsPrivateShadow ++ lsTypeParamShadow)

    extension (sym: Symbol)

      /** Given an import and accessibility, return the import's symbol that matches import<->this symbol */
      private def isInImport(imp: tpd.Import)(using Context): Option[Symbol] =
        val tpd.Import(qual, sels) = imp
        val simpleSelections = qual.tpe.member(sym.name).alternatives
        val typeSelections = sels.flatMap(n => qual.tpe.member(n.name.toTypeName).alternatives)

        sels.find(is => is.rename.toSimpleName == sym.name.toSimpleName).map(_.symbol)
          .orElse(typeSelections.map(_.symbol).find(sd => sd.name == sym.name))
          .orElse(simpleSelections.map(_.symbol).find(sd => sd.name == sym.name))

  end ShadowingData

  private object ShadowingData:
    /** A container for the results of the shadow elements analysis */
      case class ShadowResult(warnings: List[(SrcPos, WarnTypes)])

end CheckShadowing