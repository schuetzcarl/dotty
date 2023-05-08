package dotty.tools.dotc.transform

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.transform.MegaPhase
import dotty.tools.dotc.transform.MegaPhase.MiniPhase
import dotty.tools.dotc.report
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.util.{Property, SrcPos}
import dotty.tools.dotc.core.Symbols.ClassSymbol
import dotty.tools.dotc.core.Symbols.Symbol


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

  private def reportShadowing(res: ShadowingData.ShadowResult)(using Context): Unit =
    import CheckShadowing.WarnTypes
    res.warnings.foreach{ s =>
       s match
        case (t, WarnTypes.PrivateShadowing) =>
          report.warning(s"A private field is shadowing an inherited field", t)
      }


  // MiniPhase traversal "prepare" settings :
  override def prepareForValDef(tree: tpd.ValDef)(using Context): Context =
    // If private, check for possible clash with inherited symbols
    shadowingDataApply(sd =>
      sd.registerPrivateShadows(tree)
    )

end CheckShadowing

object CheckShadowing:

  val name = "checkShadowing"
  val description = "check for elements shadowing other elements in scope"

  private enum WarnTypes:
    case PrivateShadowing

  private class ShadowingData:
    import dotty.tools.dotc.transform.CheckShadowing.ShadowingData.ShadowResult
    import dotty.tools.dotc.transform.CheckShadowing.WarnTypes
    import collection.mutable.{Set => MutSet, Map => MutMap, Stack => MutStack}

    private val shadowedMemberDefs = MutSet[tpd.MemberDef]()

    def registerPrivateShadows(memDef: tpd.MemberDef)(using Context): Unit =
      if isShadowing(memDef.symbol) then shadowedMemberDefs += memDef

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
      val ls: List[(dotty.tools.dotc.util.SrcPos, WarnTypes)] =
        shadowedMemberDefs.map(memDef => (memDef.namePos, WarnTypes.PrivateShadowing)).toList
      ShadowResult(ls)

  end ShadowingData

  private object ShadowingData:
    /** A container for the results of the shadow elements analysis */
      case class ShadowResult(warnings: List[(SrcPos, WarnTypes)])

end CheckShadowing


