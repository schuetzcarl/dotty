import scala.quoted.*
import scala.tasty.inspector.*
import scala.language.experimental.erasedDefinitions

val experimentalDefinitionInLibrary = Set(

  // README
  // - Definitions should be grouped under a language feature or API
  // - API definitions that must be stabilized at the same time should be added in the same line
  // - Language definitions are assumed to be stabilized all at once unless stated otherwise


  //// New feature: Safe Exceptions
  // Can be stabilized when safe exceptions language feature is stabilized.
  "scala.CanThrow",
  "scala.unsafeExceptions", "scala.unsafeExceptions$",
  "scala.runtime.$throws$package$.$throws",

  //// New feature: Tupled Functions
  // Can be stabilized when language feature is stabilized.
  // Needs user feedback.
  // Needs generalization to polymorphic types (at least proof of concept that shows that that design is compatible).
  "scala.runtime.TupledFunctions",
  "scala.runtime.TupledFunctions$",
  "scala.util.TupledFunction",
  "scala.util.TupledFunction$",

  //// New feature: main annotation generalization
  // Can be stabilized when language feature is stabilized.
  // Needs user feedback.
  // Should argGetter/varargGetter be simplified?
  // Should we have better support for main annotation macros?
  "scala.annotation.MainAnnotation",
  "scala.annotation.MainAnnotation$",
  "scala.annotation.MainAnnotation$.Info",
  "scala.annotation.MainAnnotation$.Parameter",
  "scala.annotation.MainAnnotation$.ParameterAnnotation",


  //// New feature: prototype of new version of @main
  // This will never be stabilized. When it is ready it should replace the old @main annotation (requires scala.annotation.MainAnnotation).
  // Needs user feedback.
  "scala.annotation.newMain",
  "scala.annotation.newMain$",
  "scala.annotation.newMain$.alias",
  "scala.annotation.newMain.Help",
  "scala.annotation.newMain.Help$",
  "scala.annotation.newMain.Names",

  //// New feature: capture checking
  "scala.annotation.capability",
  "scala.annotation.retains",
  "scala.annotation.retainsByName",
  "scala.Pure",
  "scala.caps",
  "scala.caps$",

  //// New feature: into
  "scala.annotation.allowConversions",

  //// New feature: Macro annotations
  "scala.annotation.MacroAnnotation",

  //// New feature: -Ysafe-init-global
  "scala.annotation.init",
  "scala.annotation.init$",
  "scala.annotation.init$.widen",
  "scala.annotation.init$.region",

   //// New APIs: Quotes
  "scala.quoted.Quotes.reflectModule.FlagsModule.AbsOverride",
  // Can be stabilized in 3.4.0 (unsure) or later
  "scala.quoted.Quotes.reflectModule.CompilationInfoModule.XmacroSettings",
  "scala.quoted.Quotes.reflectModule.FlagsModule.JavaAnnotation",
  // Cant be stabilized yet.
  // Need newClass variant that can add constructor parameters.
  // Need experimental annotation macros to check that design works.
  "scala.quoted.Quotes.reflectModule.ClassDefModule.apply",
  "scala.quoted.Quotes.reflectModule.ClassDefModule.module",
  "scala.quoted.Quotes.reflectModule.SymbolModule.newClass",
  "scala.quoted.Quotes.reflectModule.SymbolModule.newModule",
  "scala.quoted.Quotes.reflectModule.SymbolModule.freshName",
  "scala.quoted.Quotes.reflectModule.SymbolMethods.info",

  // New feature: functions with erased parameters.
  // Need erasedDefinitions enabled.
  "scala.runtime.ErasedFunction", // will be removed (now using PolyFunction)
  "scala.quoted.Quotes.reflectModule.MethodTypeMethods.erasedParams",
  "scala.quoted.Quotes.reflectModule.MethodTypeMethods.hasErasedParams",
  "scala.quoted.Quotes.reflectModule.TermParamClauseMethods.erasedArgs",
  "scala.quoted.Quotes.reflectModule.TermParamClauseMethods.hasErasedArgs",
  "scala.quoted.Quotes.reflectModule.defnModule.PolyFunctionClass",

  // New feature: reverse method on Tuple
  "scala.Tuple.reverse",
  "scala.Tuple$.Helpers",
  "scala.Tuple$.Helpers$",
  "scala.Tuple$.Helpers$.ReverseImpl",
  "scala.Tuple$.Reverse",
  "scala.runtime.Tuples$.reverse"
)


@main def Test = {
  val inspector = new Inspector {
    def inspect(using Quotes)(tastys: List[Tasty[quotes.type]]): Unit = {
      import quotes.reflect.*
      val experimentalAnnot = Symbol.requiredClass("scala.annotation.experimental")
      object AccumulateExperimentalDefs extends TreeAccumulator[Set[Symbol]]:
        def foldTree(expDefs: Set[Symbol], tree: Tree)(owner: Symbol): Set[Symbol] =
          tree match
            case tree: Definition if tree.symbol.hasAnnotation(experimentalAnnot) => foldOverTree(expDefs + tree.symbol, tree)(owner)
            case _ => foldOverTree(expDefs, tree)(owner)

      val experimentalDefinitionsSyms = tastys.foldLeft(Set.empty[Symbol]) { (acc, tasty) =>
        AccumulateExperimentalDefs.foldTree(acc, tasty.ast)(Symbol.spliceOwner)
      }
      val experimentalDefinitions = experimentalDefinitionsSyms.map(_.fullName)
      val missingFromList = experimentalDefinitions -- experimentalDefinitionInLibrary
      val missingInLibrary =  experimentalDefinitionInLibrary -- experimentalDefinitions
      assert(missingFromList.isEmpty,
        s"""Failed @experimental definitions check
         |
         |Found @experimental definition in library not listed:
         |${missingFromList.toSeq.sorted.mkString("\n")}
         |
         |If added new experimental definitions to the library, add them to the list in tests/run-tasty-inspector/stdlibExperimentalDefinitions.scala
         |
         |Test only: sbt "scala3-bootstrapped/testCompilation tests/run-tasty-inspector/stdlibExperimentalDefinitions.scala"
         |""".stripMargin
      )
      assert(missingInLibrary.isEmpty,
        s"""Failed @experimental definitions check
          |
          |Listed @experimental definition was not found in the library
          |${missingInLibrary.toSeq.sorted.mkString("\n")}
          |
          |If experimental definition was removed or stabilized, remove from the list in tests/run-tasty-inspector/stdlibExperimentalDefinitions.scala
          |
          |Test only: sbt "scala3-bootstrapped/testCompilation tests/run-tasty-inspector/stdlibExperimentalDefinitions.scala"
          |""".stripMargin
        )
    }
  }

   // Artefact of the current test infrastructure
  // TODO improve infrastructure to avoid needing this code on each test
  val libJarClasspath = dotty.tools.dotc.util.ClasspathFromClassloader(this.getClass.getClassLoader).split(java.io.File.pathSeparator).find(x => x.contains("scala3-library-bootstrapped") && x.endsWith(".jar")).get

  TastyInspector.inspectTastyFilesInJar(libJarClasspath)(inspector)
}
