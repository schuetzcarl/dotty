
import com.typesafe.tools.mima.core._

object MiMaFilters {
  val Library: Seq[ProblemFilter] = Seq(
    ProblemFilters.exclude[MissingClassProblem]("scala.annotation.unchecked.uncheckedCaptures"),

    // Scala.js only: new runtime support class in 3.2.3; not available to users
    ProblemFilters.exclude[MissingClassProblem]("scala.scalajs.runtime.AnonFunctionXXL"),

    //  New experimental features in 3.3.X
    ProblemFilters.exclude[MissingFieldProblem]("scala.runtime.stdLibPatches.language#experimental.clauseInterleaving"),
    ProblemFilters.exclude[MissingClassProblem]("scala.runtime.stdLibPatches.language$experimental$clauseInterleaving$"),
    ProblemFilters.exclude[MissingFieldProblem]("scala.runtime.stdLibPatches.language#experimental.relaxedExtensionImports"),
    ProblemFilters.exclude[MissingClassProblem]("scala.runtime.stdLibPatches.language$experimental$relaxedExtensionImports$"),
    // end of New experimental features in 3.3.X
  )
  val TastyCore: Seq[ProblemFilter] = Seq(
  )
  val Interfaces: Seq[ProblemFilter] = Seq(
  )

  val StdlibBootstrappedBackwards: Map[String, Seq[ProblemFilter]] = Map(
    "2.13.10" -> {
      Seq(
        // Files that are not compiled in the bootstrapped library
        ProblemFilters.exclude[MissingClassProblem]("scala.AnyVal"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Unit.this"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Boolean.this"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Byte.this"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Short.this"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Int.this"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Long.this"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Float.this"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Double.this"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.Char.this"),


        // Scala language features
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.language.<clinit>"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.language#experimental.<clinit>"),
        ProblemFilters.exclude[FinalClassProblem]("scala.language$experimental$"),
        ProblemFilters.exclude[FinalClassProblem]("scala.languageFeature$*$"),

        // trait $init$
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.*.$init$"),

        // Value class extension methods
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.*$extension"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.*$extension"),

        // Companion module class
        ProblemFilters.exclude[FinalClassProblem]("scala.*$"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.*$"),

        // Tuples
        ProblemFilters.exclude[FinalClassProblem]("scala.Tuple1"),
        ProblemFilters.exclude[FinalClassProblem]("scala.Tuple2"),
        ProblemFilters.exclude[MissingFieldProblem]("scala.Tuple*._*"), // Tuple1._1, Tuple2._1, Tuple2._2

        // Scala 2 intrinsic macros
        ProblemFilters.exclude[FinalMethodProblem]("scala.StringContext.s"),

        // scala.math.Ordering.tryCompare
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.*.tryCompare"),

        // Scala 2 specialization
        ProblemFilters.exclude[MissingClassProblem]("scala.*$sp"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.*$sp"),
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.*#*#sp.$init$"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.collection.DoubleStepper"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.collection.immutable.DoubleVectorStepper"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.collection.immutable.IntVectorStepper"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.collection.immutable.LongVectorStepper"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.collection.IntStepper"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.collection.LongStepper"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.jdk.DoubleAccumulator"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.jdk.FunctionWrappers$*"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.jdk.IntAccumulator"),
        ProblemFilters.exclude[MissingTypesProblem]("scala.jdk.LongAccumulator"),
        ProblemFilters.exclude[FinalClassProblem]("scala.collection.ArrayOps$ReverseIterator"),

        // other
        ProblemFilters.exclude[FinalMethodProblem]("scala.Enumeration.ValueOrdering"),
        ProblemFilters.exclude[FinalMethodProblem]("scala.Enumeration.ValueSet"),
        ProblemFilters.exclude[FinalMethodProblem]("scala.io.Source.NoPositioner"),
        ProblemFilters.exclude[FinalMethodProblem]("scala.io.Source.RelaxedPosition"),
        ProblemFilters.exclude[FinalMethodProblem]("scala.io.Source.RelaxedPositioner"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.convert.JavaCollectionWrappers#*.empty"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.immutable.RedBlackTree#EqualsIterator.nextResult"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.immutable.SortedMapOps.coll"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.immutable.TreeMap.empty"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.immutable.TreeMap.fromSpecific"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.mutable.ArrayBuilder#ofUnit.addAll"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.mutable.LinkedHashMap.newBuilder"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.mutable.LinkedHashSet.newBuilder"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.mutable.TreeMap.empty"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.mutable.TreeMap.fromSpecific"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.reflect.ManifestFactory#NothingManifest.newArray"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.reflect.ManifestFactory#NullManifest.newArray"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.StringContext.unapplySeq"),
        ProblemFilters.exclude[MissingFieldProblem]("scala.collection.ArrayOps#ReverseIterator.xs"),
        ProblemFilters.exclude[MissingFieldProblem]("scala.runtime.NonLocalReturnControl.value"),
        ProblemFilters.exclude[ReversedMissingMethodProblem]("scala.collection.immutable.SortedMapOps.coll"),
      ) ++
      Seq( // DirectMissingMethodProblem
        "scala.collection.convert.JavaCollectionWrappers#*.iterableFactory", "scala.collection.convert.JavaCollectionWrappers#*.mapFactory", "scala.collection.convert.JavaCollectionWrappers#IteratorWrapper.remove",
        "scala.collection.immutable.ArraySeq#*.elemTag",
        "scala.collection.immutable.BitSet.bitSetFactory",
        "scala.collection.immutable.HashCollisionSetNode.copy",
        "scala.collection.immutable.MapKeyValueTupleHashIterator.next",
        "scala.collection.immutable.TreeSet.sortedIterableFactory",
        "scala.collection.LinearSeqIterator#LazyCell.this",
        "scala.collection.mutable.AnyRefMap#ToBuildFrom.newBuilder",
        "scala.collection.mutable.ArraySeq#*.elemTag",
        "scala.collection.mutable.BitSet.bitSetFactory",
        "scala.collection.mutable.LinkedHashMap.newBuilder", "scala.collection.mutable.LinkedHashSet.newBuilder",
        "scala.collection.mutable.LongMap#ToBuildFrom.newBuilder",
        "scala.collection.mutable.PriorityQueue#ResizableArrayAccess.this",
        "scala.collection.mutable.TreeMap.sortedMapFactory",
        "scala.collection.StringView.andThen", "scala.collection.StringView.compose",
        "scala.collection.View#*.iterator",
        "scala.concurrent.BatchingExecutor#AbstractBatch.this",
        "scala.concurrent.Channel#LinkedList.this",
        "scala.concurrent.duration.Deadline.apply", "scala.concurrent.duration.Deadline.copy", "scala.concurrent.duration.Deadline.copy$default$1", "scala.concurrent.duration.FiniteDuration.unary_-",
        "scala.Enumeration#ValueOrdering.this",
        "scala.io.Source#RelaxedPosition.this",
        "scala.math.BigDecimal.underlying",
        "scala.PartialFunction#OrElse.andThen", "scala.PartialFunction#OrElse.orElse",
        "scala.runtime.Rich*.num", "scala.runtime.Rich*.ord",
        "scala.ScalaReflectionException.andThen", "scala.ScalaReflectionException.compose",
        "scala.UninitializedFieldError.andThen", "scala.UninitializedFieldError.compose",
        "scala.util.Properties.<clinit>",
        "scala.util.Sorting.scala$util$Sorting$$mergeSort$default$5",
      ).map(ProblemFilters.exclude[DirectMissingMethodProblem])
    }
  )

  val StdlibBootstrappedForward: Map[String, Seq[ProblemFilter]] = Map(
    "2.13.10" -> {
      Seq(
        // Scala language features
        ProblemFilters.exclude[FinalClassProblem]("scala.languageFeature$*$"),
        ProblemFilters.exclude[MissingFieldProblem]("scala.language.experimental"),
        ProblemFilters.exclude[MissingFieldProblem]("scala.languageFeature*"),

        // https://github.com/scala/scala/blob/v2.13.10/src/library/scala/collection/immutable/Range.scala#LL155C1-L156C1
        // Issue #17519: we do not set final on the default methods of final copy method.
        ProblemFilters.exclude[FinalMethodProblem]("scala.collection.immutable.Range.copy$default$*"),

        // Value class extension methods
        ProblemFilters.exclude[DirectMissingMethodProblem]("scala.*$extension"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.*$extension"),

        // Companion module class: Missing type java.io.Serializable
        ProblemFilters.exclude[MissingTypesProblem]("scala.*$"),

        // abstract method elemTag()scala.reflect.ClassTag in class scala.collection.mutable.ArraySeq does not have a correspondent in other version
        ProblemFilters.exclude[DirectAbstractMethodProblem]("scala.collection.immutable.ArraySeq.elemTag"),
        ProblemFilters.exclude[DirectAbstractMethodProblem]("scala.collection.mutable.ArraySeq.elemTag"),

        // Non-categorized
        ProblemFilters.exclude[IncompatibleMethTypeProblem]("scala.collection.mutable.ArrayBuilder#ofUnit.addAll"),

        // Non-categorized
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.convert.JavaCollectionWrappers#JConcurrentMapWrapper.empty"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.convert.JavaCollectionWrappers#JMapWrapper.empty"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.convert.JavaCollectionWrappers#JPropertiesWrapper.empty"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.immutable.RedBlackTree#EqualsIterator.nextResult"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.immutable.SortedMapOps.coll"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.mutable.LinkedHashMap.newBuilder"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.collection.mutable.LinkedHashSet.newBuilder"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.reflect.ManifestFactory#NothingManifest.newArray"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.reflect.ManifestFactory#NullManifest.newArray"),
        ProblemFilters.exclude[IncompatibleResultTypeProblem]("scala.StringContext.unapplySeq"),

        // the type hierarchy of class scala.Array is different in other version. Missing types {java.io.Serializable,java.lang.Cloneable}
        ProblemFilters.exclude[MissingTypesProblem]("scala.Array"),

        // abstract method coll()scala.collection.immutable.SortedMapOps in interface scala.collection.immutable.SortedMapOps is present only in other version
        ProblemFilters.exclude[ReversedMissingMethodProblem]("scala.collection.immutable.SortedMapOps.coll"),
      ) ++
      Seq( // DirectMissingMethodProblem
        "scala.<:<.antisymm", "scala.<:<.refl",
        "scala.collection.BitSet.ordMsg", "scala.collection.BitSet.zipOrdMsg",
        "scala.collection.BitSetOps.computeWordForFilter", "scala.collection.BitSetOps.LogWL", "scala.collection.BitSetOps.MaxSize", "scala.collection.BitSetOps.updateArray", "scala.collection.BitSetOps.WordLength",
        "scala.collection.convert.StreamExtensions#AccumulatorFactoryInfo.*AccumulatorFactoryInfo", "scala.collection.convert.StreamExtensions#StreamShape.*StreamShape", "scala.collection.convert.StreamExtensions#StreamUnboxer.*StreamUnboxer",
        "scala.collection.immutable.List.partialNotApplied",
        "scala.collection.immutable.ListSet.emptyInstance",
        "scala.collection.immutable.Nil.andThen", "scala.collection.immutable.Nil.collectionClassName", "scala.collection.immutable.Nil.empty", "scala.collection.immutable.Nil.view",
        "scala.collection.immutable.NumericRange.defaultOrdering",
        "scala.collection.immutable.Set.emptyInstance",
        "scala.collection.immutable.Stream.collectedTail", "scala.collection.immutable.Stream.filteredTail",
        "scala.collection.immutable.TreeSeqMap#Ordering#Bin.apply", "scala.collection.immutable.TreeSeqMap#Ordering#Bin.unapply", "scala.collection.immutable.TreeSeqMap#Ordering#Iterator.empty", "scala.collection.immutable.TreeSeqMap#Ordering#Iterator.Empty", "scala.collection.immutable.TreeSeqMap#Ordering#Tip.apply", "scala.collection.immutable.TreeSeqMap#Ordering#Tip.unapply",
        "scala.collection.immutable.Vector.fillSparse",
        "scala.collection.IterableOnce.checkArraySizeWithinVMLimit",
        "scala.collection.IterableOnce.copyElemsToArray", "scala.collection.IterableOnce.copyElemsToArray$default$3", "scala.collection.IterableOnce.copyElemsToArray$default$4",
        "scala.collection.IterableOnce.elemsToCopyToArray",
        "scala.collection.LinearSeqIterator#LazyCell.this",
        "scala.collection.mutable.ArrayDeque.alloc", "scala.collection.mutable.ArrayDeque.end_=", "scala.collection.mutable.ArrayDeque.end", "scala.collection.mutable.ArrayDeque.StableSize", "scala.collection.mutable.ArrayDeque.start_=", "scala.collection.mutable.ArrayDeque.start",
        "scala.collection.mutable.CollisionProofHashMap.ordMsg",
        "scala.collection.mutable.PriorityQueue#ResizableArrayAccess.this",
        "scala.collection.mutable.RedBlackTree#Node.apply", "scala.collection.mutable.RedBlackTree#Node.leaf", "scala.collection.mutable.RedBlackTree#Node.unapply", "scala.collection.mutable.RedBlackTree#Tree.empty",
        "scala.collection.mutable.UnrolledBuffer.unrolledlength", "scala.collection.mutable.UnrolledBuffer#Unrolled.<init>$default$4",
        "scala.collection.Searching#Found.apply", "scala.collection.Searching#Found.unapply",
        "scala.collection.Searching#InsertionPoint.apply", "scala.collection.Searching#InsertionPoint.unapply",
        "scala.collection.SortedMapFactoryDefaults.empty", "scala.collection.SortedMapFactoryDefaults.fromSpecific",
        "scala.collection.SortedMapOps.ordMsg", "scala.collection.SortedSetOps.ordMsg",
        "scala.collection.SortedSetOps.zipOrdMsg",
        "scala.collection.Stepper.throwNSEE",
        "scala.collection.View.dropRightIterator", "scala.collection.View.takeRightIterator",
        "scala.collection.View#Filter.apply",
        "scala.concurrent.BatchingExecutor#AbstractBatch.this",
        "scala.concurrent.Channel#LinkedList.this",
        "scala.concurrent.ExecutionContext.opportunistic",
        "scala.concurrent.Future.addToBuilderFun", "scala.concurrent.Future.collectFailed", "scala.concurrent.Future.failedFailureFuture", "scala.concurrent.Future.failedFun", "scala.concurrent.Future.filterFailure", "scala.concurrent.Future.id", "scala.concurrent.Future.recoverWithFailed", "scala.concurrent.Future.recoverWithFailedMarker", "scala.concurrent.Future.toBoxed", "scala.concurrent.Future.zipWithTuple2Fun",
        "scala.Enumeration#ValueOrdering.this",
        "scala.io.Source#RelaxedPosition.this",
        "scala.jdk.Accumulator#AccumulatorFactoryShape.anyAccumulatorFactoryShape", "scala.jdk.Accumulator#AccumulatorFactoryShape.doubleAccumulatorFactoryShape", "scala.jdk.Accumulator#AccumulatorFactoryShape.intAccumulatorFactoryShape", "scala.jdk.Accumulator#AccumulatorFactoryShape.jDoubleAccumulatorFactoryShape", "scala.jdk.Accumulator#AccumulatorFactoryShape.jIntegerAccumulatorFactoryShape", "scala.jdk.Accumulator#AccumulatorFactoryShape.jLongAccumulatorFactoryShape", "scala.jdk.Accumulator#AccumulatorFactoryShape.longAccumulatorFactoryShape",
        "scala.jdk.FunctionWrappers#*",
        "scala.math.Ordering.tryCompare",
        "scala.PartialFunction.unlifted",
        "scala.sys.process.BasicIO.connectNoOp", "scala.sys.process.BasicIO.connectToStdIn",
        "scala.sys.process.Process.Future",
        "scala.sys.process.Process.Spawn",
        "scala.util.control.Exception#Catch.<init>$default$2", "scala.util.control.Exception#Catch.<init>$default$3",
        "scala.util.control.TailCalls#Call.apply", "scala.util.control.TailCalls#Call.unapply", "scala.util.control.TailCalls#Cont.apply", "scala.util.control.TailCalls#Cont.unapply", "scala.util.control.TailCalls#Done.apply", "scala.util.control.TailCalls#Done.unapply",
        "scala.util.Either#LeftProjection.apply", "scala.util.Either#LeftProjection.unapply", "scala.util.Either#RightProjection.apply", "scala.util.Either#RightProjection.unapply",
        "scala.util.matching.Regex#Match.unapply",
        "scala.util.Properties.coloredOutputEnabled",
        "scala.util.Properties.isAvian",
        "scala.util.Properties.versionFor",
      ).map(ProblemFilters.exclude[DirectMissingMethodProblem]) ++
      Seq( // MissingFieldProblem: static field ... in object ... does not have a correspondent in other version
        "scala.Array.UnapplySeqWrapper",
        "scala.collection.concurrent.TrieMap.RemovalPolicy",
        "scala.collection.convert.StreamExtensions.AccumulatorFactoryInfo", "scala.collection.convert.StreamExtensions.StreamShape", "scala.collection.convert.StreamExtensions.StreamUnboxer",
        "scala.collection.immutable.IntMap.Bin", "scala.collection.immutable.IntMap.Nil", "scala.collection.immutable.IntMap.Tip",
        "scala.collection.immutable.LazyList.#::", "scala.collection.immutable.LazyList.cons", "scala.collection.immutable.LazyList.Deferrer", "scala.collection.immutable.LazyList#State.Empty",
        "scala.collection.immutable.LongMap.Bin", "scala.collection.immutable.LongMap.Nil", "scala.collection.immutable.LongMap.Tip",
        "scala.collection.immutable.Range.BigDecimal", "scala.collection.immutable.Range.BigInt", "scala.collection.immutable.Range.Int", "scala.collection.immutable.Range.Long", "scala.collection.immutable.Range.Partial",
        "scala.collection.immutable.Stream.#::", "scala.collection.immutable.Stream.cons", "scala.collection.immutable.Stream.Deferrer", "scala.collection.immutable.Stream.Empty",
        "scala.collection.immutable.TreeSeqMap.OrderBy", "scala.collection.immutable.TreeSeqMap.Ordering", "scala.collection.immutable.TreeSeqMap#OrderBy.Insertion", "scala.collection.immutable.TreeSeqMap#OrderBy.Modification",
        "scala.collection.immutable.VectorMap.Tombstone",
        "scala.collection.immutable.WrappedString.UnwrapOp",
        "scala.collection.IterableOps.SizeCompareOps",
        "scala.collection.mutable.UnrolledBuffer.Unrolled",
        "scala.collection.package.:+", "scala.collection.package.+:",
        "scala.collection.Searching.Found", "scala.collection.Searching.InsertionPoint", "scala.collection.Searching.SearchImpl",
        "scala.collection.SeqFactory.UnapplySeqWrapper",
        "scala.collection.StepperShape.Shape",
        "scala.collection.View.Empty", "scala.collection.View.Filter",
        "scala.concurrent.duration.Deadline.DeadlineIsOrdered", "scala.concurrent.duration.Duration.DurationIsOrdered",
        "scala.concurrent.duration.DurationConversions.fromNowConvert", "scala.concurrent.duration.DurationConversions.spanConvert",
        "scala.concurrent.duration.FiniteDuration.FiniteDurationIsOrdered",
        "scala.concurrent.duration.package.DoubleMult", "scala.concurrent.duration.package.DurationDouble", "scala.concurrent.duration.package.DurationInt", "scala.concurrent.duration.package.DurationLong", "scala.concurrent.duration.package.fromNow", "scala.concurrent.duration.package.IntMult", "scala.concurrent.duration.package.LongMult", "scala.concurrent.duration.package.span",
        "scala.concurrent.ExecutionContext.Implicits", "scala.concurrent.ExecutionContext.parasitic",
        "scala.concurrent.Future.never",
        "scala.Function1.UnliftOps",
        "scala.jdk.Accumulator.AccumulatorFactoryShape",
        "scala.jdk.DurationConverters.JavaDurationOps", "scala.jdk.DurationConverters.ScalaDurationOps",
        "scala.jdk.FunctionWrappers.*",
        "scala.jdk.FutureConverters.CompletionStageOps", "scala.jdk.FutureConverters.FutureOps",
        "scala.jdk.OptionConverters.RichOption", "scala.jdk.OptionConverters.RichOptional", "scala.jdk.OptionConverters.RichOptionalDouble", "scala.jdk.OptionConverters.RichOptionalInt", "scala.jdk.OptionConverters.RichOptionalLong",
        "scala.math.BigDecimal.RoundingMode",
        "scala.math.Equiv.BigDecimal", "scala.math.Equiv.BigInt", "scala.math.Equiv.Boolean", "scala.math.Equiv.Byte", "scala.math.Equiv.Char", "scala.math.Equiv.DeprecatedDoubleEquiv", "scala.math.Equiv.DeprecatedFloatEquiv", "scala.math.Equiv.Double", "scala.math.Equiv.Float", "scala.math.Equiv.Implicits", "scala.math.Equiv.Int", "scala.math.Equiv.Long", "scala.math.Equiv.Short", "scala.math.Equiv.String", "scala.math.Equiv.Symbol", "scala.math.Equiv.Unit",
        "scala.math.Equiv#Double.IeeeEquiv", "scala.math.Equiv#Double.StrictEquiv", "scala.math.Equiv#Float.IeeeEquiv", "scala.math.Equiv#Float.StrictEquiv",
        "scala.math.Fractional.Implicits",
        "scala.math.Integral.Implicits",
        "scala.math.Numeric.BigDecimalAsIfIntegral", "scala.math.Numeric.BigDecimalIsFractional", "scala.math.Numeric.BigIntIsIntegral", "scala.math.Numeric.ByteIsIntegral", "scala.math.Numeric.CharIsIntegral", "scala.math.Numeric.DoubleIsFractional", "scala.math.Numeric.FloatIsFractional", "scala.math.Numeric.Implicits", "scala.math.Numeric.IntIsIntegral", "scala.math.Numeric.LongIsIntegral", "scala.math.Numeric.ShortIsIntegral",
        "scala.math.Ordering.BigDecimal",
        "scala.math.Ordering.BigInt", "scala.math.Ordering.Boolean", "scala.math.Ordering.Byte", "scala.math.Ordering.Char", "scala.math.Ordering.DeprecatedDoubleOrdering", "scala.math.Ordering.DeprecatedFloatOrdering", "scala.math.Ordering.Double", "scala.math.Ordering.Float", "scala.math.Ordering.Implicits", "scala.math.Ordering.Int", "scala.math.Ordering.Long", "scala.math.Ordering.Short", "scala.math.Ordering.String", "scala.math.Ordering.Symbol", "scala.math.Ordering.Unit",
        "scala.math.Ordering#Double.IeeeOrdering", "scala.math.Ordering#Double.TotalOrdering",
        "scala.math.Ordering#Float.IeeeOrdering", "scala.math.Ordering#Float.TotalOrdering",
        "scala.package.#::",
        "scala.PartialFunction.ElementWiseExtractor",
        "scala.Predef.any2stringadd",
        "scala.Predef.ArrowAssoc", "scala.Predef.Ensuring", "scala.Predef.StringFormat",
        "scala.runtime.Tuple2Zipped.Ops", "scala.runtime.Tuple3Zipped.Ops",
        "scala.sys.process.BasicIO.LazilyListed", "scala.sys.process.BasicIO.Streamed", "scala.sys.process.BasicIO.Uncloseable",
        "scala.sys.Prop.DoubleProp", "scala.sys.Prop.FileProp", "scala.sys.Prop.IntProp", "scala.sys.Prop.StringProp",
        "scala.util.control.Exception.Catch",
        "scala.util.control.TailCalls.Call", "scala.util.control.TailCalls.Cont", "scala.util.control.TailCalls.Done",
        "scala.util.Either.LeftProjection", "scala.util.Either.MergeableEither", "scala.util.Either.RightProjection",
        "scala.util.matching.Regex.Groups", "scala.util.matching.Regex.Match",
        "scala.util.package.chaining",
        "scala.util.Using.Manager", "scala.util.Using.Releasable", "scala.util.Using#Releasable.AutoCloseableIsReleasable",
      ).map(ProblemFilters.exclude[MissingFieldProblem])
    }
  )
}
