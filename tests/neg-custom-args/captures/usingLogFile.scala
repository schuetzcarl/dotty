import java.io.*
import annotation.capability

object Test1:

  def usingLogFile[T](op: (local: caps.Cap) ?-> FileOutputStream => T): T =
    val logFile = FileOutputStream("log")
    val result = op(logFile)
    logFile.close()
    result

  private val later = usingLogFile { f => () => f.write(0) }  // OK, `f` has global lifetime
  later()

object Test2:

  def usingLogFile[T](op: (local: caps.Cap) ?-> FileOutputStream^{local} => T): T =
    val logFile = FileOutputStream("log")
    val result = op(logFile)
    logFile.close()
    result

  val later = usingLogFile { f => () => f.write(0) } // error
  later()

  class Cell[+T](val x: T)

  private val later2 = usingLogFile { f => Cell(() => f.write(0)) } // error
  later2.x()

  var later3: () => Unit = () => ()
  usingLogFile { f => later3 = () => f.write(0) }  // error
  later3()

  var later4: Cell[() => Unit] = Cell(() => ())
  usingLogFile { f => later4 = Cell(() => f.write(0)) }  // error
  later4.x()

object Test3:

  def usingLogFile[T](op: (local: caps.Cap) ?-> FileOutputStream^{local} => T) =
    val logFile = FileOutputStream("log")
    val result = op(logFile)
    logFile.close()
    result

  val later = usingLogFile { f => () => f.write(0) } // error

object Test4:
  class Logger(f: OutputStream^):
    def log(msg: String): Unit = ???

  def usingFile[T](name: String, op: (local: caps.Cap) ?-> OutputStream^{local} => T): T =
    val f = new FileOutputStream(name)
    val result = op(f)
    f.close()
    result

  val xs: List[Int] = ???
  def good = usingFile("out", f => xs.foreach(x => f.write(x)))
  def fail =
    val later = usingFile("out", f => (y: Int) => xs.foreach(x => f.write(x + y))) // error
    later(1)

  def usingLogger[T](f: OutputStream^, op: (local: caps.Cap) ?-> Logger^{f} => T): T =
    val logger = Logger(f)
    op(logger)

  def test =
    val later = usingFile("logfile",
      usingLogger(_, l => () => l.log("test"))) // ok, since we can widen `l` to `file` instead of to `cap`
    later()
