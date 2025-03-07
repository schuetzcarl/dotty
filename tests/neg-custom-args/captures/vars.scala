class CC
type Cap = CC^

def test(cap1: Cap, cap2: Cap) =
  def f(x: String): String = if cap1 == cap1 then "" else "a"
  var x = f
  val y = x
  val z = () => if x("") == "" then "a" else "b"
  val zc: () ->{cap1} String = z
  val z2 = () => { x = identity }
  val z2c: () -> Unit = z2  // error
  var a: String => String = f

  var b: List[String => String] = Nil
  val u = a  // was error, now ok
  a("")  // was error, now ok
  b.head // was error, now ok

  def scope =
    val cap3: Cap = CC()
    def g(x: String): String = if cap3 == cap3 then "" else "a"
    def h(): String = ""
    a = x => g(x)      // error
    a = g      // error

    b = List(g) // error
    val gc = g
    g

  val s = scope // error (but should be OK, we need to allow poly-captures)
  val sc: String => String = scope // error (but should also be OK)

  def local[T](op: (local: caps.Cap) -> CC^{local} -> T): T = op(caps.cap)(CC())

  local { root => cap3 => // error
    def g(x: String): String = if cap3 == cap3 then "" else "a"
    g
  }

  class Ref:
    var elem: String ->{cap1} String = null

  val r = Ref()
  r.elem = f
  val fc = r.elem