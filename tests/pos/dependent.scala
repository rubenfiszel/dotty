object SimpleEqs {
  val x = 1
  val y: {x} = x
  // val z: {y + 1} = y + 1
}

object Call {
  dependent def foo(x: Int) = 123
  foo(1): { foo(1) }
  foo(1): Int
}

object ITE {
  dependent def foo1(b: Boolean) = {
    val res = if (b)
      1
    else
      2
    identity[{ if (b) 1 else 2 }](res)
    res
  }

  dependent def foo2(b: Boolean): { if (b) 1 else 2 } =
    if (b) 1 else 2

  var b: Boolean = true

  // Beta-reduce
  foo1(true):  { if(true) 1 else 2 }
  foo1(false): { if(false) 1 else 2 }
  foo1(b):     { if (b) 1 else 2 }

  foo1(true):  { 1 }
  foo1(false): { 2 }

  foo2(true):  { if(true) 1 else 2 }
  foo2(false): { if(false) 1 else 2 }
  foo2(b):     { if (b) 1 else 2 }
}

// object Match {
//   dependent def foo1(b: Boolean) = {
//     val res = b match {
//       case true => 1
//       case false => 2
//     }
//     identity[{ b match { case true => 1; case false => 2 } }](res)
//     res
//   }

//   dependent def foo(b: Boolean): Int =
//     b match { case true => 1; case false => 2 }
// }

object Applied {
  dependent def foo1(b: Boolean) = ???
  dependent def foo2(b: Boolean): { foo1(b) } = foo1(b)
  val a: { foo2(true) } = foo2(true)
}

object Approx1 {
  dependent def foo(x: Any): { x } = x
  class A {
    dependent def bar(i: Int): Int = i + 1
    val v: { bar(foo(1)) } = bar(foo(1))
  }

  val a = new A {}
  val b: { a.bar(foo(1)) } = a.v

  var c = new A {}
  val d: { c.bar(foo(1)) } = c.v
}

object Approx2 {
  dependent def foo(x: Any): { x } = x
  class A {
    dependent def bar(i: Int): Int = i + 1
    val v: { foo(bar(1)) } = foo(bar(1))
  }

  val a = new A {}
  val b: { foo(a.bar(1)) }= a.v

  val c = new A {}
  val d: { foo(c.bar(1)) }= c.v
}

object SimpleType {
  type A = { 2 * 2 }
}


object Ignored {
  val a = 1
  dependent def plus(a: Int, b: Int) = a + b

  type Foo = {{
    case class Bar(i: Int)
    println(Bar(1))
    plus(a, a)
  }}

  type Bar = { plus(a, a) }

  val foo: Foo = ???
  identity[Foo](identity[Bar](foo))

  implicitly[Foo =:= Bar]
}

// object AvoidLocalRefs {
//   type Id[T] = T

//   val x = 1
//   def y = { val a: {x} = x; val t: Id[{a + 1}] = a + 1; t }
//   def z: {x + 1} = { val a: {x} = x; val t: Id[{a + 1}] = a + 1; t }

//   { val a = 0; a + 1 }
//   { val a = 0; 1 + a }
// }


// object Bounds {
//   @annotation.implicitNotFound(msg = "Cannot prove that ${B} holds.")
//   sealed abstract class P[B <: Boolean](val b: B)
//   private[this] val prop_singleton = new P[true](true) {}
//   object P {
//     def assume(b: Boolean): P[b.type] = prop_singleton.asInstanceOf[P[b.type]]
//   }

//   def if_(cond: Boolean): (implicit (ev: P[cond.type]) => Unit) => Unit =
//     thn => if (cond) thn(P.assume(cond))


//   // Bounds-checked

//   def index(k: Int)(implicit ev: P[{k >= 0}]): Int = k

//   def run(i: Int) =
//     if_(i >= 0) {
//       index(i)
//     }


//   // Boxed value with a predicate

//   class PredBox[T, B <: Boolean](val v: T)(val p: P[B])
//   object PredBox {
//     def apply[T, B <: Boolean](v: T)(implicit ev: P[B]) = new PredBox[T, B](v)(ev)
//   }

//   def run2(i: Int) =
//     if_(i != 0) {
//       PredBox[Int, {i != 0}](i)
//     }
// }


// object ArithmeticIdentities {
//   type SInt = Int & Singleton

//   class DecomposeHelper[V <: SInt](val v: V) {
//     import DecomposeHelper._
//     def asSumOf[X <: SInt, Y <: SInt](x: X, y: Y)(implicit ev: {v} =:= {x + y}): SumOf[{x}, {y}] = SumOf(x, y)(ev(v))
//   }

//   object DecomposeHelper {
//     /* Axioms */
//     sealed trait Decomposition[V <: SInt]
//     case class SumOf[X <: SInt, Y <: SInt](x: X, y: Y)(val v: {x + y}) extends Decomposition[{v}] {
//       def commuted: SumOf[Y, X] = SumOf(y, x)(v.asInstanceOf[{y + x}])
//     }
//   }

//   implicit def toDecomposeHelper[V <: Int](v: V): DecomposeHelper[v.type] = new DecomposeHelper(v)


//   // Let's "show" that x + 1 == 1 + x

//   val x = 123
//   (x + 1).asSumOf(x, 1).v: {x + 1}
//   (x + 1).asSumOf(x, 1).commuted.v: {1 + x}
// }
