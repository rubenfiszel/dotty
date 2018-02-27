object foo{
  val x = List(1,2,3)
  x match {
    case t: List[tt] => t.head.asInstanceOf[tt]
  }
  x match {
    case t: List[type tt] => t.head.asInstanceOf[tt]
  }
}

object bar {

  class C[T <: Seq[_]]

  val x: AnyRef = new C

  x match {
    case x: C[type U] =>
      def x: U = x
      val s: Seq[_] = x
  }
}
