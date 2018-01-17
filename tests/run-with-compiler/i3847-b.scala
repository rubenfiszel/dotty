import dotty.tools.dotc.quoted.Runners._
import scala.quoted._
import scala.reflect.ClassTag

object Arrays {
  implicit def ArrayIsLiftable[T: Liftable](implicit t: Type[T], ct: Expr[ClassTag[T]]): Liftable[Array[List[T]]] = (arr: Array[List[T]]) => '{
    new Array[List[~t]](~(arr.length: Expr[Int]))
    // TODO add elements
  }
}

object Test {
  def main(args: Array[String]): Unit = {
    import Arrays._
    implicit val ct: Expr[ClassTag[Int]] = '(ClassTag.Int)
    val arr: Expr[Array[List[Int]]] = Array[List[Int]](List(1, 2, 3))
    println(arr.show)
  }
}