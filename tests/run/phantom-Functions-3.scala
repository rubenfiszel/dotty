
import Boo._

object Test {
  def main(args: Array[String]): Unit = {
    foo3(44, pinky, 0.4, pinky, pinky)
  }

  def foo3: (Int, Pinky, Double, Pinky, Pinky) => Unit = new Blinky2
}

class Blinky2 extends Function5[Int, Pinky, Double, Pinky, Pinky, Unit] {
  def apply(p1: Int, p2: Pinky, p3: Double, p4: Pinky, p5: Pinky) = println("Blinky.apply(" + p1 + ")")
}

object Boo extends Phantom {
  type Pinky <: this.Any
  def pinky: Pinky = assume
}
