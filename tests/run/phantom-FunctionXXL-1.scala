
import Boo._

object Test {

  def main(args: Array[String]) = {
    println(new IntPhantomFunction27().apply(pinky, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26))
  }

}

class IntPhantomFunction27 extends Function27[Pinky, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Int] {
  def apply(p1: Pinky, x1: Int, x2: Int, x3: Int, x4: Int, x5: Int, x6: Int, x7: Int, x8: Int, x9: Int, x10: Int, x11: Int, x12: Int, x13: Int, x14: Int, x15: Int, x16: Int, x17: Int, x18: Int, x19: Int, x20: Int, x21: Int, x22: Int, x23: Int, x24: Int, x25: Int, x26: Int) = 42
}

object Boo extends Phantom {
  type Pinky <: this.Any
  def pinky: Pinky = assume
}
