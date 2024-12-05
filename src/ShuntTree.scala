import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

object ShuntTreeObject {

  // ST a b
  sealed abstract class ShuntTree[A, B]
  // T a
  case class T[A, B](value: A) extends ShuntTree[A, B]
  // N (ST a b) (ST. a b) (ST a b)
  case class N[A, B](left: ShuntTree[A, B], middle: ShuntContext[A, B], right: ShuntTree[A, B]) extends ShuntTree[A, B]  

  // (ST. a b)
  sealed abstract class ShuntContext[A, B]
  // H. b
  case class H[A, B](value: B) extends ShuntContext[A, B]
  // L. (ST. a b) (ST. a b) (ST a b)
  case class L[A, B](left: ShuntContext[A, B], middle: ShuntContext[A, B], right:  ShuntTree[A, B]) extends ShuntContext[A, B]
  // R. (ST a b) (ST. a b) (ST. a b)
  case class R[A, B](left: ShuntTree[A, B], middle: ShuntContext[A, B], right:  ShuntContext[A, B]) extends ShuntContext[A, B]
  

}