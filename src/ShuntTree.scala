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
  // TODO: maybe we need an empty to represent the empty list?

  // (ST. a b)
  sealed abstract class ShuntContext[A, B]
  // H. b
  case class H[A, B](value: B) extends ShuntContext[A, B]
  // L. (ST. a b) (ST. a b) (ST a b)
  case class L[A, B](left: ShuntContext[A, B], middle: ShuntContext[A, B], right:  ShuntTree[A, B]) extends ShuntContext[A, B]
  // R. (ST a b) (ST. a b) (ST. a b)
  case class R[A, B](left: ShuntTree[A, B], middle: ShuntContext[A, B], right:  ShuntContext[A, B]) extends ShuntContext[A, B]
  
  // NOTE:
  // When use Shunt Tree as a underlying data structure of list. The internal nodes in this case should not stand for an element in the list.
  // It is more like the intermedia value of a list homomorphism scheme


  // TODO:
  // 1. need to extend the following basic list functions
  // - toList: List[A]
  // - size: BigInt
  // - height: BigInt
  // - apply(i), get element at index i
  // ...... check the scala docs, maybe there are many others can do ......
  extension[A, B](t: ShuntTree[A, B]) {
    def toList: List[A] = {
      

    }

    def size: BigInt = {

    }

    def height: BigInt = {

    }

    def apply(i: BigInt): A = {

    }
  }
  
  // 2. Should implement and prove common list aggregation operations, including but not limited to
  // - sum
  // - map
  // - zip
  // - ......
  // But maybe, can we prove the thing in a general way? i.e. + only works if it operates on addable data type

  // 3. some more advanced list operations
  // - ++ && ++:
  // foldl, foldr?
  // ...... maybe more in.

  // 4. should have a self-balancing version of Shunt Tree, but don't know how to do it yet, should we have a balanced topology tree? 

  // 5. should we support traditional tree operations like insert(+ proper balancing)? Comparing with conq tree, this seems to be an overkill.

}