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
  def max(a: BigInt, b: BigInt): BigInt = if (a > b) a else b
  
  extension[A, B](c: ShuntContext[A, B]) {


    def toList: List[A] = {
      c match {
        case H(_) => List()
        case L(left, middle, right) => left.toList ++ middle.toList ++ right.toList
        case R(left, middle, right) => left.toList ++ middle.toList ++ right.toList
      }
    }
    def size: BigInt = {
      c match {
        case H(_) => 0
        case L(left, middle, right) => left.size + middle.size + right.size
        case R(left, middle, right) => left.size + middle.size + right.size
      }
    }
    

  def height: BigInt = {
    c match {
      case H(_) => 0
      case L(left, middle, right) =>
        1 + max(left.height, max(middle.height, right.height))
      case R(left, middle, right) =>
        1 + max(left.height, max(middle.height, right.height))
    }
  }






  }

  extension[A, B](t: ShuntTree[A, B]) {

  
    def toList: List[A] = {
      t match {
        case T(value) => List(value)
        case N(left, middle, right) => left.toList ++ middle.toList ++ right.toList
      }
    }
    def size: BigInt = {
      t match {
        case T(_) => 1
        case N(left, middle, right) => left.size + middle.size + right.size
      }
    }
    def height: BigInt = {
      t match {
        case T(_) => 1
        case N(left, middle, right) =>
          1 + max(left.height, max(middle.height, right.height))
      }
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


