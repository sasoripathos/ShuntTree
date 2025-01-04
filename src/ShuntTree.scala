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

    //TODO (important): def sum 

    
  }

  // Define Tip and Bin-> TO REVISIT AND CHECK (+formally verify)
  sealed abstract class Tree[A, B]
  case class Tip[A, B](value: A) extends Tree[A, B]
  case class Bin[A, B](left: Tree[A, B], value: B, right: Tree[A, B]) extends Tree[A, B]

  // Define Shunt-> do we even need it?
  case class Shunt[A, B](left: (B, B, A) => B,
                         right: (A, B, B) => B,
                         none: (B, B, B) => B)

  // Implement scs-> check
  def scs[A, B](f: A => B, g: (B, B) => B, shunt: Shunt[A, B])(tree: Tree[A, B]): B = tree match {
    case Tip(a) => f(a)
    case Bin(left, b, right) =>
      val lRes = scs(f, g, shunt)(left)
      val rRes = scs(f, g, shunt)(right)
      shunt.none(lRes, b, rRes)
  }

  // Implement hole and connect-> check
  type Context[A, B] = (Tree[A, B], Tree[A, B]) => Tree[A, B]


  //to revisit
  def hole[A, B](b: B): Context[A, B] = (left, right) => Bin(left, b, right)

  /* 
  def connect[A, B]: Shunt[Tree[A, B], Context[A, B]] = Shunt(
    (l, b, a) => hole(b)(Tip(a), l),
    (a, b, r) => hole(b)(r, Tip(a)),
    (l, b, r) => hole(b)(l, r)
  )
*/
  //to revisit
  def zipTree[A, B, C, D](t1: Tree[A, B], t2: Tree[C, D]): Tree[(A, C), (B, D)] = (t1, t2) match {
    case (Tip(a), Tip(c)) => Tip((a, c))
    case (Bin(l1, b1, r1), Bin(l2, b2, r2)) =>
      Bin(zipTree(l1, l2), (b1, b2), zipTree(r1, r2))
    //-> missing a "case _ =>" ?"
  }


/* 2.1!
Define:
  -Tip and Bin
  -Tree (in which we define a simple sum operation)
  -Shunt
Implement:
  -scs
  -connect
  -hole


  2. agg operations:
    i)sum: In which we present the modified sum operation
  ii)zipTree :: ∀α,α,β,β′.Tree αβ→ Tree α′ β′ → Tree (α,α′) (β,β′)
  zipTree (Tip a) (Tip b) = Tip (a,b)
  zipTree (Bin t1 at2) (Bin u1 bu2) = Bin (zipTree t1 u1) (a,b) (zipTree t2 u2)

 */






   
  
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

