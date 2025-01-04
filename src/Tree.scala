import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

import Helper.*

object TreeObject {

  // Tree[T] -- Normal version
  sealed abstract class Tree[A, B]
  // Add one case for empty tree
  case class Empty[A, B]() extends Tree[A, B]
  // Single element
  case class Tip[A, B](value: A) extends Tree[A, B]
  // Join element
  case class Bin[A, B](value: B, left: Tree[A, B], right: Tree[A, B]) extends Tree[A, B] {
    require(
      left != Empty[A, B]() && right != Empty[A, B]() // as define in the paper, left and right cannot be empty
    )
  }


  // extend the following basic list functions, should be the same implementation between simple and balanced version
  extension[A, B](tr: Tree[A, B]) {

    def toPreOrderList: List[Either[A, B]] = {
      // Turn a Tree to a stainless List of Either type
      tr match {
        case Empty() => List[Either[A, B]]()
        case Tip(v) => List[Either[A, B]](Left(v))
        case Bin(v, l, r) => {
          val left = l.toPreOrderList :+ Right(v)
          val right = r.toPreOrderList
          assert(!right.isEmpty)
          assert(listLastOfConcat(left, right) == ())
          left ++ right
        }
      }
    }.ensuring(res => (
        res.size == 0
        || (res.head.isLeft && res.last.isLeft)
      )
    )

    def ==(other: Tree[A, B]): Boolean = {
      tr.toPreOrderList == other.toPreOrderList
    }

    def isEmpty: Boolean = {
      // Check if a JoinList is empty
      tr match {
        case Empty() => true
        case _ => false
      }
    }

    def height: BigInt = {
      // Calculate the hight of a tree, empty has hight 0
      tr match {
        case Empty() => BigInt(0)
        case Tip(v) => BigInt(1)
        case Bin(v, l, r) => BigInt(1) + max(l.height, r.height)
      }
    }.ensuring(_ >= BigInt(0)) // height must >= 0

    def size: BigInt = {
      // Count the number of element in JoinList
      tr match {
        case Empty() => BigInt(0)
        case Tip(_) => BigInt(1)
        case Bin(_, l, r) => BigInt(1) + l.size + r.size
      }
    }.ensuring(_ == tr.toPreOrderList.size)

    
    def last: Either[A, B] = {
      require(!tr.isEmpty)
      tr match {
        case Tip(v) => Left(v)
        case Bin(v, l, r) => {
          assert(!r.isEmpty)
          assert(listLastOfConcat(l.toPreOrderList :+ Right(v), r.toPreOrderList) == ())
          r.last
        }
      }
    }.ensuring(res => res.isLeft && res == tr.toPreOrderList.last)
    

    

    // def apply(i: BigInt): T = {
    //   // Find the i-th element from the JoinList
    //   require(i >= BigInt(0) && i < jl.size) // i should in range
    //   jl match {
    //     // should have no case for empty
    //     case Single(x) => {
    //       assert(i == BigInt(0))
    //       x
    //     }
    //     case Join(l, r) => {
    //       // Stainless list has proved the following in ListSpecs.scala
    //       ListSpecs.appendIndex(l.toList, r.toList, i)
    //       if (i < l.size) l.apply(i)
    //       else r.apply(i - l.size)
    //     }
    //   }
    // }.ensuring(_ == jl.toList.apply(i))

    
    // def contains(x: T): Boolean = {
    //   jl match {
    //     case Empty() => false
    //     case Single(y) => y == x
    //     case Join(l, r) => l.contains(x) || r.contains(x) 
    //   }
    // }.ensuring(_ == jl.toList.contains(x))

    

    // def head: T = {
    //   // Return the first element of the JoinList, only work on non-empty list
    //   require(!jl.isEmpty)
    //   sizeForNonEmpty(jl)
    //   jl.apply(BigInt(0))
    // }.ensuring(_ == jl.toList.head)

    // def tail: JoinList[T] = {
    //   // Return the tail of JoinList, which is the list without the first element
    //   require(!jl.isEmpty)
    //   jl match {
    //     case Single(_) => Empty[T]() // single element, then tail is empty
    //     case Join(l, r) => {
    //       assert(!l.isEmpty)
    //       l match {
    //         case Single(_) => {
    //           assert(l.tail.isEmpty)
    //           ListSpecs.leftUnitAppend(r.toList)
    //           r
    //         }
    //         case Join(ll, lr) => {
    //           sizeForNonEmpty(l)
    //           listTailOfConcat(l.toList, r.toList) // (l ++ r).tail == l.tail + r
    //           l.tail ++ r
    //         }
    //       }
          
    //     }
    //   }
    // }.ensuring(_.toList == jl.toList.tail)

    // def ::(t: T): JoinList[T] = {
    //   // Prepend an element to JoinList
    //   jl match {
    //     case Empty() => Single(t)
    //     case Single(x) => Join(Single(t), jl)
    //     case Join(l, r) => {
    //       val newl = l :: t
    //       assert(newl.toList == Cons(t, l.toList))
    //       ListSpecs.reverseAppend(newl.toList, r.toList)
    //       newl ++ r
    //     }
    //   }
    // }.ensuring(_.toList == t :: jl.toList)
    
    // def :+(t: T): JoinList[T] = {
    //   // Append an element to JoinList
    //   jl match {
    //     case Empty() => Single(t)
    //     case Single(x) => Join(jl, Single(t))
    //     case Join(l, r) => {
    //       ListSpecs.snocAfterAppend(l.toList, r.toList, t)
    //       l ++ (r :+ t)
    //     }
    //   }
    // }.ensuring(_.toList == jl.toList :+ t)

  }

  // // 2. extend common list aggregation operations
  // // - sum
  // // - map
  // // - zip
  // // - ......
  // // But maybe, can we prove the thing in a general way? i.e. + only works if it operates on addable data type
  // extension[T, R](jl: JoinList[T]) {
  //   def foldLeft(z: R)(f: (R, T) => R): R = {
  //     jl match {
  //       case Empty() => z
  //       case Single(x) => f(z, x)
  //       case Join(l, r) => {
  //         listFoldLeftCombine(l.toList, r.toList, f, z)
  //         r.foldLeft(l.foldLeft(z)(f))(f)
  //       }
  //     }
  //   }.ensuring(_ == jl.toList.foldLeft(z)(f))

  //   def foldRight(z: R)(f: (T, R) => R): R = {
  //     jl match {
  //       case Empty() => z
  //       case Single(x) => f(x, z)
  //       case Join(l, r) => {
  //         listFoldRightCombine(l.toList, r.toList, f, z)
  //         l.foldRight(r.foldRight(z)(f))(f)
  //       }
  //     }
  //   }.ensuring(_ == jl.toList.foldRight(z)(f))

  //   def map(f: T => R): JoinList[R] = {
  //     jl match {
  //       case Empty() => Empty[R]()
  //       case Single(x) => Single(f(x))
  //       case Join(l, r) => {
  //         distributiveOfMap(l.toList, r.toList, f)
  //         l.map(f) ++ r.map(f)
  //       }
  //     }
  //   }.ensuring(_.toList == jl.toList.map(f))

  //   // // This aggregation assumes following list homomorphism scheme, only works on non-empty case
  //   // def aggregation(combine: (R, R) => R, convert: T => R): R = {
  //   //   // Precondition 1: the combine is associative
  //   //   require(forall((x: R, y: R, z: R) => combine(combine(x, y), z) == combine(x, combine(y, z))))
  //   //   // Precondition 2: the JoinList is not empty
  //   //   require(!jl.isEmpty)

  //   //   jl match {
  //   //     case Single(x) => convert(x)
  //   //     case Join(l, r) => {
  //   //       // listFoldLeftCombine(l.toList.map(convert), r.toList.map(convert), combine, basecase)
  //   //       assert(!l.isEmpty && !r.isEmpty)
  //   //       assert(l.head == jl.head) // Head of prefix
  //   //       distributiveOfMap(l.toList, r.toList, convert) // (l ++ r).map(convert) == l.map ++ r.map
  //   //       // val resultl = l.aggregation(combine, convert)
  //   //       // val resultr = r.aggregation(combine, convert)
  //   //       // r match {
  //   //       //   case Single(y) => 
  //   //       // }
  //   //       combine(l.aggregation(combine, convert), r.aggregation(combine, convert))
  //   //     }
  //   //   }
  //   // }.ensuring(
  //   //   _ == jl.tail.map(convert).toList.foldLeft(convert(jl.head))(combine)
  //   // )
  // }

  // // 3. some more advanced list operations, different between simple and balanced version
  // // - ++ && ++:
  // // foldl, foldr?
  // // ...... maybe more in.
  // extension[T](jl: JoinList[T]) {
  //   def ++(other: JoinList[T]): JoinList[T] = {
  //     // Implementation of ++
  //     if (jl.isEmpty) then other
  //     else if (other.isEmpty) then jl
  //     else Join(jl, other)
  //   }.ensuring(_.toList == jl.toList ++ other.toList)

  //   // def listCombine(f: (T, T) => T): T = {
  //   //   // Appling a combine function to list

  //   //   // Precondition 1: the combine is associative
  //   //   require(forall((x: T, y: T, z: T) => f(f(x, y), z) == f(x, f(y, z))))
  //   //   // Precondition 2: the JoinList is not empty
  //   //   require(!jl.isEmpty)
  //   //   sizeForNonEmpty(jl)
  //   //   jl match {
  //   //     case Single(x) => x
  //   //     case Join(l, r) => {
  //   //       assert(jl.head == l.head) // head should on left
  //   //       assert(headWithConcat(l.toList, r.toList) == ()) // l ++ r = l.head :: (l.tail ++ r)
  //   //       assert(jl.tail == l.tail ++ r)
  //   //       l match {
  //   //         case Single(y) => {
  //   //           assert(jl.tail == r)
  //   //           assert(l.listCombine(f) == y)
  //   //           assert(l ++ r == (l.tail ++ r) :: y)
  //   //           f(y, r.listCombine(f))
  //   //         }
  //   //         case Join(ll, lr) => {
  //   //           // listFoldLeftCombine(l.toList, r.toList, f)
  //   //           f(l.listCombine(f), r.listCombine(f))
  //   //         }
  //   //       }
  //   //       // 
  //   //       // f(l.listCombine(f), r.listCombine(f))
  //   //     }
  //   //   }
  //   // }.ensuring(_ == jl.tail.foldLeft(jl.head)(f))
  // }

}