import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

import Helper.*

object TreeObject {

  // Tree[T] -- Normal version
  sealed abstract class Tree[A, B]
  // Add one case for empty tree
  case class Empty[A, B]() extends Tree[A, B]
  // Single leaf
  case class Tip[A, B](value: A) extends Tree[A, B]
  // Internal node
  case class Bin[A, B](value: B, left: Tree[A, B], right: Tree[A, B]) extends Tree[A, B] {
    require(
      left != Empty[A, B]() && right != Empty[A, B]() // as define in the paper, left and right cannot be empty
    )
  }


  // Extend the following basic tree functions
  extension[A, B](tr: Tree[A, B]) {

    def toInOrderList: List[Either[A, B]] = {
      // Turn a Tree to a stainless List of Either type
      tr match {
        case Empty() => List[Either[A, B]]()
        case Tip(v) => List[Either[A, B]](Left(v))
        case Bin(v, l, r) => {
          val left = l.toInOrderList :+ Right(v)
          val right = r.toInOrderList
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
      tr.toInOrderList == other.toInOrderList
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
    }.ensuring(res => res == tr.toInOrderList.size && (res == BigInt(0) || res.mod(2) == BigInt(1)))

    
    def last: Either[A, B] = {
      // Return the value of the right most leaf or the tree
      require(!tr.isEmpty)
      tr match {
        case Tip(v) => Left(v)
        case Bin(v, l, r) => {
          assert(!r.isEmpty)
          assert(listLastOfConcat(l.toInOrderList :+ Right(v), r.toInOrderList) == ())
          r.last
        }
      }
    }.ensuring(res => res.isLeft && res == tr.toInOrderList.last)


    def merge(other: Tree[A, B], newRoot: B): Tree[A, B] = {
      // Merge 2 non empty tree into a new tree with a new intermedia node
      // the new intermedia node is required because the limitation on the size of tree
      require(!tr.isEmpty && !other.isEmpty)
      Bin(newRoot, tr, other)
    }.ensuring(res => (
        res.size == tr.size + other.size + BigInt(1)
        && res.toInOrderList == (tr.toInOrderList :+ Right(newRoot)) ++ other.toInOrderList
      )
    )

    def apply(i: BigInt): Either[A, B] = {
      // Find the i-th element from the tree based on inorder
      require(i >= BigInt(0) && i < tr.size) // i should in range, implies the tree is nonempty
      tr match {
        // should have no case for empty
        case Tip(v) => {
          assert(i == BigInt(0))
          Left(v)
        }
        case Bin(v, l, r) => {
          ListSpecs.appendIndex(l.toInOrderList :+ Right(v), r.toInOrderList, i)
          assert((l.toInOrderList :+ Right(v)).size == l.size + 1)
          if (i < l.size + 1) {
            ListSpecs.snocIndex(l.toInOrderList, Right(v), i)
            if (i < l.size) l.apply(i)
            else Right(v)
          }
          else r.apply(i - l.size - BigInt(1))
        }
      }
    }.ensuring(_ == tr.toInOrderList.apply(i))

  }

  extension[A, B](l: List[Either[A, B]]) {
    def caseMap[C, D](lf: A => C, rf: B => D): List[Either[C, D]] = {
      l match {
        case Nil() => Nil()
        case Cons(x, xs) => {
          x match {
            case Left(v) => Cons(Left(lf(v)), xs.caseMap(lf, rf))
            case Right(v) => Cons(Right(rf(v)), xs.caseMap(lf, rf))
          }
        }
      }
    }.ensuring(_.size == l.size)
  }

  def caseMapDistributive[A, B, C, D](l1: List[Either[A, B]], l2: List[Either[A, B]], lf: A => C, rf: B => D): Boolean = {
    if (l1.isEmpty || l2.isEmpty) then true
    else {
      l1 match {
        case Cons(x, xs) => {
          assert(l1 ++ l2 == Cons(x, xs ++ l2))
          // prependEqualListContact(xs ++ l2, x)
          x match {
            case Left(v) => {
              assert((l1 ++ l2).caseMap(lf, rf) == Left(lf(v)) :: (xs ++ l2).caseMap(lf, rf)) // by definition
              assert(l1.caseMap(lf, rf) == Left(lf(v)) :: xs.caseMap(lf, rf))
              assert(l1.caseMap(lf, rf) ++ l2.caseMap(lf, rf) == Left(lf(v)) :: (xs.caseMap(lf, rf) ++ l2.caseMap(lf, rf)))
              caseMapDistributive(xs, l2, lf, rf)
            }
            case Right(v) => {
              assert((l1 ++ l2).caseMap(lf, rf) == Right(rf(v)) :: (xs ++ l2).caseMap(lf, rf)) // by definition
              assert(l1.caseMap(lf, rf) == Right(rf(v)) :: xs.caseMap(lf, rf))
              assert(l1.caseMap(lf, rf) ++ l2.caseMap(lf, rf) == Right(rf(v)) :: (xs.caseMap(lf, rf) ++ l2.caseMap(lf, rf)))
              caseMapDistributive(xs, l2, lf, rf)
            }
          }
        }
      }
    } 
    (l1 ++ l2).caseMap(lf, rf) == l1.caseMap(lf, rf) ++ l2.caseMap(lf, rf)
  }.holds

  extension[A, B](tr: Tree[A, B]) {
    def map[C, D](lf: A => C, rf: B => D): Tree[C, D] = {
      tr match {
        case Empty() => Empty[C, D]()
        case Tip(v) => Tip(lf(v))
        case Bin(v, l, r) => {
          val newl = l.map(lf, rf) // newl.toInOrderList == l.toInOrderList.caseMap(lf, rf)
          val newr = r.map(lf, rf) // newr.toInOrderList == r.toInOrderList.caseMap(lf, rf)
          val newv = rf(v)
          
          assert(tr.toInOrderList == (l.toInOrderList :+ Right(v)) ++ r.toInOrderList)
          caseMapDistributive(l.toInOrderList :+ Right(v), r.toInOrderList, lf, rf)
          // RHS = (l.toInOrderList :+ Right(v) ++ r.toInOrderList).caseMap(lf, rf)
          // = (l.toInOrderList :+ Right(v)).caseMap(lf, rf) ++ r.toInOrderList.caseMap(lf, rf)
          assert(tr.toInOrderList.caseMap(lf, rf) == (l.toInOrderList :+ Right(v)).caseMap(lf, rf) ++ r.toInOrderList.caseMap(lf, rf))

          
          ListSpecs.snocIsAppend(l.toInOrderList, Right(v))
          caseMapDistributive(l.toInOrderList, List[Either[A, B]](Right(v)), lf, rf)
          // RHS = (l.toInOrderList.caseMap(lf, rf) ++ [Right(v)].caseMap(lf, rf)) ++ r.toInOrderList.caseMap(lf, rf)
          assert(tr.toInOrderList.caseMap(lf, rf) == (l.toInOrderList.caseMap(lf, rf) ++ List[Either[A, B]](Right(v)).caseMap(lf, rf)) ++ r.toInOrderList.caseMap(lf, rf))
          
          assert(newl.toInOrderList == l.toInOrderList.caseMap(lf, rf))
          assert(newr.toInOrderList == r.toInOrderList.caseMap(lf, rf))
          assert(List[Either[C, D]](Right(newv)) == List[Either[A, B]](Right(v)).caseMap(lf, rf))
          // RHS = (newl.toInOrderList ++ Right(newv)) ++ newr.toInOrderList
          assert(tr.toInOrderList.caseMap(lf, rf) == (newl.toInOrderList ++ List[Either[C, D]](Right(newv))) ++ newr.toInOrderList)

          ListSpecs.snocIsAppend(newl.toInOrderList, Right(newv))
          // RHS = Bin(newv, newl, newr) == LHS
          assert(tr.toInOrderList.caseMap(lf, rf) == (newl.toInOrderList :+ Right(newv)) ++ newr.toInOrderList)

          // Return result
          Bin(newv, newl, newr)
        }
      }
    }.ensuring(res => (
        res.size == tr.size
        && 
        res.toInOrderList == tr.toInOrderList.caseMap(lf, rf)
      )
    )
  }

}