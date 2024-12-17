import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

object JoinListObject {

  // helper funtions
  def max(x: BigInt, y: BigInt) = if x >= y then x else y
  def abs(x: BigInt) = if BigInt(0) > x then -x else x

  // JoinList[T]
  sealed abstract class JoinList[T]
  // Add one case for empty list
  case class Empty[T]() extends JoinList[T]
  // Single element
  case class Single[T](value: T) extends JoinList[T]
  // Join element
  case class Join[T](left: JoinList[T], right: JoinList[T]) extends JoinList[T] {
    require(
      left != Empty[T]() && right != Empty[T]() // as define in the paper, left and right cannot be empty
    )
  }

  // construct the special operations for JoinList (as it is a tree)
  extension[T](jl: JoinList[T]) {
    def height: BigInt = {
      // Calculate the hight of a tree, empty has hight 0
      jl match {
        case Empty() => BigInt(0)
        case Single(x) => BigInt(1)
        case Join(l, r) => max(l.height, r.height) + BigInt(1)
      }
    }.ensuring(_ >= BigInt(0)) // height must >= 0

    def isBalanced: Boolean = {
      jl match {
        case Join(l, r) => BigInt(-1) <= l.height - r.height && l.height - r.height <= BigInt(1) && l.isBalanced && r.isBalanced // both child are balanced, constructor ensured the hight differences
        case _ => true // true for empty and single node
      }
    }
  }

  // Proof for tree properties
  // p1: a JoinList with element has at least size 1
  def sizeForNonEmpty[T](jl: JoinList[T]): Unit = {
    require(!jl.isEmpty)
    jl match {
      case Single(x) => {
        assert(jl.size == BigInt(1))
        ()
      }
      case Join(l, r) => {
        sizeForNonEmpty(l)
        sizeForNonEmpty(r)
        assert(jl.size >= BigInt(1))
        ()
      }
    }
  }.ensuring(jl.size >= BigInt(1))



  // extend the following basic list functions
  extension[T](jl: JoinList[T]) {
    def toList: List[T] = {
      // Turn a JoinList to a stainless List
      jl match {
        case Empty() => Nil[T]()
        case Single(x) => Cons(x, Nil[T]())
        case Join(l, r) => l.toList ++ r.toList
      }
    }

    def size: BigInt = {
      // Count the number of element in JoinList
      jl match {
        case Empty() => BigInt(0)
        case Single(x) => BigInt(1)
        case Join(l, r) => l.size + r.size
      }
    }.ensuring(_ == jl.toList.size)

    def apply(i: BigInt): T = {
      // Find the i-th element from the JoinList
      require(i >= BigInt(0) && i < jl.size) // i should in range
      jl match {
        // should have no case for empty
        case Single(x) => {
          assert(i == BigInt(0))
          x
        }
        case Join(l, r) => {
          // Stainless list has proved the following in ListSpecs.scala
          ListSpecs.appendIndex(l.toList, r.toList, i)
          if (i < l.size) l.apply(i)
          else r.apply(i - l.size)
        }
      }
    }.ensuring(_ == jl.toList.apply(i))

    def content: Set[T] = {
      // Get the set of elements in the JoinList
      jl match {
        case Empty() => Set[T]()
        case Single(x) => Set(x)
        case Join(l, r) => l.content ++ r.content // set union
      }
    }.ensuring(_ == jl.toList.content)

    def contains(x: T): Boolean = {
      jl match {
        case Empty() => false
        case Single(y) => y == x
        case Join(l, r) => l.contains(x) || r.contains(x) 
      }
    }.ensuring(_ == jl.toList.contains(x))

    def isEmpty: Boolean = {
      // Check if a JoinList is empty
      jl match {
        case Empty() => true
        case _ => false
      }
    }

    def head: T = {
      // Return the first element of the JoinList, only work on non-empty list
      require(!jl.isEmpty)
      sizeForNonEmpty(jl)
      jl.apply(BigInt(0))
    }.ensuring(_ == jl.toList.head)

    // naive concat
    def concat(other: JoinList[T]): JoinList[T] = {
      if (jl.isEmpty) then other
      else if (other.isEmpty) then jl
      else Join(jl, other)
    }.ensuring(_.toList == jl.toList ++ other.toList)
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
  extension[T](jl: JoinList[T]) {

    def ++(other: JoinList[T]): JoinList[T] = {
      require(jl.isBalanced && other.isBalanced)
      decreases(abs(jl.height - other.height))
      if (jl.isEmpty) then other // if self is empty, just return the other 
      else if (other.isEmpty) then jl // if other is empty, just return self
      else {
        // if neither are empty
        if (BigInt(-1) <= jl.height - other.height && jl.height - other.height <= BigInt(1)) {
          // 1. if 2 trees have good heights, just join
          Join(jl, other)
        } else if (BigInt(-1) > jl.height - other.height) {
          // 2. if other is taller
          other match {
            case Join(rl, rr) => {
              ListSpecs.appendAssoc(jl.toList, rl.toList, rr.toList)
              if (rr.height >= rl.height) {
                // since newl.height at most increase 1, would always be balanced
                Join(jl ++ rl, rr)
              } else {
                // otherwise,
                assert(other.height == rl.height + 1)
                rl match {
                  case Join(rll, rlr) => {
                    ListSpecs.appendAssoc(jl.toList, rll.toList, rlr.toList)
                    val newl = jl ++ rll
                    ListSpecs.appendAssoc(newl.toList, rlr.toList, rr.toList)
                    if (newl.height == other.height - 3) {
                      Join(Join(newl, rlr), rr)
                    } else {
                      Join(newl, Join(rlr, rr))
                    }
                  }
                }
              }
            }
          }
        } else {
          // 3. if self is taller -- BigInt(1) < jl.height - other.height
          jl match {
            case Join(ll, lr) => {
              ListSpecs.appendAssoc(ll.toList, lr.toList, other.toList)
              if (ll.height >= lr.height) {
                // Since lr ++ other would at most increase height by 1
                Join(ll, lr ++ other)
              } else {
                lr match {
                  case Join(lrl, lrr) => {
                    ListSpecs.appendAssoc(lrl.toList, lrr.toList, other.toList)
                    val newr = lrr ++ other
                    ListSpecs.appendAssoc(ll.toList, lrl.toList, newr.toList)
                    if (newr.height == jl.height - 3) {
                      Join(ll, Join(lrl, newr))
                    } else {
                      Join(Join(ll, lrl), newr)
                    }
                  }
                }
              }
            }
          }
        }
      }
    }.ensuring( res => (
      res.toList == jl.toList ++ other.toList
      && res.isBalanced // list is balanced and order is preserved
      && res.height <= max(jl.height, other.height) + 1 // result height is bounded
      && res.height >= max(jl.height, other.height)
    ))
  }

  // 4. should have a self-balancing version of Shunt Tree, but don't know how to do it yet, should we have a balanced topology tree? 

  // 5. should we support traditional tree operations like insert(+ proper balancing)? Comparing with conq tree, this seems to be an overkill.

}