import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

import Helper.*

object BalancedJoinListObject {

  // JoinList[T] -- balanced version

  sealed abstract class JoinList[T]
  // Add one case for empty list
  case class Empty[T]() extends JoinList[T]
  // Single element
  case class Single[T](value: T) extends JoinList[T]
  // Join element
  case class Join[T](left: JoinList[T], right: JoinList[T]) extends JoinList[T] {
    require(
      left != Empty[T]() && right != Empty[T]() // as define in the paper, left and right cannot be empty
      && BigInt(-1) <= left.height - right.height && left.height - right.height <= BigInt(1) // require balanced
      // by recursivly of require(), left and right must also be balanced, proved in isBalanced
    )
  }

  // construct the special operations for balanced JoinList (as it is a tree)
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
        case Join(l, r) => {
          // constructor ensured the hight differences
          assert(BigInt(-1) <= l.height - r.height && l.height - r.height <= BigInt(1))
          // tree is balanced as long as both child are balanced
          l.isBalanced && r.isBalanced
        }
        case _ => true // true for empty and single node
      }
    }.ensuring(_ == true) // A JoinList by definition is always balanced
  }



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

    def tail: JoinList[T] = {
      // Return the tail of JoinList, which is the list without the first element
      require(!jl.isEmpty)
      jl match {
        case Single(_) => Empty[T]() // single element, then tail is empty
        case Join(l, r) => {
          assert(!l.isEmpty)
          l match {
            case Single(_) => {
              assert(l.tail.isEmpty)
              ListSpecs.leftUnitAppend(r.toList)
              r
            }
            case Join(ll, lr) => {
              sizeForNonEmpty(l)
              listTailOfConcat(l.toList, r.toList) // (l ++ r).tail == l.tail + r
              l.tail ++ r
            }
          }
          
        }
      }
    }.ensuring(_.toList == jl.toList.tail)

    

    def ::(t: T): JoinList[T] = {
      // Prepend an element to JoinList
      jl match {
        case Empty() => Single(t)
        case Single(x) => Join(Single(t), jl)
        case Join(l, r) => {
          val newl = l :: t
          assert(newl.toList == Cons(t, l.toList))
          ListSpecs.reverseAppend(newl.toList, r.toList)
          newl ++ r
        }
      }
    }.ensuring(_.toList == t :: jl.toList)

    def :+(t: T): JoinList[T] = {
      // Append an element to JoinList
      jl match {
        case Empty() => Single(t)
        case Single(x) => Join(jl, Single(t))
        case Join(l, r) => {
          ListSpecs.snocAfterAppend(l.toList, r.toList, t)
          l ++ (r :+ t)
        }
      }
    }.ensuring(_.toList == jl.toList :+ t)

    def take(i: BigInt): JoinList[T] = {
    require(i >= 0)

    jl match {
      case Empty() => Empty[T]()
      case Single(x) =>
        if (i <= 0) Empty[T]()
        else Single(x)
      case Join(l, r) =>
        if (i <= l.size) l.take(i)
        else l.++(r.take(i - l.size)) // Combine with balancing using ++
    }
  }.ensuring { res =>
    res.toList.content.subsetOf(jl.toList.content) && // Ensure the content is a subset of the original
    (res.size == (
      if (i <= 0) BigInt(0)
      else if (i >= jl.size) jl.size
      else i
    )) &&
    res.isBalanced // Ensure the result is balanced
  }

    def drop(i: BigInt): JoinList[T] = {
      require(i >= 0)

      jl match {
        case Empty() => Empty[T]()
        case Single(x) =>
          if (i <= 0) Single(x)
          else Empty[T]()
        case Join(l, r) =>
          if (i < l.size) l.drop(i) ++ r // Combine with balancing using ++
          else r.drop(i - l.size)
      }
    }.ensuring { res =>
      res.toList.content.subsetOf(jl.toList.content) && // Ensure the content is a subset of the original
      (res.size == (
        if (i <= 0) jl.size
        else if (i >= jl.size) BigInt(0)
        else jl.size - i
      )) &&
      res.isBalanced // Ensure the result is balanced
    }

    def slice(from: BigInt, to: BigInt): JoinList[T] = {
      require(0 <= from && from <= to && to <= jl.size)

      jl.drop(from).take(to - from) // Combine drop and take
    }.ensuring { res =>
      res.toList.content.subsetOf(jl.toList.content) && // Ensure the content is a subset of the original
      res.size == (to - from) && // Ensure the size matches the slice range
      res.isBalanced // Ensure the result is balanced
    }
/*
    //Take the first `i` elements of a JoinList
    def take(i: BigInt): JoinList[T] = {
      require(i >= 0)

      jl match {
        case Empty() => Empty[T]()
        case Single(x) =>
          if (i <= 0) Empty[T]()
          else Single(x)
        case Join(l, r) =>
          if (i <= l.size) l.take(i)
          else Join(l, r.take(i - l.size))
      }
      /*
    * 1) The content of the result is a subset of the original JoinList's content
     * 2) The size of the result matches the specified conditions:
     * 3) If `i <= 0`, the result size is 0
     * 4) If `i >= jl.size`, the result size equals the size of the original JoinList
     * 5) Otherwise, the result size equals `i`
     * */
    }.ensuring { res =>
      res.toList.content.subsetOf(jl.toList.content) && res.isBalanced &&
      (res.size == (
        if (i <= 0) BigInt(0)
        else if (i >= jl.size) jl.size
        else i
      ))
    }

     //Drop the first `i` elements of a JoinList
    def drop(i: BigInt): JoinList[T] = {
      require(i >= 0)

      jl match {
        case Empty() => Empty[T]()
        case Single(x) =>
          if (i <= 0) Single(x)
          else Empty[T]()
        case Join(l, r) =>
          if (i < l.size) Join(l.drop(i), r)
          else r.drop(i - l.size)
      }

      /* 
     * 1) The content of the result is a subset of the original JoinList's content
     * 2) The size of the result matches the specified conditions:
     * 3) If `i <= 0`, the result size equals the original JoinList size
     * 4) If `i >= jl.size`, the result size is 0
     * 5) Otherwise, the result size equals `jl.size - i`
       */
    }.ensuring { res =>
      res.toList.content.subsetOf(jl.toList.content) &&
      (res.size == (
        if (i <= 0) jl.size
        else if (i >= jl.size) BigInt(0)
        else jl.size - i
      ))
    }
    */


  }
  
  // 2. extend common list aggregation operations
  // - sum
  // - map
  // - zip
  // - ......
  // But maybe, can we prove the thing in a general way? i.e. + only works if it operates on addable data type
  extension[T, R](jl: JoinList[T]) {
    def foldLeft(z: R)(f: (R, T) => R): R = {
      jl match {
        case Empty() => z
        case Single(x) => f(z, x)
        case Join(l, r) => {
          listFoldLeftCombine(l.toList, r.toList, f, z)
          r.foldLeft(l.foldLeft(z)(f))(f)
        }
      }
    }.ensuring(_ == jl.toList.foldLeft(z)(f))

    def map(f: T => R): JoinList[R] = {
      jl match {
        case Empty() => Empty[R]()
        case Single(x) => Single(f(x))
        case Join(l, r) => {
          distributiveOfMap(l.toList, r.toList, f)
          l.map(f) ++ r.map(f)
        }
      }
    }.ensuring(_.toList == jl.toList.map(f))

    // def sum(combine: (R, R) => R, convert: T => R, basecase: R): R = {
    //   jl match {
    //     case Empty() => basecase
    //     case Single(x) => combine(basecase, convert(x))
    //     case Join(l, r) => {
    //       // Unsure about this, maybe try foldl first
    //       r.sum(combine, convert, l.sum(combine, convert, basecase))
    //     }
    //   }
    // }.ensuring(_ == jl.toList.map(convert).foldLeft(basecase)(combine))
  }

  // 3. some more advanced list operations, different between simple and balanced version
  // - ++ && ++:
  // foldl, foldr?
  // ...... maybe more in.
  extension[T](jl: JoinList[T]) {

    def ++(other: JoinList[T]): JoinList[T] = {
      // Prove that: we can concat 2 balanced JoinList and form another balanced Join List whose height grows at most 1
      decreases(abs(jl.height - other.height))
      // Input must have been balanced
      assert(jl.isBalanced && other.isBalanced)
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
      && res.isBalanced // list is balanced and order is preserved, balanced has been proved
      && res.height <= max(jl.height, other.height) + 1 // result height is bounded
      && res.height >= max(jl.height, other.height)
    ))

    def --(other: JoinList[T]): JoinList[T] = {
    jl match {
      case Empty() => Empty[T]()
      case Single(x) =>
        if (other.contains(x)) Empty[T]()
        else Single(x)
      case Join(l, r) =>
        val newLeft = l -- other
        val newRight = r -- other
        if (newLeft.isEmpty && newRight.isEmpty) Empty[T]()
        else if (newLeft.isEmpty) newRight
        else if (newRight.isEmpty) newLeft
        else newLeft.++(newRight)
    }
  }.ensuring { res =>
    res.size <= jl.size && // Ensure the result size is not greater than the original
    res.content == jl.content -- other.content && // Ensure the result content matches the set difference
    res.isBalanced // Ensure the result is balanced
  }

    def &(other: JoinList[T]): JoinList[T] = {
      jl match {
        case Empty() => Empty[T]() // Base case: intersection with an empty list is empty
        case Single(x) =>
          if (other.contains(x)) Single(x) // If `other` contains the element, include it
          else Empty[T]() // Otherwise, exclude it
        case Join(left, right) =>
          val leftIntersection = left & other // Recursively compute intersection for the left subtree
          val rightIntersection = right & other // Recursively compute intersection for the right subtree
          // Combine the results with balancing
          if (leftIntersection.isEmpty && rightIntersection.isEmpty) Empty[T]()
          else if (leftIntersection.isEmpty) rightIntersection
          else if (rightIntersection.isEmpty) leftIntersection
          else leftIntersection.++(rightIntersection)
      }
    }.ensuring { res =>
      res.size <= jl.size && // Result size is not bigger than the original
      res.content.subsetOf(jl.content) && // Result content is a subset of the original jl
      res.content.subsetOf(other.content) && // Result content is a subset of the other jl
      res.isBalanced // Ensure the result is balanced
    }

    

    
  }

  // 4. should have a self-balancing version of Shunt Tree, but don't know how to do it yet, should we have a balanced topology tree? 

  // 5. should we support traditional tree operations like insert(+ proper balancing)? Comparing with conq tree, this seems to be an overkill.



  // ---------- Proof for Join List properties ---------- 

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
}