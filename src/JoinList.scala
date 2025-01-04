import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

import Helper.*

object JoinListObject {

  // JoinList[T] -- Normal version
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


  // extend the following basic list functions, should be the same implementation between simple and balanced version
  extension[T](jl: JoinList[T]) {

    def ==(other: JoinList[T]): Boolean = {
      jl.toList == other.toList
    }
    

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
              //listTailOfConcat(l.toList, r.toList) // (l ++ r).tail == l.tail + r
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
      res.toList.content.subsetOf(jl.toList.content) &&
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

    def slice(from: BigInt, to: BigInt): JoinList[T] = {
      require(0 <= from && from <= to && to <= jl.size)

      jl.drop(from).take(to - from)
    }.ensuring { res =>
      res.toList.content.subsetOf(jl.toList.content) &&
      res.size == (to - from)
    }
    
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

    def foldRight(z: R)(f: (T, R) => R): R = {
      jl match {
        case Empty() => z
        case Single(x) => f(x, z)
        case Join(l, r) => {
          listFoldRightCombine(l.toList, r.toList, f, z)
          l.foldRight(r.foldRight(z)(f))(f)
        }
      }
    }.ensuring(_ == jl.toList.foldRight(z)(f))

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

/*
    def zip(that: JoinList[R]): JoinList[(T, R)] = {
      decreases(jl) // Specifica la misura
      (jl, that) match {
        case (Empty(), _) => 
          Empty[(T, R)]()
        case (_, Empty()) => 
          Empty[(T, R)]()
        case (Single(x), Single(y)) =>
          Single((x, y))
        case (Join(l1, r1), Join(l2, r2)) =>
          val leftZip = l1.zip(l2)
          val rightZip = r1.zip(r2)
          distributiveOfZip(l1.toList, l2.toList)
          distributiveOfZip(r1.toList, r2.toList)
          Join(leftZip, rightZip)
        case (Join(l, r), Single(y)) =>
          val leftZip = l.zip(Single(y))
          val rightZip = r.zip(Single(y))
          distributiveOfZip(l.toList, List(y))
          distributiveOfZip(r.toList, List(y))
          Join(leftZip, rightZip)
        case (Single(x), Join(l, r)) =>
          val leftZip = Single(x).zip(l)
          val rightZip = Single(x).zip(r)
          distributiveOfZip(List(x), l.toList)
          distributiveOfZip(List(x), r.toList)
          Join(leftZip, rightZip)
      }
}.ensuring { res =>
  res.size == (if (jl.size <= that.size) jl.size else that.size) &&
    res.toList == jl.toList.zip(that.toList)
}
    */

  }

  // 3. some more advanced list operations, different between simple and balanced version
  // - ++ && ++:
  // foldl, foldr?
  // ...... maybe more in.
  extension[T](jl: JoinList[T]) {
    def ++(other: JoinList[T]): JoinList[T] = {
      // Implementation of ++
      if (jl.isEmpty) then other
      else if (other.isEmpty) then jl
      else Join(jl, other)
    }.ensuring(_.toList == jl.toList ++ other.toList)

    def --(that: JoinList[T]): JoinList[T] = {
      // Remove all elements of `that` from `jl`
      jl match {
        case Empty() => Empty[T]()
        case Single(x) =>
          if (that.contains(x)) Empty[T]()
          else Single(x)
        case Join(l, r) =>
          val newLeft = l -- that
          val newRight = r -- that
          if (newLeft.isEmpty && newRight.isEmpty) Empty[T]()
          else if (newLeft.isEmpty) newRight
          else if (newRight.isEmpty) newLeft
          else Join(newLeft, newRight)
      }
      //it do not consider element order here!
    }.ensuring { res =>
      res.size <= jl.size && // Ensure the result size is not greater than the original
      res.content == jl.content -- that.content // Ensure the result content matches the set difference
    }
   
    def &(that: JoinList[T]): JoinList[T] = {
      jl match {
        case Empty() => Empty[T]() // Base case: inters with an empty list is empty
        case Single(x) =>
          if (that.contains(x)) Single(x) // If `that` contains the element, include it
          else Empty[T]() // Otherwise, exclude it
        case Join(left, right) =>
          val leftIntersection = left & that // Recursively compute inters for the left subtree
          val rightIntersection = right & that // Recursively compute intersection for the right subtree
          // Combine the results
          if (leftIntersection.isEmpty && rightIntersection.isEmpty) Empty[T]()
          else if (leftIntersection.isEmpty) rightIntersection
          else if (rightIntersection.isEmpty) leftIntersection
          else Join(leftIntersection, rightIntersection)
      }
    }.ensuring { res =>
      res.size <= jl.size && // Result size is not bigger than the original
        res.content.subsetOf(jl.content) && // Result content is a subset of the original jl
        res.content.subsetOf(that.content) // Result content is a subset of the other jl
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

  def joinListAggregation[T](jl: JoinList[T], f: ListAggFunction[T]): T = {
    // Precondition: the JoinList is not empty
    require(!jl.isEmpty)
    decreases(jl)

    jl match {
      case Single(v) => {
        assert(jl.toList == Cons(v, Nil[T]()))
        v
      }
      case Join(l, r) => {
        assert(jl.toList == l.toList ++ r.toList)
        sizeForNonEmpty(l)
        sizeForNonEmpty(r)
        listAggregationDistributive(l.toList, r.toList, f) // rhs == f.execute(listAggregation(l, f), listAggregation(r))
        f.execute(joinListAggregation(l, f), joinListAggregation(r, f))
      }
    }

  }.ensuring(_ == listAggregation(jl.toList, f))

  // def joinListHomomorphism[T, R](agg: ListAggFunction[R], jl: JoinList[T], f: T => R): R = {
  //   val mappedList = jl.map(f)
  //   assert(mappedList == jl.toList.map(f)) // definition by f

  // }.ensuring(_ == listAggregation(jl.toList.map(f), agg))


}