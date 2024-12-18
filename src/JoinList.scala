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
      if (jl.isEmpty) then other
      else if (other.isEmpty) then jl
      else Join(jl, other)
    }.ensuring(_.toList == jl.toList ++ other.toList)
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