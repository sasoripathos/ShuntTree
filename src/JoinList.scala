import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

object JoinListObject {

  // helper funtions
  def max(x: BigInt, y: BigInt) = if x >= y then x else y
  // def pow(base: BigInt, exp: BigInt): BigInt = {
  //   require(exp >= 0) // only handle non neg exp
  //   if (exp == BigInt(0)) then BigInt(1)
  //   else base * pow(base, exp - BigInt(1))
  // }

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
      && BigInt(-1) <= left.height - right.height && left.height - right.height <= BigInt(1) // ensure the 2 lists are balanced
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
    }//.ensuring(pow(BigInt(2), _) >= jl.size * BigInt(2)) // 2 ^ (height - 1) >= size of the list since it is balanced

    def isBalanced: Boolean = {
      jl match {
        case Join(l, r) => BigInt(-1) <= l.height - r.height && l.height - r.height <= BigInt(1) && l.isBalanced && r.isBalanced // both child are balanced, constructor ensured the hight differences
        case _ => true // true for empty and single node
      }
    }
  }

  // Proof for tree properties
  // P1. a JoinList is always balanced
  def joinListIsAlwaysBalanced[T](jl: JoinList[T]): Unit = {
    jl match {
      case Join(l, r) => {
        assert(BigInt(-1) <= l.height - r.height && l.height - r.height <= BigInt(1))
        joinListIsAlwaysBalanced(l)
        joinListIsAlwaysBalanced(r)
      } // both child are balanced, constructor ensured the hight differences
      case _ => {
        assert(jl.isBalanced)
        ()
      } // true for empty and single node
    }
  }.ensuring(jl.isBalanced)

  // p2: a JoinList with element has at least size 1
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
        assert(jl.size >= 1)
        ()
      }
    }
  }.ensuring(jl.size >= BigInt(1))

  // P3: a JoinList with element has at least hight 1
  def heightForNonEmpty[T](jl: JoinList[T]): Unit = {
    require(!jl.isEmpty)
    jl match {
      case Single(x) => {
        assert(jl.height == BigInt(1))
        ()
      }
      case Join(l, r) => {
        heightForNonEmpty(l)
        heightForNonEmpty(r)
        assert(jl.height >= BigInt(1))
      }
    }
  }.ensuring(jl.height >= BigInt(1))

  // P4: a JoinList with at least 2 element has at least hight 2
  def heightForAtLeastTwoElement[T](jl: JoinList[T]): Unit = {
    require(jl.size >= BigInt(2))
    assert(jl.isJoin)
    jl match {
      case Join(l, r) => {
        heightForNonEmpty(l)
        heightForNonEmpty(r)
        assert(jl.height >= BigInt(1) + BigInt(1))
        ()
      }
    }
  }.ensuring(jl.height >= BigInt(2))

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

    def isJoin: Boolean = {
      // Check if a JoinList is of shape Join(l, r)
      jl match {
        case Join(l, r) => true
        case _ => false
      }
    }

    def head: T = {
      // Return the first element of the JoinList, only work on non-empty list
      require(!jl.isEmpty)
      sizeForNonEmpty(jl)
      jl.apply(BigInt(0))
    }.ensuring(_ == jl.toList.head)

    // def :+(v: T): JoinList[T] = {
    //   // append an element, return a new (balanced) JoinList
    //   jl match {
    //     case Empty() => Single(v) // this is the only element
    //     case Single(x) => { // 2-element list
    //       assert(Single(v).size == jl.size)
    //       assert(Single(v).size > 0)
    //       Join(jl, Single(v)) 
    //     }
    //     case Join(l, r) => {
    //       val newr = r :+ v // for sure insert to right
    //       assert(l.height >= 1) // non-empty has height >= 1
    //       assert(newr.height <= r.height + BigInt(1) && newr.height >= r.height) // insert would at most result it height + 1, at least the same height
    //       if (BigInt(-1) <= l.height - newr.height && l.height - newr.height <= BigInt(1)) then Join(l, newr)
    //       else {
    //         assert(l.height - newr.height == -2 && newr.height == r.height + 1)
    //         assert(newr.isJoin) // because height > 1
    //         // newr must be a Join
    //         newr match {
    //           case Join(rl, rr) => {
    //             assert(BigInt(-1) <= l.height - rl.height && l.height - rl.height <= BigInt(1))
    //             Join(Join(l, rl), rr)
    //           }
    //         }
    //       }
    //     }
    //   }
    // }.ensuring(_ == jl.toList :+ v)

    // def ::(v: T): JoinList[T] = {
    //   // prepend
      
    // }
    // def tail: JoinList[T] = {
    //   // Return the tail JoinList of the given list only work on non-empty list
    //   require(!jl.isEmpty)
    //   jl match {
    //     case Single(x) => Empty[T]() // Single element has an empty tail
    //     case Join(l, r) => l.tail ++ 
    //   }
    // }
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
  // extension[T](jl: JoinList(T)) {
  //   def ++(other: JoinList[T]): JoinList[T] = {
  //     if (jl.isEmpty) then other // if self is empty, just return the other 
  //     else if (other.isEmpty) then jl // if other is empty, just return self
  //     else {
  //       // if neither are empty, insert the shorter to the taller
  //       if (jl.height >= other.height)
  //     }
  //   }.ensuring(_.toList == jl.toList ++ other.toList)
  // }

  // 4. should have a self-balancing version of Shunt Tree, but don't know how to do it yet, should we have a balanced topology tree? 

  // 5. should we support traditional tree operations like insert(+ proper balancing)? Comparing with conq tree, this seems to be an overkill.

}