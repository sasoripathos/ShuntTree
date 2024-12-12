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
      require(i >= 0 && i < jl.size) // i should in range
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
        case _ false
      }
    }

    def head: T = {
      // Return the first element of the JoinList, only work on non-empty list
      require(!jl.isEmpty)
      jl match {
        case Single(x) => x
        case Join(l, r) => l.head
      }
    }.ensuring(_ == jl.toList.head)

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
  //     jl match {
  //       case Empty() => other
  //       case 
  //     }
  //   } 
  // }

  // 4. should have a self-balancing version of Shunt Tree, but don't know how to do it yet, should we have a balanced topology tree? 

  // 5. should we support traditional tree operations like insert(+ proper balancing)? Comparing with conq tree, this seems to be an overkill.

}