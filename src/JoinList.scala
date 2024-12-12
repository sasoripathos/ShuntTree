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
  case class Join[T](left: JoinList[T], right: JoinList[T]) extends JoinList[T]

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

    def height: BigInt = {
      // JoinList is like tree, height is to calculate the hight of a tree, empty has hight 0
      jl match {
        case Empty() => BigInt(0)
        case Single(x) => BigInt(1)
        case Join(l, r) => max(l.height, r.height) + BigInt(1)
      }
    }//.ensuring(pow(BigInt(2), _) >= jl.size * BigInt(2)) // 2 ^ (height - 1) >= size of the list since it is balanced

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

    // TODO:  check the scala/stainless docs, maybe there are many others can do ......
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