import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

object Helper {

  // Helper funtions for proof
  def max(x: BigInt, y: BigInt) = if x >= y then x else y

  def abs(x: BigInt) = if BigInt(0) > x then -x else x

  // Helper proof for Stainless list
  def listTailOfConcat[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty)
    if (l2.isEmpty) then {
      ListSpecs.rightUnitAppend(l1)
      ()
    } else {
      l1 match {
        case Cons(x, xs) => {
          assert(l1 == x :: xs) // by definition
          assert(l1 ++ l2 == Cons(x, xs ++ l2)) // by definition
          assert((l1 ++ l2).tail == xs ++ l2)
          assert(l1.tail == xs)
          ()
        }
      }
    }
  }.ensuring((l1 ++ l2).tail == l1.tail ++ l2)

  def listFoldLeftCombine[T, R](l1: List[T], l2: List[T], f: (R, T) => R, basecase: R): Unit = {
    if (l1.isEmpty) then {
      assert(l1 ++ l2 == l2)
      assert(l1.foldLeft(basecase)(f) == basecase)
      ()
    } else if (l2.isEmpty) then {
      assert(l1 ++ l2 == l1)
      assert(l2.foldLeft(l1.foldLeft(basecase)(f))(f) == l1.foldLeft(basecase)(f))
      ()
    } else {
      l1 match {
        case Cons(x, xs) => {
          assert((l1 ++ l2).foldLeft(basecase)(f) == (xs ++ l2).foldLeft(f(basecase, x))(f)) // by definition
          listFoldLeftCombine(xs, l2, f, f(basecase, x))
        }
      }
    }
  }.ensuring((l1 ++ l2).foldLeft(basecase)(f) == l2.foldLeft(l1.foldLeft(basecase)(f))(f))

  // def prependEQ

  def distributiveOfMap[T, R](l1: List[T], l2: List[T], f: T => R): Unit = {
    if (l1.isEmpty) then {
      assert(l1 ++ l2 == l2)
      assert(l1.map(f) == Nil[R]())
      ()
    } else if (l2.isEmpty) then {
      assert(l1 ++ l2 == l1)
      assert(l2.map(f) == Nil[R]())
      ()
    } else {
      l1 match {
        case Cons(x, xs) => {
          assert((l1 ++ l2).map(f) == f(x) :: (xs ++ l2).map(f)) // by definition
          distributiveOfMap(xs, l2, f)
        }
      }
    }
  }.ensuring((l1 ++ l2).map(f) == l1.map(f) ++ l2.map(f))

  // def listHeadWithConcat[T](l1: List[T], l2: List[T]): Unit = {
  //   require(!l1.isEmpty)
  //   l1 match {
  //     case Cons(x, Nil()) => {
  //       assert(l1.tail.isEmpty)
  //       assert(l1.tail ++ l2 == l2)
  //       assert(l1 ++ l2 == x :: l2)
  //       ()
  //     }
  //     case Cons(x, xs) => {
  //       assert(!xs.isEmpty)
  //       val headList = Cons(x, Nil())
  //       assert(l1 == headList ++ xs)
  //       ()
  //     }
  //   }
  // }.ensuring(l1 ++ l2 == l1.head :: (l1.tail ++ l2))

  def listAggregation[T, R](l: List[T], combine: (R, R) => R, convert: T => R): R = {
    // Precondition 1: the combine is associative
    require(forall((x: R, y: R, z: R) => combine(combine(x, y), z) == combine(x, combine(y, z))))
    // Precondition 2: the JoinList is not empty
    require(!l.isEmpty)

    l match {
      case Cons(x, Nil()) => convert(x)
      case Cons(x, xs) => {
        assert(!xs.isEmpty)
        xs.map(convert).foldLeft(convert(x))(combine)
      }
    }
  }.ensuring(
    _ == l.tail.map(convert).foldLeft(convert(l.head))(combine)
  )

  // def listAggregationDistributive[T, R](l1: List[T], l2: List[T], combine: (R, R) => R, convert: T => R): Boolean = {
  //     // Precondition 1: the combine is associative
  //     require(forall((x: R, y: R, z: R) => combine(combine(x, y), z) == combine(x, combine(y, z))))
  //     // Precondition 2: 2 JoinList is not empty
  //     require(!l1.isEmpty && !l2.isEmpty)

  //     l1 match {
  //       case Cons(x, Nil()) => {
  //         // val lagg = Cons(x, l2)
  //         assert(l1 ++ l2 == Cons(x, l2)) // by definition
  //         // val covertedL2 = l2.map(convert)
  //         assert(listAggregation(l1 ++ l2, combine, convert) == l2.map(convert).foldLeft(convert(x))(combine)) // LHS is this
  //         assert(listAggregation(l1, combine, convert) == convert(x))
  //         l2 match {
  //           case Cons(y, Nil()) => {
  //             assert(listAggregation(l2, combine, convert) == convert(y))
  //             assert(l2.map(convert) == Cons(convert(y), Nil[R]()))
  //             assert(l2.map(convert).foldLeft(convert(x))(combine) == combine(convert(x), convert(y)))
  //             true
  //           }
  //           case Cons(y, ys) => {
  //             assert(listAggregation(l2, combine, convert) == ys.map(convert).foldLeft(convert(y))(combine)) // provide above
  //             assert(l2.map(convert) == Cons(convert(y), ys.map(convert))) // by definition
  //             assert(l2.map(convert).foldLeft(convert(x))(combine) == ys.map(convert).foldLeft(combine(convert(x), convert(y)))(combine))
  //             // assert(l2 == Cons(y, Nil()) ++ ys)
  //             assert(l2 == y :: ys)
  //             assert(Cons(y, Nil()) == y :: Nil())
  //             assert(ListSpecs.reverseAppend(Cons(y, Nil()), ys) && ListSpecs.reverseReverse(Cons(y, Nil()) ++ ys))
  //             assert(l2 == Cons(y, Nil()) ++ ys)
  //             listAggregationDistributive(Cons(y, Nil()), ys, combine, convert) // if this holde , RHS = combine(convert(x), combine(convert(y), agg(ys)))
  //             // by association, RHS = combine(combine(convert(x), convert(y)), ys) = ys.foldleft(combine(x, y))(combine)
  //             true
  //           }
  //         }
  //       }
  //       case Cons(x, xs) => {
  //         assert(!xs.isEmpty)
  //         true
  //       }
  //     }
  //     listAggregation(l1 ++ l2, combine, convert) == combine(listAggregation(l1, combine, convert), listAggregation(l2, combine, convert))
  //   }.holds
}