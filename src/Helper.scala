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

  def listFoldRightCombine[T, R](l1: List[T], l2: List[T], f: (T, R) => R, basecase: R): Unit = {
    if (l1.isEmpty) then {
      assert(l1 ++ l2 == l2)
      assert(l1.foldRight(l2.foldRight(basecase)(f))(f) == l2.foldRight(basecase)(f))
      ()
    } else if (l2.isEmpty) then {
      assert(l1 ++ l2 == l1)
      assert(l2.foldRight(basecase)(f) == basecase)
      ()
    } else {
      l1 match {
        case Cons(x, xs) => {
          assert(l1.foldRight(l2.foldRight(basecase)(f))(f) == f(x, xs.foldRight(l2.foldRight(basecase)(f))(f)))
          assert(l1 ++ l2 == Cons(x, xs ++ l2))
          assert((l1 ++ l2).foldRight(basecase)(f) == f(x, (xs ++ l2).foldRight(basecase)(f)))
          listFoldRightCombine(xs, l2, f, basecase)
        }
      }
    }
  }.ensuring((l1 ++ l2).foldRight(basecase)(f) == l1.foldRight(l2.foldRight(basecase)(f))(f))

  def listLastOfConcat[T](l1: List[T], l2: List[T]): Unit = {
    require(!l2.isEmpty)
    l1 match {
      case Nil() => {
        assert(l1 ++ l2 == l2)
        ()
      }
      case Cons(x, xs) => {
        assert(l1 ++ l2 == Cons(x, xs ++ l2)) // by definition
        assert((l1 ++ l2).last == (xs ++ l2).last)
        listLastOfConcat(xs, l2)
      }
    }
  }.ensuring((l1 ++ l2).last == l2.last)

  // def listFoldLeftWhenAssociative[T](x: T, xs: List[T], f: (T, T) => T, zero: T):Boolean = {
  //   // Precondition: the combine is associative
  //   require(forall((x: T, y: T, z: T) => f(f(x, y), z) == f(x, f(y, z))))

  //   val l = x :: xs
  //   val one = f(zero, x)
  //   assert(l.foldLeft(zero)(f) == xs.foldLeft(one)(f)) // LHS by definition
  //   xs match {
  //     case Nil() => {
  //       assert(xs.foldLeft(f(zero, x))(f) == f(zero, x))
  //       assert(xs.foldLeft(x)(f) == x)
  //       true
  //     }
  //     case Cons(x2, xss) => {
  //       assert(xs == x2 :: xss)
  //       assert(l.foldLeft(zero)(f) == xss.foldLeft(f(one, x2))(f)) // LHS
  //       assert(l.foldLeft(zero)(f) == xss.foldLeft(f(zero, f(x, x2)))(f)) // by associative
  //       assert(l.foldLeft(zero)(f) == (f(x, x2) :: xss).foldLeft(zero)(f)) // by definition
  //       assert(xs.foldLeft(x)(f) == (x2 :: xss).foldLeft(x)(f)) // by definition
  //       assert(xs.foldLeft(x)(f) == xss.foldLeft(f(x, x2))(f)) // by definition
  //       // listFoldLeftWhenAssociative(f(x, x2), xss, f, zero) // LHS = f(zero, xss.foldLeft(f(x, x2))(f))
  //       listFoldLeftWhenAssociative(x2, xss, f, x)
  //       && listFoldLeftWhenAssociative(x2, xss, f, one)
  //       // // listFoldLeftWhenAssociative(x2, xss, f, one) // LHS = xs.foldLeft(one)(f) == f(f(zero, x), xss.foldLeft(x2)(f)) == f(zero, f(x, xss.foldLeft(x2)(f)))
  //       // assert(listFoldLeftWhenAssociative(x2, xss, f, one) ==> (xs.foldLeft(one)(f) == f(one, xss.foldLeft(x2)(f)))) // by definition
  //       // assert(listFoldLeftWhenAssociative(x2, xss, f, one) ==> (xs.foldLeft(one)(f) == f(zero, f(x, xss.foldLeft(x2)(f))))) // by associative
  //       // // listFoldLeftWhenAssociative(x2, xss, f, x)
  //       // assert(listFoldLeftWhenAssociative(x2, xss, f, x) ==> (xs.foldLeft(x)(f) == f(x, xss.foldLeft(x2)(f))))
  //       // // assert(xs.foldLeft(one)(f) == f(zero, xs.foldLeft(x)(f)))
  //       // listFoldLeftWhenAssociative(x2, xss, f, one)  && listFoldLeftWhenAssociative(x2, xss, f, x)
  //     }
  //   }

  //   l.foldLeft(zero)(f) == f(zero, xs.foldLeft(x)(f))
  // }.holds

  def prependEqualListContact[T](l: List[T], x: T): Boolean = {
    l match {
      case Nil() => {
        assert(x :: l == Cons(x, Nil[T]()))
        true
      }
      case Cons(y, ys) => {
        assert(x :: l == Cons(x, l)) // by definition
        assert(Cons(x, Nil[T]()) ++ l == Cons(x, l))
        true
      }
    }
    x :: l == Cons(x, Nil[T]()) ++ l
  }.holds

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

  /*
  def distributiveOfZip[T, R](l1: List[T], l2: List[R]): Unit = {
  if (l1.isEmpty || l2.isEmpty) {

    assert(l1.zip(l2) == Nil[(T, R)]())
    ()
  } else {
    (l1, l2) match {
      case (Cons(x1, xs1), Cons(x2, xs2)) =>

        assert(l1.zip(l2) == Cons((x1, x2), xs1.zip(xs2)))

        assert(l1.zip(l2).size == (if (l1.size <= l2.size) l1.size else l2.size))

        distributiveOfZip(xs1, xs2)
    }
  }
}.ensuring { res =>

  l1.zip(l2).size == (if (l1.size <= l2.size) l1.size else l2.size)
}
  */




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

  def foldLeftTailProp[T, R](l: List[T], t: T, f: (R, T) => R, zero: R): Boolean = {
    val em = Nil[T]()
    l match {
      case Nil() => {
        assert(l :+ t == Cons(t, em)) 
        assert((l :+ t).foldLeft(zero)(f) == em.foldLeft(f(zero, t))(f))
        true
      }
      case Cons(x, xs) => {
        assert(l :+ t == Cons(x, xs :+ t))
        assert((l :+ t).foldLeft(zero)(f) == (xs :+ t).foldLeft(f(zero, x))(f))
        assert(xs.foldLeft(f(zero, x))(f) == l.foldLeft(zero)(f)) // by definition
        foldLeftTailProp(xs, t, f, f(zero, x)) // == f(xs.foldLeft(f(zero, x))(f), t) == f(l.foldLeft(zero)(f), t)
      }
    }
    (l :+ t).foldLeft(zero)(f) == f(l.foldLeft(zero)(f), t)
  }.holds

  // def foldLeftMiddleSplit[T](l1: List[T], y: T, ys: List[T], f: (T, T) => T, zero: T): Boolean = {
  //   // Precondition 1: the combine is associative
  //   require(forall((x: T, y: T, z: T) => f(f(x, y), z) == f(x, f(y, z))))
  //   require(!l1.isEmpty)
  //   val l2 = y :: ys
  //   if (l1.isEmpty)`{
  //     assert((l1 ++ (y :: ys)).foldLeft(zero)(f) == (y :: ys).foldLeft(zero)(f))

  //   } else {
  //   //   ys match {
  //   //     case Nil() => {
  //   //       assert(l2 == Cons(y, Nil[T]()))
  //   //       assert(ys.foldLeft(y)(f) == y)
  //   //       ListSpecs.snocIsAppend(l1, y)
  //   //       assert(l1 ++ l2 == l1 :+ y)
  //   //       foldLeftTailProp(l1, y, f, zero)
  //   //     }
  //   //     case Cons(y2, yss) => {
          

  //   //       listFoldLeftCombine(l1, l2, f, zero)
  //   //       assert((l1 ++ l2).foldLeft(zero)(f) == l2.foldLeft(l1.foldLeft(zero)(f))(f))

  //   //       prependEqualListContact(ys, y)
  //   //       assert(l2 == Cons(y, Nil[T]()) ++ ys)
  //   //       assert(l2.foldLeft(l1.foldLeft(zero)(f))(f) == ys.foldLeft(f(l1.foldLeft(zero)(f), y))(f))
  //   //       assert(Cons(y, Nil[T]()).foldLeft(l1.foldLeft(zero)(f))(f) == f(l1.foldLeft(zero)(f), y))
  //   //       foldLeftMiddleSplit(Cons(y, Nil[T]()), y2, yss, f, l1.foldLeft(zero)(f)) // l2.foldLeft(l1.foldLeft(zero)(f))(f) = f([y].foldLeft(aggl1)(f), yss.foldLeft(y2)(f))
  //   //     }
  //   //   }
  //   // }
    
  //   (l1 ++ (y :: ys)).foldLeft(zero)(f) == f(l1.foldLeft(zero)(f), ys.foldLeft(y)(f))
  // }

  abstract class AggFunction[T]:
    def execute(x: T, y: T): T

    // This should insure all the implementation to have this property
    @law
    def isAssociative(x: T, y: T, z: T): Boolean = {
      execute(execute(x, y), z) == execute(x, execute(y, z))
    }
    // def isAssociative(x: T, y: T, z: T): Boolean
    
  // An example for Integer addition
  case class SumBigInt() extends AggFunction[BigInt] {
    override def execute(x: BigInt, y: BigInt): BigInt = {
      x + y
    }
  }

  def listAggregation[T](l: List[T], f: AggFunction[T]): T = {
    // Precondition: the JoinList is not empty
    require(!l.isEmpty)
    decreases(l)

    l match {
      case Cons(x, Nil()) => x
      case Cons(x, xs) => {
        assert(!xs.isEmpty)
        f.execute(x, listAggregation(xs, f))
      }
    }
  }.ensuring( res =>
    (l.tail.isEmpty && res == l.head) || (res == f.execute(l.head, listAggregation(l.tail, f)))
  )

  def listAggregationDistributive[T](l1: List[T], l2: List[T], f: AggFunction[T]): Boolean = {
    // Precondition 1: f is associative (as specified in @law)
    // Precondition 2: 2 JoinList is not empty
    require(!l1.isEmpty && !l2.isEmpty)

    decreases(l1)

    l1 match {
      case Cons(x, Nil()) => {
        assert(!l2.isEmpty)
        assert(l1 ++ l2 == Cons(x, l2)) // by definition
        assert(listAggregation(l1 ++ l2, f) == f.execute(x, listAggregation(l2, f))) // LHS by definition
        assert(listAggregation(l1, f) == x)
        assert(listAggregation(l1 ++ l2, f) == f.execute(listAggregation(l1, f), listAggregation(l2, f)))
        true
      }
      case Cons(x, xs) => {
        // RHS == f.execute(x, f.execute(listAggregation(xs, f), listAggregation(l2, f))))
        val rhs1 = listAggregation(l1, f)
        val rhs2 = listAggregation(l2, f)
        val rhs = f.execute(rhs1, rhs2)
        val tailAgg = listAggregation(xs, f)

        // RHS == f.execute(f.execute(x, listAggregation(xs, f)), listAggregation(l2, f))
        assert(rhs1 == f.execute(x, tailAgg))
        assert(rhs == f.execute(f.execute(x, tailAgg), rhs2))

        // RHS == f.execute(x, f.execute(listAggregation(xs, f), listAggregation(l2, f)))
        f.isAssociative(x, tailAgg, rhs2)
        assert(rhs == f.execute(x, f.execute(tailAgg, rhs2)))

        // RHS == f.execute(x, listAggregation(xs ++ l2, f))
        val ans = listAggregationDistributive(xs, l2, f) // f.execute(listAggregation(xs, f), listAggregation(l2, f)) == listAggregation(xs ++ l2, f)
        assert(rhs == f.execute(x, listAggregation(xs ++ l2, f)))
        // RHS == LHS
        assert(l1 ++ l2 == Cons(x, xs ++ l2))
        assert(listAggregation(l1 ++ l2, f) == f.execute(x, listAggregation(xs ++ l2, f)))
        assert(listAggregation(l1 ++ l2, f) == rhs)

        // Return result
        ans
      }
    }
    listAggregation(l1 ++ l2, f) == f.execute(listAggregation(l1, f), listAggregation(l2, f))
  }.holds
}