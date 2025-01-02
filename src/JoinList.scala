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

    // // This aggregation assumes following list homomorphism scheme, only works on non-empty case
    // def aggregation(combine: (R, R) => R, convert: T => R): R = {
    //   // Precondition 1: the combine is associative
    //   require(forall((x: R, y: R, z: R) => combine(combine(x, y), z) == combine(x, combine(y, z))))
    //   // Precondition 2: the JoinList is not empty
    //   require(!jl.isEmpty)

    //   jl match {
    //     case Single(x) => convert(x)
    //     case Join(l, r) => {
    //       // listFoldLeftCombine(l.toList.map(convert), r.toList.map(convert), combine, basecase)
    //       assert(!l.isEmpty && !r.isEmpty)
    //       assert(l.head == jl.head) // Head of prefix
    //       distributiveOfMap(l.toList, r.toList, convert) // (l ++ r).map(convert) == l.map ++ r.map
    //       // val resultl = l.aggregation(combine, convert)
    //       // val resultr = r.aggregation(combine, convert)
    //       // r match {
    //       //   case Single(y) => 
    //       // }
    //       combine(l.aggregation(combine, convert), r.aggregation(combine, convert))
    //     }
    //   }
    // }.ensuring(
    //   _ == jl.tail.map(convert).toList.foldLeft(convert(jl.head))(combine)
    // )
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

    // def listCombine(f: (T, T) => T): T = {
    //   // Appling a combine function to list

    //   // Precondition 1: the combine is associative
    //   require(forall((x: T, y: T, z: T) => f(f(x, y), z) == f(x, f(y, z))))
    //   // Precondition 2: the JoinList is not empty
    //   require(!jl.isEmpty)
    //   sizeForNonEmpty(jl)
    //   jl match {
    //     case Single(x) => x
    //     case Join(l, r) => {
    //       assert(jl.head == l.head) // head should on left
    //       assert(headWithConcat(l.toList, r.toList) == ()) // l ++ r = l.head :: (l.tail ++ r)
    //       assert(jl.tail == l.tail ++ r)
    //       l match {
    //         case Single(y) => {
    //           assert(jl.tail == r)
    //           assert(l.listCombine(f) == y)
    //           assert(l ++ r == (l.tail ++ r) :: y)
    //           f(y, r.listCombine(f))
    //         }
    //         case Join(ll, lr) => {
    //           // listFoldLeftCombine(l.toList, r.toList, f)
    //           f(l.listCombine(f), r.listCombine(f))
    //         }
    //       }
    //       // 
    //       // f(l.listCombine(f), r.listCombine(f))
    //     }
    //   }
    // }.ensuring(_ == jl.tail.foldLeft(jl.head)(f))
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



  // def joinListHeadWithConcat[T](l1: JoinList[T], l2: JoinList[T]): Unit = {
  //   require(!l1.isEmpty)
  //   l1 match {
  //     case Single(x) => {
  //       assert(l1.tail.isEmpty)
  //       assert(l1.tail ++ l2 == l2)
  //       assert(l1.head == x)
  //       assert(l1 == l1.tail :: l1.head)
  //       assert(l1 ++ l2 == l2 :: x)
  //       ()
  //     }
  //     case Join(l, r) => {
  //       assert(!r.isEmpty)
  //       // val headList = Single(x, Nil())
  //       assert(l1 == l ++ r)
  //       listHeadWithConcat(l1.toList, l2.toList)
  //       ()
  //     }
  //   }
  // }.ensuring(l1 ++ l2 == (l1.tail ++ l2) :: l1.head)

  // def prependIsAddSimple[T](jl: JoinList[T], x: T): Boolean = {
  //   jl match {
  //     case Empty() => {
  //       assert((jl :: x) == Single[T](x))
  //       // assert(Single[T](x) ++ jl == Single[T](x))
  //       true
  //     }
  //     case Single(y) => {
  //       assert(jl :: x == Join(Single[T](x), jl))
  //       // assert(Single[T](x) ++ jl == Join(Single[T](x), jl))
  //       true
  //     }
  //     case Join(l, r) => {
  //       val newl = l :: x
  //       assert(jl :: x == newl ++ r)
  //       ListSpecs.appendAssoc(Single[T](x).toList, l.toList, r.toList)
  //       assert((Single[T](x) ++ l) ++ r ==  Single[T](x) ++ (l ++ r))
  //       // if l :: x == single(x) ++ l, then by association, holds
  //       prependIsAddSimple(l, x)
  //     }
  //   }
  //   jl :: x == Single[T](x) ++ jl
  // }.holds

  // def joinListAppendAssoc[T](l1: JoinList[T], l2: JoinList[T], l3: JoinList[T]): Boolean = {
  //   decreases(l1, l2, l3)
  //   if (l1.isEmpty || l2.isEmpty || l3.isEmpty) {
  //     assert((l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3))
  //     true
  //   } else {
  //     assert(!l1.isEmpty)
  //     assert(l1 ++ l2 == Join(l1, l2)) // by definition
  //     assert(Join(l1, l2).toList == l1.toList ++ l2.toList)
  //     assert(((l1 ++ l2) ++ l3).toList == (l1.toList ++ l2.toList) ++ l3.toList)
  //     assert((l1 ++ (l2 ++ l3)).toList == l1.toList ++ (l2.toList ++ l3.toList))
  //     ListSpecs.appendAssoc(l1.toList, l2.toList, l3.toList)
  //     assert(((l1 ++ l2) ++ l3).toList == (l1 ++ (l2 ++ l3)).toList)
  //     val lhs = (l1 ++ l2) ++ l3
  //     val rhs = l1 ++ (l2 ++ l3)
  //     assert(lhs.toList == rhs.toList)
  //     assert(lhs == rhs)
  //     true
  //     // l1 match {
  //     //   case Single(x) => {
  //     //     assert(l1 ++ l2 == Join(l1, l2)) // by definition
  //     //     assert(Join(l1, l2).toList == l1.toList ++ l2.toList)
  //     //     assert(((l1 ++ l2) ++ l3).toList == (l1.toList ++ l2.toList) ++ l3.toList)
  //     //     assert((l1 ++ (l2 ++ l3)).toList == l1.toList ++ (l2.toList ++ l3.toList))
  //     //     ListSpecs.appendAssoc(l1.toList, l2.toList, l3.toList)
  //     //     assert(((l1 ++ l2) ++ l3).toList == (l1 ++ (l2 ++ l3)).toList)
  //     //     val lhs = (l1 ++ l2) ++ l3
  //     //     val rhs = l1 ++ (l2 ++ l3)
  //     //     assert(lhs.toList == rhs.toList)
  //     //     true
  //     //     // l2 match {
  //     //     //   case Single(y) => {
  //     //     //     l3 match {
  //     //     //       case Single(z) => {
  //     //     //         assert(((l1 ++ l2) ++ l3).toList == List[T](x, y, z))
  //     //     //         assert((l1 ++ (l2 ++ l3)).toList == List[T](x, y, z))
  //     //     //         true
  //     //     //       }
  //     //     //       case Join(p, q) => {
  //     //     //         assert(l3 == p ++ q)    // LHS = (l1 ++ l2) ++ (p ++ q)
  //     //     //         (joinListAppendAssoc(l1 ++ l2, p , q)  // == ((l1 ++ l2) ++ p) ++ q
  //     //     //           && joinListAppendAssoc(l1, l2, p) // == (l1 ++ (l2 ++ p)) ++ q
  //     //     //           && joinListAppendAssoc(l1, l2 ++ p, q) // == l1 ++ ((l2 ++ p) ++ q)
  //     //     //           && joinListAppendAssoc(l2, p, q)
  //     //     //         )
  //     //     //       }
  //     //     //     }
  //     //     //   }
  //     //     //   case Join(p, q) => {
  //     //     //     assert(l2 == p ++ q)
  //     //     //     (joinListAppendAssoc(l1, p, q) // LHS = ((l1 ++ p) + q) + l3
  //     //     //       && joinListAppendAssoc(l1 ++ p, q, l3) // = (l1 ++ p) + (q + l3)
  //     //     //       && joinListAppendAssoc(l1, p, q ++ l3) // = l1 ++ (p + (q + l3))
  //     //     //       && joinListAppendAssoc(p, q, l3) // = l1 ++ (l2 + l3)
  //     //     //     )  
  //     //     //   }
  //     //     // }
  //     //   }
  //     //   case Join(l, r) => {
  //     //     assert(l1 == l ++ r)
  //     //     (joinListAppendAssoc(l, r, l2)           //  LHS == (l ++ (r ++ l2)) ++ l3
  //     //       && joinListAppendAssoc(l, r ++ l2, l3) //  == l ++ ((r ++ l2) ++ l3)
  //     //       && joinListAppendAssoc(r, l2, l3)      //  == l ++ (r ++ (l2 ++ l3))
  //     //       && joinListAppendAssoc(l, r, l2 ++ l3) //  == (l ++ r) ++ (l2 ++ l3) == l1 ++ (l2 ++ l3)
  //     //     ) 
  //     //   }
  //     // }
  //   }
  //   (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
  // }.holds

  // def joinListPreJoinSingleIsPrepend(x: T, l2: JoinList[T]): Boolean = {
  //   val lx = Single[T](x)
  //   l2 match {
  //     case Empty() => {
  //       assert(l1 ++ l2 == l1)
  //       assert(l2 :: x == l1)
  //       true
  //     }
  //     case Single(y) => {
  //       assert(l1 ++ l2 == Join(l1, l2))
  //       assert(l2 :: x == Join(l1, l2))
  //       true
  //     }
  //     case Join(l, r) => {
  //       // assert(l1 ++ l2 == l1 ++ (l ++ r))
  //       assert(l1 ++ l2 == Join(l1, l2))
  //       assert(l2 :: x == (l :: x) ++ r)
  //       joinListPreJoinSingleIsPrepend(x, l) // then l :: x == l1 ++ l
  //       // then (l1 ++ l) ++ r == l1 
  //     }
  //   }
  //   Single[T](x) ++ l2 == l2 :: x 
  // }.holds
}