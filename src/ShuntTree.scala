import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

import Helper.*
import TreeObject.*

object ShuntTreeObject {

  // ST a b, ShuntTree
  sealed abstract class ShuntTree[A, B]
  // T a
  case class T[A, B](value: A) extends ShuntTree[A, B]
  // N (ST a b) (ST. a b) (ST a b)
  case class N[A, B](left: ShuntTree[A, B], middle: ShuntContext[A, B], right: ShuntTree[A, B]) extends ShuntTree[A, B]


  // (ST. a b): ShuntContext
  sealed abstract class ShuntContext[A, B]
  // H. b
  case class H[A, B](value: B) extends ShuntContext[A, B]
  // L. (ST. a b) (ST. a b) (ST a b)
  case class L[A, B](left: ShuntContext[A, B], middle: ShuntContext[A, B], right: ShuntTree[A, B]) extends ShuntContext[A, B]
  // R. (ST a b) (ST. a b) (ST. a b)
  case class R[A, B](left: ShuntTree[A, B], middle: ShuntContext[A, B], right: ShuntContext[A, B]) extends ShuntContext[A, B]


  // ---------- Functions for ShuntContext ----------
  extension[A, B](tr: ShuntTree[A, B]) {
    def size: BigInt = {
      decreases(tr)
      tr match {
        // case E() => BigInt(0)
        case T(_) => BigInt(1)
        case N(left, middle, right) => left.size + middle.size + right.size
      }
    }.ensuring(res => (
        res >= BigInt(0) && res.mod(BigInt(2)) == BigInt(1)
      )
    )

    def height: BigInt = {
      decreases(tr)
      tr match {
        case T(_) => BigInt(1)
        case N(left, middle, right) => {
          val hleft = left.height
          val hright = right.height
          val (ml, mr, mt) = middle.height
          // left and right should apply to open ports of m, and should compare with closed path in m
          max(max(ml + left.height, mr + right.height), mt)
        }
      }
    }.ensuring(_ >= BigInt(1))
  }


  // ---------- Functions for ShuntContext ----------
  extension[A, B](ct: ShuntContext[A, B]) {
    def size: BigInt = {
      decreases(ct)
      ct match {
        case H(_) => BigInt(1)
        case L(left, middle, right) => left.size + middle.size + right.size
        case R(left, middle, right) => left.size + middle.size + right.size
      }
    }.ensuring(res => res >= BigInt(1) && res.mod(BigInt(2)) == BigInt(1))

    def height: (BigInt, BigInt, BigInt)= {
      // Height for a context is partial height, this function is to provide help to calculate the tree height
      // case of context decides how subtree is attached, so should calculate the partial length for 3 cases
      // (open port for external left tree, open port for external right, longest path ends at leaf)
      decreases(ct)
      ct match {
        case H(_) => (BigInt(1), BigInt(1), BigInt(0)) //Hole would be an internal node, contribute 1 for left right subtree, no existing tree, gives 0
        case L(l, m, r) => {
          val (mlh, mrh, mth) = m.height // for m, the opened port mlh for context l, mrh for tree r
          val (llh, lrh, lth) = l.height // all 3 casese for l should connect with mlh
          (mlh + llh, mlh + lrh, max(max(mth, mrh + r.height), mlh + lth))
        }
        case R(l, m, r) => {
          val (mlh, mrh, mth) = m.height // for m, the opened port mrh for context r, mlh for tree l
          val (rlh, rrh, rth) = r.height // all 3 casese for r should connect with mrh
          (mrh + rlh, mrh + rrh, max(max(mth, mlh + l.height), mrh + rth))
        }
      }
    }.ensuring((r1, r2, r3) => max(max(r1, r2), r3) >= BigInt(1))
  }

  // ----------- Shunt Operation -----------
  sealed trait ShuntOperation[X, Y]:
    def left(b: Y, a: Y, c: X): Y
    def right(b: X, a: Y, c: Y): Y
    def none(b: X, a: Y, c: X): X
  
  // An example for integer sum on tree
  case class TreeIntSumOp() extends ShuntOperation[BigInt, BigInt]:
    override def left(b: BigInt, a: BigInt, c: BigInt): BigInt = b + a + c
    override def right(b: BigInt, a: BigInt, c: BigInt): BigInt = b + a + c
    override def none(b: BigInt, a: BigInt, c: BigInt): BigInt = b + a + c
  
  


  
  // ----------- Shunt Contraction Scheme -----------
  sealed abstract class ShuntContractionScheme[A, B, X, Y]:
    def leaf(v: A): X
    def internal(v: B): Y
    def shuntops: ShuntOperation[X, Y]

    def applyOnTree(tr: Tree[A, B]): X = {
      decreases(tr)
      tr match {
        case Tip(v) => leaf(v)
        case Bin(v, l, r) => {
          val resultL = applyOnTree(l) // X
          val resultR = applyOnTree(r) // X
          shuntops.none(resultL, internal(v), resultR)
        }
      }
    }

    def applyOnShuntTree(tr: ShuntTree[A, B]): X = {
      decreases(tr)
      tr match {
        case T(v) => leaf(v)
        case N(l, c, r) => {
          val resultL = applyOnShuntTree(l) // X
          val resultR = applyOnShuntTree(r) // X
          shuntops.none(resultL, applyOnShuntContext(c), resultR) // X
        }
      }
    }//.ensuring(_ == applyOnTree(s2t(tr)))

    def applyOnShuntContext(ct: ShuntContext[A, B]): Y = {
      decreases(ct)
      ct match {
        case H(v) => internal(v)
        case L(l, m, r) => {
          // sc, sc, st
          val resultL = applyOnShuntContext(l) // Y
          val resultM = applyOnShuntContext(m) // Y
          val resultR = applyOnShuntTree(r) // x
          shuntops.left(resultL, resultM, resultR) // Y
        }
        case R(l, m, r) => {
          // st, sc, sc
          val resultL = applyOnShuntTree(l) // Y
          val resultM = applyOnShuntContext(m) // Y
          val resultR = applyOnShuntContext(r) // x
          shuntops.right(resultL, resultM, resultR) // Y
        }
      }
    }


  // Example Scheme for integer sum on tree
  case class TreeIntSumScheme() extends ShuntContractionScheme[BigInt, BigInt, BigInt, BigInt]:
    override def leaf(v: BigInt): BigInt = v
    override def internal(v: BigInt): BigInt = v
    override def shuntops: ShuntOperation[BigInt, BigInt] = TreeIntSumOp()
    
  // // def treeSum(st: ShuntTree[BigInt, BigInt]): Boolean
  // case class TreeConstruction[A, B, X, Y]() extends ShuntContractionScheme[A, B, Tree[A, B], Context[X, Y]]:
  //   override def leaf(v: A): BigInt = v
  //   override def internal(v: BigInt): BigInt = v
  //   override def shuntops: ShuntOperation[BigInt, BigInt] = TreeIntSumOp()
    
  // ----------- Functions for tree construction -----------
  type Context[A, B] = (Tree[A, B], Tree[A, B]) => Tree[A, B]

  def hole[A, B](v: B): Context[A, B] = {
    (l: Tree[A, B], r: Tree[A, B]) => {
      // require(!l.isEmpty && !r.isEmpty)
      Bin(v, l, r)
    }
  }

  def connectL[A, B](b: Context[A, B], a: Context[A, B], c: Tree[A, B]): Context[A, B] = {
    // require(!c.isEmpty)
    (l: Tree[A, B], r: Tree[A, B]) => {
      // require(!l.isEmpty && !r.isEmpty)
      a(b(l, r), c)
    }
  }

  def connectR[A, B](b: Tree[A, B], a: Context[A, B], c: Context[A, B]): Context[A, B] = {
    // require(!b.isEmpty)
    (l: Tree[A, B], r: Tree[A, B]) => {
      // require(!l.isEmpty && !r.isEmpty)
      a(b, c(l, r))
    }
  }

  def connectN[A, B](b: Tree[A, B], a: Context[A, B], c: Tree[A, B]): Tree[A, B] = {
    a(b, c)
  }

  def s2t[A, B](st: ShuntTree[A, B]): Tree[A, B] = {
    st match {
      // case E() => Empty()
      case T(v) => Tip(v)
      case N(b, a, c) => {
        val lt = s2t(b) // lt.size == b.size
        val rt = s2t(c) // rt.size == c.size
        connectN(lt, s2c(a), rt)
      }
    }
  }//.ensuring(res => st.isEmpty || res.size > BigInt(0))

  def s2c[A, B](sc: ShuntContext[A, B]): Context[A, B] = {
    sc match {
      case H(v) => hole(v)
      case L(b, a, c) => connectL(s2c(b), s2c(a), s2t(c))
      case R(b, a, c) => connectR(s2t(b), s2c(a), s2c(c))
    }
  }
  


  // ----------- Some properties ----------
  // def holeSizeProp[A, B](l: Tree[A, B], r: Tree[A, B], v: B): Boolean = {
  //   require(!l.isEmpty && !r.isEmpty)
  //   val f = hole[A, B](v)
  //   val res = f(l, r)
  //   res.size == BigInt(1) + l.size + r.size
  // }.holds

  // def connectLSizeProp[A, B](b: Context[A, B], a: Context[A, B], c: Tree[A, B], l: Tree[A, B], r: Tree[A, B]): Boolean = {
  //   require(!l.isEmpty && !r.isEmpty && !c.isEmpty)
  //   val f = connectL(b, a, c) // a function
  //   val res = f(l, r) // a tree
  //   assert(res == a(b(l, r), c)) // by definition
  //   assert(b(l, r))
  //   res.size == BigInt(2) + l.size + r.size + c.size
  // }.holds

  // def contextSizeProp[A, B](l: Tree[A, B], r: Tree[A, B], f: Context[A, B]): Boolean = {
  //   require(!l.isEmpty && !r.isEmpty)
  //   val res = f(l, r)
  //   res.size >= BigInt(1) + l.size + r.size
  // }.holds

/*
  // Define Tip and Bin-> TO REVISIT AND CHECK (+formally verify)
  sealed abstract class Tree[A, B]
  case class Tip[A, B](value: A) extends Tree[A, B]
  case class Bin[A, B](left: Tree[A, B], value: B, right: Tree[A, B]) extends Tree[A, B]

  
  // Implement scs-> check
  def scs[A, B](f: A => B, g: (B, B) => B, shunt: Shunt[A, B])(tree: Tree[A, B]): B = tree match {
    case Tip(a) => f(a)
    case Bin(left, b, right) =>
      val lRes = scs(f, g, shunt)(left)
      val rRes = scs(f, g, shunt)(right)
      shunt.none(lRes, b, rRes)
  }

  // Implement hole and connect-> check
  type Context[A, B] = (Tree[A, B], Tree[A, B]) => Tree[A, B]


  //to revisit
  def hole[A, B](b: B): Context[A, B] = (left, right) => Bin(left, b, right)

  /* 
  def connect[A, B]: Shunt[Tree[A, B], Context[A, B]] = Shunt(
    (l, b, a) => hole(b)(Tip(a), l),
    (a, b, r) => hole(b)(r, Tip(a)),
    (l, b, r) => hole(b)(l, r)
  )
*/
  //to revisit
  def zipTree[A, B, C, D](t1: Tree[A, B], t2: Tree[C, D]): Tree[(A, C), (B, D)] = (t1, t2) match {
    case (Tip(a), Tip(c)) => Tip((a, c))
    case (Bin(l1, b1, r1), Bin(l2, b2, r2)) =>
      Bin(zipTree(l1, l2), (b1, b2), zipTree(r1, r2))
    //-> missing a "case _ =>" ?"
  }

*/
/* 2.1!
Define:
  -Tip and Bin
  -Tree (in which we define a simple sum operation)
  -Shunt
Implement:
  -scs
  -connect
  -hole


  2. agg operations:
    i)sum: In which we present the modified sum operation
  ii)zipTree :: ∀α,α,β,β′.Tree αβ→ Tree α′ β′ → Tree (α,α′) (β,β′)
  zipTree (Tip a) (Tip b) = Tip (a,b)
  zipTree (Bin t1 at2) (Bin u1 bu2) = Bin (zipTree t1 u1) (a,b) (zipTree t2 u2)

 */

}

