/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Word
public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.Kernel.Basic
public import Geb.Prototypes.GoedelT.Equations
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The translation of the kernel into the internal language

The kernel's types and terms ({name}`Geb.Kernel.infer`) translated into the Mitchell–Bénabou
language ({name}`Geb.FreeTopos.Internal.Term`). A kernel label, a natural number, is a
bitstring of the language: a list of bits, the bits the coproduct of the terminal object with
itself, least significant first, in the bijective numeration of {cite}`Oitavem2010`
({name}`Geb.Oitavem.unrank`), in which the bit zero is the digit one and the bit one the digit
two, so that every list is the numeral of exactly one number. The bitstrings are the initial
algebra of the functor taking {lit}`X` to {lit}`1 + X + X`, whose fold and its uniqueness are
the list object's composed with the coproduct's. The base type of trees is the rose-tree object
over the bitstrings, and the unit, product, function and list types are the terminal object,
products, exponentials and list objects. A term former is the language's former of the same
name; a quoted tree is the construction of its nodes, each label the numeral built by the
definitions of the empty bitstring and of a bit before a bitstring; the conditional, the
kernel's folds and iteration, its case analysis of lists and its primitives are applications of
definitions of the language. The fold whose step sees the node is the rose-tree fold at pairs of
a rebuilt node and its value, as the kernel's is.

A fold of the library whose step uses a variable of the context folds into the exponential of that
variable's type and is applied to it, as the benchmark's appending does. The primitives are
functions of the labels and the children of trees, the labels' arithmetic structural recursion on
the bits: the numeral {lit}`b :: w` denotes {lit}`2 w + 1 + b`, so that addition, subtraction and
comparison proceed from the least significant bits with a successor as the carry, multiplication by
doubling, and division by the long division of the bits, and iteration applies the step twice the
tail's number of times and then once or twice.

## Main definitions

* {lit}`Translation.ty` — the translation of a kernel type.
* {lit}`Translation.prims`, {lit}`Translation.lib` — the primitive arrows and the definitions
  the translation applies.
* {lit}`Translation.numeral`, {lit}`Translation.quoteT` — the bitstring of a label, and the
  translation of a quoted tree.
* {lit}`Translation.term` — the translation of a kernel term, with its kernel type.
* {lit}`Translation.globals` — the constants of a translated program.
* {lit}`Translation.thm` — the translation of a theorem of Gödel's T.

## References

* {cite}`Oitavem2010`, Remark 2.2, for the bijective numeration of the bitstrings.

## Tags

internal language, System T, translation, rose tree, bitstring, bijective numeration
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Translation

open PartialHorn (Tree)
open Internal (Term Defn Prim Globals Definition weaken1)
open scoped FinEnum

/-! The types. -/

/-- The type of bits: the coproduct of the terminal object with itself, whose left injection is
the bit zero and whose right injection the bit one. -/
def bitTy : Tree := coprod one one

/-- The type of bitstrings: lists of bits, the least significant first. -/
def bitsTy : Tree := list bitTy

/-- The type of trees: rose trees whose labels are bitstrings. -/
def treeTy : Tree := lrose bitsTy

/-- The type of the results of a comparison: less, equal and greater, the left injection and
the right injection of the two bits. -/
def ordTy : Tree := coprod one bitTy

/-- The translation of a kernel type: the base type to the trees, and the unit, product,
function and list types to the terminal object, products, exponentials and list objects;
nothing for a tree that is not a type. -/
def ty : Tree → Option Tree :=
  RoseTree.elim fun l rs ↦
    match l, rs with
    | Kernel.Label.tyTree, [] => some treeTy
    | Kernel.Label.tyUnit, [] => some one
    | Kernel.Label.tyProd, [a, b] => do pure (prod (← a) (← b))
    | Kernel.Label.tyArrow, [a, b] => do pure (exp (← a) (← b))
    | Kernel.Label.tyList, [a] => do pure (list (← a))
    | _, _ => none

/-! The primitive arrows and the terms built with them. -/

/-- The primitive arrows: the empty list and construction, of an object parameter, the
construction of a rose tree over an object parameter of labels, the injections into a coproduct
and its case analysis, by these indices. -/
def prims : List Prim :=
  [Internal.nilPrim, Internal.consPrim, Internal.lnodePrim, Internal.inlPrim, Internal.inrPrim,
    Internal.casePrim]

/-- The empty list of elements of the type {lit}`a`. -/
def nilT (a : Tree) : Term := Term.arr 0 [a] Term.star

/-- The list of an element of the type {lit}`a` before a list. -/
def consT (a : Tree) (h t : Term) : Term := Term.arr 1 [a] (Term.pair h t)

/-- The tree of a pair of a label and a list of children. -/
def nodeT (p : Term) : Term := Term.arr 2 [bitsTy] p

/-- The bit zero. -/
def bit0T : Term := Term.arr 3 [one, one] Term.star

/-- The bit one. -/
def bit1T : Term := Term.arr 4 [one, one] Term.star

/-- The case analysis of a bit at the type {lit}`c`: the term {lit}`t` at zero and {lit}`u` at
one, each the body of an abstraction over the terminal object, so that the one not selected is
not reduced. -/
def ifBit (c : Tree) (b t u : Term) : Term :=
  Term.app (Term.arr 5 [one, one, c]
    (Term.pair (Term.lam one (weaken1 t)) (Term.lam one (weaken1 u)))) b

/-- Less, in the comparison type. -/
def ltO : Term := Term.arr 3 [one, bitTy] Term.star

/-- Equal, in the comparison type. -/
def eqO : Term := Term.arr 4 [one, bitTy] bit0T

/-- Greater, in the comparison type. -/
def gtO : Term := Term.arr 4 [one, bitTy] bit1T

/-- The case analysis of a comparison at the type {lit}`c`: the terms at less, equal and
greater. -/
def ifOrd (c : Tree) (o l e g : Term) : Term :=
  Term.app (Term.arr 5 [one, bitTy, c] (Term.pair (Term.lam one (weaken1 l))
    (Term.lam bitTy (ifBit c (Term.var 0) (weaken1 e) (weaken1 g))))) o

/-- The leaf of a label. -/
def leafT (l : Term) : Term := nodeT (Term.pair l (nilT treeTy))

/-! The definitions. -/

/-- The variable of a de Bruijn index. -/
abbrev v (i : ℕ) : Term := Term.var i

/-- The application of the definition of an index at objects to arguments, the first first. -/
def call (k : ℕ) (θ : List Tree) (args : List Term) : Term := Term.defn k θ args.reverse

/-- A definition in object parameters from parameters of types, the first first, so that the
last is the variable of index zero in its body. -/
def mkDefn (arity : ℕ) (params : List Tree) (type : Tree) (body : Term) : Defn :=
  ⟨arity, params.reverse, type, body⟩

/-! The indices of the definitions, in the order of {lit}`lib`. -/

namespace D

/-- The empty bitstring. -/
abbrev bnil : ℕ := 0
/-- The bit zero before a bitstring. -/
abbrev b0 : ℕ := 1
/-- The bit one before a bitstring. -/
abbrev b1 : ℕ := 2
/-- The label of a tree. -/
abbrev lab : ℕ := 3
/-- The label and the list of the children of a tree. -/
abbrev unnode : ℕ := 4
/-- The list of the children of a tree. -/
abbrev children : ℕ := 5
/-- The conditional on a bitstring, not empty or empty. -/
abbrev cond : ℕ := 6
/-- The tail of a list. -/
abbrev tail : ℕ := 7
/-- The head of a list, or a default. -/
abbrev headD : ℕ := 8
/-- The case analysis of a list. -/
abbrev lcase : ℕ := 9
/-- Whether a list is empty, as one or zero. -/
abbrev isNil : ℕ := 10
/-- The successor. -/
abbrev succ : ℕ := 11
/-- The length of a list. -/
abbrev length : ℕ := 12
/-- The predecessor, zero at zero. -/
abbrev pred : ℕ := 13
/-- Doubling. -/
abbrev dbl : ℕ := 14
/-- Addition. -/
abbrev add : ℕ := 15
/-- The comparison of two numbers. -/
abbrev cmp : ℕ := 16
/-- Whether one number is less than another, as one or zero. -/
abbrev ltB : ℕ := 17
/-- Whether two numbers are equal, as one or zero. -/
abbrev eqB : ℕ := 18
/-- Subtraction of a number at most the first. -/
abbrev subE : ℕ := 19
/-- Truncated subtraction. -/
abbrev sub : ℕ := 20
/-- Multiplication. -/
abbrev mul : ℕ := 21
/-- The quotient and the remainder. -/
abbrev divMod : ℕ := 22
/-- The base-two logarithm. -/
abbrev log2 : ℕ := 23
/-- Iteration of a function as many times as a number. -/
abbrev iter : ℕ := 24
/-- The applications of a list of functions to one argument. -/
abbrev mapApp : ℕ := 25
/-- The conjunction of two numbers read as truth values. -/
abbrev and : ℕ := 26
/-- Whether a list of functions holds, elementwise, of a list of trees of the same length. -/
abbrev allZip : ℕ := 27
/-- Whether two trees are equal, as one or zero. -/
abbrev equal : ℕ := 28

end D

/-- The object variable of a definition's first object parameter. -/
abbrev X₀ : Tree := x 0

/-- The object variable of a definition's second object parameter. -/
abbrev X₁ : Tree := x 1

/-- The empty bitstring, zero and false. -/
def bnilT : Term := call D.bnil [] []

/-- The bit zero before a bitstring. -/
def b0T (w : Term) : Term := call D.b0 [] [w]

/-- The bit one before a bitstring. -/
def b1T (w : Term) : Term := call D.b1 [] [w]

/-- One and true. -/
def trueT : Term := b0T bnilT

/-- The numeral of a natural number: the bitstring of its index in the enumeration of
{cite}`Oitavem2010`. -/
def numeral (n : ℕ) : Term :=
  (Oitavem.unrank n).foldr (fun b w ↦ if b then b1T w else b0T w) bnilT

/-- The translation of a quoted tree: the construction of each node from its label's numeral
and the list of its children's translations. -/
def quoteT : Tree → Term :=
  RoseTree.elim fun l cs ↦ nodeT (Term.pair (numeral l) (cs.foldr (consT treeTy) (nilT treeTy)))

/-- The conditional on a bitstring at the type {lit}`a`: the second term when the bitstring is
not empty, the third when it is. -/
def condT (a : Tree) (c t u : Term) : Term := call D.cond [a] [c, t, u]

/-- The case analysis of a list at the element type {lit}`a` and the result type {lit}`b`: the
value at the empty list, and the function of the head and the tail. -/
def lcaseB (a b : Tree) (l n c : Term) : Term :=
  call D.lcase [a, b] [l, Term.lam one (weaken1 n), c]

/-- The comparison of two bitstrings. -/
def cmpT (m n : Term) : Term := call D.cmp [] [m, n]

/-- The bit of a sum's least significant place, at the least significant bits {lit}`d` and
{lit}`e` of the summands: one when they are equal. -/
def digitT (d e : Term) : Term :=
  ifBit bitTy d (ifBit bitTy e bit1T bit0T) (ifBit bitTy e bit0T bit1T)

/-- The comparison of two bits. -/
def bitOrdT (d e : Term) : Term :=
  ifBit ordTy d (ifBit ordTy e eqO ltO) (ifBit ordTy e gtO eqO)

/-- The definitions the translation applies, by the indices of {lit}`D`, each over those
before it: the bitstrings' constructions, the label, the children and the conditional, the
tail, head and case analysis of lists, the arithmetic, comparison, logarithm and iteration of
bitstrings, the applications of a list of functions, and the equality of trees. -/
def lib : List Defn := [
  -- the empty bitstring, and a bit before a bitstring
  mkDefn 0 [] bitsTy (nilT bitTy),
  mkDefn 0 [bitsTy] bitsTy (consT bitTy bit0T (v 0)),
  mkDefn 0 [bitsTy] bitsTy (consT bitTy bit1T (v 0)),
  -- the label of a tree: the fold taking each node to its label
  mkDefn 0 [treeTy] bitsTy (Term.roseRec bitsTy (Term.fst (v 0)) (v 0)),
  -- the label and the children: the fold rebuilding each child from its own
  mkDefn 0 [treeTy] (prod bitsTy (list treeTy))
    (Term.roseRec (prod bitsTy (list treeTy))
      (Term.pair (Term.fst (v 0))
        (Term.listRec (nilT treeTy) (consT treeTy (nodeT (v 1)) (v 0)) (Term.snd (v 0))))
      (v 0)),
  -- the children
  mkDefn 0 [treeTy] (list treeTy) (Term.snd (call D.unnode [] [v 0])),
  -- the conditional on a bitstring, by its fold into functions of the two branches
  mkDefn 1 [bitsTy, X₀, X₀] X₀
    (Term.app (Term.app (Term.listRec (Term.lam X₀ (Term.lam X₀ (v 0)))
      (Term.lam X₀ (Term.lam X₀ (v 1))) (v 2)) (v 1)) (v 0)),
  -- the tail of a list: the second component of the pair of the list and its tail
  mkDefn 1 [list X₀] (list X₀)
    (Term.snd (Term.listRec (Term.pair (nilT X₀) (nilT X₀))
      (Term.pair (consT X₀ (v 1) (Term.fst (v 0))) (Term.fst (v 0))) (v 0))),
  -- the head of a list, or the default for the empty list
  mkDefn 1 [X₀, list X₀] X₀
    (Term.app (Term.listRec (Term.lam X₀ (v 0)) (Term.lam X₀ (v 2)) (v 0)) (v 1)),
  -- the case analysis of a list: the fold into functions of the pair of the two cases, whose
  -- value is the pair of the list and the case's value, so that a construction's case receives
  -- the tail; the empty list's case is a function of the terminal object, so that it is not
  -- reduced unless selected
  (let C := exp X₀ (exp (list X₀) X₁)
   let P := prod (exp one X₁) C
   let tl := Term.fst (Term.app (v 1) (v 0))
   mkDefn 2 [list X₀, exp one X₁, C] X₁
    (Term.snd (Term.app (Term.listRec
      (Term.lam P (Term.pair (nilT X₀) (Term.app (Term.fst (v 0)) Term.star)))
      (Term.lam P (Term.pair (consT X₀ (v 2) tl) (Term.app (Term.app (Term.snd (v 0)) (v 2)) tl)))
      (v 2)) (Term.pair (v 1) (v 0))))),
  -- whether a list is empty
  mkDefn 1 [list X₀] bitsTy (Term.listRec trueT bnilT (v 0)),
  -- the successor, of the pair of the bitstring and its successor: a bit zero becomes one, and a
  -- bit one becomes zero before the successor of the rest
  mkDefn 0 [bitsTy] bitsTy
    (Term.snd (Term.listRec (Term.pair bnilT trueT)
      (Term.pair (consT bitTy (v 1) (Term.fst (v 0)))
        (ifBit bitsTy (v 1) (b1T (Term.fst (v 0))) (b0T (Term.snd (v 0)))))
      (v 0))),
  -- the length of a list of the object parameter
  mkDefn 1 [list X₀] bitsTy (Term.listRec bnilT (call D.succ [] [v 0]) (v 0)),
  -- the predecessor: a bit zero becomes one before the predecessor of the rest, unless the rest
  -- is empty, and a bit one becomes zero
  mkDefn 0 [bitsTy] bitsTy
    (Term.snd (Term.listRec (Term.pair bnilT bnilT)
      (Term.pair (consT bitTy (v 1) (Term.fst (v 0)))
        (ifBit bitsTy (v 1) (condT bitsTy (Term.fst (v 0)) (b1T (Term.snd (v 0))) bnilT)
          (b0T (Term.fst (v 0)))))
      (v 0))),
  -- doubling: a bit zero becomes one before the rest doubled, and a bit one becomes one before
  -- zero before the rest
  mkDefn 0 [bitsTy] bitsTy
    (Term.snd (Term.listRec (Term.pair bnilT bnilT)
      (Term.pair (consT bitTy (v 1) (Term.fst (v 0)))
        (ifBit bitsTy (v 1) (b1T (Term.snd (v 0))) (b1T (b0T (Term.fst (v 0))))))
      (v 0))),
  -- addition, by recursion on the second summand into functions of the first: the least
  -- significant bits' place, and the sum of the rests, its successor unless both bits are zero
  mkDefn 0 [bitsTy, bitsTy] bitsTy
    (Term.app (Term.snd (Term.listRec (Term.pair bnilT (Term.lam bitsTy (v 0)))
      (Term.pair (consT bitTy (v 1) (Term.fst (v 0)))
        (Term.lam bitsTy (lcaseB bitTy bitsTy (v 0) (consT bitTy (v 2) (Term.fst (v 1)))
          (Term.lam bitTy (Term.lam bitsTy (consT bitTy (digitT (v 1) (v 4))
            (Term.app (Term.lam bitsTy (ifBit bitsTy (v 2)
                (ifBit bitsTy (v 5) (v 0) (call D.succ [] [v 0])) (call D.succ [] [v 0])))
              (Term.app (Term.snd (v 3)) (v 0)))))))))
      (v 0))) (v 1)),
  -- comparison, by recursion on the second number into functions of the first: the comparison
  -- of the rests, and of the least significant bits where the rests are equal
  mkDefn 0 [bitsTy, bitsTy] ordTy
    (Term.app (Term.listRec (Term.lam bitsTy (condT ordTy (v 0) gtO eqO))
      (Term.lam bitsTy (lcaseB bitTy ordTy (v 0) ltO
        (Term.lam bitTy (Term.lam bitsTy
          (ifOrd ordTy (Term.app (v 3) (v 0)) ltO (bitOrdT (v 1) (v 4)) gtO)))))
      (v 0)) (v 1)),
  -- less, by the comparison
  mkDefn 0 [bitsTy, bitsTy] bitsTy (ifOrd bitsTy (cmpT (v 1) (v 0)) trueT bnilT bnilT),
  -- equality, by recursion on the second number into functions of the first: the first is
  -- empty where the second is, and otherwise has an equal least significant bit before a rest
  -- equal to the second's, which the first unequal bits decide without the rests
  mkDefn 0 [bitsTy, bitsTy] bitsTy
    (Term.app (Term.listRec (Term.lam bitsTy (call D.isNil [bitTy] [v 0]))
      (Term.lam bitsTy (lcaseB bitTy bitsTy (v 0) bnilT
        (Term.lam bitTy (Term.lam bitsTy
          (ifBit bitsTy (v 1) (ifBit bitsTy (v 4) (Term.app (v 3) (v 0)) bnilT)
            (ifBit bitsTy (v 4) bnilT (Term.app (v 3) (v 0))))))))
      (v 0)) (v 1)),
  -- subtraction of a number at most the first, by recursion on it into functions of the first:
  -- the difference of the rests doubled where the bits are equal, the bit zero before it where
  -- the first's bit is one, and before its predecessor where the first's bit is zero
  mkDefn 0 [bitsTy, bitsTy] bitsTy
    (Term.app (Term.listRec (Term.lam bitsTy (v 0))
      (Term.lam bitsTy (lcaseB bitTy bitsTy (v 0) bnilT
        (Term.lam bitTy (Term.lam bitsTy (Term.app (Term.lam bitsTy
          (ifBit bitsTy (v 2)
            (ifBit bitsTy (v 5) (call D.dbl [] [v 0]) (b0T (call D.pred [] [v 0])))
            (ifBit bitsTy (v 5) (b0T (v 0)) (call D.dbl [] [v 0]))))
          (Term.app (v 3) (v 0)))))))
      (v 0)) (v 1)),
  -- truncated subtraction
  mkDefn 0 [bitsTy, bitsTy] bitsTy
    (condT bitsTy (call D.ltB [] [v 1, v 0]) bnilT (call D.subE [] [v 1, v 0])),
  -- multiplication, by recursion on the second factor into functions of the first: the product
  -- with the rest doubled, and the first once or twice
  mkDefn 0 [bitsTy, bitsTy] bitsTy
    (Term.app (Term.listRec (Term.lam bitsTy bnilT)
      (Term.lam bitsTy (call D.add []
        [call D.dbl [] [Term.app (v 1) (v 0)], ifBit bitsTy (v 2) (v 0) (call D.dbl [] [v 0])]))
      (v 0)) (v 1)),
  -- the quotient and the remainder, zero and the dividend for the divisor zero, else by long
  -- division, by recursion on the dividend into functions of the divisor: the rest's remainder
  -- with the bit, at most twice the divisor, less than it, from once to twice it, or twice it
  (let P := prod bitsTy bitsTy
   mkDefn 0 [bitsTy, bitsTy] P
    (condT P (v 0)
      (Term.app (Term.listRec (Term.lam bitsTy (Term.pair bnilT bnilT))
        (Term.lam bitsTy (Term.app (Term.lam P (Term.app (Term.lam bitsTy
            (ifOrd P (cmpT (v 0) (v 2))
              (Term.pair (call D.dbl [] [Term.fst (v 1)]) (v 0))
              (Term.pair (b0T (Term.fst (v 1))) bnilT)
              (ifOrd P (cmpT (v 0) (call D.dbl [] [v 2]))
                (Term.pair (b0T (Term.fst (v 1))) (call D.subE [] [v 0, v 2]))
                (Term.pair (b1T (Term.fst (v 1))) bnilT)
                (Term.pair (b1T (Term.fst (v 1))) bnilT))))
            (consT bitTy (v 3) (Term.snd (v 0)))))
          (Term.app (v 1) (v 0))))
        (v 1)) (v 0))
      (Term.pair bnilT (v 1)))),
  -- the base-two logarithm: the length, where a bit is one, and its predecessor where none is,
  -- from the fold into the pair of the length and whether a bit is one
  (let P := prod bitsTy bitsTy
   mkDefn 0 [bitsTy] bitsTy
    (Term.app (Term.lam P (condT bitsTy (Term.snd (v 0)) (Term.fst (v 0))
        (call D.pred [] [Term.fst (v 0)])))
      (Term.listRec (Term.pair bnilT bnilT)
        (Term.app (Term.lam P (Term.pair (call D.succ [] [Term.fst (v 0)])
          (ifBit bitsTy (v 2) (Term.snd (v 0)) trueT))) (v 0))
        (v 0)))),
  -- iteration, by recursion on the number into functions of the function and the start: the
  -- function applied twice the rest's number of times, and then once or twice
  (let F := exp X₀ X₀
   mkDefn 1 [bitsTy, F, X₀] X₀
    (Term.app (Term.app (Term.listRec (Term.lam F (Term.lam X₀ (v 0)))
      (Term.lam F (Term.lam X₀ (Term.app (Term.lam X₀
          (ifBit X₀ (v 4) (Term.app (v 2) (v 0)) (Term.app (v 2) (Term.app (v 2) (v 0)))))
        (Term.app (Term.app (v 2) (v 1)) (Term.app (Term.app (v 2) (v 1)) (v 0))))))
      (v 2)) (v 1)) (v 0))),
  -- the applications of a list of functions to one argument
  mkDefn 2 [list (exp X₀ X₁), X₀] (list X₁)
    (Term.app (Term.listRec (Term.lam X₀ (nilT X₁))
      (Term.lam X₀ (consT X₁ (Term.app (v 2) (v 0)) (Term.app (v 1) (v 0)))) (v 1)) (v 0)),
  -- conjunction
  mkDefn 0 [bitsTy, bitsTy] bitsTy (condT bitsTy (v 1) (v 0) bnilT),
  -- whether a list of functions holds of a list of trees of its length, elementwise
  mkDefn 0 [list (exp treeTy bitsTy), list treeTy] bitsTy
    (Term.app (Term.listRec
      (Term.lam (list treeTy) (call D.isNil [treeTy] [v 0]))
      (Term.lam (list treeTy) (condT bitsTy (call D.isNil [treeTy] [v 0]) bnilT
        (call D.and [] [Term.app (v 2) (call D.headD [treeTy] [leafT bnilT, v 0]),
          Term.app (v 1) (call D.tail [treeTy] [v 0])])))
      (v 1)) (v 0)),
  -- equality of trees: the fold into functions of the second tree, comparing the labels and
  -- the children elementwise
  mkDefn 0 [treeTy, treeTy] bitsTy
    (Term.app (Term.roseRec (exp treeTy bitsTy)
      (Term.lam treeTy (call D.and []
        [call D.eqB [] [Term.fst (v 1), call D.lab [] [v 0]],
          call D.allZip [] [Term.snd (v 1), call D.children [] [v 0]]])) (v 1)) (v 0))]

/-! The kernel's constants. -/

/-- The fold of trees at the result type {lit}`a`: the rose-tree fold into functions of the
step, each node's value the step at the leaf of its label and the list of its children's
values at the step. -/
def foldT (a : Tree) : Term :=
  let F := exp treeTy (exp (list a) a)
  Term.lam F (Term.lam treeTy (Term.app (Term.roseRec (exp F a)
    (Term.lam F (Term.app (Term.app (v 0) (leafT (Term.fst (v 1))))
      (call D.mapApp [F, a] [Term.snd (v 1), v 0]))) (v 0)) (v 1)))

/-- The subtrees of a list of pairs of a subtree and a value. -/
def fstsT (ps : Term) : Term := Term.listRec (nilT treeTy) (consT treeTy (Term.fst (v 1)) (v 0)) ps

/-- The values of a list of pairs of a subtree and a value of the type {lit}`a`. -/
def sndsT (a : Tree) (ps : Term) : Term :=
  Term.listRec (nilT a) (consT a (Term.snd (v 1)) (v 0)) ps

/-- The fold of trees whose step sees the node itself, at the result type {lit}`a`: the rose-tree
fold into functions of the step, each node's value at the step the pair of the node, rebuilt
from its children's first components, and the step at the node and the children's second
components, the fold at pairs of {name}`Geb.Kernel.Const.para`. -/
def paraT (a : Tree) : Term :=
  let F := exp treeTy (exp (list a) a)
  let P := prod treeTy a
  Term.lam F (Term.lam treeTy (Term.snd (Term.app (Term.roseRec (exp F P)
    (Term.lam F (Term.app (Term.lam (list P)
        (Term.app
          (Term.lam treeTy (Term.pair (v 0) (Term.app (Term.app (v 2) (v 0)) (sndsT a (v 1)))))
          (nodeT (Term.pair (Term.fst (v 2)) (fstsT (v 0))))))
      (call D.mapApp [F, P] [Term.snd (v 1), v 0]))) (v 0)) (v 1))))

/-- Iteration at the result type {lit}`a`: the step iterated as many times as the tree's
label. -/
def iterT (a : Tree) : Term :=
  Term.lam (exp a a) (Term.lam a (Term.lam treeTy
    (call D.iter [a] [call D.lab [] [v 0], v 2, v 1])))

/-- The right fold of lists of elements of the type {lit}`a` at the result type {lit}`b`: the
list fold into functions of the pair of the step and the start. -/
def foldrT (a b : Tree) : Term :=
  let P := prod (exp a (exp b b)) b
  Term.lam (exp a (exp b b)) (Term.lam b (Term.lam (list a) (Term.app (Term.listRec
    (Term.lam P (Term.snd (v 0)))
    (Term.lam P (Term.app (Term.app (Term.fst (v 0)) (v 2)) (Term.app (v 1) (v 0)))) (v 0))
    (Term.pair (v 2) (v 1)))))

/-- Case analysis of lists of elements of the type {lit}`a` at the result type {lit}`b`. -/
def lcaseT (a b : Tree) : Term :=
  Term.lam (list a) (Term.lam b (Term.lam (exp a (exp (list a) b))
    (lcaseB a b (v 2) (v 1) (v 0))))

/-- A binary primitive on labels: the leaf of a function of the two labels. -/
def binT (f : Term → Term → Term) : Term :=
  Term.lam treeTy (Term.lam treeTy (leafT (f (call D.lab [] [v 1]) (call D.lab [] [v 0]))))

/-- The translation of the kernel's primitive of an index, each a function of the labels and
the children of trees. -/
def primT (k : ℕ) : Option Term :=
  match k with
  | Kernel.Prim.label => some (Term.lam treeTy (leafT (call D.lab [] [v 0])))
  | Kernel.Prim.arity =>
    some (Term.lam treeTy (leafT (call D.length [treeTy] [call D.children [] [v 0]])))
  | Kernel.Prim.child => some (Term.lam treeTy (Term.lam treeTy (call D.headD [treeTy]
      [leafT bnilT, call D.iter [list treeTy] [call D.lab [] [v 0],
        Term.lam (list treeTy) (call D.tail [treeTy] [v 0]), call D.children [] [v 1]]])))
  | Kernel.Prim.node =>
    some (Term.lam treeTy (Term.lam (list treeTy)
      (nodeT (Term.pair (call D.lab [] [v 1]) (v 0)))))
  | Kernel.Prim.children => some (Term.lam treeTy (call D.children [] [v 0]))
  | Kernel.Prim.add => some (binT fun m n ↦ call D.add [] [m, n])
  | Kernel.Prim.sub => some (binT fun m n ↦ call D.sub [] [m, n])
  | Kernel.Prim.mul => some (binT fun m n ↦ call D.mul [] [m, n])
  | Kernel.Prim.div => some (binT fun m n ↦ Term.fst (call D.divMod [] [m, n]))
  | Kernel.Prim.mod => some (binT fun m n ↦ Term.snd (call D.divMod [] [m, n]))
  | Kernel.Prim.eq => some (binT fun m n ↦ call D.eqB [] [m, n])
  | Kernel.Prim.lt => some (binT fun m n ↦ call D.ltB [] [m, n])
  | Kernel.Prim.equal =>
    some (Term.lam treeTy (Term.lam treeTy (leafT (call D.equal [] [v 1, v 0]))))
  | Kernel.Prim.log2 => some (Term.lam treeTy (leafT (call D.log2 [] [call D.lab [] [v 0]])))
  | _ => none

/-! The translation of terms. -/

/-- The domain and codomain of a kernel function type. -/
def arrowParts (t : Tree) : Option (Tree × Tree) :=
  if t.label = Kernel.Label.tyArrow then
    match t.children with
    | [a, b] => some (a, b)
    | _ => none
  else none

/-- The factors of a kernel product type. -/
def prodParts (t : Tree) : Option (Tree × Tree) :=
  if t.label = Kernel.Label.tyProd then
    match t.children with
    | [a, b] => some (a, b)
    | _ => none
  else none

/-- The element type of a kernel list type. -/
def listPart (t : Tree) : Option Tree :=
  if t.label = Kernel.Label.tyList then
    match t.children with
    | [a] => some a
    | _ => none
  else none

/-- The translation of a term, as a function of the types of the globals and of the context:
the term's kernel type, as the kernel's checker infers it, and its translation. -/
abbrev Tr : Type := List Tree → List Tree → Option (Tree × Term)

/-- One node of the translation: the node's label, and each child as a tree with its
translation. -/
def termStep (l : ℕ) (cs : List (Tree × Tr)) : Tr := fun gt Γ ↦
  match l, cs with
  | Kernel.Label.var, [(n, _)] => do pure (← Γ[n.label]?, v n.label)
  | Kernel.Label.lam, [(A, _), (_, b)] =>
    if Kernel.Ty.IsTy A then do
      let (B, t) ← b gt (A :: Γ)
      pure (Kernel.tArrow A B, Term.lam (← ty A) t)
    else none
  | Kernel.Label.app, [(_, f), (_, x)] => do
    let (F, tf) ← f gt Γ
    let (X, tx) ← x gt Γ
    let (A, B) ← arrowParts F
    if X = A then pure (B, Term.app tf tx) else none
  | Kernel.Label.unit, [] => some (Kernel.tUnit, Term.star)
  | Kernel.Label.pair, [(_, a), (_, b)] => do
    let (A, ta) ← a gt Γ
    let (B, tb) ← b gt Γ
    pure (Kernel.tProd A B, Term.pair ta tb)
  | Kernel.Label.fst, [(_, p)] => do
    let (P, tp) ← p gt Γ
    pure ((← prodParts P).1, Term.fst tp)
  | Kernel.Label.snd, [(_, p)] => do
    let (P, tp) ← p gt Γ
    pure ((← prodParts P).2, Term.snd tp)
  | Kernel.Label.quote, [(t, _)] => some (Kernel.tT, quoteT t)
  | Kernel.Label.cond, [(_, c), (_, a), (_, b)] => do
    let (C, tc) ← c gt Γ
    let (A, ta) ← a gt Γ
    let (B, tb) ← b gt Γ
    if C = Kernel.tT ∧ B = A then pure (A, condT (← ty A) (call D.lab [] [tc]) ta tb) else none
  | Kernel.Label.fold, [(A, _)] => do pure (Kernel.foldTy A, foldT (← ty A))
  | Kernel.Label.iter, [(A, _)] => do pure (Kernel.iterTy A, iterT (← ty A))
  | Kernel.Label.nil, [(A, _)] => do pure (Kernel.tList A, nilT (← ty A))
  | Kernel.Label.cons, [(_, x), (_, xs)] => do
    let (X, tx) ← x gt Γ
    let (L, txs) ← xs gt Γ
    let A ← listPart L
    if X = A then pure (L, consT (← ty A) tx txs) else none
  | Kernel.Label.foldr, [(A, _), (B, _)] => do
    pure (Kernel.foldrTy A B, foldrT (← ty A) (← ty B))
  | Kernel.Label.prim, [(k, _)] => do pure ((← Kernel.prims[k.label]?).1, ← primT k.label)
  | Kernel.Label.ref, [(n, _)] => do pure (← gt[n.label]?, call (lib.length + n.label) [] [])
  | Kernel.Label.lcase, [(A, _), (B, _)] => do
    pure (Kernel.lcaseTy A B, lcaseT (← ty A) (← ty B))
  | Kernel.Label.para, [(A, _)] => do pure (Kernel.foldTy A, paraT (← ty A))
  | _, _ => none

/-- The translation of a kernel term in a context, with the types of the globals: its kernel
type and its translation. -/
def term (gt Γ : List Tree) (t : Tree) : Option (Tree × Term) := RoseTree.para termStep t gt Γ

/-- The translation of a program's definitions, each closed, over those before it: the
kernel types of the globals and the definitions of the language, which follow the library's. -/
def program (ds : List Tree) : Option (List Tree × List Defn) :=
  ds.foldl (fun acc t ↦ do
    let (gt, defs) ← acc
    let (A, u) ← term gt [] t
    pure (gt ++ [A], defs ++ [mkDefn 0 [] (← ty A) u])) (some ([], []))

/-- The constants of a translated program: the primitive arrows, and the library's definitions
followed by the program's, whose operations follow the signature's. -/
def globals (defs : List Defn) : Globals :=
  ⟨prims, (lib ++ defs).map Definition.language, sig.length⟩

/-- The translation of a theorem of Gödel's T, with the types of the globals: the
equality of its sides' translations, in the translation of its context. -/
def thm (gt : List Tree) (a : GoedelT.Thm) : Option Internal.Thm := do
  let Γ ← a.ctx.mapM ty
  let (_, l) ← term gt a.ctx a.eqn.lhs
  let (_, r) ← term gt a.ctx a.eqn.rhs
  pure ⟨0, Γ, [], Term.eq l r⟩

end Geb.FreeTopos.Translation

end
