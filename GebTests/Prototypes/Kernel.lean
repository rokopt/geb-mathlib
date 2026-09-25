/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel -- shake: keep
public meta import Geb.Prototypes.Kernel -- shake: keep

set_option doc.verso true in
/-!
# Kernel examples

Programs written in the kernel's readable syntax, read, checked and run: factorial beyond a
machine word by iteration, the size and the mirror image of a tree by the fold, the reversal
of a list by the right fold, case analysis of lists, definitions referring to earlier ones,
a conditional, and the reader's type abbreviations, lists of binders and local bindings.
Ill-typed, malformed and unresolved programs, and programs whose last definition is not a
function on trees, are rejected. A program's bundle round-trips through its image and runs a
named definition; truncated, extended, altered and mislabelled images, and bundles referring
forward, are rejected.

The programs are string constants, converted to lists of characters inside each
{lit}`#guard`: core's {lit}`String.toList` depends on {lit}`Classical.choice`, and a
{lit}`#guard` is not a declaration, so no declaration here acquires that dependency.

## Main definitions

* {lit}`datum` reads a quoted tree from text.
* {lit}`imageOf` writes the image of a program's bundle.
* {lit}`factorial`, {lit}`size`, {lit}`reverse`, {lit}`mirror`, {lit}`reverseChildren`,
  {lit}`quadruple`, {lit}`isZero`, {lit}`listCase`, {lit}`sugar` and {lit}`numerals` are
  programs.

## Tags

bootstrap, kernel, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Tests

/-- The tree a datum's text denotes, or the leaf of label zero. -/
def datum (s : List Char) : Tree :=
  ((readSExps s).bind (·.head?) |>.bind readDatum).getD (leaf 0)

/-- Factorial, iterating over pairs of a counter and a product. -/
def factorial : String := "
; n! as the second component after n steps from (0, 1)
(def fact (lam (n T)
  (snd (iter (Prod T T)
         (lam (p (Prod T T)) (pair (add (fst p) 1) (mul (snd p) (add (fst p) 1))))
         (pair 0 1)
         n))))"

/-- The number of nodes of a tree. -/
def size : String := "
(def sum (lam (xs (List T)) (foldr T T (lam (a T) (lam (b T) (add a b))) 0 xs)))
(def size (lam (t T) (fold T (lam (l T) (lam (rs (List T)) (add 1 (sum rs)))) t)))"

/-- The reversal of a list, in linear time by a right fold into functions. -/
def reverse : String := "
(def rev (lam (xs (List T))
  ((foldr T (Arrow (List T) (List T))
     (lam (x T) (lam (k (Arrow (List T) (List T))) (lam (acc (List T)) (k (cons x acc)))))
     (lam (acc (List T)) acc)
     xs)
   (nil T))))"

/-- The mirror image of a tree: the children of every node in reverse order. -/
def mirror : String := reverse ++ "
(def mirror (lam (t T) (fold T (lam (l T) (lam (rs (List T)) (node l (rev rs)))) t)))"

/-- The root's children in reverse order, the subtrees unchanged. -/
def reverseChildren : String := reverse ++ "
(def main (lam (t T) (node t (rev (children t)))))"

/-- A definition referring to an earlier one. -/
def quadruple : String := "
(def double (lam (x T) (add x x)))
(def quadruple (lam (x T) (double (double x))))"

/-- The conditional on a label. -/
def isZero : String := "(def isZero (lam (x T) (if x 0 1)))"

/-- Case analysis of lists: the tree labelled by the root's first child, over the remaining
children, or the leaf of label zero for a leaf. -/
def listCase : String := "
(def main (lam ((t T))
  (lcase T T (children t) 0 (lam ((x T) (r (List T))) (node x r)))))"

/-- A type abbreviation, abstractions over lists of binders, and a local binding. -/
def sugar : String := "
(deftype Pair (Prod T T))
(def swap (lam ((p Pair)) (pair (snd p) (fst p))))
(def add3 (lam ((x T) (y T) (z T)) (add x (add y z))))
(def main (lam (t T) (let s T (add3 t t t) (fst (swap (pair t s))))))"

/-- Numeral abbreviations, one naming another, read in a term and in a quoted datum. -/
def numerals : String := "
(defnum two 2)
(defnum pairLabel two)
(def main (lam ((t T)) (node 0 (cons (add t two) (cons (quote (pairLabel 5 two)) (nil T))))))"

#guard runMain factorial.toList (leaf 30) = some (leaf 265252859812191058636308480000000)
#guard runMain factorial.toList (leaf 0) = some (leaf 1)
#guard runMain size.toList (datum "(1 (2) (3 (4) (5)))".toList) = some (leaf 5)
#guard runMain mirror.toList (datum "(1 (2) (3 (4) (5)))".toList) =
  some (datum "(1 (3 (5) (4)) (2))".toList)
#guard runMain reverseChildren.toList (datum "(1 (2 (5) (6)) (3) (4))".toList) =
  some (datum "(1 (4) (3) (2 (5) (6)))".toList)
#guard runMain quadruple.toList (leaf 5) = some (leaf 20)
#guard runMain isZero.toList (leaf 0) = some (leaf 1)
#guard runMain isZero.toList (leaf 7) = some (leaf 0)
#guard runMain sugar.toList (leaf 5) = some (leaf 15)
#guard runMain numerals.toList (leaf 3) = some (mk 0 [leaf 5, mk 2 [leaf 5, leaf 2]])
#guard runMain listCase.toList (datum "(9 (4) (5) (6))".toList) =
  some (datum "(4 (5) (6))".toList)
#guard runMain listCase.toList (leaf 9) = some (leaf 0)
#guard runMain "(def f (lam () 1))".toList (leaf 1) = none
#guard runMain "(deftype P (Prod T T)) (def f (lam (x T) P))".toList (leaf 1) = none
#guard runMain "(def f (lam (x Q) x))".toList (leaf 1) = none
#guard runMain "(def f (lam (x T) (add x 18446744073709551615)))".toList (leaf 1) =
  some (leaf 18446744073709551616)
-- ill-typed
#guard runMain "(def f (lam (x T) (add x unit)))".toList (leaf 1) = none
#guard runMain "(def f (lam (x T) (x x)))".toList (leaf 1) = none
#guard runMain "(def f (lam (x T) (if x unit 1)))".toList (leaf 1) = none
-- malformed or unresolved
#guard runMain "(def f (lam (x T) x)".toList (leaf 1) = none
#guard runMain "(def f (lam (x T) y))".toList (leaf 1) = none
#guard runMain "(def f (lam (x Nat) x))".toList (leaf 1) = none
#guard runMain "(defnum n m) (def f (lam (x T) x))".toList (leaf 1) = none
#guard runMain "(defnum n (1 2)) (def f (lam (x T) x))".toList (leaf 1) = none
-- the last definition is not a function on trees
#guard runMain "(def f unit)".toList (leaf 1) = none

/-- The image of a program's bundle, or the empty image when the program does not read. -/
def imageOf (text : List Char) : ByteArray :=
  ((readProgram text).map (writeImage ∘ bundle)).getD .empty

-- an image round-trips and runs its named definitions
#guard readImage (imageOf quadruple.toList) == (readProgram quadruple.toList).map bundle
#guard (readImage (imageOf quadruple.toList)).bind (runEntry · "double".toList (leaf 5)) =
  some (leaf 10)
#guard (readImage (imageOf quadruple.toList)).bind (runEntry · "quadruple".toList (leaf 5)) =
  some (leaf 20)
#guard (readImage (imageOf quadruple.toList)).bind (runEntry · "triple".toList (leaf 5)) = none
-- malformed images
#guard readImage ((imageOf quadruple.toList).extract 0 ((imageOf quadruple.toList).size - 1)) =
  none
#guard readImage ((imageOf quadruple.toList).push 0) = none
#guard readImage ((imageOf quadruple.toList).set! 0 0) = none
#guard readImage ((imageOf quadruple.toList).set! 4 2) = none
#guard readImage ((imageOf quadruple.toList).set! 20 0xFF) !=
  readImage (imageOf quadruple.toList)
#guard readImage .empty = none
-- a bundle whose definition refers to itself, and a tree that is not a bundle
#guard runEntry (mk 100 [mk 101 [mk 23 [leaf 0]], mk 102 [nameTree "f".toList]]) "f".toList
  (leaf 0) = none
#guard unbundle (leaf 0) = none
-- files as trees
#guard (toBytes (ofBytes ⟨#[1, 2, 255]⟩)).map (·.data) = some #[1, 2, 255]
#guard toBytes (mk 0 [leaf 256]) = none
-- weakening shifts the free variables of a term and not its bound ones, and substitution
-- replaces the innermost free variable, weakened under a binder, and lowers the others
#guard wk 2 (mk 9 [tT, mk 10 [Tm.var 0, Tm.var 1]]) = mk 9 [tT, mk 10 [Tm.var 0, Tm.var 3]]
#guard subst (Tm.var 4) (mk 12 [Tm.var 0, Tm.var 1]) = mk 12 [Tm.var 4, Tm.var 0]
#guard subst (Tm.var 4) (mk 9 [tT, Tm.var 1]) = mk 9 [tT, Tm.var 5]
#guard subst (Tm.var 4) (mk 15 [Tm.var 0]) = mk 15 [Tm.var 0]
-- a substituted term keeps its type
#guard ((infer [] [tT] (subst (mk 15 [leaf 7]) (mk 12 [Tm.var 0, Tm.var 1]))).map (·.1)) =
  some (tProd tT tT)

end Geb.Kernel.Tests

end
