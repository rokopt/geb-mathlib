/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Syntax
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The internal language of a topos as an LF signature

An LF signature ({cite}`HarperHonsellPlotkin1993`; {cite}`HarperLicata2007`, Section 3, for the
method) representing a fragment of the Mitchell–Bénabou language of the free elementary topos with
a natural numbers object ({cite}`MacLaneMoerdijk1992`, Section VI.5), whose terms and
derivations are those of {lit}`Geb.FreeTopos.Internal`: the types built from the terminal object,
binary products, exponentials, the subobject classifier, the natural numbers object, list objects
and the rose-tree object of natural-number labels; the terms built from variables by the element
of the terminal object, pairs and their components, abstraction and application, zero and the
successor, the empty list and the construction of a list, the construction of a rose tree, each
applied to a term as the primitive arrows of {lit}`Geb.FreeTopos.Internal` are, the folds of the
natural numbers, of lists and of rose trees, and the equality of two terms, a formula; and the
derivability of formulas.

The object types are the canonical terms of the type {lit}`tp`. A term of an object type
{lit}`A` is a canonical term of {lit}`tm A`, a variable of the language a variable of LF, and an
abstraction a constant {lit}`lam` applied to an LF abstraction, so that the language's binders
are LF's, in the manner of higher-order abstract syntax ({cite}`HarperLicata2007`, Section 3.1).
The step of a fold is an LF abstraction over the recursion's value, over the element before it for
a list, and over the pair of a label and the list of the children's values for a rose tree. A
derivation of a formula
{lit}`φ` is a canonical term of {lit}`pf φ`, built from constants, one for each rule:

* the equality of a term with itself, and the substitution of equals into a predicate, an LF
  abstraction ({lit}`refl`, {lit}`leib`), from which symmetry, transitivity and congruence are
  derived;
* the β rule of abstraction, the computation and η rules of pairs, the η rule of the terminal
  type, and the computation rules of the folds ({lit}`beta`, {lit}`fstPair`, {lit}`sndPair`,
  {lit}`pairEta`, {lit}`unitEta`, {lit}`natZero`, {lit}`natSucc`, {lit}`listNil`,
  {lit}`listCons`, {lit}`roseNode`);
* the extensionality of functions and of formulas ({lit}`funExt`, {lit}`propExt`);
* induction over the natural numbers, lists and rose trees, its predicate an LF abstraction
  ({lit}`natInd`, {lit}`listInd`, {lit}`roseInd`), the hypothesis at a rose tree's children
  being that the list of the predicate's values at them is the list of truths.

These are rules of a local set theory ({cite}`RuizHernandezSolorzano2021`, Section 3.2) and of
the derivations of {lit}`Geb.FreeTopos.Internal`, whose induction applies to the innermost
variable where this one names its predicate. The folds are the language's: a start and a step,
an LF abstraction, may mention the variables around them, so that the folds have parameters, as
the folds with a parameter of a cartesian closed category with a natural numbers object or list
objects do. The declarations of lists, then of rose trees, follow the rules, so that the indices
of the declarations before each are those of the signature without it.

## Main definitions

* {lit}`objSig`, {lit}`ruleSig`, {lit}`listSig`, {lit}`roseSig`, {lit}`sig` — the declarations of
  the types and terms, of the rules, of lists and of rose trees, and the signature of all.
* {lit}`tp`, {lit}`tm`, {lit}`pf` and the constants' applications — the expressions of the
  signature.

## References

* {cite}`HarperLicata2007`, Section 3.
* {cite}`MacLaneMoerdijk1992`, Section VI.5.
* {cite}`RuizHernandezSolorzano2021`, Section 3.2.

## Tags

logical framework, LF, higher-order abstract syntax, Mitchell–Bénabou language, local set theory
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

/-- The variable of a de Bruijn index, applied to no argument. -/
abbrev v (i : ℕ) : Expr := Expr.var i

/-- The type of object types (index 0). -/
def tp : Expr := Expr.const 0

/-- The terminal object (1). -/
def one : Expr := Expr.const 1

/-- The binary product (2). -/
def prod (a b : Expr) : Expr := Expr.const 2 [a, b]

/-- The exponential {lit}`exp A B`, of functions from {lit}`A` to {lit}`B` (3). -/
def exp (a b : Expr) : Expr := Expr.const 3 [a, b]

/-- The subobject classifier, the type of formulas (4). -/
def omega : Expr := Expr.const 4

/-- The natural numbers object (5). -/
def nat : Expr := Expr.const 5

/-- The family of terms of an object type (6). -/
def tm (a : Expr) : Expr := Expr.const 6 [a]

/-- The element of the terminal object (7). -/
def star : Expr := Expr.const 7

/-- The pair of two terms (8). -/
def pair (a b s t : Expr) : Expr := Expr.const 8 [a, b, s, t]

/-- The first component of a pair (9). -/
def fst (a b p : Expr) : Expr := Expr.const 9 [a, b, p]

/-- The second component of a pair (10). -/
def snd (a b p : Expr) : Expr := Expr.const 10 [a, b, p]

/-- The abstraction of a term, given as an LF abstraction (11). -/
def lam (a b f : Expr) : Expr := Expr.const 11 [a, b, f]

/-- The application of a term of an exponential to an argument (12). -/
def app (a b f s : Expr) : Expr := Expr.const 12 [a, b, f, s]

/-- Zero, the primitive arrow from the terminal object applied to a term of it (13). -/
def zeroAt (t : Expr) : Expr := Expr.const 13 [t]

/-- Zero at the element of the terminal object. -/
def zero : Expr := zeroAt star

/-- The successor (14). -/
def succ (n : Expr) : Expr := Expr.const 14 [n]

/-- The fold of a natural number into the type {lit}`C` from a start by a step, an LF
abstraction (15). -/
def natRec (c z s n : Expr) : Expr := Expr.const 15 [c, z, s, n]

/-- The equality of two terms of a type, a formula (16). -/
def eq (a s t : Expr) : Expr := Expr.const 16 [a, s, t]

/-- The family of derivations of a formula (17). -/
def pf (φ : Expr) : Expr := Expr.const 17 [φ]

/-- The list object of an object type (30). -/
def list (a : Expr) : Expr := Expr.const 30 [a]

/-- The empty list of elements of {lit}`A`, the primitive arrow from the terminal object applied
to a term of it (31). -/
def nilAt (a t : Expr) : Expr := Expr.const 31 [a, t]

/-- The empty list at the element of the terminal object. -/
def nil (a : Expr) : Expr := nilAt a star

/-- The construction of a list of elements of {lit}`A`, applied to a pair of an element and a
list (32). -/
def cons (a p : Expr) : Expr := Expr.const 32 [a, p]

/-- The fold of a list of elements of {lit}`A` into the type {lit}`C` from a start by a step, an
LF abstraction over the element and the value (33). -/
def listRec (a c z s l : Expr) : Expr := Expr.const 33 [a, c, z, s, l]

/-- The rose-tree object of natural-number labels (37). -/
def rose : Expr := Expr.const 37

/-- The construction of a rose tree, applied to a pair of a label and a list of trees (38). -/
def node (p : Expr) : Expr := Expr.const 38 [p]

/-- The fold of a rose tree into the type {lit}`C` by a step, an LF abstraction over the pair of a
label and the list of the children's values (39). -/
def roseRec (c s t : Expr) : Expr := Expr.const 39 [c, s, t]

open Expr in
/-- The declarations of the types and terms: {lit}`tp`, the object types, {lit}`tm`, the term
constants, {lit}`eq` and {lit}`pf`. -/
def objSig : Sig :=
  [ type,
    tp,
    arrow tp (arrow tp tp),
    arrow tp (arrow tp tp),
    tp,
    tp,
    arrow tp type,
    tm one,
    pi tp (pi tp (arrow (tm (v 1)) (arrow (tm (v 0)) (tm (prod (v 1) (v 0)))))),
    pi tp (pi tp (arrow (tm (prod (v 1) (v 0))) (tm (v 1)))),
    pi tp (pi tp (arrow (tm (prod (v 1) (v 0))) (tm (v 0)))),
    pi tp (pi tp (arrow (arrow (tm (v 1)) (tm (v 0))) (tm (exp (v 1) (v 0))))),
    pi tp (pi tp (arrow (tm (exp (v 1) (v 0))) (arrow (tm (v 1)) (tm (v 0))))),
    arrow (tm one) (tm nat),
    arrow (tm nat) (tm nat),
    pi tp (arrow (tm (v 0)) (arrow (arrow (tm (v 0)) (tm (v 0))) (arrow (tm nat) (tm (v 0))))),
    pi tp (arrow (tm (v 0)) (arrow (tm (v 0)) (tm omega))),
    arrow (tm omega) type ]

open Expr in
/-- The declarations of the rules, from index 18: {lit}`refl`, {lit}`leib`, {lit}`beta`,
{lit}`fstPair`, {lit}`sndPair`, {lit}`pairEta`, {lit}`unitEta`, {lit}`natZero`,
{lit}`natSucc`, {lit}`funExt`, {lit}`propExt` and {lit}`natInd`. -/
def ruleSig : Sig :=
  [ -- refl : Π A:tp. Π t:tm A. pf (eq A t t)
    pi tp (pi (tm (v 0)) (pf (eq (v 1) (v 0) (v 0)))),
    -- leib : Π A:tp. Π P:tm A → tm Ω. Π t u:tm A. pf (eq A t u) → pf (P t) → pf (P u)
    pi tp (pi (arrow (tm (v 0)) (tm omega)) (pi (tm (v 1)) (pi (tm (v 2))
      (arrow (pf (eq (v 3) (v 1) (v 0)))
        (arrow (pf (var 2 [v 1])) (pf (var 2 [v 0]))))))),
    -- beta : Π A B:tp. Π f:tm A → tm B. Π a:tm A. pf (eq B (app A B (lam A B (λx. f x)) a) (f a))
    pi tp (pi tp (pi (arrow (tm (v 1)) (tm (v 0))) (pi (tm (v 2))
      (pf (eq (v 2) (app (v 3) (v 2) (lam (v 3) (v 2) (Expr.lam (var 2 [v 0]))) (v 0))
        (var 1 [v 0])))))),
    -- fstPair : Π A B:tp. Π a:tm A. Π b:tm B. pf (eq A (fst A B (pair A B a b)) a)
    pi tp (pi tp (pi (tm (v 1)) (pi (tm (v 1))
      (pf (eq (v 3) (fst (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))) (v 1)))))),
    -- sndPair : Π A B:tp. Π a:tm A. Π b:tm B. pf (eq B (snd A B (pair A B a b)) b)
    pi tp (pi tp (pi (tm (v 1)) (pi (tm (v 1))
      (pf (eq (v 2) (snd (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))) (v 0)))))),
    -- pairEta : Π A B:tp. Π p:tm (A × B). pf (eq (A × B) (pair A B (fst A B p) (snd A B p)) p)
    pi tp (pi tp (pi (tm (prod (v 1) (v 0)))
      (pf (eq (prod (v 2) (v 1))
        (pair (v 2) (v 1) (fst (v 2) (v 1) (v 0)) (snd (v 2) (v 1) (v 0))) (v 0))))),
    -- unitEta : Π t:tm 1. pf (eq 1 t star)
    pi (tm one) (pf (eq one (v 0) star)),
    -- natZero : Π C:tp. Π z:tm C. Π s:tm C → tm C. pf (eq C (natRec C z (λx. s x) zero) z)
    pi tp (pi (tm (v 0)) (pi (arrow (tm (v 1)) (tm (v 1)))
      (pf (eq (v 2) (natRec (v 2) (v 1) (Expr.lam (var 1 [v 0])) zero) (v 1))))),
    -- natSucc : Π C z s. Π n:tm N.
    --   pf (eq C (natRec C z (λx. s x) (succ n)) (s (natRec C z (λx. s x) n)))
    pi tp (pi (tm (v 0)) (pi (arrow (tm (v 1)) (tm (v 1))) (pi (tm nat)
      (pf (eq (v 3) (natRec (v 3) (v 2) (Expr.lam (var 2 [v 0])) (succ (v 0)))
        (var 1 [natRec (v 3) (v 2) (Expr.lam (var 2 [v 0])) (v 0)])))))),
    -- funExt : Π A B:tp. Π f g:tm (exp A B).
    --   (Π x:tm A. pf (eq B (app A B f x) (app A B g x))) → pf (eq (exp A B) f g)
    pi tp (pi tp (pi (tm (exp (v 1) (v 0))) (pi (tm (exp (v 2) (v 1)))
      (arrow (pi (tm (v 3))
          (pf (eq (v 3) (app (v 4) (v 3) (v 2) (v 0)) (app (v 4) (v 3) (v 1) (v 0)))))
        (pf (eq (exp (v 3) (v 2)) (v 1) (v 0))))))),
    -- propExt : Π φ ψ:tm Ω. (pf φ → pf ψ) → (pf ψ → pf φ) → pf (eq Ω φ ψ)
    pi (tm omega) (pi (tm omega)
      (arrow (arrow (pf (v 1)) (pf (v 0)))
        (arrow (arrow (pf (v 0)) (pf (v 1))) (pf (eq omega (v 1) (v 0)))))),
    -- natInd : Π P:tm N → tm Ω. pf (P zero) → (Π n:tm N. pf (P n) → pf (P (succ n))) →
    --   Π n:tm N. pf (P n)
    pi (arrow (tm nat) (tm omega))
      (arrow (pf (var 0 [zero]))
        (arrow (pi (tm nat) (arrow (pf (var 1 [v 0])) (pf (var 1 [succ (v 0)]))))
          (pi (tm nat) (pf (var 1 [v 0]))))) ]

open Expr in
/-- The declarations of lists, from index 30: the list object {lit}`list`, the empty list
{lit}`nilAt`, the construction {lit}`cons` and the fold {lit}`listRec`, then the rules
{lit}`listNil`, {lit}`listCons` and {lit}`listInd`. -/
def listSig : Sig :=
  [ arrow tp tp,
    -- nilAt : Π A:tp. tm 1 → tm (list A)
    pi tp (arrow (tm one) (tm (list (v 0)))),
    -- cons : Π A:tp. tm (A × list A) → tm (list A)
    pi tp (arrow (tm (prod (v 0) (list (v 0)))) (tm (list (v 0)))),
    -- listRec : Π A C:tp. tm C → (tm A → tm C → tm C) → tm (list A) → tm C
    pi tp (pi tp (arrow (tm (v 0)) (arrow (arrow (tm (v 1)) (arrow (tm (v 0)) (tm (v 0))))
      (arrow (tm (list (v 1))) (tm (v 0)))))),
    -- listNil : Π A C:tp. Π z:tm C. Π s:tm A → tm C → tm C.
    --   pf (eq C (listRec A C z (λh r. s h r) (nil A)) z)
    pi tp (pi tp (pi (tm (v 0)) (pi (arrow (tm (v 2)) (arrow (tm (v 1)) (tm (v 1))))
      (pf (eq (v 2) (listRec (v 3) (v 2) (v 1) (Expr.lam (Expr.lam (var 2 [v 1, v 0])))
        (nil (v 3))) (v 1)))))),
    -- listCons : Π A C z s. Π h:tm A. Π t:tm (list A).
    --   pf (eq C (listRec A C z (λh r. s h r) (cons A (pair A (list A) h t)))
    --     (s h (listRec A C z (λh r. s h r) t)))
    pi tp (pi tp (pi (tm (v 0)) (pi (arrow (tm (v 2)) (arrow (tm (v 1)) (tm (v 1))))
      (pi (tm (v 3)) (pi (tm (list (v 4)))
        (pf (eq (v 4)
          (listRec (v 5) (v 4) (v 3) (Expr.lam (Expr.lam (var 4 [v 1, v 0])))
            (cons (v 5) (pair (v 5) (list (v 5)) (v 1) (v 0))))
          (var 2 [v 1, listRec (v 5) (v 4) (v 3) (Expr.lam (Expr.lam (var 4 [v 1, v 0])))
            (v 0)])))))))),
    -- listInd : Π A:tp. Π P:tm (list A) → tm Ω. pf (P (nil A)) →
    --   (Π h:tm A. Π t:tm (list A). pf (P t) → pf (P (cons A (pair A (list A) h t)))) →
    --   Π l:tm (list A). pf (P l)
    pi tp (pi (arrow (tm (list (v 0))) (tm omega))
      (arrow (pf (var 0 [nil (v 1)]))
        (arrow (pi (tm (v 1)) (pi (tm (list (v 2)))
            (arrow (pf (var 2 [v 0]))
              (pf (var 2 [cons (v 3) (pair (v 3) (list (v 3)) (v 1) (v 0))])))))
          (pi (tm (list (v 1))) (pf (var 1 [v 0])))))) ]

open Expr in
/-- The declarations of rose trees, from index 37: the rose-tree object {lit}`rose`, the
construction {lit}`node` and the fold {lit}`roseRec`, then the rules {lit}`roseNode` and
{lit}`roseInd`. -/
def roseSig : Sig :=
  [ tp,
    -- node : tm (N × list rose) → tm rose
    arrow (tm (prod nat (list rose))) (tm rose),
    -- roseRec : Π C:tp. (tm (N × list C) → tm C) → tm rose → tm C
    pi tp (arrow (arrow (tm (prod nat (list (v 0)))) (tm (v 0))) (arrow (tm rose) (tm (v 0)))),
    -- roseNode : Π C:tp. Π s:tm (N × list C) → tm C. Π l:tm N. Π cs:tm (list rose).
    --   pf (eq C (roseRec C (λx. s x) (node (pair l cs)))
    --     (s (pair l (listRec rose (list C) (nil C)
    --       (λh acc. cons C (pair (roseRec C (λx. s x) h) acc)) cs))))
    pi tp (pi (arrow (tm (prod nat (list (v 0)))) (tm (v 0))) (pi (tm nat) (pi (tm (list rose))
      (pf (eq (v 3) (roseRec (v 3) (Expr.lam (var 3 [v 0]))
          (node (pair nat (list rose) (v 1) (v 0))))
        (var 2 [pair nat (list (v 3)) (v 1) (listRec rose (list (v 3)) (nil (v 3))
          (Expr.lam (Expr.lam (cons (v 5) (pair (v 5) (list (v 5))
            (roseRec (v 5) (Expr.lam (var 5 [v 0])) (v 1)) (v 0))))) (v 0))])))))),
    -- roseInd : Π P:tm rose → tm Ω.
    --   (Π l:tm N. Π cs:tm (list rose).
    --     pf (eq (list Ω) (listRec rose (list Ω) (nil Ω) (λh acc. cons Ω (pair (P h) acc)) cs)
    --       (listRec rose (list Ω) (nil Ω) (λh acc. cons Ω (pair (eq 1 star star) acc)) cs)) →
    --     pf (P (node (pair l cs)))) →
    --   Π t:tm rose. pf (P t)
    pi (arrow (tm rose) (tm omega))
      (arrow (pi (tm nat) (pi (tm (list rose))
          (arrow (pf (eq (list omega)
              (listRec rose (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (var 4 [v 1]) (v 0))))) (v 0))
              (listRec rose (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (eq one star star) (v 0))))) (v 0))))
            (pf (var 2 [node (pair nat (list rose) (v 1) (v 0))])))))
        (pi (tm rose) (pf (var 1 [v 0])))) ]

/-- The signature of the fragment: the types and terms, then the rules, then lists, then rose
trees. -/
def sig : Sig := objSig ++ ruleSig ++ listSig ++ roseSig

end Geb.LF.Topos

end
