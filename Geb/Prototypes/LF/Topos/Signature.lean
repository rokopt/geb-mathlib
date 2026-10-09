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
binary products, exponentials, the subobject classifier and the natural numbers object; the
terms built from variables by the element of the terminal object, pairs and their components,
abstraction and application, zero and the successor, each applied to a term as the primitive
arrows of {lit}`Geb.FreeTopos.Internal` are, the fold of the natural numbers, and the
equality of two terms, a formula; and the derivability of formulas.

The object types are the canonical terms of the type {lit}`tp`. A term of an object type
{lit}`A` is a canonical term of {lit}`tm A`, a variable of the language a variable of LF, and an
abstraction a constant {lit}`lam` applied to an LF abstraction, so that the language's binders
are LF's, in the manner of higher-order abstract syntax ({cite}`HarperLicata2007`, Section 3.1).
The step of a fold is an LF abstraction over the recursion's value. A derivation of a formula
{lit}`φ` is a canonical term of {lit}`pf φ`, built from constants, one for each rule:

* the equality of a term with itself, and the substitution of equals into a predicate, an LF
  abstraction ({lit}`refl`, {lit}`leib`), from which symmetry, transitivity and congruence are
  derived;
* the β rule of abstraction, the computation and η rules of pairs, the η rule of the terminal
  type, and the computation rules of the fold ({lit}`beta`, {lit}`fstPair`, {lit}`sndPair`,
  {lit}`pairEta`, {lit}`unitEta`, {lit}`natZero`, {lit}`natSucc`);
* the extensionality of functions and of formulas ({lit}`funExt`, {lit}`propExt`);
* induction over the natural numbers, its predicate an LF abstraction ({lit}`natInd`).

These are rules of a local set theory ({cite}`RuizHernandezSolorzano2021`, Section 3.2) and of
the derivations of {lit}`Geb.FreeTopos.Internal`, whose induction applies to the innermost
variable where this one names its predicate. The fold is the language's: its start and its step,
an LF abstraction, may mention the variables around it, so that the fold has parameters, as the
folds with a parameter of a cartesian closed category with a natural numbers object do.

## Main definitions

* {lit}`objSig`, {lit}`ruleSig`, {lit}`sig` — the declarations of the types and terms, of the
  rules, and the signature of both.
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

/-- The signature of the fragment: the types and terms, then the rules. -/
def sig : Sig := objSig ++ ruleSig

end Geb.LF.Topos

end
