/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF

/-!
# Tests for canonical LF

The signature of the simply typed λ-calculus with its terms indexed by their types, after
Section 3 of Harper and Licata's "Mechanizing metatheory in a logical framework": the type of
object types {lit}`tp`, the function type {lit}`arr`, the family {lit}`tm` of terms of a type,
and abstraction {lit}`lam`, higher-order in its body, and application {lit}`app`. The signature
is well formed; the identity abstraction and an application of it check against their types;
the variable of a function type, not η-expanded, does not check where an abstraction is
expected; a variable does not check against a type other than its own; and the hereditary
substitution of the identity for a variable at the head of an application reduces the redex it
creates.

## Tags

prototype, logical framework, LF, canonical forms, hereditary substitution
-/

@[expose] public section

namespace Geb.LF.Tests

open Expr

/-- The intrinsically typed simply typed λ-calculus: {lit}`tp : type` (index 0),
{lit}`arr : tp → tp → tp` (1), {lit}`tm : tp → type` (2),
{lit}`lam : Π A B:tp. (tm A → tm B) → tm (arr A B)` (3) and
{lit}`app : Π A B:tp. tm (arr A B) → tm A → tm B` (4). -/
def stlc : Sig :=
  [ type,
    pi (const 0) (pi (const 0) (const 0)),
    pi (const 0) type,
    pi (const 0) (pi (const 0) (pi (pi (const 2 [var 1]) (const 2 [var 1]))
      (const 2 [const 1 [var 2, var 1]]))),
    pi (const 0) (pi (const 0) (pi (const 2 [const 1 [var 1, var 0]])
      (pi (const 2 [var 2]) (const 2 [var 2])))) ]

/-- The signature is well formed. -/
theorem stlc_ok : stlc.ok = true := by decide

/-- The identity abstraction at a type variable {lit}`A : tp` is a term of {lit}`tm (arr A A)`. -/
theorem lam_id_checks :
    Checks stlc [const 0] (const 3 [var 0, var 0, lam (var 0)])
      (const 2 [const 1 [var 0, var 0]]) = true := by
  decide

/-- The identity abstraction applied to a variable {lit}`y : tm A` is a term of {lit}`tm A`. -/
theorem app_lam_id_checks :
    Checks stlc [const 2 [var 0], const 0]
      (const 4 [var 1, var 1, const 3 [var 1, var 1, lam (var 0)], var 0])
      (const 2 [var 1]) = true := by
  decide

/-- A variable {lit}`f : tm A → tm A` given as the body of {lit}`lam` without η-expansion does
not check: the argument expects an abstraction. -/
theorem lam_eta_short_fails :
    Checks stlc [pi (const 2 [var 0]) (const 2 [var 1]), const 0]
      (const 3 [var 1, var 1, var 0]) (const 2 [const 1 [var 1, var 1]]) = false := by
  decide

/-- Its η-expansion {lit}`λ x. f x` checks. -/
theorem lam_eta_long_checks :
    Checks stlc [pi (const 2 [var 0]) (const 2 [var 1]), const 0]
      (const 3 [var 1, var 1, lam (var 1 [var 0])]) (const 2 [const 1 [var 1, var 1]]) = true := by
  decide

/-- A variable {lit}`y : tm A` does not check against {lit}`tm (arr A A)`. -/
theorem var_wrong_type_fails :
    Checks stlc [const 2 [var 0], const 0] (var 0) (const 2 [const 1 [var 1, var 1]]) = false := by
  decide

/-- Substituting {lit}`λ x. x` for {lit}`f` in {lit}`f y`, at the simple type of a function
between base types, reduces to {lit}`y`, renumbered past the removed variable. -/
theorem hsub_reduces :
    hsub (RoseTree.node .arrow [RoseTree.node (.base 0) [], RoseTree.node (.base 0) []])
      (lam (var 0)) (var 0 [var 1]) 0 = some (var 0) := by
  decide

end Geb.LF.Tests

end
