/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Definitional

set_option doc.verso true in
/-!
# A constant equal to its own successor

The equation {lit}`c = succ(c)`, over zero and successor with a new constant {lit}`c`, is a
guarded block rather than a definition of {lit}`c` by a term of zero and successor. Its
presentation creates nothing: closed terms of zero and successor with one class are equal
({lit}`eq_of_cls_inlTerm_eq_cls`). It does not eliminate {lit}`c`: the class of {lit}`c` is the
class of no such term ({lit}`cls_inlTerm_ne_cls_c`). And the natural numbers are a model of it
for no value of {lit}`c` ({lit}`not_satisfies_natAlg`). Both separations are by the model whose
values are the closed terms of zero and successor together with one further value for
{lit}`c`, fixed by successor.

## Main definitions

* {lit}`constEq` — the presentation of {lit}`c = succ(c)`.
* {lit}`optAlg` — the closed terms of zero and successor, and a value for {lit}`c`.

## Main statements

* {lit}`eval_optAlg_inlTerm` — a closed term of zero and successor is its own value.
* {lit}`cls_inlTerm_ne_cls_c`, {lit}`eq_of_cls_inlTerm_eq_cls` — the presentation neither
  eliminates {lit}`c` nor creates identifications.
* {lit}`not_satisfies_natAlg` — no natural number satisfies the equation.

## Tags

guarded recursion, equational presentation, non-eliminable constant, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.ConstantTests

open PFunctor Geb.Definition.Presentation

/-- The operations of the natural numbers: zero and successor. -/
inductive Op
  | zero
  | succ

/-- The arguments of an operation: none for zero, one for successor. -/
def arity : Op → Type
  | .zero => PEmpty
  | .succ => Unit

/-- The signature of zero and successor. -/
abbrev natSig : PFunctor.{0, 0} := ⟨Op, arity⟩

/-- The signature of one constant. -/
abbrev constSig : PFunctor.{0, 0} := ⟨Unit, fun _ ↦ PEmpty⟩

/-- Zero and successor with the constant. -/
abbrev sig : PFunctor.{0, 0} := sum natSig constSig

/-- The constant. -/
def c : sig.FreeM PEmpty := FreeM.liftBind (P := sig) (.inr ()) fun x ↦ nomatch x

/-- The successor of a term. -/
def succ (t : sig.FreeM PEmpty) : sig.FreeM PEmpty :=
  FreeM.liftBind (P := sig) (.inl Op.succ) fun _ ↦ t

/-- The presentation of {lit}`c = succ(c)`: one equation, without variables. -/
def constEq : Presentation.{0, 0, 0} sig where
  E := ⟨Unit, fun _ ↦ PEmpty⟩
  lhs _ := FreeM.liftBind (P := sig) (.inr ()) fun x ↦ nomatch x
  rhs _ := FreeM.liftBind (P := sig) (.inl Op.succ) fun _ ↦
    FreeM.liftBind (P := sig) (.inr ()) fun x ↦ nomatch x

/-- The closed terms of zero and successor, and a further value, {lit}`none`, for the constant,
fixed by successor. -/
def optAlg : sig.Obj (Option (natSig.FreeM PEmpty)) → Option (natSig.FreeM PEmpty)
  | ⟨.inl .zero, _⟩ => some (.liftBind Op.zero fun x ↦ nomatch x)
  | ⟨.inl .succ, k⟩ => (k ()).map fun t ↦ .liftBind Op.succ fun _ ↦ t
  | ⟨.inr (), _⟩ => none

/-- The model satisfies the equation: the value of the constant is fixed by successor. -/
theorem optAlg_satisfies : constEq.Satisfies optAlg := fun _ _ ↦ rfl

/-- A closed term of zero and successor is its own value. -/
theorem eval_optAlg_inlTerm (t : natSig.FreeM PEmpty) :
    eval optAlg PEmpty.elim (inlTerm constSig t) = some t := by
  refine FreeM.rec (motive := fun t ↦ eval optAlg PEmpty.elim (inlTerm constSig t) = some t)
    (fun x ↦ nomatch x) ?_ t
  intro a ts ih
  cases a with
  | zero =>
    change some (FreeM.liftBind (P := natSig) Op.zero fun x ↦ nomatch x) = _
    exact congrArg (fun k ↦ some (FreeM.liftBind (P := natSig) Op.zero k))
      (funext fun x : PEmpty ↦ nomatch x)
  | succ =>
    exact congrArg (Option.map fun t ↦ FreeM.liftBind (P := natSig) Op.succ fun _ ↦ t) (ih ())

/-- The value of classes in the model. -/
def value : constEq.Cls PEmpty → Option (natSig.FreeM PEmpty) :=
  constEq.lift optAlg optAlg_satisfies PEmpty.elim

/-- The constant is not eliminable: its class is the class of no closed term of zero and
successor. -/
theorem cls_inlTerm_ne_cls_c (t : natSig.FreeM PEmpty) :
    constEq.cls (inlTerm constSig t) ≠ constEq.cls c := fun h ↦ by
  have hv := congrArg value h
  change eval optAlg PEmpty.elim (inlTerm constSig t) = none at hv
  rw [eval_optAlg_inlTerm] at hv
  exact nomatch hv

/-- The presentation creates no identifications: closed terms of zero and successor with one
class are equal. -/
theorem eq_of_cls_inlTerm_eq_cls {s t : natSig.FreeM PEmpty}
    (h : constEq.cls (inlTerm constSig s) = constEq.cls (inlTerm constSig t)) : s = t := by
  have hv := congrArg value h
  change eval optAlg PEmpty.elim (inlTerm constSig s) =
    eval optAlg PEmpty.elim (inlTerm constSig t) at hv
  rw [eval_optAlg_inlTerm, eval_optAlg_inlTerm] at hv
  exact Option.some.inj hv

/-- The natural numbers, the constant read as {lit}`v`. -/
def natAlg (v : ℕ) : sig.Obj ℕ → ℕ
  | ⟨.inl .zero, _⟩ => 0
  | ⟨.inl .succ, k⟩ => k () + 1
  | ⟨.inr (), _⟩ => v

/-- No natural number is a solution of {lit}`c = succ(c)`. -/
theorem not_satisfies_natAlg (v : ℕ) : ¬ constEq.Satisfies (natAlg v) := fun h ↦ by
  have hv : v = v + 1 := h () fun x ↦ nomatch x
  omega

end Geb.Definition.ConstantTests

end
