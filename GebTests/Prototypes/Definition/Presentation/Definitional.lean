/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Definitional

set_option doc.verso true in
/-!
# A definition of depth two as a presentation

Over a signature with zero, successor and doubling, the operation {lit}`quad` is defined by
{lit}`quad(x) = double(double(x))`, a body of depth two, which no one-step presentation
expresses. The presentation of the definition changes nothing: a term using {lit}`quad` has the
class of its unfolding, distinct terms of the signature keep distinct classes, and the natural
numbers, with {lit}`quad` read through its body, are a model of it.

## Main definitions

* {lit}`sig` — zero, successor and doubling.
* {lit}`quadDef` — the definition of {lit}`quad`.
* {lit}`natAlg` — the natural numbers.

## Main statements

* {lit}`unfoldOps_quad` — the unfolding of a use of {lit}`quad` is its body.
* {lit}`cls_quad` — a use of {lit}`quad` has the class of its unfolding.
* {lit}`cls_zero_ne_cls_one` — zero and one keep distinct classes.

## Tags

definition, definitional extension, equational presentation, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.DefinitionalTests

open PFunctor Geb.Definition.Presentation

/-- The operations: zero, successor and doubling. -/
inductive Op
  | zero
  | succ
  | double

/-- The arguments of an operation: none for zero, one for successor and doubling. -/
def arity : Op → Type
  | .zero => PEmpty
  | .succ => Unit
  | .double => Unit

/-- The signature of zero, successor and doubling. -/
abbrev sig : PFunctor.{0, 0} := ⟨Op, arity⟩

/-- The signature of the defined operation: one operation of one argument. -/
abbrev quadSig : PFunctor.{0, 0} := ⟨Unit, fun _ ↦ Unit⟩

variable {Γ : Type}

/-- Zero. -/
def zero : sig.FreeM Γ := .liftBind Op.zero fun x : PEmpty ↦ nomatch x

/-- The successor of a term. -/
def succ (t : sig.FreeM Γ) : sig.FreeM Γ := .liftBind Op.succ fun _ ↦ t

/-- The double of a term. -/
def double (t : sig.FreeM Γ) : sig.FreeM Γ := .liftBind Op.double fun _ ↦ t

/-- The definition {lit}`quad(x) = double(double(x))`. -/
def quadDef : Derived sig quadSig := fun _ ↦ double (double (.pure ()))

/-- The defined operation applied to a term. -/
def quad (t : (sum sig quadSig).FreeM Γ) : (sum sig quadSig).FreeM Γ :=
  FreeM.liftBind (P := sum sig quadSig) (.inr ()) fun _ ↦ t

/-- The unfolding of a use of {lit}`quad` is its body at the argument. -/
theorem unfoldOps_quad (t : sig.FreeM Γ) :
    unfoldOps quadDef (quad (inlTerm quadSig t)) = double (double t) :=
  congrArg (fun s ↦ double (double s)) (unfoldOps_inlTerm quadDef t)

/-- A use of {lit}`quad` has the class of its unfolding. -/
theorem cls_quad (t : sig.FreeM Γ) :
    (ofDerived quadDef).cls (quad (inlTerm quadSig t)) =
      (ofDerived quadDef).cls (inlTerm quadSig (double (double t))) :=
  (cls_inlTerm_unfoldOps quadDef _).symm.trans
    (congrArg (fun s ↦ (ofDerived quadDef).cls (inlTerm quadSig s)) (unfoldOps_quad t))

/-- Zero and one keep distinct classes: the presentation identifies no terms of the
signature. -/
theorem cls_zero_ne_cls_one :
    (ofDerived quadDef).cls (inlTerm quadSig (zero : sig.FreeM Γ)) ≠
      (ofDerived quadDef).cls (inlTerm quadSig (succ zero)) := fun h ↦
  nomatch ((FreeM.liftBind_inj _ _ _ _).mp (eq_of_cls_inlTerm_eq quadDef h)).1

/-- The natural numbers: zero, successor and doubling. -/
def natAlg : sig.Obj ℕ → ℕ
  | ⟨.zero, _⟩ => 0
  | ⟨.succ, k⟩ => k () + 1
  | ⟨.double, k⟩ => 2 * k ()

-- The natural numbers, with `quad` read through its body, are a model, in which `quad` of three
-- is twelve.
example : (ofDerived quadDef).Satisfies (derivedAlg natAlg (handler quadDef)) :=
  satisfies_derivedAlg quadDef natAlg

example : eval (derivedAlg natAlg (handler quadDef)) (fun _ : Unit ↦ 3) (quad (.pure ())) = 12 :=
  rfl

-- The classes are the terms of the signature.
example : (ofDerived quadDef).Cls Γ ≃ sig.FreeM Γ := clsEquivBase quadDef

end Geb.Definition.DefinitionalTests

end
