/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Theory

set_option doc.verso true in
/-!
# The operations of a model of the theory of an elementary topos

A model of the partial Horn theory {lit}`theory` interprets each operation as a partial
function on sorted values. This module reads the model's objects and arrows as types and its
operations as functions on the arguments at which the axioms make them defined, and states the
axioms as equations between those functions: the domain, the codomain, identities and
composition with the laws of a category.

The value of an operation defined at its arguments is the value the model's partial function
returns, read at the operation's result sort ({name}`Geb.PartialHorn.Model.get`), so no value is
chosen.

## Main definitions

* {lit}`dom`, {lit}`cod`, {lit}`idA`, {lit}`compA` — the domain, the codomain, identities and
  composition of a model of the theory.

## Main statements

* {lit}`dom_compA`, {lit}`cod_compA`, {lit}`compA_assoc`, {lit}`compA_idA`, {lit}`idA_compA` —
  the laws of a category.

## Tags

elementary topos, model, partial Horn logic, category
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts

universe v

/-- A model of the theory of an elementary topos with the data objects. -/
structure ToposModel where
  /-- The model. -/
  model : PartialHorn.Model.{v} sig
  /-- The model satisfies the axioms. -/
  isModel : IsModel theory model

namespace ToposModel

variable (T : ToposModel.{v})

/-- The objects of a model. -/
abbrev Obj : Type v := T.model.Car obj

/-- The arrows of a model. -/
abbrev Ar : Type v := T.model.Car arr

/-- An axiom of the category block, by index, is valid in the model. -/
theorem axCategory (k : ℕ) (hk : k < categoryAxioms.length := by decide) :
    (categoryAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- The simplification of a term's value at explicit values, with the given lemmas: the
terms' builders unfold, and the value of each operation's application is the operation at its
arguments' values. -/
local macro "simp_eval" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [x, dfd, dom, cod, idt, comp, eval_op, eval_var, List.mapM_cons,
    List.mapM_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, $ls,*] at *)

/-- Every arrow has a domain. -/
theorem domOf_exists (f : T.Ar) : ∃ o, T.model.op 0 [⟨arr, f⟩] = some ⟨obj, o⟩ := by
  have h : Valid T.model [arr] [] (dfd (dom (x 0))) := T.axCategory 0
  obtain ⟨w, hw, -⟩ := h [⟨arr, f⟩] rfl (by simp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The domain of an arrow. -/
def domOf (f : T.Ar) : T.Obj := T.model.get (T.domOf_exists f)

/-- The model's domain operation at an arrow. -/
@[simp] theorem op_domOf (f : T.Ar) : T.model.op 0 [⟨arr, f⟩] = some ⟨obj, T.domOf f⟩ :=
  T.model.op_eq_get _

/-- Every arrow has a codomain. -/
theorem codOf_exists (f : T.Ar) : ∃ o, T.model.op 1 [⟨arr, f⟩] = some ⟨obj, o⟩ := by
  have h : Valid T.model [arr] [] (dfd (cod (x 0))) := T.axCategory 1
  obtain ⟨w, hw, -⟩ := h [⟨arr, f⟩] rfl (by simp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The codomain of an arrow. -/
def codOf (f : T.Ar) : T.Obj := T.model.get (T.codOf_exists f)

/-- The model's codomain operation at an arrow. -/
@[simp] theorem op_codOf (f : T.Ar) : T.model.op 1 [⟨arr, f⟩] = some ⟨obj, T.codOf f⟩ :=
  T.model.op_eq_get _

/-- Every object has an identity. -/
theorem idOf_exists (a : T.Obj) : ∃ i, T.model.op 2 [⟨obj, a⟩] = some ⟨arr, i⟩ := by
  have h : Valid T.model [obj] [] (dfd (idt (x 0))) := T.axCategory 2
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The identity of an object. -/
def idOf (a : T.Obj) : T.Ar := T.model.get (T.idOf_exists a)

/-- The model's identity operation at an object. -/
@[simp] theorem op_idOf (a : T.Obj) : T.model.op 2 [⟨obj, a⟩] = some ⟨arr, T.idOf a⟩ :=
  T.model.op_eq_get _

/-- Two arrows compose when the codomain of the first is the domain of the second. -/
theorem compOf_exists {g f : T.Ar} (h : T.codOf f = T.domOf g) :
    ∃ c, T.model.op 3 [⟨arr, g⟩, ⟨arr, f⟩] = some ⟨arr, c⟩ := by
  have hv : Valid T.model [arr, arr] [⟨cod (x 1), dom (x 0)⟩] (dfd (comp (x 0) (x 1))) :=
    T.axCategory 4
  obtain ⟨w, hw, -⟩ := hv [⟨arr, g⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq, Eqn.Holds]
    simp_eval [op_codOf, op_domOf, h]
    exact ⟨_, rfl, rfl⟩)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The composite of {lit}`g` after {lit}`f`. -/
def compOf (g f : T.Ar) (h : T.codOf f = T.domOf g) : T.Ar := T.model.get (T.compOf_exists h)

/-- The model's composition at two composable arrows. -/
@[simp] theorem op_compOf {g f : T.Ar} (h : T.codOf f = T.domOf g) :
    T.model.op 3 [⟨arr, g⟩, ⟨arr, f⟩] = some ⟨arr, T.compOf g f h⟩ :=
  T.model.op_eq_get _

/-- Two values an equation's sides have at an assignment where it holds are equal. -/
theorem holds_eq {ρ : List T.model.Val} {q : Eqn} (h : q.Holds T.model ρ) {a b : T.model.Val}
    (ha : eval T.model ρ q.lhs = some a) (hb : eval T.model ρ q.rhs = some b) : a = b := by
  obtain ⟨w, h1, h2⟩ := h
  rw [ha] at h1
  rw [hb] at h2
  exact (Option.some.inj h1).trans (Option.some.inj h2).symm

/-- Two values of one sort are equal when they are equal as sorted values. -/
theorem val_inj {s : ℕ} {a b : T.model.Car s} (h : (⟨s, a⟩ : T.model.Val) = ⟨s, b⟩) : a = b :=
  eq_of_heq (Sigma.mk.inj h).2

/-- The domain of a composite is the domain of its first arrow. -/
theorem domOf_compOf {g f : T.Ar} (h : T.codOf f = T.domOf g) :
    T.domOf (T.compOf g f h) = T.domOf f := by
  have hv : Valid T.model [arr, arr] [dfd (comp (x 0) (x 1))]
      ⟨dom (comp (x 0) (x 1)), dom (x 1)⟩ := T.axCategory 5
  have hq := hv [⟨arr, g⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨arr, T.compOf g f h⟩, by simp_eval [T.op_compOf h], by simp_eval [T.op_compOf h]⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_compOf h, op_domOf])
    (by simp_eval [op_domOf])

/-- The codomain of a composite is the codomain of its second arrow. -/
theorem codOf_compOf {g f : T.Ar} (h : T.codOf f = T.domOf g) :
    T.codOf (T.compOf g f h) = T.codOf g := by
  have hv : Valid T.model [arr, arr] [dfd (comp (x 0) (x 1))]
      ⟨cod (comp (x 0) (x 1)), cod (x 0)⟩ := T.axCategory 6
  have hq := hv [⟨arr, g⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨arr, T.compOf g f h⟩, by simp_eval [T.op_compOf h], by simp_eval [T.op_compOf h]⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_compOf h, op_codOf])
    (by simp_eval [op_codOf])

/-- The domain of an identity. -/
theorem domOf_idOf (a : T.Obj) : T.domOf (T.idOf a) = a := by
  have hv : Valid T.model [obj] [] ⟨dom (idt (x 0)), x 0⟩ := T.axCategory 8
  exact T.val_inj <| T.holds_eq (hv [⟨obj, a⟩] rfl (by simp)) (by simp_eval [op_idOf, op_domOf])
    (by simp_eval [])

/-- The codomain of an identity. -/
theorem codOf_idOf (a : T.Obj) : T.codOf (T.idOf a) = a := by
  have hv : Valid T.model [obj] [] ⟨cod (idt (x 0)), x 0⟩ := T.axCategory 9
  exact T.val_inj <| T.holds_eq (hv [⟨obj, a⟩] rfl (by simp)) (by simp_eval [op_idOf, op_codOf])
    (by simp_eval [])

/-- An arrow after the identity of its domain is the arrow. -/
theorem compOf_idOf (f : T.Ar) :
    T.compOf f (T.idOf (T.domOf f)) (T.codOf_idOf _) = f := by
  have hv : Valid T.model [arr] [] ⟨comp (x 0) (idt (dom (x 0))), x 0⟩ := T.axCategory 10
  exact T.val_inj <| T.holds_eq (hv [⟨arr, f⟩] rfl (by simp))
    (by simp_eval [op_domOf, op_idOf, T.op_compOf (T.codOf_idOf _)]) (by simp_eval [])

/-- The identity of an arrow's codomain after the arrow is the arrow. -/
theorem idOf_compOf (f : T.Ar) :
    T.compOf (T.idOf (T.codOf f)) f (T.domOf_idOf _).symm = f := by
  have hv : Valid T.model [arr] [] ⟨comp (idt (cod (x 0))) (x 0), x 0⟩ := T.axCategory 11
  exact T.val_inj <| T.holds_eq (hv [⟨arr, f⟩] rfl (by simp))
    (by simp_eval [op_codOf, op_idOf, T.op_compOf (T.domOf_idOf _).symm]) (by simp_eval [])

/-- Composition is associative. -/
theorem compOf_assoc {h g f : T.Ar} (hgf : T.codOf f = T.domOf g)
    (hhg : T.codOf g = T.domOf h) :
    T.compOf h (T.compOf g f hgf) ((T.codOf_compOf hgf).trans hhg) =
      T.compOf (T.compOf h g hhg) f (hgf.trans (T.domOf_compOf hhg).symm) := by
  have hv : Valid T.model [arr, arr, arr] [dfd (comp (x 0) (comp (x 1) (x 2)))]
      ⟨comp (x 0) (comp (x 1) (x 2)), comp (comp (x 0) (x 1)) (x 2)⟩ := T.axCategory 7
  have hq := hv [⟨arr, h⟩, ⟨arr, g⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨arr, T.compOf h (T.compOf g f hgf) ((T.codOf_compOf hgf).trans hhg)⟩,
      by simp_eval [T.op_compOf hgf, T.op_compOf ((T.codOf_compOf hgf).trans hhg)],
      by simp_eval [T.op_compOf hgf, T.op_compOf ((T.codOf_compOf hgf).trans hhg)]⟩)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_compOf hgf, T.op_compOf ((T.codOf_compOf hgf).trans hhg)])
    (by simp_eval [T.op_compOf hhg, T.op_compOf (hgf.trans (T.domOf_compOf hhg).symm)])

end ToposModel

end Geb.FreeTopos

end
