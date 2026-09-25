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
composition with the laws of a category; the terminal and initial objects; binary products and
coproducts; and equalizers and coequalizers, each with the equations and the uniqueness of its
universal property.

The value of an operation defined at its arguments is the value the model's partial function
returns, read at the operation's result sort ({name}`Geb.PartialHorn.Model.get`), so no value is
chosen.

## Main definitions

* {lit}`ToposModel` — a model of the theory with its proof.
* {lit}`ToposModel.domOf`, {lit}`ToposModel.codOf`, {lit}`ToposModel.idOf`,
  {lit}`ToposModel.compOf` — the domain, the codomain, identities and composition.
* {lit}`ToposModel.oneOf`, {lit}`ToposModel.prodOf`, {lit}`ToposModel.eqzOf`,
  {lit}`ToposModel.zeroOf`, {lit}`ToposModel.coprodOf`, {lit}`ToposModel.coeqzOf` — the finite
  limits and colimits, with their universal morphisms.

## Main statements

* {lit}`ToposModel.compOf_assoc`, {lit}`ToposModel.compOf_idOf`, {lit}`ToposModel.idOf_compOf`
  — the laws of a category.
* {lit}`ToposModel.eq_bangOf`, {lit}`ToposModel.pairOf_eta`, {lit}`ToposModel.eqLiftOf_eta`,
  {lit}`ToposModel.eq_absurdOf`, {lit}`ToposModel.copairOf_eta`,
  {lit}`ToposModel.coeqDescOf_eta` — the uniqueness of each universal morphism.

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
  `(tactic| simp only [x, dfd, dom, cod, idt, comp, one, bang, prod, fst, snd, pair, eqz, eqIncl,
    eqLift, zero, absurd, coprod, inl, inr, copair, coeqz, coeqProj, coeqDesc, exp, ev, curry,
    omega, tru, chi, chiInv, nat, zeroN, succ, natRec, list, nil, cons, listRec, rose, node,
    roseRec, prodMapLeft, prodMapRight, listMap, monoCond, truthEq, truthIncl, truthLift,
    eval_op, eval_var, List.mapM_cons,
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

/-- Composites of equal arrows are equal, whatever the proofs that they compose. -/
theorem compOf_congr {g g' f f' : T.Ar} (hg : g = g') (hf : f = f') (h : T.codOf f = T.domOf g)
    (h' : T.codOf f' = T.domOf g') : T.compOf g f h = T.compOf g' f' h' := by
  subst hg hf
  rfl

/-- An axiom of the terminal block, by index, is valid in the model. -/
theorem axTerminal (k : ℕ) (hk : k < terminalAxioms.length := by decide) :
    (terminalAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- The terminal object is defined. -/
theorem oneOf_exists : ∃ o, T.model.op 4 [] = some ⟨obj, o⟩ := by
  have h : Valid T.model [] [] (dfd one) := T.axTerminal 0
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The terminal object. -/
def oneOf : T.Obj := T.model.get T.oneOf_exists

/-- The model's terminal object. -/
@[simp] theorem op_oneOf : T.model.op 4 [] = some ⟨obj, T.oneOf⟩ := T.model.op_eq_get _

/-- Every object has a morphism to the terminal object. -/
theorem bangOf_exists (a : T.Obj) : ∃ f, T.model.op 5 [⟨obj, a⟩] = some ⟨arr, f⟩ := by
  have h : Valid T.model [obj] [] ⟨dom (bang (x 0)), x 0⟩ := T.axTerminal 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval []
  obtain ⟨l, hl, -⟩ := Option.bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The morphism from an object to the terminal object. -/
def bangOf (a : T.Obj) : T.Ar := T.model.get (T.bangOf_exists a)

/-- The model's morphism to the terminal object. -/
@[simp] theorem op_bangOf (a : T.Obj) : T.model.op 5 [⟨obj, a⟩] = some ⟨arr, T.bangOf a⟩ :=
  T.model.op_eq_get _

/-- The domain of the morphism from an object to the terminal object is that object. -/
theorem domOf_bangOf (a : T.Obj) : T.domOf (T.bangOf a) = a := by
  have h : Valid T.model [obj] [] ⟨dom (bang (x 0)), x 0⟩ := T.axTerminal 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp)) (by simp_eval [op_bangOf, op_domOf])
    (by simp_eval [])

/-- The codomain of the morphism from an object to the terminal object is the terminal
object. -/
theorem codOf_bangOf (a : T.Obj) : T.codOf (T.bangOf a) = T.oneOf := by
  have h : Valid T.model [obj] [] ⟨cod (bang (x 0)), one⟩ := T.axTerminal 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp)) (by simp_eval [op_bangOf, op_codOf])
    (by simp_eval [op_oneOf])

/-- A morphism to the terminal object is the morphism from its domain. -/
theorem eq_bangOf {f : T.Ar} (hf : T.codOf f = T.oneOf) : f = T.bangOf (T.domOf f) := by
  have h : Valid T.model [arr] [⟨cod (x 0), one⟩] ⟨x 0, bang (dom (x 0))⟩ := T.axTerminal 3
  have hq := h [⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.oneOf⟩, by simp_eval [op_codOf, hf], by simp_eval [op_oneOf]⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval []) (by simp_eval [op_domOf, op_bangOf])

/-- An axiom of the product block, by index, is valid in the model. -/
theorem axProduct (k : ℕ) (hk : k < productAxioms.length := by decide) :
    (productAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Every two objects have a product. -/
theorem prodOf_exists (a b : T.Obj) :
    ∃ p, T.model.op 6 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨obj, p⟩ := by
  have h : Valid T.model [obj, obj] [] (dfd (prod (x 0) (x 1))) := T.axProduct 0
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The product of two objects. -/
def prodOf (a b : T.Obj) : T.Obj := T.model.get (T.prodOf_exists a b)

/-- The model's product of two objects. -/
@[simp] theorem op_prodOf (a b : T.Obj) :
    T.model.op 6 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨obj, T.prodOf a b⟩ :=
  T.model.op_eq_get _

/-- Every product has a first projection. -/
theorem fstOf_exists (a b : T.Obj) :
    ∃ f, T.model.op 7 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨arr, f⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (fst (x 0) (x 1)), prod (x 0) (x 1)⟩ :=
    T.axProduct 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval []
  obtain ⟨l, hl, -⟩ := Option.bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The first projection of a product. -/
def fstOf (a b : T.Obj) : T.Ar := T.model.get (T.fstOf_exists a b)

/-- The model's first projection. -/
@[simp] theorem op_fstOf (a b : T.Obj) :
    T.model.op 7 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨arr, T.fstOf a b⟩ :=
  T.model.op_eq_get _

/-- Every product has a second projection. -/
theorem sndOf_exists (a b : T.Obj) :
    ∃ f, T.model.op 8 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨arr, f⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (snd (x 0) (x 1)), prod (x 0) (x 1)⟩ :=
    T.axProduct 3
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval []
  obtain ⟨l, hl, -⟩ := Option.bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The second projection of a product. -/
def sndOf (a b : T.Obj) : T.Ar := T.model.get (T.sndOf_exists a b)

/-- The model's second projection. -/
@[simp] theorem op_sndOf (a b : T.Obj) :
    T.model.op 8 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨arr, T.sndOf a b⟩ :=
  T.model.op_eq_get _

/-- The domain of the first projection is the product. -/
theorem domOf_fstOf (a b : T.Obj) : T.domOf (T.fstOf a b) = T.prodOf a b := by
  have h : Valid T.model [obj, obj] [] ⟨dom (fst (x 0) (x 1)), prod (x 0) (x 1)⟩ :=
    T.axProduct 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_fstOf, op_domOf]) (by simp_eval [op_prodOf])

/-- The codomain of the first projection is the first factor. -/
theorem codOf_fstOf (a b : T.Obj) : T.codOf (T.fstOf a b) = a := by
  have h : Valid T.model [obj, obj] [] ⟨cod (fst (x 0) (x 1)), x 0⟩ := T.axProduct 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_fstOf, op_codOf]) (by simp_eval [])

/-- The domain of the second projection is the product. -/
theorem domOf_sndOf (a b : T.Obj) : T.domOf (T.sndOf a b) = T.prodOf a b := by
  have h : Valid T.model [obj, obj] [] ⟨dom (snd (x 0) (x 1)), prod (x 0) (x 1)⟩ :=
    T.axProduct 3
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_sndOf, op_domOf]) (by simp_eval [op_prodOf])

/-- The codomain of the second projection is the second factor. -/
theorem codOf_sndOf (a b : T.Obj) : T.codOf (T.sndOf a b) = b := by
  have h : Valid T.model [obj, obj] [] ⟨cod (snd (x 0) (x 1)), x 1⟩ := T.axProduct 4
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_sndOf, op_codOf]) (by simp_eval [])

/-- Two morphisms of one domain have a pairing. -/
theorem pairOf_exists {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    ∃ p, T.model.op 9 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨arr, p⟩ := by
  have hv : Valid T.model [arr, arr] [⟨dom (x 0), dom (x 1)⟩] (dfd (pair (x 0) (x 1))) :=
    T.axProduct 6
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.domOf g⟩, by simp_eval [op_domOf, h], by simp_eval [op_domOf]⟩)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The pairing of two morphisms of one domain. -/
def pairOf (f g : T.Ar) (h : T.domOf f = T.domOf g) : T.Ar := T.model.get (T.pairOf_exists h)

/-- The model's pairing. -/
@[simp] theorem op_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.model.op 9 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨arr, T.pairOf f g h⟩ :=
  T.model.op_eq_get _

/-- A pairing is defined at its components. -/
theorem holds_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    (dfd (pair (x 0) (x 1))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩] :=
  ⟨⟨arr, T.pairOf f g h⟩, by simp_eval [T.op_pairOf h], by simp_eval [T.op_pairOf h]⟩

/-- The domain of a pairing is its components' domain. -/
theorem domOf_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.domOf (T.pairOf f g h) = T.domOf f := by
  have hv : Valid T.model [arr, arr] [dfd (pair (x 0) (x 1))]
      ⟨dom (pair (x 0) (x 1)), dom (x 0)⟩ := T.axProduct 7
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_pairOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_pairOf h, op_domOf])
    (by simp_eval [op_domOf])

/-- The codomain of a pairing is the product of its components' codomains. -/
theorem codOf_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.codOf (T.pairOf f g h) = T.prodOf (T.codOf f) (T.codOf g) := by
  have hv : Valid T.model [arr, arr] [dfd (pair (x 0) (x 1))]
      ⟨cod (pair (x 0) (x 1)), prod (cod (x 0)) (cod (x 1))⟩ := T.axProduct 8
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_pairOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_pairOf h, op_codOf])
    (by simp_eval [op_codOf, op_prodOf])

/-- The first projection after a pairing is its first component. -/
theorem fstOf_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.compOf (T.fstOf (T.codOf f) (T.codOf g)) (T.pairOf f g h)
      ((T.codOf_pairOf h).trans (T.domOf_fstOf _ _).symm) = f := by
  have hv : Valid T.model [arr, arr] [dfd (pair (x 0) (x 1))]
      ⟨comp (fst (cod (x 0)) (cod (x 1))) (pair (x 0) (x 1)), x 0⟩ := T.axProduct 9
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_pairOf h)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_pairOf h, op_codOf, op_fstOf,
      T.op_compOf ((T.codOf_pairOf h).trans (T.domOf_fstOf _ _).symm)])
    (by simp_eval [])

/-- The second projection after a pairing is its second component. -/
theorem sndOf_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.compOf (T.sndOf (T.codOf f) (T.codOf g)) (T.pairOf f g h)
      ((T.codOf_pairOf h).trans (T.domOf_sndOf _ _).symm) = g := by
  have hv : Valid T.model [arr, arr] [dfd (pair (x 0) (x 1))]
      ⟨comp (snd (cod (x 0)) (cod (x 1))) (pair (x 0) (x 1)), x 1⟩ := T.axProduct 10
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_pairOf h)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_pairOf h, op_codOf, op_sndOf,
      T.op_compOf ((T.codOf_pairOf h).trans (T.domOf_sndOf _ _).symm)])
    (by simp_eval [])

/-- A morphism into a product is the pairing of its composites with the projections. -/
theorem pairOf_eta {k : T.Ar} {a b : T.Obj} (h : T.codOf k = T.prodOf a b) :
    T.pairOf (T.compOf (T.fstOf a b) k (h.trans (T.domOf_fstOf a b).symm))
      (T.compOf (T.sndOf a b) k (h.trans (T.domOf_sndOf a b).symm))
      ((T.domOf_compOf _).trans (T.domOf_compOf _).symm) = k := by
  have hv : Valid T.model [arr, obj, obj] [⟨cod (x 0), prod (x 1) (x 2)⟩]
      ⟨pair (comp (fst (x 1) (x 2)) (x 0)) (comp (snd (x 1) (x 2)) (x 0)), x 0⟩ :=
    T.axProduct 11
  have hq := hv [⟨arr, k⟩, ⟨obj, a⟩, ⟨obj, b⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.prodOf a b⟩, by simp_eval [op_codOf, h], by simp_eval [op_prodOf]⟩)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [op_fstOf, op_sndOf, T.op_compOf (h.trans (T.domOf_fstOf a b).symm),
      T.op_compOf (h.trans (T.domOf_sndOf a b).symm),
      T.op_pairOf ((T.domOf_compOf (h.trans (T.domOf_fstOf a b).symm)).trans
        (T.domOf_compOf (h.trans (T.domOf_sndOf a b).symm)).symm)])
    (by simp_eval [])

/-- An axiom of the equalizer block, by index, is valid in the model. -/
theorem axEqualizer (k : ℕ) (hk : k < equalizerAxioms.length := by decide) :
    (equalizerAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Two arrows are parallel: they have one domain and one codomain. -/
def Par (f g : T.Ar) : Prop := T.domOf f = T.domOf g ∧ T.codOf f = T.codOf g

/-- Two parallel arrows have an equalizer. -/
theorem eqzOf_exists {f g : T.Ar} (hp : T.Par f g) :
    ∃ e, T.model.op 10 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨obj, e⟩ := by
  have hv : Valid T.model [arr, arr] [⟨dom (x 0), dom (x 1)⟩, ⟨cod (x 0), cod (x 1)⟩]
      (dfd (eqz (x 0) (x 1))) := T.axEqualizer 2
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.domOf g⟩, by simp_eval [op_domOf, hp.1], by simp_eval [op_domOf]⟩,
      ⟨⟨obj, T.codOf g⟩, by simp_eval [op_codOf, hp.2], by simp_eval [op_codOf]⟩⟩)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The equalizer of two parallel arrows. -/
def eqzOf (f g : T.Ar) (hp : T.Par f g) : T.Obj := T.model.get (T.eqzOf_exists hp)

/-- The model's equalizer. -/
@[simp] theorem op_eqzOf {f g : T.Ar} (hp : T.Par f g) :
    T.model.op 10 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨obj, T.eqzOf f g hp⟩ :=
  T.model.op_eq_get _

/-- The equalizer of two parallel arrows is defined at them. -/
theorem holds_eqzOf {f g : T.Ar} (hp : T.Par f g) :
    (dfd (eqz (x 0) (x 1))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩] :=
  ⟨⟨obj, T.eqzOf f g hp⟩, by simp_eval [T.op_eqzOf hp], by simp_eval [T.op_eqzOf hp]⟩

/-- An equalizer has an inclusion. -/
theorem eqInclOf_exists {f g : T.Ar} (hp : T.Par f g) :
    ∃ e, T.model.op 11 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨arr, e⟩ := by
  have hv : Valid T.model [arr, arr] [dfd (eqz (x 0) (x 1))] (dfd (eqIncl (x 0) (x 1))) :=
    T.axEqualizer 4
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_eqzOf hp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The inclusion of the equalizer of two parallel arrows. -/
def eqInclOf (f g : T.Ar) (hp : T.Par f g) : T.Ar := T.model.get (T.eqInclOf_exists hp)

/-- The model's inclusion of an equalizer. -/
@[simp] theorem op_eqInclOf {f g : T.Ar} (hp : T.Par f g) :
    T.model.op 11 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨arr, T.eqInclOf f g hp⟩ :=
  T.model.op_eq_get _

/-- The domain of an equalizer's inclusion is the equalizer. -/
theorem domOf_eqInclOf {f g : T.Ar} (hp : T.Par f g) :
    T.domOf (T.eqInclOf f g hp) = T.eqzOf f g hp := by
  have hv : Valid T.model [arr, arr] [dfd (eqz (x 0) (x 1))]
      ⟨dom (eqIncl (x 0) (x 1)), eqz (x 0) (x 1)⟩ := T.axEqualizer 5
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_eqzOf hp)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_eqInclOf hp, op_domOf])
    (by simp_eval [T.op_eqzOf hp])

/-- The codomain of an equalizer's inclusion is the arrows' domain. -/
theorem codOf_eqInclOf {f g : T.Ar} (hp : T.Par f g) :
    T.codOf (T.eqInclOf f g hp) = T.domOf f := by
  have hv : Valid T.model [arr, arr] [dfd (eqz (x 0) (x 1))]
      ⟨cod (eqIncl (x 0) (x 1)), dom (x 0)⟩ := T.axEqualizer 6
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_eqzOf hp)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_eqInclOf hp, op_codOf])
    (by simp_eval [op_domOf])

/-- An equalizer's inclusion equalizes the arrows. -/
theorem compOf_eqInclOf {f g : T.Ar} (hp : T.Par f g) :
    T.compOf f (T.eqInclOf f g hp) (T.codOf_eqInclOf hp) =
      T.compOf g (T.eqInclOf f g hp) ((T.codOf_eqInclOf hp).trans hp.1) := by
  have hv : Valid T.model [arr, arr] [dfd (eqz (x 0) (x 1))]
      ⟨comp (x 0) (eqIncl (x 0) (x 1)), comp (x 1) (eqIncl (x 0) (x 1))⟩ := T.axEqualizer 7
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_eqzOf hp)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_eqInclOf hp, T.op_compOf (T.codOf_eqInclOf hp)])
    (by simp_eval [T.op_eqInclOf hp, T.op_compOf ((T.codOf_eqInclOf hp).trans hp.1)])

/-- A morphism that equalizes two parallel arrows factors through their equalizer. -/
theorem eqLiftOf_exists {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    ∃ l, T.model.op 12 [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] = some ⟨arr, l⟩ := by
  have hv : Valid T.model [arr, arr, arr]
      [dfd (eqz (x 0) (x 1)), ⟨comp (x 0) (x 2), comp (x 1) (x 2)⟩]
      (dfd (eqLift (x 0) (x 1) (x 2))) := T.axEqualizer 10
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.eqzOf f g hp⟩, by simp_eval [T.op_eqzOf hp], by simp_eval [T.op_eqzOf hp]⟩,
      ⟨⟨arr, T.compOf g k (hk.trans hp.1)⟩, by simp_eval [T.op_compOf hk, he],
        by simp_eval [T.op_compOf (hk.trans hp.1)]⟩⟩)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The factorization through the equalizer of two parallel arrows of a morphism that
equalizes them. -/
def eqLiftOf (f g k : T.Ar) (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) : T.Ar :=
  T.model.get (T.eqLiftOf_exists hp hk he)

/-- The model's factorization through an equalizer. -/
@[simp] theorem op_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    T.model.op 12 [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] = some ⟨arr, T.eqLiftOf f g k hp hk he⟩ :=
  T.model.op_eq_get _

/-- A factorization through an equalizer is defined at its arguments. -/
theorem holds_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    (dfd (eqLift (x 0) (x 1) (x 2))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] :=
  ⟨⟨arr, T.eqLiftOf f g k hp hk he⟩, by simp_eval [T.op_eqLiftOf hp hk he],
    by simp_eval [T.op_eqLiftOf hp hk he]⟩

/-- The domain of a factorization through an equalizer is the factored morphism's. -/
theorem domOf_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    T.domOf (T.eqLiftOf f g k hp hk he) = T.domOf k := by
  have hv : Valid T.model [arr, arr, arr] [dfd (eqLift (x 0) (x 1) (x 2))]
      ⟨dom (eqLift (x 0) (x 1) (x 2)), dom (x 2)⟩ := T.axEqualizer 11
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_eqLiftOf hp hk he)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_eqLiftOf hp hk he, op_domOf])
    (by simp_eval [op_domOf])

/-- The codomain of a factorization through an equalizer is the equalizer. -/
theorem codOf_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    T.codOf (T.eqLiftOf f g k hp hk he) = T.eqzOf f g hp := by
  have hv : Valid T.model [arr, arr, arr] [dfd (eqLift (x 0) (x 1) (x 2))]
      ⟨cod (eqLift (x 0) (x 1) (x 2)), eqz (x 0) (x 1)⟩ := T.axEqualizer 12
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_eqLiftOf hp hk he)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_eqLiftOf hp hk he, op_codOf])
    (by simp_eval [T.op_eqzOf hp])

/-- The inclusion after a factorization through an equalizer is the factored morphism. -/
theorem eqInclOf_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    T.compOf (T.eqInclOf f g hp) (T.eqLiftOf f g k hp hk he)
      ((T.codOf_eqLiftOf hp hk he).trans (T.domOf_eqInclOf hp).symm) = k := by
  have hv : Valid T.model [arr, arr, arr] [dfd (eqLift (x 0) (x 1) (x 2))]
      ⟨comp (eqIncl (x 0) (x 1)) (eqLift (x 0) (x 1) (x 2)), x 2⟩ := T.axEqualizer 13
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_eqLiftOf hp hk he)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_eqLiftOf hp hk he, T.op_eqInclOf hp,
      T.op_compOf ((T.codOf_eqLiftOf hp hk he).trans (T.domOf_eqInclOf hp).symm)])
    (by simp_eval [])

/-- The composite of two parallel arrows with an arrow into their equalizer, through the
inclusion, is equal. -/
theorem compOf_eqInclOf_comp {f g m : T.Ar} (hp : T.Par f g)
    (hm : T.codOf m = T.domOf (T.eqInclOf f g hp)) :
    T.compOf f (T.compOf (T.eqInclOf f g hp) m hm)
        ((T.codOf_compOf hm).trans (T.codOf_eqInclOf hp)) =
      T.compOf g (T.compOf (T.eqInclOf f g hp) m hm)
        (((T.codOf_compOf hm).trans (T.codOf_eqInclOf hp)).trans hp.1) :=
  calc _ = T.compOf (T.compOf f (T.eqInclOf f g hp) (T.codOf_eqInclOf hp)) m
        (hm.trans (T.domOf_compOf _).symm) := T.compOf_assoc hm (T.codOf_eqInclOf hp)
    _ = T.compOf (T.compOf g (T.eqInclOf f g hp) ((T.codOf_eqInclOf hp).trans hp.1)) m
        (hm.trans (T.domOf_compOf _).symm) := T.compOf_congr (T.compOf_eqInclOf hp) rfl _ _
    _ = _ := (T.compOf_assoc hm ((T.codOf_eqInclOf hp).trans hp.1)).symm

/-- A morphism into an equalizer is the factorization of its composite with the inclusion. -/
theorem eqLiftOf_eta {f g m : T.Ar} (hp : T.Par f g) (hm : T.codOf m = T.eqzOf f g hp) :
    T.eqLiftOf f g (T.compOf (T.eqInclOf f g hp) m (hm.trans (T.domOf_eqInclOf hp).symm)) hp
      ((T.codOf_compOf _).trans (T.codOf_eqInclOf hp)) (T.compOf_eqInclOf_comp hp _) = m := by
  have hv : Valid T.model [arr, arr, arr] [dfd (eqz (x 0) (x 1)), ⟨cod (x 2), eqz (x 0) (x 1)⟩]
      ⟨eqLift (x 0) (x 1) (comp (eqIncl (x 0) (x 1)) (x 2)), x 2⟩ := T.axEqualizer 14
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, m⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.eqzOf f g hp⟩, by simp_eval [T.op_eqzOf hp], by simp_eval [T.op_eqzOf hp]⟩,
      ⟨⟨obj, T.eqzOf f g hp⟩, by simp_eval [op_codOf, hm], by simp_eval [T.op_eqzOf hp]⟩⟩)
  have hlift := T.op_eqLiftOf hp ((T.codOf_compOf _).trans (T.codOf_eqInclOf hp))
    (T.compOf_eqInclOf_comp hp (hm.trans (T.domOf_eqInclOf hp).symm))
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_eqInclOf hp, T.op_compOf (hm.trans (T.domOf_eqInclOf hp).symm), hlift])
    (by simp_eval [])

/-- An axiom of the initial block, by index, is valid in the model. -/
theorem axInitial (k : ℕ) (hk : k < initialAxioms.length := by decide) :
    (initialAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- The initial object is defined. -/
theorem zeroOf_exists : ∃ o, T.model.op 13 [] = some ⟨obj, o⟩ := by
  have h : Valid T.model [] [] (dfd zero) := T.axInitial 0
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The initial object. -/
def zeroOf : T.Obj := T.model.get T.zeroOf_exists

/-- The model's initial object. -/
@[simp] theorem op_zeroOf : T.model.op 13 [] = some ⟨obj, T.zeroOf⟩ := T.model.op_eq_get _

/-- Every object has a morphism from the initial object. -/
theorem absurdOf_exists (a : T.Obj) : ∃ f, T.model.op 14 [⟨obj, a⟩] = some ⟨arr, f⟩ := by
  have h : Valid T.model [obj] [] ⟨dom (absurd (x 0)), zero⟩ := T.axInitial 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval []
  obtain ⟨l, hl, -⟩ := Option.bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The morphism from the initial object to an object. -/
def absurdOf (a : T.Obj) : T.Ar := T.model.get (T.absurdOf_exists a)

/-- The model's morphism from the initial object. -/
@[simp] theorem op_absurdOf (a : T.Obj) :
    T.model.op 14 [⟨obj, a⟩] = some ⟨arr, T.absurdOf a⟩ :=
  T.model.op_eq_get _

/-- The domain of the morphism from the initial object is the initial object. -/
theorem domOf_absurdOf (a : T.Obj) : T.domOf (T.absurdOf a) = T.zeroOf := by
  have h : Valid T.model [obj] [] ⟨dom (absurd (x 0)), zero⟩ := T.axInitial 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp))
    (by simp_eval [op_absurdOf, op_domOf]) (by simp_eval [op_zeroOf])

/-- The codomain of the morphism from the initial object to an object is that object. -/
theorem codOf_absurdOf (a : T.Obj) : T.codOf (T.absurdOf a) = a := by
  have h : Valid T.model [obj] [] ⟨cod (absurd (x 0)), x 0⟩ := T.axInitial 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp))
    (by simp_eval [op_absurdOf, op_codOf]) (by simp_eval [])

/-- A morphism from the initial object is the morphism to its codomain. -/
theorem eq_absurdOf {f : T.Ar} (hf : T.domOf f = T.zeroOf) : f = T.absurdOf (T.codOf f) := by
  have h : Valid T.model [arr] [⟨dom (x 0), zero⟩] ⟨x 0, absurd (cod (x 0))⟩ := T.axInitial 3
  have hq := h [⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.zeroOf⟩, by simp_eval [op_domOf, hf], by simp_eval [op_zeroOf]⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval []) (by simp_eval [op_codOf, op_absurdOf])

/-- An axiom of the coproduct block, by index, is valid in the model. -/
theorem axCoproduct (k : ℕ) (hk : k < coproductAxioms.length := by decide) :
    (coproductAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Every two objects have a coproduct. -/
theorem coprodOf_exists (a b : T.Obj) :
    ∃ p, T.model.op 15 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨obj, p⟩ := by
  have h : Valid T.model [obj, obj] [] (dfd (coprod (x 0) (x 1))) := T.axCoproduct 0
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The coproduct of two objects. -/
def coprodOf (a b : T.Obj) : T.Obj := T.model.get (T.coprodOf_exists a b)

/-- The model's coproduct of two objects. -/
@[simp] theorem op_coprodOf (a b : T.Obj) :
    T.model.op 15 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨obj, T.coprodOf a b⟩ :=
  T.model.op_eq_get _

/-- Every coproduct has a first injection. -/
theorem inlOf_exists (a b : T.Obj) :
    ∃ f, T.model.op 16 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨arr, f⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (inl (x 0) (x 1)), x 0⟩ := T.axCoproduct 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval []
  obtain ⟨l, hl, -⟩ := Option.bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The first injection into a coproduct. -/
def inlOf (a b : T.Obj) : T.Ar := T.model.get (T.inlOf_exists a b)

/-- The model's first injection. -/
@[simp] theorem op_inlOf (a b : T.Obj) :
    T.model.op 16 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨arr, T.inlOf a b⟩ :=
  T.model.op_eq_get _

/-- Every coproduct has a second injection. -/
theorem inrOf_exists (a b : T.Obj) :
    ∃ f, T.model.op 17 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨arr, f⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (inr (x 0) (x 1)), x 1⟩ := T.axCoproduct 3
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval []
  obtain ⟨l, hl, -⟩ := Option.bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := Option.bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The second injection into a coproduct. -/
def inrOf (a b : T.Obj) : T.Ar := T.model.get (T.inrOf_exists a b)

/-- The model's second injection. -/
@[simp] theorem op_inrOf (a b : T.Obj) :
    T.model.op 17 [⟨obj, a⟩, ⟨obj, b⟩] = some ⟨arr, T.inrOf a b⟩ :=
  T.model.op_eq_get _

/-- The domain of the first injection is the first summand. -/
theorem domOf_inlOf (a b : T.Obj) : T.domOf (T.inlOf a b) = a := by
  have h : Valid T.model [obj, obj] [] ⟨dom (inl (x 0) (x 1)), x 0⟩ := T.axCoproduct 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_inlOf, op_domOf]) (by simp_eval [])

/-- The codomain of the first injection is the coproduct. -/
theorem codOf_inlOf (a b : T.Obj) : T.codOf (T.inlOf a b) = T.coprodOf a b := by
  have h : Valid T.model [obj, obj] [] ⟨cod (inl (x 0) (x 1)), coprod (x 0) (x 1)⟩ :=
    T.axCoproduct 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_inlOf, op_codOf]) (by simp_eval [op_coprodOf])

/-- The domain of the second injection is the second summand. -/
theorem domOf_inrOf (a b : T.Obj) : T.domOf (T.inrOf a b) = b := by
  have h : Valid T.model [obj, obj] [] ⟨dom (inr (x 0) (x 1)), x 1⟩ := T.axCoproduct 3
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_inrOf, op_domOf]) (by simp_eval [])

/-- The codomain of the second injection is the coproduct. -/
theorem codOf_inrOf (a b : T.Obj) : T.codOf (T.inrOf a b) = T.coprodOf a b := by
  have h : Valid T.model [obj, obj] [] ⟨cod (inr (x 0) (x 1)), coprod (x 0) (x 1)⟩ :=
    T.axCoproduct 4
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_inrOf, op_codOf]) (by simp_eval [op_coprodOf])

/-- Two morphisms of one codomain have a copairing. -/
theorem copairOf_exists {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    ∃ p, T.model.op 18 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨arr, p⟩ := by
  have hv : Valid T.model [arr, arr] [⟨cod (x 0), cod (x 1)⟩] (dfd (copair (x 0) (x 1))) :=
    T.axCoproduct 6
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.codOf g⟩, by simp_eval [op_codOf, h], by simp_eval [op_codOf]⟩)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The copairing of two morphisms of one codomain. -/
def copairOf (f g : T.Ar) (h : T.codOf f = T.codOf g) : T.Ar :=
  T.model.get (T.copairOf_exists h)

/-- The model's copairing. -/
@[simp] theorem op_copairOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.model.op 18 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨arr, T.copairOf f g h⟩ :=
  T.model.op_eq_get _

/-- A copairing is defined at its components. -/
theorem holds_copairOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    (dfd (copair (x 0) (x 1))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩] :=
  ⟨⟨arr, T.copairOf f g h⟩, by simp_eval [T.op_copairOf h], by simp_eval [T.op_copairOf h]⟩

/-- The domain of a copairing is the coproduct of its components' domains. -/
theorem domOf_copairOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.domOf (T.copairOf f g h) = T.coprodOf (T.domOf f) (T.domOf g) := by
  have hv : Valid T.model [arr, arr] [dfd (copair (x 0) (x 1))]
      ⟨dom (copair (x 0) (x 1)), coprod (dom (x 0)) (dom (x 1))⟩ := T.axCoproduct 7
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_copairOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_copairOf h, op_domOf])
    (by simp_eval [op_domOf, op_coprodOf])

/-- The codomain of a copairing is its components' codomain. -/
theorem codOf_copairOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.codOf (T.copairOf f g h) = T.codOf f := by
  have hv : Valid T.model [arr, arr] [dfd (copair (x 0) (x 1))]
      ⟨cod (copair (x 0) (x 1)), cod (x 0)⟩ := T.axCoproduct 8
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_copairOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_copairOf h, op_codOf])
    (by simp_eval [op_codOf])

/-- A copairing after the first injection is its first component. -/
theorem copairOf_inlOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.compOf (T.copairOf f g h) (T.inlOf (T.domOf f) (T.domOf g))
      ((T.codOf_inlOf _ _).trans (T.domOf_copairOf h).symm) = f := by
  have hv : Valid T.model [arr, arr] [dfd (copair (x 0) (x 1))]
      ⟨comp (copair (x 0) (x 1)) (inl (dom (x 0)) (dom (x 1))), x 0⟩ := T.axCoproduct 9
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_copairOf h)
  have hc := T.op_compOf ((T.codOf_inlOf (T.domOf f) (T.domOf g)).trans (T.domOf_copairOf h).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_copairOf h, op_domOf, op_inlOf, hc])
    (by simp_eval [])

/-- A copairing after the second injection is its second component. -/
theorem copairOf_inrOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.compOf (T.copairOf f g h) (T.inrOf (T.domOf f) (T.domOf g))
      ((T.codOf_inrOf _ _).trans (T.domOf_copairOf h).symm) = g := by
  have hv : Valid T.model [arr, arr] [dfd (copair (x 0) (x 1))]
      ⟨comp (copair (x 0) (x 1)) (inr (dom (x 0)) (dom (x 1))), x 1⟩ := T.axCoproduct 10
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_copairOf h)
  have hc := T.op_compOf ((T.codOf_inrOf (T.domOf f) (T.domOf g)).trans (T.domOf_copairOf h).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_copairOf h, op_domOf, op_inrOf, hc])
    (by simp_eval [])

/-- A morphism from a coproduct is the copairing of its composites with the injections. -/
theorem copairOf_eta {k : T.Ar} {a b : T.Obj} (h : T.domOf k = T.coprodOf a b) :
    T.copairOf (T.compOf k (T.inlOf a b) ((T.codOf_inlOf a b).trans h.symm))
      (T.compOf k (T.inrOf a b) ((T.codOf_inrOf a b).trans h.symm))
      ((T.codOf_compOf _).trans (T.codOf_compOf _).symm) = k := by
  have hv : Valid T.model [arr, obj, obj] [⟨dom (x 0), coprod (x 1) (x 2)⟩]
      ⟨copair (comp (x 0) (inl (x 1) (x 2))) (comp (x 0) (inr (x 1) (x 2))), x 0⟩ :=
    T.axCoproduct 11
  have hq := hv [⟨arr, k⟩, ⟨obj, a⟩, ⟨obj, b⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.coprodOf a b⟩, by simp_eval [op_domOf, h], by simp_eval [op_coprodOf]⟩)
  have hl := T.op_compOf ((T.codOf_inlOf a b).trans h.symm)
  have hr := T.op_compOf ((T.codOf_inrOf a b).trans h.symm)
  have hp := T.op_copairOf ((T.codOf_compOf ((T.codOf_inlOf a b).trans h.symm)).trans
    (T.codOf_compOf ((T.codOf_inrOf a b).trans h.symm)).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [op_inlOf, op_inrOf, hl, hr, hp])
    (by simp_eval [])

/-- An axiom of the coequalizer block, by index, is valid in the model. -/
theorem axCoequalizer (k : ℕ) (hk : k < coequalizerAxioms.length := by decide) :
    (coequalizerAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Two parallel arrows have a coequalizer. -/
theorem coeqzOf_exists {f g : T.Ar} (hp : T.Par f g) :
    ∃ e, T.model.op 19 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨obj, e⟩ := by
  have hv : Valid T.model [arr, arr] [⟨dom (x 0), dom (x 1)⟩, ⟨cod (x 0), cod (x 1)⟩]
      (dfd (coeqz (x 0) (x 1))) := T.axCoequalizer 2
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.domOf g⟩, by simp_eval [op_domOf, hp.1], by simp_eval [op_domOf]⟩,
      ⟨⟨obj, T.codOf g⟩, by simp_eval [op_codOf, hp.2], by simp_eval [op_codOf]⟩⟩)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The coequalizer of two parallel arrows. -/
def coeqzOf (f g : T.Ar) (hp : T.Par f g) : T.Obj := T.model.get (T.coeqzOf_exists hp)

/-- The model's coequalizer. -/
@[simp] theorem op_coeqzOf {f g : T.Ar} (hp : T.Par f g) :
    T.model.op 19 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨obj, T.coeqzOf f g hp⟩ :=
  T.model.op_eq_get _

/-- The coequalizer of two parallel arrows is defined at them. -/
theorem holds_coeqzOf {f g : T.Ar} (hp : T.Par f g) :
    (dfd (coeqz (x 0) (x 1))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩] :=
  ⟨⟨obj, T.coeqzOf f g hp⟩, by simp_eval [T.op_coeqzOf hp], by simp_eval [T.op_coeqzOf hp]⟩

/-- A coequalizer has a projection. -/
theorem coeqProjOf_exists {f g : T.Ar} (hp : T.Par f g) :
    ∃ e, T.model.op 20 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨arr, e⟩ := by
  have hv : Valid T.model [arr, arr] [dfd (coeqz (x 0) (x 1))] (dfd (coeqProj (x 0) (x 1))) :=
    T.axCoequalizer 4
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_coeqzOf hp)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The projection onto the coequalizer of two parallel arrows. -/
def coeqProjOf (f g : T.Ar) (hp : T.Par f g) : T.Ar := T.model.get (T.coeqProjOf_exists hp)

/-- The model's projection onto a coequalizer. -/
@[simp] theorem op_coeqProjOf {f g : T.Ar} (hp : T.Par f g) :
    T.model.op 20 [⟨arr, f⟩, ⟨arr, g⟩] = some ⟨arr, T.coeqProjOf f g hp⟩ :=
  T.model.op_eq_get _

/-- The domain of a coequalizer's projection is the arrows' codomain. -/
theorem domOf_coeqProjOf {f g : T.Ar} (hp : T.Par f g) :
    T.domOf (T.coeqProjOf f g hp) = T.codOf f := by
  have hv : Valid T.model [arr, arr] [dfd (coeqz (x 0) (x 1))]
      ⟨dom (coeqProj (x 0) (x 1)), cod (x 0)⟩ := T.axCoequalizer 5
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_coeqzOf hp)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqProjOf hp, op_domOf])
    (by simp_eval [op_codOf])

/-- The codomain of a coequalizer's projection is the coequalizer. -/
theorem codOf_coeqProjOf {f g : T.Ar} (hp : T.Par f g) :
    T.codOf (T.coeqProjOf f g hp) = T.coeqzOf f g hp := by
  have hv : Valid T.model [arr, arr] [dfd (coeqz (x 0) (x 1))]
      ⟨cod (coeqProj (x 0) (x 1)), coeqz (x 0) (x 1)⟩ := T.axCoequalizer 6
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_coeqzOf hp)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqProjOf hp, op_codOf])
    (by simp_eval [T.op_coeqzOf hp])

/-- A coequalizer's projection coequalizes the arrows. -/
theorem compOf_coeqProjOf {f g : T.Ar} (hp : T.Par f g) :
    T.compOf (T.coeqProjOf f g hp) f (T.domOf_coeqProjOf hp).symm =
      T.compOf (T.coeqProjOf f g hp) g (hp.2.symm.trans (T.domOf_coeqProjOf hp).symm) := by
  have hv : Valid T.model [arr, arr] [dfd (coeqz (x 0) (x 1))]
      ⟨comp (coeqProj (x 0) (x 1)) (x 0), comp (coeqProj (x 0) (x 1)) (x 1)⟩ :=
    T.axCoequalizer 7
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_coeqzOf hp)
  have h1 := T.op_compOf (T.domOf_coeqProjOf hp).symm
  have h2 := T.op_compOf (hp.2.symm.trans (T.domOf_coeqProjOf hp).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqProjOf hp, h1])
    (by simp_eval [T.op_coeqProjOf hp, h2])

/-- A morphism that coequalizes two parallel arrows descends through their coequalizer. -/
theorem coeqDescOf_exists {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    ∃ l, T.model.op 21 [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] = some ⟨arr, l⟩ := by
  have hv : Valid T.model [arr, arr, arr]
      [dfd (coeqz (x 0) (x 1)), ⟨comp (x 2) (x 0), comp (x 2) (x 1)⟩]
      (dfd (coeqDesc (x 0) (x 1) (x 2))) := T.axCoequalizer 10
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.coeqzOf f g hp⟩, by simp_eval [T.op_coeqzOf hp],
        by simp_eval [T.op_coeqzOf hp]⟩,
      ⟨⟨arr, T.compOf k g (hp.2.symm.trans hk)⟩, by simp_eval [T.op_compOf hk, he],
        by simp_eval [T.op_compOf (hp.2.symm.trans hk)]⟩⟩)
  simp_eval []
  exact T.model.exists_op_eq hw rfl

/-- The descent through the coequalizer of two parallel arrows of a morphism that
coequalizes them. -/
def coeqDescOf (f g k : T.Ar) (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) : T.Ar :=
  T.model.get (T.coeqDescOf_exists hp hk he)

/-- The model's descent through a coequalizer. -/
@[simp] theorem op_coeqDescOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    T.model.op 21 [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] = some ⟨arr, T.coeqDescOf f g k hp hk he⟩ :=
  T.model.op_eq_get _

/-- A descent through a coequalizer is defined at its arguments. -/
theorem holds_coeqDescOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    (dfd (coeqDesc (x 0) (x 1) (x 2))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] :=
  ⟨⟨arr, T.coeqDescOf f g k hp hk he⟩, by simp_eval [T.op_coeqDescOf hp hk he],
    by simp_eval [T.op_coeqDescOf hp hk he]⟩

/-- The domain of a descent through a coequalizer is the coequalizer. -/
theorem domOf_coeqDescOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    T.domOf (T.coeqDescOf f g k hp hk he) = T.coeqzOf f g hp := by
  have hv : Valid T.model [arr, arr, arr] [dfd (coeqDesc (x 0) (x 1) (x 2))]
      ⟨dom (coeqDesc (x 0) (x 1) (x 2)), coeqz (x 0) (x 1)⟩ := T.axCoequalizer 11
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_coeqDescOf hp hk he)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqDescOf hp hk he, op_domOf])
    (by simp_eval [T.op_coeqzOf hp])

/-- The codomain of a descent through a coequalizer is the descended morphism's. -/
theorem codOf_coeqDescOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    T.codOf (T.coeqDescOf f g k hp hk he) = T.codOf k := by
  have hv : Valid T.model [arr, arr, arr] [dfd (coeqDesc (x 0) (x 1) (x 2))]
      ⟨cod (coeqDesc (x 0) (x 1) (x 2)), cod (x 2)⟩ := T.axCoequalizer 12
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_coeqDescOf hp hk he)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqDescOf hp hk he, op_codOf])
    (by simp_eval [op_codOf])

/-- A descent through a coequalizer after the projection is the descended morphism. -/
theorem coeqDescOf_coeqProjOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    T.compOf (T.coeqDescOf f g k hp hk he) (T.coeqProjOf f g hp)
      ((T.codOf_coeqProjOf hp).trans (T.domOf_coeqDescOf hp hk he).symm) = k := by
  have hv : Valid T.model [arr, arr, arr] [dfd (coeqDesc (x 0) (x 1) (x 2))]
      ⟨comp (coeqDesc (x 0) (x 1) (x 2)) (coeqProj (x 0) (x 1)), x 2⟩ := T.axCoequalizer 13
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_coeqDescOf hp hk he)
  have hc := T.op_compOf ((T.codOf_coeqProjOf hp).trans (T.domOf_coeqDescOf hp hk he).symm)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_coeqDescOf hp hk he, T.op_coeqProjOf hp, hc]) (by simp_eval [])

/-- An arrow out of a coequalizer, after the projection, coequalizes the two parallel
arrows. -/
theorem compOf_coeqProjOf_comp {f g m : T.Ar} (hp : T.Par f g)
    (hm : T.codOf (T.coeqProjOf f g hp) = T.domOf m) :
    T.compOf (T.compOf m (T.coeqProjOf f g hp) hm) f
        ((T.domOf_coeqProjOf hp).symm.trans (T.domOf_compOf hm).symm) =
      T.compOf (T.compOf m (T.coeqProjOf f g hp) hm) g
        (hp.2.symm.trans ((T.domOf_coeqProjOf hp).symm.trans (T.domOf_compOf hm).symm)) :=
  calc _ = T.compOf m (T.compOf (T.coeqProjOf f g hp) f (T.domOf_coeqProjOf hp).symm)
        ((T.codOf_compOf _).trans hm) := (T.compOf_assoc (T.domOf_coeqProjOf hp).symm hm).symm
    _ = T.compOf m (T.compOf (T.coeqProjOf f g hp) g
          (hp.2.symm.trans (T.domOf_coeqProjOf hp).symm)) ((T.codOf_compOf _).trans hm) :=
        T.compOf_congr rfl (T.compOf_coeqProjOf hp) _ _
    _ = _ := T.compOf_assoc (hp.2.symm.trans (T.domOf_coeqProjOf hp).symm) hm

/-- A morphism out of a coequalizer is the descent of its composite with the projection. -/
theorem coeqDescOf_eta {f g m : T.Ar} (hp : T.Par f g) (hm : T.domOf m = T.coeqzOf f g hp) :
    T.coeqDescOf f g (T.compOf m (T.coeqProjOf f g hp) ((T.codOf_coeqProjOf hp).trans hm.symm))
      hp ((T.domOf_coeqProjOf hp).symm.trans (T.domOf_compOf _).symm)
      (T.compOf_coeqProjOf_comp hp _) = m := by
  have hv : Valid T.model [arr, arr, arr]
      [dfd (coeqz (x 0) (x 1)), ⟨dom (x 2), coeqz (x 0) (x 1)⟩]
      ⟨coeqDesc (x 0) (x 1) (comp (x 2) (coeqProj (x 0) (x 1))), x 2⟩ := T.axCoequalizer 14
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, m⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.coeqzOf f g hp⟩, by simp_eval [T.op_coeqzOf hp],
        by simp_eval [T.op_coeqzOf hp]⟩,
      ⟨⟨obj, T.coeqzOf f g hp⟩, by simp_eval [op_domOf, hm], by simp_eval [T.op_coeqzOf hp]⟩⟩)
  have hc := T.op_compOf ((T.codOf_coeqProjOf hp).trans hm.symm)
  have hd := T.op_coeqDescOf hp ((T.domOf_coeqProjOf hp).symm.trans (T.domOf_compOf _).symm)
    (T.compOf_coeqProjOf_comp hp ((T.codOf_coeqProjOf hp).trans hm.symm))
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqProjOf hp, hc, hd])
    (by simp_eval [])

end ToposModel

end Geb.FreeTopos

end
