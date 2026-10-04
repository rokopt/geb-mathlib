/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.GoedelT.MirrorTerms
public import Geb.Prototypes.GoedelT.Equations

set_option doc.verso true in
/-!
# The equations of Gödel's T written in Geb

The checker of Gödel's T written in Geb represents an equation as the node of label zero over
its type and its two sides, {lit}`encEqn`, and a theorem as the node of label zero over the node
of its context and its equation, {lit}`encThm`. Its operations on equations and theorems, in
their Lean mirror, are proved to act on these encodings as {lit}`Geb.GoedelT` acts on
{name}`Geb.GoedelT.Eqn` and {name}`Geb.GoedelT.Thm`: weakening, removal of the innermost
variable, substitution, instantiation of variables, the test of an equation's typing and of
hypotheses' weakening, the citation of a theorem, and the table of axioms.

## Main definitions

* {lit}`encEqn`, {lit}`encThm` — equations and theorems as the checker written in Geb
  represents them.

## Main statements

* {lit}`cite_eq` — the mirror's citation of a theorem is the encoding of
  {name}`Geb.GoedelT.Thm.cite`.
* {lit}`axioms_eq` — the mirror's axioms are the encodings of {name}`Geb.GoedelT.axioms`.

## Tags

equation, sequent, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.GoedelT

namespace GebTests.Prototypes.GoedelT.MirrorEquations

open Geb Geb.Kernel Geb.GoedelT GebTests.Prototypes.GoedelT.MirrorTyping
  GebTests.Prototypes.GoedelT.MirrorTerms
open scoped FinEnum

/-- An equation as the checker written in Geb represents it: the node of label zero over its
type and its two sides. -/
def encEqn (q : Eqn) : Tree := RoseTree.node 0 [q.ty, q.lhs, q.rhs]

/-- The encoding of equations is injective. -/
theorem encEqn_inj {q q' : Eqn} : encEqn q = encEqn q' ↔ q = q' := by
  refine ⟨fun h ↦ ?_, congrArg encEqn⟩
  have := congrArg RoseTree.children h
  simp only [encEqn, RoseTree.children_node, List.cons.injEq, and_true] at this
  exact Eqn.ext this.1 this.2.1 this.2.2

/-- The encoding of optional equations is injective. -/
theorem enc_map_inj {o o' : Option Eqn} : enc (o.map encEqn) = enc (o'.map encEqn) ↔ o = o' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  cases o <;> cases o'
  · rfl
  · cases h
  · cases h
  · have := congrArg RoseTree.children h
    simp only [Option.map_some, enc, RoseTree.children_node, List.cons.injEq, and_true,
      encEqn_inj] at this
    rw [this]

/-- The mirror's equation. -/
theorem eqn_eq (A a b : Tree) : «Equations.eqn» A a b = encEqn ⟨A, a, b⟩ := rfl

/-- The mirror's type of an equation. -/
theorem eqTy_eq (q : Eqn) : «Equations.eqTy» (encEqn q) = q.ty := by
  simp [«Equations.eqTy», encEqn, child_node]

/-- The mirror's left side of an equation. -/
theorem eqLhs_eq (q : Eqn) : «Equations.eqLhs» (encEqn q) = q.lhs := by
  simp [«Equations.eqLhs», encEqn, child_node]

/-- The mirror's right side of an equation. -/
theorem eqRhs_eq (q : Eqn) : «Equations.eqRhs» (encEqn q) = q.rhs := by
  simp [«Equations.eqRhs», encEqn, child_node]

/-- The mirror's binding of a present optional tree. -/
theorem bindO_some (t : Tree) (f : Tree → Tree) :
    «Equations.bindO» (enc (some t)) f = f t := by
  simp [«Equations.bindO», isSome_enc, get_enc]

/-- The mirror's binding of an absent optional tree. -/
theorem bindO_none (f : Tree → Tree) : «Equations.bindO» (enc none) f = enc none := rfl

/-- The mirror's map of a list. -/
theorem mapT_eq (f : Tree → Tree) (xs : List Tree) : «Equations.mapT» f xs = xs.map f :=
  xs.rec rfl fun _ _ ih ↦ by
    simp only [«Equations.mapT», Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The mirror's conjunction of truth values, as a proposition. -/
theorem and_label (a b : Tree) :
    («Prelude.and» a b).label ≠ 0 ↔ a.label ≠ 0 ∧ b.label ≠ 0 := by
  unfold «Prelude.and»
  split <;> simp_all

/-- The mirror's test of every element of a list, as a proposition. -/
theorem allT_label (f : Tree → Tree) (xs : List Tree) :
    («Equations.allT» f xs).label ≠ 0 ↔ ∀ x ∈ xs, (f x).label ≠ 0 :=
  xs.rec (by simp [«Equations.allT», Const.foldr]) fun x xs ih ↦ by
    simp only [«Equations.allT», Const.foldr, List.foldr_cons] at ih ⊢
    rw [and_label, ih, List.forall_mem_cons]

/-- The mirror's test of a term's type in a context. -/
theorem hasType_label (G : List Glob) (Γ : Ctx) (t A : Tree) :
    («Equations.hasType» (G.map (·.1)) Γ t A).label ≠ 0 ↔ typeOf G Γ t = some A := by
  simp only [«Equations.hasType», typeIn_eq]
  change _ ↔ tyOf G Γ t = some A
  cases tyOf G Γ t <;> simp [isSome_enc, get_enc, equal_label]

/-- The mirror's test of an equation's typing in a context. -/
theorem typedIn_label (G : List Glob) (Γ : Ctx) (q : Eqn) :
    («Equations.typedIn» (G.map (·.1)) Γ (encEqn q)).label ≠ 0 ↔ q.Typed G Γ := by
  simp only [«Equations.typedIn», and_label, hasType_label, eqTy_eq, eqLhs_eq, eqRhs_eq,
    Eqn.Typed]

/-- The mirror's weakening of an equation. -/
theorem eqWk_eq (n : ℕ) (q : Eqn) :
    «Equations.eqWk» (leaf n) (encEqn q) = encEqn (q.wk n) := by
  simp only [«Equations.eqWk», eqTy_eq, eqLhs_eq, eqRhs_eq, wk_eq]
  rfl

/-- The mirror's removal of an equation's innermost variable. -/
theorem eqLower_eq (q : Eqn) : «Equations.eqLower» (encEqn q) = encEqn q.lower := by
  simp only [«Equations.eqLower», eqTy_eq, eqLhs_eq, eqRhs_eq]
  rw [show «Equations.mk1» (leaf 15) (leaf 0) = mk Label.quote [leaf 0] from rfl, subst_eq,
    subst_eq]
  rfl

/-- The mirror's weakening of a list of equations. -/
theorem mapT_eqWk (n : ℕ) (H : List Eqn) :
    «Equations.mapT» («Equations.eqWk» (leaf n)) (H.map encEqn) =
      (H.map (Eqn.wk n)).map encEqn := by
  rw [mapT_eq, List.map_map, List.map_map]
  exact List.map_congr_left fun q _ ↦ eqWk_eq n q

/-- The mirror's removal of the innermost variable from a list of equations. -/
theorem mapT_eqLower (H : List Eqn) :
    «Equations.mapT» «Equations.eqLower» (H.map encEqn) =
      (H.map Eqn.lower).map encEqn := by
  rw [mapT_eq, List.map_map, List.map_map]
  exact List.map_congr_left fun q _ ↦ eqLower_eq q

/-- The mirror's test that hypotheses are weakenings of hypotheses typed in a context. -/
theorem weakens_label (G : List Glob) (Γ : Ctx) (H0 H : List Eqn) :
    («Equations.weakens» (G.map (·.1)) Γ (H0.map encEqn) (H.map encEqn)).label ≠ 0 ↔
      H0.map (Eqn.wk 1) = H ∧ ∀ h ∈ H0, h.Typed G Γ := by
  simp only [«Equations.weakens», and_label, equal_label, mapT_eqWk, allT_label,
    List.forall_mem_map, typedIn_label]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  have := congrArg RoseTree.children h
  simp only [Const.node, RoseTree.children_node] at this
  exact List.map_injective_iff.mpr (fun _ _ ↦ encEqn_inj.mp) this

/-- The mirror's list of a function's values at the elements of a list, as a kernel term. -/
theorem mapBy_eq (A B body xs : Tree) :
    «Equations.mapBy» A B body xs = mapBy A B body xs := by
  simp only [«Equations.mapBy», tyList_eq]
  rfl

/-- The mirror's weakening below bound variables. -/
theorem wkAt_eq (k n : ℕ) (t : Tree) :
    «Equations.wkAt» (leaf k) (leaf n) t = GoedelT.wkAt k n t :=
  trav_eq _ _ (wkVar_eq n) t k

/-- The mirror's substitution in an equation. -/
theorem eqSubst_eq (u : Tree) (q : Eqn) :
    «Equations.eqSubst» u (encEqn q) = encEqn (q.subst u) := by
  simp only [«Equations.eqSubst», eqTy_eq, eqLhs_eq, eqRhs_eq, subst_eq]
  rfl

/-- The mirror's weakening of an equation below bound variables. -/
theorem eqWkAt_eq (k n : ℕ) (q : Eqn) :
    «Equations.eqWkAt» (leaf k) (leaf n) (encEqn q) = encEqn (q.wkAt k n) := by
  simp only [«Equations.eqWkAt», eqTy_eq, eqLhs_eq, eqRhs_eq, wkAt_eq]
  rfl

/-- The fold of the mirror's instantiation gives the number of terms and the instantiation. -/
theorem foldr_instAll (us : List Tree) :
    (Const.foldr (fun (u : Tree) (r : Tree × (Tree → Tree)) ↦ (Const.add r.1 (leaf 1),
        fun q ↦ r.2 («Equations.eqSubst» («Equations.wk» r.1 u) q))) (leaf 0, id)
        us).1 = leaf us.length ∧
      ∀ q, (Const.foldr (fun (u : Tree) (r : Tree × (Tree → Tree)) ↦ (Const.add r.1 (leaf 1),
        fun q ↦ r.2 («Equations.eqSubst» («Equations.wk» r.1 u) q))) (leaf 0, id)
        us).2 (encEqn q) = encEqn (instAll us q) :=
  us.rec ⟨rfl, fun _ ↦ rfl⟩ fun u us ih ↦ by
    simp only [Const.foldr, List.foldr_cons] at ih ⊢
    refine ⟨by rw [ih.1]; rfl, fun q ↦ ?_⟩
    rw [ih.1, wk_eq, eqSubst_eq, ih.2]
    rfl

/-- The mirror's instantiation of an equation's variables. -/
theorem instAll_eq (us : List Tree) (q : Eqn) :
    «Equations.instAll» us (encEqn q) = encEqn (instAll us q) :=
  (foldr_instAll us).2 q

/-- A theorem as the checker written in Geb represents it: the node of label zero over the node
of its context and its equation. -/
def encThm (th : Thm) : Tree := RoseTree.node 0 [RoseTree.node 0 th.ctx, encEqn th.eqn]

/-- The mirror's theorem. -/
theorem thm_eq (Γ : Ctx) (q : Eqn) : «Equations.thm» Γ (encEqn q) = encThm ⟨Γ, q⟩ := rfl

/-- The right fold testing a relation between the elements of two lists at the same positions,
with the test of their lengths' equality. -/
theorem foldr_forall₂ (f : Tree → Tree → Tree) (R : Tree → Tree → Prop)
    (hf : ∀ u A, (f u A).label ≠ 0 ↔ R u A) (us : List Tree) :
    ∀ As : List Tree, (Const.foldr (fun (u : Tree) (r : List Tree → Tree) (As : List Tree) ↦
        Const.lcase As (leaf 0) fun A As' ↦ «Prelude.and» (f u A) (r As'))
        (fun _ ↦ leaf 1) us As).label ≠ 0 ∧ us.length = As.length ↔ List.Forall₂ R us As :=
  us.rec (fun As ↦ by
      cases As with
      | nil => exact ⟨fun _ ↦ List.Forall₂.nil, fun _ ↦ ⟨Nat.one_ne_zero, rfl⟩⟩
      | cons A As => exact ⟨fun h ↦ absurd h.2 (Nat.succ_ne_zero _).symm, fun h ↦ nomatch h⟩)
    fun u us ih As ↦ by
    cases As with
    | nil => exact ⟨fun h ↦ absurd rfl h.1, fun h ↦ nomatch h⟩
    | cons A As =>
      simp only [Const.foldr, List.foldr_cons, Const.lcase, List.length_cons,
        Nat.add_right_cancel_iff, List.forall₂_cons, and_label, hf] at ih ⊢
      rw [and_assoc, ih As]

/-- The mirror's test of terms' types, one for each type of a list. -/
theorem typesMatch_label (G : List Glob) (Γ : Ctx) (us As : List Tree) :
    («Equations.typesMatch» (G.map (·.1)) Γ us As).label ≠ 0 ↔
      List.Forall₂ (fun u A ↦ typeOf G Γ u = some A) us As := by
  refine Iff.trans ?_ (foldr_forall₂ _ _ (fun u A ↦ hasType_label G Γ u A) us As)
  unfold «Equations.typesMatch»
  rw [and_label, length_eq, length_eq, eq_leaf]
  exact and_comm

/-- The mirror's citation of a theorem. -/
theorem cite_eq (G : List Glob) (Γ : Ctx) (us : List Tree) (th : Thm) :
    «Equations.cite» (G.map (·.1)) Γ us (encThm th) = enc ((th.cite G Γ us).map encEqn) := by
  have h0 : Const.child (encThm th) (leaf 0) = RoseTree.node 0 th.ctx := by
    simp [encThm, child_node]
  have h1 : Const.child (encThm th) (leaf 1) = encEqn th.eqn := by
    simp [encThm, child_node]
  simp only [«Equations.cite», h0, h1, Const.children, RoseTree.children_node, length_eq,
    eqWkAt_eq, instAll_eq, Thm.cite, Thm.inst, typesMatch_label]
  split_ifs <;> rfl

/-- The mirror's reversal of a list, onto a list. -/
theorem foldr_reverse (xs : List Tree) :
    ∀ acc : List Tree, Const.foldr (fun (x : Tree) (k : List Tree → List Tree) (acc : List Tree) ↦
      k (x :: acc)) (fun acc ↦ acc) xs acc = xs.reverse ++ acc :=
  xs.rec (fun _ ↦ rfl) fun x xs ih acc ↦ by
    simp only [Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih, List.reverse_cons, List.append_assoc]
    rfl

/-- The mirror's application of a term to a list of arguments. -/
theorem apps_eq (f : Tree) (xs : List Tree) : «Reader.apps» f xs = apps f xs := by
  unfold «Reader.apps» «Prelude.reverse»
  rw [foldr_reverse, List.append_nil]
  simp only [Const.foldr, List.foldr_reverse]
  rfl

/-- The mirror's axioms are the kernel's. -/
theorem axioms_eq : «Equations.axioms» = axioms.map encThm := by
  simp only [axioms, List.map_cons, List.map_nil, axLabelNode, axChildrenNode, axNodeEta,
    axChildrenLabel, axLabelSucc, axAddIter, axPredIter, axSubIter, axMulIter, axDivIter,
    axModIter, axEqDef, axLtDef, axLog2Def, axArityDef, axChildDef, axEqualRefl, axEqualSubst,
    axEqualBool, divMod, tailT, tT2, tProd, node2_eq, tList_eq]
  rfl

end GebTests.Prototypes.GoedelT.MirrorEquations

end
