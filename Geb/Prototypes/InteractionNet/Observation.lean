/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Kernel
public import Geb.Prototypes.InteractionNet.Erasure
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Tree observations in the kernel interaction system

Each kernel tree has a closed constructor-value representation in the interaction system.
Read-back recovers that tree, so the representation is injective. The generic erasure
theorem applies to these values, including trees with arbitrarily large labels and any
finite branching. These are representation properties, independent of compilation adequacy.

## Main definitions

* {lit}`treeValue` — a kernel tree as first-order constructor data.
* {lit}`treeTerm` — its closed net representation.

## Main statements

* {lit}`readback_treeTerm` — observation recovers every represented tree.
* {lit}`treeTerm_injective` — distinct trees have distinct representations.
* {lit}`names_eq_nil_of_readback` — successful tree read-back contains no unresolved names.
* {lit}`reaches_erase_treeTerm` — the kernel net system erases every represented tree.

## Tags

interaction net, tree, observation, read-back, representation, erasure
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- Represent a kernel tree by its constructor and the representations of its children. -/
def treeValue : Tree → Value dataArity :=
  RoseTree.elim fun l vs ↦ Term.agent (.inl (.tree l vs.length)) vs.get

/-- Representation of a node preserves its label and represents its children in order. -/
@[simp] theorem treeValue_node (l : ℕ) (ts : List Tree) :
    treeValue (RoseTree.node l ts) =
      Term.agent (.inl (.tree l (ts.map treeValue).length)) (ts.map treeValue).get := by
  change RoseTree.elim _ _ = _
  rw [RoseTree.elim_node]
  rfl

/-- The closed term representing a kernel tree at a net port. -/
def treeTerm (t : Tree) : Term (netArity (φ := Op) dataArity) ℕ :=
  Value.embed dataArity (treeValue t)

/-- Represented trees contain no free wire names. -/
@[simp] theorem treeTerm_names (t : Tree) : (treeTerm t).names = [] :=
  Value.embed_names dataArity (treeValue t)

/-- Read-back recovers every represented kernel tree. -/
@[simp] theorem readback_treeTerm (t : Tree) : readback (treeTerm t) = some t := by
  apply RoseTree.ind (P := fun t ↦ readback (treeTerm t) = some t) (fun l ts ih ↦ ?_) t
  unfold treeTerm
  rw [treeValue_node, Value.embed_agent]
  change ((List.ofFn fun i ↦ readback (Value.embed dataArity ((ts.map treeValue).get i))).mapM
    id).map (RoseTree.node l) = _
  simp only [← Function.comp_def, ← List.map_ofFn, List.ofFn_get, List.map_map]
  have h : ts.map (fun t ↦ readback (treeTerm t)) = ts.map some :=
    List.map_congr_left fun x hx ↦ ih x hx
  change ((ts.map fun t ↦ readback (treeTerm t)).mapM id).map (RoseTree.node l) = _
  rw [h, List.mapM_map]
  have hs : (List.mapM some ts : Option (List Tree)) = some ts :=
    List.rec (by rfl) (fun a as ih ↦ by simp [List.mapM_cons, ih]) ts
  exact congrArg (Option.map (RoseTree.node l)) hs

/-- The observation distinguishes every pair of different represented trees. -/
theorem treeTerm_injective : Function.Injective treeTerm := by
  intro x y h
  have hr := congrArg readback h
  simpa only [readback_treeTerm, Option.some.injEq] using hr

private theorem sequence_isSome {α : Type} (xs : List (Option α)) (ys : List α)
    (h : xs.mapM id = some ys) : ∀ x ∈ xs, x.isSome = true := by
  apply List.rec (motive := fun xs ↦ ∀ ys,
    xs.mapM id = some ys → ∀ x ∈ xs, x.isSome = true)
    (fun _ _ _ hm ↦ False.elim (List.not_mem_nil hm)) (fun x xs ih ys h z hz ↦ ?_) xs ys h
  cases x with
  | none => simp [List.mapM_cons] at h
  | some a =>
    cases hs : xs.mapM id with
    | none => simp [List.mapM_cons, hs] at h
    | some bs =>
      rcases List.mem_cons.mp hz with rfl | hz
      · rfl
      · exact ih bs hs z hz

/-- Every successful tree observation contains no unresolved wire names. -/
theorem names_eq_nil_of_readback (t : Term (netArity (φ := Op) dataArity) ℕ) (y : Tree)
    (h : readback t = some y) : t.names = [] := by
  apply PFunctor.FreeM.rec (motive := fun t ↦ ∀ y, readback t = some y → Term.names t = [])
    (fun _ _ h ↦ by cases h) (fun a ts ih y h ↦ ?_) t y h
  cases a with
  | inr a => cases h
  | inl a =>
    cases a with
    | inr n => cases h
    | inl a =>
      cases a <;> simp only [readback] at h <;> try contradiction
      rename_i l n
      obtain ⟨ys, hy, _⟩ := Option.map_eq_some_iff.mp h
      change (List.ofFn fun i ↦ Term.names (ts i)).flatten = []
      apply List.flatten_eq_nil_iff.mpr
      intro ns hn
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hn
      have hi := sequence_isSome _ ys hy _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hi
      exact ih i z hz

/-- Erasing a represented tree terminates without altering its continuation. -/
theorem reaches_erase_treeTerm (P : List Tree) (t : Tree)
    (c : Config (netArity (φ := Op) dataArity)) :
    (system P).Reaches (eraseTasks dataArity [treeTerm t] c) c :=
  reaches_erase dataArity (program P) (treeValue t) c

end Geb.InteractionNet.Kernel

end
