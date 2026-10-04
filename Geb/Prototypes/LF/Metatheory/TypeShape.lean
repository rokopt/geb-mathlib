/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.Scope
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The shape of types

A kind or type of canonical LF is built from {lit}`type`, dependent products and applications
of constants: no variable heads an application at a position where a type is expected. An
expression of that shape ({lit}`Expr.TypeShape`) keeps it under renaming and hereditary
substitution, which can change an expression only at an application of the substituted variable,
and so keeps its erasure to a simple type ({cite}`HarperLicata2007`, Lemma 2.9: erasure is
invariant under substitution). Every kind and type that the judgments accept has the shape
({lit}`judgeWith_typeShape`), as has every classifier a spine instantiates a classifier of the
shape to ({lit}`spine_typeShape`).

## Main definitions

* {lit}`Expr.TypeShape` — an expression is built as a kind or type is.

## Main statements

* {lit}`typeShape_rename`, {lit}`typeShape_hsubWith` — the shape is kept by renaming and by
  substitution, and the erasure with it.
* {lit}`judgeWith_typeShape` — kinds and types have the shape.
* {lit}`spine_typeShape` — so have the classifiers a spine instantiates to.

## References

* {cite}`HarperLicata2007`, Lemma 2.9.

## Tags

logical framework, LF, erasure, simple type, hereditary substitution
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- One step of the shape of a kind or type, at a node of a label, from its children's: the kind
of types, a product of two expressions of the shape, or the application of a constant. -/
def typeShapeStep (l : Label) (cs : List Bool) : Bool :=
  match l, cs with
    | .type, [] => true
    | .pi, [a, b] => a && b
    | .app (.const _), _ => true
    | _, _ => false

/-- An expression is built as a kind or type is: from {lit}`type`, products and applications of
constants. -/
def Expr.TypeShape : Expr → Bool := RoseTree.elim typeShapeStep

/-- The computation rule of the shape. -/
theorem typeShape_node (l : Label) (cs : List Expr) :
    Expr.TypeShape (RoseTree.node l cs) = typeShapeStep l (cs.map Expr.TypeShape) :=
  RoseTree.elim_node _ l cs

/-- Renaming keeps the shape. -/
theorem typeShape_rename : ∀ (e : Expr) (ρ : ℕ → ℕ), (e.rename ρ).TypeShape = e.TypeShape :=
  RoseTree.ind fun l cs ih ρ ↦ by
    rw [rename_node, typeShape_node, typeShape_node]
    rcases l with _ | _ | _ | (i | c)
    · rcases cs with _ | ⟨d, cs⟩
      · rfl
      · rfl
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · rfl
      · rfl
      · simp only [Label.rename, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
          typeShapeStep, ih a (by simp), ih b (by simp)]
      · rfl
    · rfl
    · rfl
    · rfl

/-- Substitution keeps the shape, and with it the erasure, whatever the reduction: it can change
an expression only at an application of the substituted variable, and an expression of the shape
has none at a position the shape or the erasure inspects. -/
theorem typeShape_hsubWith (red : Expr → List Expr → Option Expr) :
    ∀ (e n : Expr) (j : ℕ) (e' : Expr), e.TypeShape = true → hsubWith red e n j = some e' →
      e'.TypeShape = true ∧ e'.erase = e.erase :=
  RoseTree.ind fun l cs ih n j e' hs h ↦ by
    rw [typeShape_node] at hs
    rcases l with _ | _ | _ | (i | c)
    · rcases cs with _ | ⟨d, cs⟩
      · rw [hsubWith_node_of_ne _ _ (fun i h ↦ by cases h)] at h
        simp only [List.zipIdx_nil, List.map_nil, List.mapM_nil, Option.pure_def,
          Option.map_eq_map, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl⟩
      · simp [typeShapeStep] at hs
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · simp [typeShapeStep] at hs
      · simp [typeShapeStep] at hs
      · simp only [List.map_cons, List.map_nil, typeShapeStep, Bool.and_eq_true] at hs
        rw [hsubWith_node_of_ne _ _ (fun i h ↦ by cases h), Option.map_eq_map,
          Option.map_eq_some_iff] at h
        obtain ⟨ys, hys, rfl⟩ := h
        rw [mapM_id_eq_some_iff] at hys
        rcases ys with _ | ⟨a', _ | ⟨b', _ | ⟨d', ys⟩⟩⟩
        · simp at hys
        · simp at hys
        · simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
            List.cons.injEq] at hys
          obtain ⟨ha, hb, -⟩ := hys
          obtain ⟨ha₁, ha₂⟩ := ih a (by simp) _ _ _ hs.1 ha
          obtain ⟨hb₁, hb₂⟩ := ih b (by simp) _ _ _ hs.2 hb
          refine ⟨?_, ?_⟩
          · rw [typeShape_node]
            simp only [List.map_cons, List.map_nil, typeShapeStep, ha₁, hb₁, Bool.and_self]
          · rw [erase_node, erase_node]
            simp only [List.map_cons, List.map_nil, eraseStep, ha₂, hb₂]
        · simp at hys
      · simp [typeShapeStep] at hs
    · simp [typeShapeStep] at hs
    · simp [typeShapeStep] at hs
    · rw [hsubWith_node_of_ne _ _ (fun i h ↦ by cases h), Option.map_eq_map,
        Option.map_eq_some_iff] at h
      obtain ⟨ys, -, rfl⟩ := h
      exact ⟨rfl, rfl⟩

/-- The kinds and the types the judgments accept have the shape. -/
theorem judgeWith_typeShape {eqv : Expr → Expr → Bool} {sig : Sig} :
    ∀ (e : Expr) (Γ : Ctx),
      (judgeWith eqv sig e Γ .kind = true → e.TypeShape = true) ∧
        (judgeWith eqv sig e Γ .type = true → e.TypeShape = true) :=
  RoseTree.ind fun l cs ih Γ ↦ by
    rw [judgeWith_node, typeShape_node]
    rcases l with _ | _ | _ | (i | c)
    · rcases cs with _ | ⟨d, cs⟩
      · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
      · exact ⟨fun h ↦ by simp [judgeStep] at h, fun h ↦ by simp [judgeStep] at h⟩
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · exact ⟨fun h ↦ by simp [judgeStep] at h, fun h ↦ by simp [judgeStep] at h⟩
      · exact ⟨fun h ↦ by simp [judgeStep] at h, fun h ↦ by simp [judgeStep] at h⟩
      · simp only [judgeStep, List.map_cons, List.map_nil, typeShapeStep, Bool.and_eq_true]
        exact ⟨fun h ↦ ⟨(ih a (by simp) Γ).2 h.1, (ih b (by simp) (a :: Γ)).1 h.2⟩,
          fun h ↦ ⟨(ih a (by simp) Γ).2 h.1, (ih b (by simp) (a :: Γ)).2 h.2⟩⟩
      · exact ⟨fun h ↦ by simp [judgeStep] at h, fun h ↦ by simp [judgeStep] at h⟩
    · exact ⟨fun h ↦ by simp [judgeStep] at h, fun h ↦ by simp [judgeStep] at h⟩
    · exact ⟨fun h ↦ by simp [judgeStep] at h, fun h ↦ by simp [judgeStep] at h⟩
    · exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- A spine instantiates a classifier of the shape to one of the shape. -/
theorem spine_typeShape {Γ : Ctx} :
    ∀ (ms : List (Expr × (Ctx → Mode → Bool))) (c r : Expr), c.TypeShape = true →
      spine Γ c ms = some r → r.TypeShape = true :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (c r : Expr), c.TypeShape = true →
      spine Γ c ms = some r → r.TypeShape = true)
    (fun c r hc h ↦ by
      simp only [spine, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
      rw [← h]
      exact hc)
    (fun m ms ih c r hc h ↦ by
      simp only [spine, List.foldlM_cons] at h
      obtain ⟨c', hc', hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l, cs, rfl⟩ := exists_node c
      rw [RoseTree.label_node, RoseTree.children_node] at hc'
      rcases l with _ | _ | _ | _
      · simp at hc'
      · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
        · simp at hc'
        · simp at hc'
        · simp only at hc'
          split_ifs at hc'
          rw [typeShape_node] at hc
          simp only [List.map_cons, List.map_nil, typeShapeStep, Bool.and_eq_true] at hc
          exact ih c' r (typeShape_hsubWith _ b m.1 0 c' hc.2 hc').1 hr
        · simp at hc'
      · simp at hc'
      · simp at hc')

end Geb.LF

end
