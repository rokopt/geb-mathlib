/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraph
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Separating a configuration's head equation

Adding an equation introduces its two root fragments and retains every original fragment.
The same occurrence bijection applies to cells, leaves, boundaries and complete endpoints.
Its explicit positions distinguish the new head from the shifted equation occurrences.

## Main definitions

* {lit}`Config.headOccurrencesEquiv` — separate the two new fragments from the old forest.
* {lit}`Config.headLeafEquiv` — the corresponding leaf occurrence bijection.

## Main statements

* {lit}`Config.headLeafEquiv_name` — separating the head equation preserves names.

## Tags

interaction net, compiler, configuration, equation, occurrence, forest
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

variable {α : Type} {arity : α → ℕ}

/-- Separate any family of fragment occurrences into the head's two sides and the old forest. -/
def headOccurrencesEquiv (c : Config arity) (e : Equation arity ℕ)
    (F : TermFragment arity ℕ → Type) :
    F e.1.fragment ⊕ (F e.2.fragment ⊕ (Σ i, F (c.graphFragments i))) ≃
      (Σ i, F (({ c with equations := e :: c.equations } : Config arity).graphFragments i)) where
  toFun p := match p with
    | .inl p => ⟨.inr (.inl 0), p⟩
    | .inr (.inl p) => ⟨.inr (.inr 0), p⟩
    | .inr (.inr ⟨.inl i, p⟩) => ⟨.inl i, p⟩
    | .inr (.inr ⟨.inr (.inl i), p⟩) => ⟨.inr (.inl i.succ), p⟩
    | .inr (.inr ⟨.inr (.inr i), p⟩) => ⟨.inr (.inr i.succ), p⟩
  invFun p := match p with
    | ⟨.inl i, p⟩ => .inr (.inr ⟨.inl i, p⟩)
    | ⟨.inr (.inl i), p⟩ =>
      Fin.cases (fun p ↦ Sum.inl p) (fun i p ↦ .inr (.inr ⟨.inr (.inl i), p⟩)) i p
    | ⟨.inr (.inr i), p⟩ =>
      Fin.cases (fun p ↦ Sum.inr (.inl p)) (fun i p ↦ .inr (.inr ⟨.inr (.inr i), p⟩)) i p
  left_inv p := by
    rcases p with p | (p | ⟨i | (i | i), p⟩) <;> rfl
  right_inv p := by
    rcases p with ⟨i | (i | i), p⟩
    · rfl
    · revert p
      exact Fin.cases (fun _ ↦ rfl) (fun _ _ ↦ rfl) i
    · revert p
      exact Fin.cases (fun _ ↦ rfl) (fun _ _ ↦ rfl) i

/-- Leaf occurrences in the two head terms and the remaining configuration. -/
def headLeafEquiv (c : Config arity) (e : Equation arity ℕ) :
    e.1.fragment.Leaf ⊕ (e.2.fragment.Leaf ⊕ c.GraphLeaf) ≃
      ({ c with equations := e :: c.equations } : Config arity).GraphLeaf :=
  c.headOccurrencesEquiv e (fun f ↦ f.Leaf)

/-- The head decomposition retains the name of every old or newly included leaf. -/
theorem headLeafEquiv_name (c : Config arity) (e : Equation arity ℕ)
    (p : e.1.fragment.Leaf ⊕ (e.2.fragment.Leaf ⊕ c.GraphLeaf)) :
    ({ c with equations := e :: c.equations } : Config arity).graphLeafName
      (c.headLeafEquiv e p) =
        Sum.elim e.1.fragment.name (Sum.elim e.2.fragment.name c.graphLeafName) p := by
  rcases p with p | (p | ⟨i | (i | i), p⟩) <;> rfl

/-- A leaf of the new left term is distinct from every original configuration occurrence. -/
theorem headLeaf_left_ne_rest (c : Config arity) (e : Equation arity ℕ)
    (p : e.1.fragment.Leaf) (q : c.GraphLeaf) :
    c.headLeafEquiv e (.inl p) ≠ c.headLeafEquiv e (.inr (.inr q)) := by
  intro h
  cases (c.headLeafEquiv e).injective h

end Geb.InteractionNet.Config

end
