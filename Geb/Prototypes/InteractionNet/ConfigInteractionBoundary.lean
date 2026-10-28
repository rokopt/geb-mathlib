/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigAppendOccurrences
public import Geb.Prototypes.InteractionNet.ConfigInteractionAllocation
public import Geb.Prototypes.InteractionNet.RuleInstantiationForest
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Boundary positions in the complete interaction result

The textual target's roots and named leaves have explicit positions in the joined forest.
Old configuration roots and leaves stay in the argument context; replacement equation
roots and internal leaf occurrences stay in the rule's closure boundary.

## Main definitions

* {lit}`Config.interactionResultBoundaryEquiv` — the textual target boundary in the joined forest.

## Main statements

* {lit}`Config.interactionResultBoundary_old_root` — context roots retain their boundary positions.
* {lit}`Config.interactionResultBoundary_rule_leaf` — argument and internal leaves correspond.

## Tags

interaction net, compiler, interaction, boundary, root, leaf, occurrence
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

variable {α : Type} {arity : α → ℕ} {a b : α}

private theorem cast_root {f g : TermFragment arity ℕ} (h : g = f) :
    (congrArg (fun f ↦ Unit ⊕ f.Leaf) h).mpr (.inl ()) = .inl () := by cases h; rfl

private theorem cast_leaf {f g : TermFragment arity ℕ} (h : g = f) (p : f.Leaf) :
    (congrArg (fun f ↦ Unit ⊕ f.Leaf) h).mpr (.inr p) =
      .inr ((congrArg TermFragment.Leaf h).mpr p) := by cases h; rfl

/-- Concatenation places each fragment's distinguished root at its concatenated root index. -/
theorem appendOccurrencesEquiv_root (c : Config arity) (es : List (Equation arity ℕ))
    (p : EquationGraph.Root es ⊕ c.GraphRoot) :
    c.appendOccurrencesEquiv es (fun f ↦ Unit ⊕ f.Leaf)
      (match p with | .inl i => .inl ⟨i, .inl ()⟩ | .inr i => .inr ⟨i, .inl ()⟩) =
        ⟨c.appendRootEquiv es p, .inl ()⟩ := by
  cases p with
  | inl i => exact congrArg (Sigma.mk _) (cast_root (c.appendRootEquiv_fragment es (.inl i)))
  | inr i => exact congrArg (Sigma.mk _) (cast_root (c.appendRootEquiv_fragment es (.inr i)))

/-- Concatenation's boundary and leaf bijections identify the same named endpoint. -/
theorem appendOccurrencesEquiv_leaf (c : Config arity) (es : List (Equation arity ℕ))
    (p : EquationGraph.Leaf es ⊕ c.GraphLeaf) :
    c.appendOccurrencesEquiv es (fun f ↦ Unit ⊕ f.Leaf)
      (match p with | .inl ⟨i, p⟩ => .inl ⟨i, .inr p⟩ | .inr ⟨i, p⟩ => .inr ⟨i, .inr p⟩) =
        ⟨(c.appendOccurrencesEquiv es (fun f ↦ f.Leaf) p).1,
          .inr (c.appendOccurrencesEquiv es (fun f ↦ f.Leaf) p).2⟩ := by
  rcases p with ⟨i, p⟩ | ⟨i, p⟩
  · exact congrArg (Sigma.mk _) (cast_leaf (c.appendRootEquiv_fragment es (.inl i)) p)
  · exact congrArg (Sigma.mk _) (cast_leaf (c.appendRootEquiv_fragment es (.inr i)) p)

/-- Locate argument leaves and internal rule occurrences in the joined forest's boundary. -/
def interactionLeafBoundary (c : Config arity) (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    ((Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ r.InternalLeaf) ↪
      c.AgentPairBoundary xs ys ⊕ r.ClosedBoundary where
  toFun p := match p with | .inl p => .inl (.inl p) | .inr q => .inr (.inr q)
  inj' := by
    rintro (p | p) (q | q) h
    · exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj h))
    · cases h
    · cases h
    · exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))

/-- The boundary allocation retains the replacement occurrence selected by leaf allocation. -/
theorem interactionForestBoundaryEquiv_leaf (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (next : ℕ) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) (i : EquationGraph.Root r.equations)
    (q : (EquationGraph.fragments r.equations i).Leaf)
    (p : (r.instantiationFragments next xs ys i q).Leaf) :
    c.interactionForestBoundaryEquiv r linear next xs ys (.inl ⟨i, .inr ⟨q, p⟩⟩) =
      c.interactionLeafBoundary r xs ys
        (r.replacementLeavesEquiv linear next xs ys ⟨⟨i, q⟩, p⟩) := by
  dsimp only [Rule.instantiationFragments] at p ⊢
  simp only [interactionForestBoundaryEquiv, Rule.attachedBoundarySplit, Equiv.trans_apply,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.coe_fn_mk, Rule.instantiationFragments]
  cases r.replacementLeavesEquiv linear next xs ys ⟨⟨i, q⟩, p⟩ <;> rfl

/-- Compiling the instantiated leaf and then allocating it selects the same joined boundary. -/
theorem instantiationBoundary_leaf (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (next : ℕ) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) (p : EquationGraph.Leaf (r.instantiate next xs ys)) :
    c.interactionForestBoundaryEquiv r linear next xs ys
      (.inl (r.instantiationBoundaryEquiv next xs ys ⟨p.1, .inr p.2⟩)) =
        c.interactionLeafBoundary r xs ys (r.instantiateLeavesEquiv linear next xs ys p) :=
  c.interactionForestBoundaryEquiv_leaf r linear next xs ys _ _ _

/-- Identify the complete textual target's boundary with the joined argument and rule forest. -/
def interactionResultBoundaryEquiv (c : Config arity) (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :=
  (c.appendOccurrencesEquiv (r.instantiate c.nextName xs ys) (fun f ↦ Unit ⊕ f.Leaf)).symm.trans
    ((Equiv.sumCongr (r.instantiationBoundaryEquiv c.nextName xs ys)
      (Equiv.refl c.GraphForestBoundary)).trans
        (c.interactionForestBoundaryEquiv r linear c.nextName xs ys))

/-- The joined boundary retains every original context root at its original forest position. -/
theorem interactionResultBoundary_old_root (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) (i : c.GraphRoot) :
    c.interactionResultBoundaryEquiv r linear xs ys
      ⟨c.appendRootEquiv (r.instantiate c.nextName xs ys) (.inr i), .inl ()⟩ =
        .inl (.inr ⟨i, .inl ()⟩) := by
  rw [← c.appendOccurrencesEquiv_root _ (.inr i)]
  simp only [interactionResultBoundaryEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- Every replacement equation root is retained in the rule's closure boundary. -/
theorem interactionResultBoundary_rule_root (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) (i : EquationGraph.Root r.equations) :
    c.interactionResultBoundaryEquiv r linear xs ys
      ⟨c.appendRootEquiv (r.instantiate c.nextName xs ys)
        (.inl ((EquationGraph.substRootEquiv (r.argumentSubstitution c.nextName xs ys)
          r.equations).symm i)), .inl ()⟩ = .inr (.inl i) := by
  erw [← c.appendOccurrencesEquiv_root _ (.inl _)]
  simp only [interactionResultBoundaryEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  change Sum.inr (Sum.inl ((EquationGraph.substRootEquiv
    (r.argumentSubstitution c.nextName xs ys) r.equations)
      ((EquationGraph.substRootEquiv (r.argumentSubstitution c.nextName xs ys)
        r.equations).symm i))) = _
  rw [Equiv.apply_symm_apply]

/-- Each allocated argument or internal occurrence is at its named position in the joined forest. -/
theorem interactionResultBoundary_rule_leaf (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ)
    (p : (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ r.InternalLeaf) :
    let q := c.appendOccurrencesEquiv (r.instantiate c.nextName xs ys) (fun f ↦ f.Leaf)
      (.inl ((r.instantiateLeavesEquiv linear c.nextName xs ys).symm p))
    c.interactionResultBoundaryEquiv r linear xs ys ⟨q.1, .inr q.2⟩ =
      c.interactionLeafBoundary r xs ys p := by
  dsimp only
  rw [← c.appendOccurrencesEquiv_leaf _ (.inl _)]
  simp only [interactionResultBoundaryEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply, Sum.map_inl]
  rw [c.instantiationBoundary_leaf, Equiv.apply_symm_apply]

/-- Every original context occurrence retains its named position in the joined forest. -/
theorem interactionResultBoundary_old_leaf (c : Config arity) (r : Rule arity a b)
    (linear : r.Linear) (xs : Fin (arity a) → Term arity ℕ)
    (ys : Fin (arity b) → Term arity ℕ) (p : c.GraphLeaf) :
    let q := c.appendOccurrencesEquiv (r.instantiate c.nextName xs ys) (fun f ↦ f.Leaf) (.inr p)
    c.interactionResultBoundaryEquiv r linear xs ys ⟨q.1, .inr q.2⟩ =
      .inl (.inr ⟨p.1, .inr p.2⟩) := by
  dsimp only
  rw [← c.appendOccurrencesEquiv_leaf _ (.inr p)]
  simp only [interactionResultBoundaryEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

end Geb.InteractionNet.Config

end
