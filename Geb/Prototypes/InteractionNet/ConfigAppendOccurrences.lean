/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ForestIso
public import Geb.Prototypes.InteractionNet.ConfigGraph
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Separating a prefix of configuration equations

Prepending a rule's replacement equations preserves the original interface and equation
positions. Root bijections separate the new equation forest from the retained configuration
forest. Transport along the corresponding term equalities applies uniformly to leaves,
cells and complete fragment endpoints.

## Main definitions

* {lit}`EquationGraph.appendRootEquiv` — roots of concatenated equation lists.
* {lit}`Config.appendRootEquiv` — replacement roots followed by the retained configuration.
* {lit}`Config.appendOccurrencesEquiv` — the induced correspondence on fragment occurrences.

## Tags

interaction net, compiler, equation, concatenation, forest, occurrence
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α ν : Type} {arity : α → ℕ}

namespace EquationGraph

/-- Concatenation interleaves the left and right root blocks of the two equation lists. -/
def appendRootEquiv (es fs : List (Equation arity ν)) : Root es ⊕ Root fs ≃ Root (es ++ fs) :=
  (Equiv.sumSumSumComm (Fin es.length) (Fin es.length) (Fin fs.length) (Fin fs.length)).trans
    (Equiv.sumCongr (finSumFinEquiv.trans (finCongr (@List.length_append _ es fs).symm))
      (finSumFinEquiv.trans (finCongr (@List.length_append _ es fs).symm)))

/-- A concatenated root still contains the term at its original equation position. -/
theorem term_append (es fs : List (Equation arity ν)) (p : Root es ⊕ Root fs) :
    term (es ++ fs) (appendRootEquiv es fs p) = Sum.elim (term es) (term fs) p := by
  rcases p with (i | i) | (i | i) <;>
    simp [term, appendRootEquiv, Equiv.sumSumSumComm, finSumFinEquiv, List.get_eq_getElem]

end EquationGraph

namespace Config

/-- Move replacement roots past the original interface and join the two equation-root blocks. -/
def appendRootEquiv (c : Config arity) (es : List (Equation arity ℕ)) :
    EquationGraph.Root es ⊕ c.GraphRoot ≃
      ({ c with equations := es ++ c.equations } : Config arity).GraphRoot :=
  let e : EquationGraph.Root es ⊕ c.GraphRoot ≃
      Fin c.interface.length ⊕ (EquationGraph.Root es ⊕ EquationGraph.Root c.equations) :=
    { toFun := fun p ↦ match p with
        | .inl i => .inr (.inl i)
        | .inr (.inl i) => .inl i
        | .inr (.inr i) => .inr (.inr i)
      invFun := fun p ↦ match p with
        | .inl i => .inr (.inl i)
        | .inr (.inl i) => .inl i
        | .inr (.inr i) => .inr (.inr i)
      left_inv := by rintro (i | (i | i)) <;> rfl
      right_inv := by rintro (i | (i | i)) <;> rfl }
  e.trans (Equiv.sumCongr (Equiv.refl _) (EquationGraph.appendRootEquiv es c.equations))

/-- The fragment at a prepended or retained root is unchanged by equation concatenation. -/
theorem appendRootEquiv_fragment (c : Config arity) (es : List (Equation arity ℕ))
    (p : EquationGraph.Root es ⊕ c.GraphRoot) :
    ({ c with equations := es ++ c.equations } : Config arity).graphFragments
      (c.appendRootEquiv es p) = Sum.elim (EquationGraph.fragments es) c.graphFragments p := by
  rcases p with i | (i | i)
  · exact congrArg Term.fragment (EquationGraph.term_append es c.equations (.inl i))
  · rfl
  · exact congrArg Term.fragment (EquationGraph.term_append es c.equations (.inr i))

/-- Any family of fragment occurrences splits into newly prepended and retained positions. -/
def appendOccurrencesEquiv (c : Config arity) (es : List (Equation arity ℕ))
    (F : TermFragment arity ℕ → Type) :
    (Σ i, F (EquationGraph.fragments es i)) ⊕ (Σ i, F (c.graphFragments i)) ≃
      (Σ i, F (({ c with equations := es ++ c.equations } : Config arity).graphFragments i)) :=
  let split : (Σ i, F (EquationGraph.fragments es i)) ⊕ (Σ i, F (c.graphFragments i)) ≃
      (Σ i : EquationGraph.Root es ⊕ c.GraphRoot,
        F (Sum.elim (EquationGraph.fragments es) c.graphFragments i)) :=
    { toFun := fun p ↦ match p with
        | .inl ⟨i, p⟩ => ⟨.inl i, p⟩
        | .inr ⟨i, p⟩ => ⟨.inr i, p⟩
      invFun := fun p ↦ match p with
        | ⟨.inl i, p⟩ => .inl ⟨i, p⟩
        | ⟨.inr i, p⟩ => .inr ⟨i, p⟩
      left_inv := by rintro (⟨i, p⟩ | ⟨i, p⟩) <;> rfl
      right_inv := by rintro ⟨i | i, p⟩ <;> rfl }
  split.trans (familyEquiv (c.appendRootEquiv es) (fun i ↦
    { toFun := (congrArg F (c.appendRootEquiv_fragment es i)).mpr
      invFun := (congrArg F (c.appendRootEquiv_fragment es i)).mp
      left_inv := by intro p; exact cast_cast _ _ _
      right_inv := by intro p; exact cast_cast _ _ _ }))

end Config

end Geb.InteractionNet

end
