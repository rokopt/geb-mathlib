/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraphRenaming
public import Geb.Prototypes.InteractionNet.GraphClosure
public import Geb.Prototypes.InteractionNet.OccurrencePermutation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Equation order does not change a compiled graph

Permuting equations changes the enumeration of their term occurrences but preserves the
root wires joining each left side to its right side. A constructive position bijection
transports each term fragment and its named leaves. The graph compiler consequently
produces an isomorphic finite net with the same ordered external boundary.

## Main statements

* {lit}`Config.toFiniteNet_perm` — equation permutations preserve the compiled graph.
* {lit}`Config.swapGraphIso` — reversing an equation preserves the compiled graph.

## Tags

interaction net, compiler, configuration, equation, permutation, isomorphism
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- Equal terms at corresponding roots preserve the complete graph interpretation. -/
def reorderGraphIso (c d : Config arity) (hc : c.Closed) (hd : d.Closed)
    (b : Fin c.interface.length ≃ Fin d.interface.length) (e : c.GraphRoot ≃ d.GraphRoot)
    (terms : ∀ i, d.graphTerm (e i) = c.graphTerm i)
    (roots : c.graphRootWiring.map (Equiv.sumCongr b e) = d.graphRootWiring) :
    ((c.toFiniteNet hc).2.2.reboundary b).Iso (d.toFiniteNet hd).2.2 := by
  let h (i : c.GraphRoot) : TermFragment.Renaming id (c.graphFragments i)
      (d.graphFragments (e i)) := by
    rw [graphFragments_term, graphFragments_term, terms]
    exact ((c.graphTerm i).fragment).renameCorrespondence id
  apply indexedIso c d hc hd b
  apply occurrenceIso c d hc hd b e (fun i ↦ (h i).cells) (fun i ↦ (h i).leaves)
    (fun i ↦ (h i).labels) (fun i ↦ (h i).wires) (fun i ↦ (h i).loops) roots
  intro p q hpq
  change (d.graphFragments (e p.1)).name ((h p.1).leaves p.2) =
    (d.graphFragments (e q.1)).name ((h q.1).leaves q.2)
  rw [(h p.1).names, (h q.1).names]
  exact hpq

/-- Reordering equations preserves the compiled finite graph up to internal cell renaming. -/
theorem toFiniteNet_perm (c : Config arity) (es : List (Equation arity ℕ))
    (hp : es.Perm c.equations) (hc : c.Closed) :
    Nonempty ((c.toFiniteNet hc).2.2.Iso
      (({ c with equations := es } : Config arity).toFiniteNet (c.closed_perm es hp hc)).2.2) := by
  obtain ⟨e, he⟩ := OccurrencePermutation.exists_get_equiv hp.symm
  let d : Config arity := { c with equations := es }
  let roots : c.GraphRoot ≃ d.GraphRoot :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr e e)
  have ht (i : c.GraphRoot) : d.graphTerm (roots i) = c.graphTerm i := by
    rcases i with i | (i | i)
    · rfl
    · exact congrArg Prod.fst (he i)
    · exact congrArg Prod.snd (he i)
  have hw : c.graphRootWiring.map (Equiv.sumCongr (Equiv.refl _) roots) =
      d.graphRootWiring := by
    have h : Wiring.Respects (Equiv.sumCongr (Equiv.refl _) roots).toEmbedding
        c.graphRootWiring d.graphRootWiring := by
      rintro (i | (i | (i | i))) <;> rfl
    exact h.map_eq (Wiring.respects_refl _) _ (fun _ ↦ rfl)
  have h := reorderGraphIso c d hc (c.closed_perm es hp hc) (Equiv.refl _) roots ht hw
  rw [PortNet.reboundary_refl] at h
  exact ⟨h⟩

/-- Exchange only the two root occurrences of the head equation. -/
def swapHeadRoots (n : ℕ) : Fin (n + 1) ⊕ Fin (n + 1) ≃
    Fin (n + 1) ⊕ Fin (n + 1) where
  toFun p := match p with
    | .inl i => Fin.cases (.inr 0) (fun j ↦ .inl j.succ) i
    | .inr i => Fin.cases (.inl 0) (fun j ↦ .inr j.succ) i
  invFun p := match p with
    | .inl i => Fin.cases (.inr 0) (fun j ↦ .inl j.succ) i
    | .inr i => Fin.cases (.inl 0) (fun j ↦ .inr j.succ) i
  left_inv p := by
    rcases p with i | i <;> exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv p := by
    rcases p with i | i <;> exact Fin.cases rfl (fun _ ↦ rfl) i

/-- Reversing the head equation changes only the enumeration of its two term occurrences. -/
def swapGraphIso (c : Config arity) (eqn : Equation arity ℕ)
    (closed : ({ c with equations := eqn :: c.equations } : Config arity).Closed) :
    (({ c with equations := eqn :: c.equations } : Config arity).toFiniteNet closed).2.2.Iso
      (({ c with equations := (eqn.2, eqn.1) :: c.equations } : Config arity).toFiniteNet
        (c.closed_swap eqn closed)).2.2 := by
  let d : Config arity := { c with equations := eqn :: c.equations }
  let d' : Config arity := { c with equations := (eqn.2, eqn.1) :: c.equations }
  let e : d.GraphRoot ≃ d'.GraphRoot :=
    Equiv.sumCongr (Equiv.refl _) (swapHeadRoots c.equations.length)
  have ht (i : d.GraphRoot) : d'.graphTerm (e i) = d.graphTerm i := by
    rcases i with i | (i | i)
    · rfl
    · exact Fin.cases rfl (fun _ ↦ rfl) i
    · exact Fin.cases rfl (fun _ ↦ rfl) i
  have hw : d.graphRootWiring.map (Equiv.sumCongr (Equiv.refl _) e) =
      d'.graphRootWiring := by
    have h : Wiring.Respects (Equiv.sumCongr (Equiv.refl _) e).toEmbedding
        d.graphRootWiring d'.graphRootWiring := by
      rintro (i | (i | (i | i)))
      · rfl
      · rfl
      · exact Fin.cases rfl (fun _ ↦ rfl) i
      · exact Fin.cases rfl (fun _ ↦ rfl) i
    exact h.map_eq (Wiring.respects_refl _) _ (fun _ ↦ rfl)
  have h := reorderGraphIso d d' closed (c.closed_swap eqn closed) (Equiv.refl _) e ht hw
  rw [PortNet.reboundary_refl] at h
  exact h

end Geb.InteractionNet.Config

end
