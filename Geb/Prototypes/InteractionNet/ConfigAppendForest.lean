/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigAppendOccurrences
public import Geb.Prototypes.InteractionNet.ConfigGraphContext
public import Geb.Prototypes.InteractionNet.PortNetSum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Compiling a prefix of configuration equations

A prefix of replacement equations contributes its term forest alongside the existing
configuration forest. The occurrence bijection for concatenation preserves cells, symbols
and wires. Transporting the surrounding matching along this bijection therefore gives
the graph of the complete configuration.

## Main definitions

* {lit}`Config.appendForest` — replacement fragments beside the retained forest.
* {lit}`Config.appendGraphIso` — compile the prefix and retained forest in their common context.

## Tags

interaction net, compiler, equation, concatenation, forest, assembly, isomorphism
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- Place a prefix's equation fragments beside the retained configuration forest. -/
def appendForest (c : Config arity) (es : List (Equation arity ℕ)) :
    PortNet arity (Sum.elim
      (fun p : Σ i, (EquationGraph.fragments es i).Cell ↦
        (EquationGraph.fragments es p.1).label p.2) c.graphLabel)
      ((Σ i, Unit ⊕ (EquationGraph.fragments es i).Leaf) ⊕ c.GraphForestBoundary) :=
  (PortNet.sigma (fun i ↦ (EquationGraph.fragments es i).net)).sum c.graphForest

private theorem cast_label {f g : TermFragment arity ℕ} (h : g = f) (p : f.Cell) :
    g.label ((congrArg TermFragment.Cell h).mpr p) = f.label p := by cases h; rfl

/-- Concatenation retains the symbol on every newly prepended and original cell. -/
theorem appendForest_label (c : Config arity) (es : List (Equation arity ℕ))
    (p : (Σ i, (EquationGraph.fragments es i).Cell) ⊕ c.GraphCell) :
    ({ c with equations := es ++ c.equations } : Config arity).graphLabel
      (c.appendOccurrencesEquiv es (fun f ↦ f.Cell) p) =
        Sum.elim (fun p : Σ i, (EquationGraph.fragments es i).Cell ↦
          (EquationGraph.fragments es p.1).label p.2) c.graphLabel p := by
  rcases p with ⟨i, p⟩ | ⟨i, p⟩
  · exact cast_label (c.appendRootEquiv_fragment es (.inl i)) p
  · exact cast_label (c.appendRootEquiv_fragment es (.inr i)) p

private theorem cast_partner {f g : TermFragment arity ℕ} (h : g = f)
    (p : Endpoint arity f.label (Unit ⊕ f.Leaf)) :
    g.net.wiring.partner
      ((congrArg (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf)) h).mpr p) =
        (congrArg (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf)) h).mpr
          (f.net.wiring.partner p) := by cases h; rfl

private theorem occurrences_wiring (c : Config arity) (es : List (Equation arity ℕ)) :
    ((Wiring.sigma (fun i ↦ (EquationGraph.fragments es i).net.wiring)).sum
      (Wiring.sigma (fun i ↦ (c.graphFragments i).net.wiring))).map
        (c.appendOccurrencesEquiv es (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf))) =
      Wiring.sigma (fun i ↦ (({ c with equations := es ++ c.equations } :
        Config arity).graphFragments i).net.wiring) := by
  have h : Wiring.Respects
      (c.appendOccurrencesEquiv es (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf))).toEmbedding
      ((Wiring.sigma (fun i ↦ (EquationGraph.fragments es i).net.wiring)).sum
        (Wiring.sigma (fun i ↦ (c.graphFragments i).net.wiring)))
      (Wiring.sigma (fun i ↦ (({ c with equations := es ++ c.equations } :
        Config arity).graphFragments i).net.wiring)) := by
    rintro (⟨i, p⟩ | ⟨i, p⟩)
    · exact congrArg (Sigma.mk (c.appendRootEquiv es (.inl i)))
        (cast_partner (c.appendRootEquiv_fragment es (.inl i)) p)
    · exact congrArg (Sigma.mk (c.appendRootEquiv es (.inr i)))
        (cast_partner (c.appendRootEquiv_fragment es (.inr i)) p)
  exact h.map_eq (Wiring.respects_refl _) _ (fun _ ↦ rfl)

private def allocationEquiv (c : Config arity) (es : List (Equation arity ℕ)) :
    (Σ i, Endpoint arity (EquationGraph.fragments es i).label
      (Unit ⊕ (EquationGraph.fragments es i).Leaf)) ⊕
      (Σ i, Endpoint arity (c.graphFragments i).label (Unit ⊕ (c.graphFragments i).Leaf)) ≃
        Endpoint arity (Sum.elim
          (fun p : Σ i, (EquationGraph.fragments es i).Cell ↦
            (EquationGraph.fragments es p.1).label p.2) c.graphLabel)
          ((Σ i, Unit ⊕ (EquationGraph.fragments es i).Leaf) ⊕ c.GraphForestBoundary) :=
  (Equiv.sumCongr (PortNet.sigmaEndpointEquiv arity (fun i ↦ (EquationGraph.fragments es i).label))
    (PortNet.sigmaEndpointEquiv arity (fun i ↦ (c.graphFragments i).label))).trans
      (PortNet.sumEndpointEquiv arity _ _ _ _)

private theorem cast_boundary {f g : TermFragment arity ℕ} (h : g = f) (p : Unit ⊕ f.Leaf) :
    (congrArg (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf)) h).mpr (.inl p) =
      Sum.inl ((congrArg (fun f ↦ Unit ⊕ f.Leaf) h).mpr p) := by cases h; rfl

private theorem cast_cell {f g : TermFragment arity ℕ} (h : g = f) (v : f.Cell)
    (p : Fin (arity (f.label v) + 1)) :
    (congrArg (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf)) h).mpr (.inr ⟨v, p⟩) =
      Sum.inr ⟨(congrArg TermFragment.Cell h).mpr v,
        Fin.cast (congrArg (fun a ↦ arity a + 1) (cast_label h v).symm) p⟩ := by cases h; rfl

/-- Separating a prefix preserves the complete forest matching under its occurrence bijection. -/
theorem appendForest_wiring (c : Config arity) (es : List (Equation arity ℕ)) :
    (c.appendForest es).wiring.map (endpointEquiv arity
      (c.appendOccurrencesEquiv es (fun f ↦ Unit ⊕ f.Leaf))
      (c.appendOccurrencesEquiv es (fun f ↦ f.Cell)) (c.appendForest_label es)) =
        ({ c with equations := es ++ c.equations } : Config arity).graphForest.wiring := by
  let d : Config arity := { c with equations := es ++ c.equations }
  have he : (allocationEquiv c es).trans (endpointEquiv arity
      (c.appendOccurrencesEquiv es (fun f ↦ Unit ⊕ f.Leaf))
      (c.appendOccurrencesEquiv es (fun f ↦ f.Cell)) (c.appendForest_label es)) =
        (c.appendOccurrencesEquiv es (fun f ↦ Endpoint arity f.label (Unit ⊕ f.Leaf))).trans
          (PortNet.sigmaEndpointEquiv arity
            (Γ := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
              (fun i ↦ (d.graphFragments i).label)) := by
    ext p
    rcases p with ⟨i, p | ⟨v, p⟩⟩ | ⟨i, p | ⟨v, p⟩⟩
    · exact congrArg (fun q ↦ (PortNet.sigmaEndpointEquiv arity
        (Γ := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
              (fun i ↦ (d.graphFragments i).label)) ⟨c.appendRootEquiv es (.inl i), q⟩)
          (cast_boundary (c.appendRootEquiv_fragment es (.inl i)) p).symm
    · exact congrArg (fun q ↦ (PortNet.sigmaEndpointEquiv arity
        (Γ := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
              (fun i ↦ (d.graphFragments i).label)) ⟨c.appendRootEquiv es (.inl i), q⟩)
          (cast_cell (c.appendRootEquiv_fragment es (.inl i)) v p).symm
    · exact congrArg (fun q ↦ (PortNet.sigmaEndpointEquiv arity
        (Γ := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
              (fun i ↦ (d.graphFragments i).label)) ⟨c.appendRootEquiv es (.inr i), q⟩)
          (cast_boundary (c.appendRootEquiv_fragment es (.inr i)) p).symm
    · exact congrArg (fun q ↦ (PortNet.sigmaEndpointEquiv arity
        (Γ := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
              (fun i ↦ (d.graphFragments i).label)) ⟨c.appendRootEquiv es (.inr i), q⟩)
          (cast_cell (c.appendRootEquiv_fragment es (.inr i)) v p).symm
  have ha : ((Wiring.sigma (fun i ↦ (EquationGraph.fragments es i).net.wiring)).sum
      (Wiring.sigma (fun i ↦ (c.graphFragments i).net.wiring))).map (allocationEquiv c es) =
        (c.appendForest es).wiring := by
    dsimp only [allocationEquiv]
    erw [Wiring.map_trans, Wiring.map_sum]
    rfl
  erw [← ha, ← Wiring.map_trans, he, Wiring.map_trans, occurrences_wiring]
  rfl

/-- A prefix and the retained configuration are term forests, without closed components. -/
theorem appendForest_loops (c : Config arity) (es : List (Equation arity ℕ)) :
    (c.appendForest es).loops = 0 := by
  simp [appendForest, PortNet.sum, PortNet.sigma, EquationGraph.fragments,
    Term.fragment_loops, graphForest_loops]

/-- The complete surrounding matching expressed on the prefix and retained forest boundaries. -/
def appendContextWiring (c : Config arity) (es : List (Equation arity ℕ))
    (closed : ({ c with equations := es ++ c.equations } : Config arity).Closed) :
    Wiring (Fin c.interface.length ⊕
      ((Σ i, Unit ⊕ (EquationGraph.fragments es i).Leaf) ⊕ c.GraphForestBoundary)) :=
  (({ c with equations := es ++ c.equations } : Config arity).graphContextWiring closed).map
    (Equiv.sumCongr (Equiv.refl _) (c.appendOccurrencesEquiv es (fun f ↦ Unit ⊕ f.Leaf))).symm

/-- Compiling the whole configuration agrees with attaching its context to the separated forests. -/
def appendGraphIso (c : Config arity) (es : List (Equation arity ℕ))
    (closed : ({ c with equations := es ++ c.equations } : Config arity).Closed) :
    let := sigmaEnum (C := fun i ↦ (EquationGraph.fragments es i).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (EquationGraph.fragments es i).Leaf)
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    (({ c with equations := es ++ c.equations } : Config arity).occurrenceNet closed).Iso
      ((c.appendForest es).couple (c.appendContextWiring es closed)) := by
  let := sigmaEnum (C := fun i ↦ (EquationGraph.fragments es i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (EquationGraph.fragments es i).Leaf)
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  let d : Config arity := { c with equations := es ++ c.equations }
  let := sigmaEnum (C := fun i ↦ (d.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (d.graphFragments i).Leaf)
  have hb : (c.appendContextWiring es closed).map (Equiv.sumCongr (Equiv.refl _)
      (c.appendOccurrencesEquiv es (fun f ↦ Unit ⊕ f.Leaf))) = d.graphContextWiring closed :=
    Wiring.map_symm_map
      (Equiv.sumCongr (Equiv.refl _) (c.appendOccurrencesEquiv es (fun f ↦ Unit ⊕ f.Leaf))).symm _
  have h := PortNet.coupleIso (c.appendForest es) d.graphForest
    (c.appendContextWiring es closed) (d.graphContextWiring closed)
    (c.appendOccurrencesEquiv es (fun f ↦ Unit ⊕ f.Leaf))
    (c.appendOccurrencesEquiv es (fun f ↦ f.Cell)) (c.appendForest_label es)
    (c.appendForest_wiring es) ((c.appendForest_loops es).trans d.graphForest_loops.symm) hb
  rw [d.occurrenceNet_eq_graphForest_couple closed]
  exact h.symm

end Geb.InteractionNet.Config

end
