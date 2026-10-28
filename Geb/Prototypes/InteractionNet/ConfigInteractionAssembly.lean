/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigAppendForest
public import Geb.Prototypes.InteractionNet.ConfigInteractionAllocation
public import Geb.Prototypes.InteractionNet.RuleInstantiationForest
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Assembling the textual result of interaction

Compiling the instantiated equation prefix agrees with attaching the argument and internal
variable fragments to the original rule forest. The surrounding configuration is retained.
Transporting the result's boundary matching across this correspondence gives one assembly
of the complete textual target.

## Main definitions

* {lit}`Config.interactionAssemblyWiring` — the target context on the attached forest.
* {lit}`Config.interactionAssemblyIso` — compilation agrees with this assembly.

## Main statements

* {lit}`Config.interactionAssembly_wiring` — the forest correspondence preserves every wire.

## Tags

interaction net, compiler, interaction, equation, forest, assembly
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {a b : α}

/-- Transport the textual target's matching to the attached rule and retained context forest. -/
def interactionAssemblyWiring (c : Config arity) (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations := r.instantiate c.nextName xs ys ++
      c.equations } : Config arity).Closed) :=
  (c.appendContextWiring (r.instantiate c.nextName xs ys) closed).map
    (Equiv.sumCongr (Equiv.refl (Fin c.interface.length))
      (Equiv.sumCongr (r.instantiationBoundaryEquiv c.nextName xs ys)
        (Equiv.refl c.GraphForestBoundary)))

/-- All instantiated equation sides and the original context compile to the attached forest. -/
theorem interactionAssembly_wiring (c : Config arity) (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (c.appendForest (r.instantiate c.nextName xs ys)).wiring.map
      (endpointEquiv arity
        (Equiv.sumCongr (r.instantiationBoundaryEquiv c.nextName xs ys) (Equiv.refl _))
        (Equiv.sumCongr (r.instantiationCellsEquiv c.nextName xs ys) (Equiv.refl _))
        (PortNet.sum_label _ _ (r.instantiationCellsEquiv_label c.nextName xs ys)
          (fun _ ↦ rfl))) = (c.interactionAttachedForest r c.nextName xs ys).wiring := by
  apply PortNet.sum_wiring
  · exact r.instantiationForest_wiring c.nextName xs ys
  · rw [endpointEquiv_refl]
    exact Wiring.map_refl _

/-- The textual target compiles to the attached rule forest in its surrounding wiring. -/
def interactionAssemblyIso (c : Config arity) (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (closed : ({ c with equations := r.instantiate c.nextName xs ys ++
      c.equations } : Config arity).Closed) :
    let := sigmaEnum (C := fun i ↦ ((EquationGraph.fragments r.equations i).attach
      (r.instantiationFragments c.nextName xs ys i)).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ ((EquationGraph.fragments r.equations i).attach
      (r.instantiationFragments c.nextName xs ys i)).Leaf)
    let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
    let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
    (({ c with equations := r.instantiate c.nextName xs ys ++ c.equations } :
      Config arity).occurrenceNet closed).Iso
        ((c.interactionAttachedForest r c.nextName xs ys).couple
          (c.interactionAssemblyWiring r xs ys closed)) := by
  let := sigmaEnum (C := fun i ↦ ((EquationGraph.fragments r.equations i).attach
    (r.instantiationFragments c.nextName xs ys i)).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ ((EquationGraph.fragments r.equations i).attach
    (r.instantiationFragments c.nextName xs ys i)).Leaf)
  let := sigmaEnum (C := fun i ↦ (c.graphFragments i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
  let := sigmaEnum (C := fun i ↦
    (EquationGraph.fragments (r.instantiate c.nextName xs ys) i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕
    (EquationGraph.fragments (r.instantiate c.nextName xs ys) i).Leaf)
  refine (c.appendGraphIso (r.instantiate c.nextName xs ys) closed).trans ?_
  apply PortNet.coupleIso _ _ _ _
    (Equiv.sumCongr (r.instantiationBoundaryEquiv c.nextName xs ys) (Equiv.refl _))
    (Equiv.sumCongr (r.instantiationCellsEquiv c.nextName xs ys) (Equiv.refl _))
    (PortNet.sum_label _ _ (r.instantiationCellsEquiv_label c.nextName xs ys) (fun _ ↦ rfl))
    (c.interactionAssembly_wiring r xs ys)
  · exact congrArg (· + c.graphForest.loops) (r.instantiationForest_loops c.nextName xs ys)
  · rfl

end Geb.InteractionNet.Config

end
