/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraph
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Occurrence correspondences for renamed terms

Changing variable names preserves every cell, ordered cell port and leaf occurrence of a
term graph. The correspondence records its cell and leaf bijections together with their
matching, symbol and name equations. It therefore composes directly with forest assembly.

## Main definitions

* {lit}`TermFragment.Renaming` — a graph correspondence with a specified change of leaf names.
* {lit}`Term.fragmentRenaming` — the occurrence correspondence induced by textual renaming.

## Tags

interaction net, term, graph, renaming, occurrence, compiler
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α ν μ : Type} {arity : α → ℕ}

namespace TermFragment

/-- Renaming wire names preserves the fragment's cells, leaves, ordered ports and matching. -/
structure Renaming (σ : ν → μ) (f : TermFragment arity ν) (g : TermFragment arity μ) where
  /-- Corresponding syntax cells. -/
  cells : f.Cell ≃ g.Cell
  /-- Corresponding variable occurrences. -/
  leaves : f.Leaf ≃ g.Leaf
  /-- Every cell retains its symbol. -/
  labels : ∀ c, g.label (cells c) = f.label c
  /-- Every leaf has the specified new name. -/
  names : ∀ p, g.name (leaves p) = σ (f.name p)
  /-- The cell and leaf bijections preserve the wire matching. -/
  wires : f.net.wiring.map
    (endpointEquiv arity (Equiv.sumCongr (Equiv.refl Unit) leaves) cells labels) = g.net.wiring
  /-- Closed wire components are preserved. -/
  loops : f.net.loops = g.net.loops

/-- Consecutive fragment correspondences preserve cells, leaves, wires and closed components. -/
def Renaming.trans {κ : Type} {σ : ν → μ} {τ : μ → κ}
    {f : TermFragment arity ν} {g : TermFragment arity μ} {h : TermFragment arity κ}
    (i : Renaming σ f g) (j : Renaming τ g h) : Renaming (τ ∘ σ) f h where
  cells := i.cells.trans j.cells
  leaves := i.leaves.trans j.leaves
  labels c := (j.labels (i.cells c)).trans (i.labels c)
  names p := (j.names (i.leaves p)).trans (congrArg τ (i.names p))
  wires := by
    have he : (endpointEquiv arity (Equiv.sumCongr (Equiv.refl Unit) i.leaves)
        i.cells i.labels).trans (endpointEquiv arity
          (Equiv.sumCongr (Equiv.refl Unit) j.leaves) j.cells j.labels) =
        endpointEquiv arity (Equiv.sumCongr (Equiv.refl Unit) (i.leaves.trans j.leaves))
          (i.cells.trans j.cells) (fun c ↦ (j.labels (i.cells c)).trans (i.labels c)) := by
      ext p
      rcases p with (u | p) | ⟨c, p⟩ <;> rfl
    rw [← he, Wiring.map_trans, i.wires, j.wires]
  loops := i.loops.trans j.loops

/-- The direct renaming operation preserves the original occurrence positions. -/
def renameCorrespondence (σ : ν → μ) (f : TermFragment arity ν) : Renaming σ f (f.rename σ) where
  cells := Equiv.refl _
  leaves := Equiv.refl _
  labels _ := rfl
  names _ := rfl
  wires := by
    have he : endpointEquiv (label := f.label) (label' := f.label) arity
        (Equiv.sumCongr (Equiv.refl Unit) (Equiv.refl f.Leaf)) (Equiv.refl f.Cell)
          (fun _ ↦ rfl) = Equiv.refl _ := by
      ext p
      rcases p with (u | p) | ⟨c, p⟩ <;> rfl
    exact (congrArg (fun e ↦ f.net.wiring.map e) he).trans (Wiring.map_refl _)
  loops := rfl

end TermFragment

/-- Compiling a textually renamed term preserves cells and renames each leaf occurrence. -/
def Term.fragmentRenaming (σ : ν → μ) (t : Term arity ν) :
    TermFragment.Renaming σ t.fragment (t.subst (fun x ↦ Term.var (σ x))).fragment := by
  rw [Term.fragment_rename]
  exact t.fragment.renameCorrespondence σ

end Geb.InteractionNet

end
