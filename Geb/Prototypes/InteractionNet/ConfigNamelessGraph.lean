/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraphIso
public import Geb.Prototypes.InteractionNet.CouplingIdentity
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Graph assembly of closed constructor forests

When a configuration has neither equations nor variable occurrences, its term roots are
attached directly to the corresponding external interface positions. Assembly then only
renames the forest boundary. It changes no cell or internal wire and creates no closed wire.
This identifies the compiled final constructor configurations with their term fragments.

## Main statements

* {lit}`Config.occurrenceNet_eq_forest` — final nameless configurations retain their term forest.

## Tags

interaction net, compiler, constructor, normal form, graph, boundary
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Config

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

/-- A configuration with no textual names has no graph leaf occurrence. -/
theorem noGraphLeaf (c : Config arity) (hn : c.names = []) (p : c.GraphLeaf) : False := by
  have hp : 0 < (c.graphLeafOrder.map c.graphLeafName).count (c.graphLeafName p) :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨p,
    TermFragment.forestOrder_cover _ c.graphRootOrder_cover c.graphFragments p, rfl⟩)
  rw [c.graphLeaf_count, hn, List.count_nil] at hp
  exact Nat.not_lt_zero _ hp

/-- Without equations or names, every forest boundary is one external interface root. -/
def forestBoundaryEquiv (c : Config arity) (he : c.equations = []) (hn : c.names = []) :
    (Σ i, Unit ⊕ (c.graphFragments i).Leaf) ≃ Fin c.interface.length where
  toFun p := match p with
    | ⟨.inl i, .inl _⟩ => i
    | ⟨.inr (.inl i), .inl _⟩ => Fin.elim0 (Fin.cast (congrArg List.length he) i)
    | ⟨.inr (.inr i), .inl _⟩ => Fin.elim0 (Fin.cast (congrArg List.length he) i)
    | ⟨i, .inr p⟩ => (c.noGraphLeaf hn ⟨i, p⟩).elim
  invFun i := ⟨.inl i, .inl ()⟩
  left_inv p := by
    rcases p with ⟨i, u | p⟩
    · rcases i with i | (i | i)
      · cases u; rfl
      · exact Fin.elim0 (Fin.cast (congrArg List.length he) i)
      · exact Fin.elim0 (Fin.cast (congrArg List.length he) i)
    · exact (c.noGraphLeaf hn ⟨i, p⟩).elim
  right_inv _ := rfl

/-- Assembly of an equation-free nameless forest only exposes its roots as the interface. -/
theorem occurrenceNet_eq_forest (c : Config arity) (closed : c.Closed)
    (he : c.equations = []) (hn : c.names = []) :
    c.occurrenceNet closed = (PortNet.sigma (fun i ↦ (c.graphFragments i).net)).reboundary
      (c.forestBoundaryEquiv he hn) := by
  let f := c.graphFragments
  let B := Σ i, Unit ⊕ (f i).Leaf
  let := sigmaEnum (C := fun i ↦ (f i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (f i).Leaf)
  let n := PortNet.sigma (fun i ↦ (f i).net)
  let leaves := (c.graphLeafWiring closed).map (PortNet.emptyCellEquiv _).symm
  let w := (c.graphRootWiring.sum leaves).map (TermFragment.assemblyBoundaryEquiv f)
  let e := (c.forestBoundaryEquiv he hn).trans c.graphBoundaryEquiv.symm
  let pair := Equiv.sumCongr e (Equiv.refl B)
  have hw : (Wiring.identityBoundary B).map pair = w := by
    have h : Wiring.Respects pair.toEmbedding (Wiring.identityBoundary B) w := by
      rintro (⟨i, u | p⟩ | ⟨i, u | p⟩)
      · cases u
        rcases i with i | (i | i)
        · rfl
        · exact Fin.elim0 (Fin.cast (congrArg List.length he) i)
        · exact Fin.elim0 (Fin.cast (congrArg List.length he) i)
      · exact (c.noGraphLeaf hn ⟨i, p⟩).elim
      · cases u
        rcases i with i | (i | i)
        · rfl
        · exact Fin.elim0 (Fin.cast (congrArg List.length he) i)
        · exact Fin.elim0 (Fin.cast (congrArg List.length he) i)
      · exact (c.noGraphLeaf hn ⟨i, p⟩).elim
    exact h.map_eq (Wiring.respects_refl w) pair (fun _ ↦ rfl)
  change (n.couple w).reboundary c.graphBoundaryEquiv = _
  rw [← hw, PortNet.couple_of_equiv, PortNet.reboundary_trans]
  have hb : e.trans c.graphBoundaryEquiv = c.forestBoundaryEquiv he hn := by
    apply Equiv.ext
    intro p
    exact c.graphBoundaryEquiv.apply_symm_apply _
  rw [hb]

end Geb.InteractionNet.Config

end
