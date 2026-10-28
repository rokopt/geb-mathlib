/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraph
public import Geb.Prototypes.InteractionNet.PortNetSum
public import Geb.Prototypes.InteractionNet.CouplingCancellation
public import Geb.Prototypes.InteractionNet.AssemblyIso
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Variable fragments in disjoint graph unions

A variable fragment contributes a boundary wire and no cells. Removing its empty cell
summand identifies its disjoint union with another net with an adjoined boundary wire.
The identification commutes with attachment of any surrounding matching.

## Main statements

* {lit}`TermFragment.var_sum_wiring` — a disjoint variable fragment is an adjoined wire.

## Tags

interaction net, compiler, variable, disjoint union, boundary
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.TermFragment

open scoped FinEnum

private local instance : FinEnum Bool := boolEnum

variable {α ν C B Γ : Type} {arity : α → ℕ} {label : C → α}

/-- The endpoints of a variable fragment are exactly the two ends of one wire. -/
def varEndpointEquiv (x : ν) :
    Endpoint arity (var (arity := arity) x).label
      (Unit ⊕ (var (arity := arity) x).Leaf) ≃ Bool where
  toFun p := match p with
    | .inl (.inl _) => false
    | .inl (.inr _) => true
    | .inr ⟨c, _⟩ => Fin.elim0 c
  invFun b := if b then .inl (.inr ()) else .inl (.inl ())
  left_inv p := by
    rcases p with (u | u) | ⟨c, p⟩
    · cases u; rfl
    · cases u; rfl
    · exact Fin.elim0 c
  right_inv b := by cases b <;> rfl

/-- Removing the variable's empty cell summand preserves every remaining cell's symbol. -/
theorem var_sum_label (x : ν) (c : (var (arity := arity) x).Cell ⊕ C) :
    label (PortNet.emptyCellEquiv C c) = Sum.elim (var x).label label c := by
  cases c with
  | inl c => exact Fin.elim0 c
  | inr c => rfl

/-- A variable fragment beside a net is a separate Boolean boundary wire beside its cells. -/
theorem var_sum_wiring (x : ν) (n : PortNet arity label B) :
    ((var x).net.sum n).wiring.map (endpointEquiv arity
      (Equiv.sumCongr Equiv.boolEquivPUnitSumPUnit.symm (Equiv.refl B))
      (PortNet.emptyCellEquiv C) (var_sum_label x)) = n.adjoinWire.wiring := by
  have hv : (var (arity := arity) x).net.wiring.map (varEndpointEquiv x) = Wiring.wire := by
    ext b
    cases b <;> rfl
  have he : (PortNet.sumEndpointEquiv arity (var x).label label _ B).trans
      (endpointEquiv arity
        (Equiv.sumCongr Equiv.boolEquivPUnitSumPUnit.symm (Equiv.refl B))
        (PortNet.emptyCellEquiv C) (var_sum_label x)) =
      (Equiv.sumCongr (varEndpointEquiv x) (Equiv.refl _)).trans
        (Equiv.sumAssoc Bool B (CellPort arity label)).symm := by
    ext p
    rcases p with ((u | u) | ⟨c, p⟩) | (b | ⟨c, p⟩)
    · rfl
    · rfl
    · exact Fin.elim0 c
    · rfl
    · rfl
  change (((var x).net.wiring.sum n.wiring).map _).map _ = _
  erw [← Wiring.map_trans, he, Wiring.map_trans, Wiring.map_sum, hv, Wiring.map_refl]
  rfl

/-- A variable's disjoint wire identification commutes with an arbitrary boundary context. -/
def varSumCoupleIso [FinEnum C] [FinEnum B] [FinEnum Γ]
    (x : ν) (n : PortNet arity label B)
    (w : Wiring (Γ ⊕ ((Unit ⊕ (var (arity := arity) x).Leaf) ⊕ B))) :
    let := boolEnum
    (((var x).net.sum n).couple w).Iso
      (n.adjoinWire.couple (w.map (Equiv.sumCongr (Equiv.refl Γ)
        (Equiv.sumCongr Equiv.boolEquivPUnitSumPUnit.symm (Equiv.refl B))))) := by
  let := boolEnum
  apply PortNet.coupleIso _ _ _ _ _ _ (var_sum_label x) (var_sum_wiring x n) ?_ rfl
  exact Nat.zero_add _

end Geb.InteractionNet.TermFragment

end
