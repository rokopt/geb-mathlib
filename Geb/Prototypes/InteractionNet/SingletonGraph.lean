/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigNamelessGraph
public import Geb.Prototypes.InteractionNet.ConfigGraphRenaming
public import Geb.Prototypes.InteractionNet.ClosedTermReadback
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Compiled singleton constructor configurations

The canonical final configuration consists of one closed term at the interface and no
equations. Its occurrence graph is the term fragment with its root exposed at external
port zero. Explicit cell bijections remove the singleton forest index and connect the
configuration compiler to the whole-net read-back theorem for term fragments.

## Main definitions

* {lit}`Config.singleton` — one interface term with no equations.
* {lit}`Term.closedBoundaryEquiv` — identify a closed term's root with external port zero.
* {lit}`Config.singletonCellEquiv` — identify term cells with singleton-forest cells.

## Main statements

* {lit}`Config.singleton_readTree` — the compiled singleton reads its syntax constructor tree.

## Tags

interaction net, compiler, singleton, constructor, graph, read-back
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

namespace Term

/-- A nameless term has no graph leaf occurrence. -/
theorem noFragmentLeaf {ν : Type} (t : Term arity ν) (hn : t.names = [])
    (p : t.fragment.Leaf) : False := by
  have h : t.fragment.name p ∈ t.fragment.names :=
    List.mem_map.mpr ⟨p, t.fragment.cover p, rfl⟩
  rw [fragment_names, hn] at h
  exact List.not_mem_nil h

/-- The sole boundary of a nameless term is its root, assigned external port zero. -/
def closedBoundaryEquiv {ν : Type} (t : Term arity ν) (hn : t.names = []) :
    Unit ⊕ t.fragment.Leaf ≃ Fin 1 where
  toFun p := match p with
    | .inl _ => 0
    | .inr p => (t.noFragmentLeaf hn p).elim
  invFun _ := .inl ()
  left_inv p := by
    rcases p with u | p
    · cases u; rfl
    · exact (t.noFragmentLeaf hn p).elim
  right_inv i := (Fin.eq_zero i).symm

end Term

namespace Config

/-- A final configuration exposes one term and has no pending equation. -/
def singleton (t : Term arity ℕ) (next : ℕ) : Config arity := ⟨[t], [], next⟩

/-- A nameless singleton configuration is closed. -/
theorem singleton_closed (t : Term arity ℕ) (next : ℕ) (hn : t.names = []) :
    (singleton t next).Closed := by
  simp only [Closed, names, singleton, List.flatMap_cons, List.flatMap_nil, List.append_nil, hn]
  exact fun _ h ↦ (List.not_mem_nil h).elim

/-- Every syntax cell belongs to the sole root of a singleton configuration. -/
def singletonCellEquiv (t : Term arity ℕ) (next : ℕ) :
    t.fragment.Cell ≃ (singleton t next).GraphCell where
  toFun c := ⟨.inl (0 : Fin 1), c⟩
  invFun p := match p with
    | ⟨.inl i, c⟩ => Fin.cases
        (motive := fun i ↦ ((singleton t next).graphFragments (.inl i)).Cell → t.fragment.Cell)
        id (fun j ↦ Fin.elim0 j) i c
    | ⟨.inr (.inl i), _⟩ => Fin.elim0 i
    | ⟨.inr (.inr i), _⟩ => Fin.elim0 i
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨i | (i | i), c⟩
    · have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      rfl
    · exact Fin.elim0 i
    · exact Fin.elim0 i

/-- The compiled occurrence graph of a closed singleton is its root-exposed term fragment. -/
def singletonOccurrenceIso (t : Term arity ℕ) (next : ℕ) (hn : t.names = []) :
    (t.fragment.net.reboundary (t.closedBoundaryEquiv hn)).Iso
      ((singleton t next).occurrenceNet (singleton_closed t next hn)) := by
  let c := singleton t next
  have hc : c.names = [] := by
    simp only [c, singleton, names, List.flatMap_cons, List.flatMap_nil, List.append_nil, hn]
  rw [c.occurrenceNet_eq_forest (singleton_closed t next hn) rfl hc]
  let n : PortNet arity c.graphLabel (Σ i, Unit ⊕ (c.graphFragments i).Leaf) :=
    PortNet.sigma (fun i ↦ (c.graphFragments i).net)
  let eb : (Σ i, Unit ⊕ (c.graphFragments i).Leaf) ≃ Fin 1 := c.forestBoundaryEquiv rfl hc
  let cells := singletonCellEquiv t next
  have labels (d : t.fragment.Cell) : c.graphLabel (cells d) = t.fragment.label d := rfl
  refine ⟨cells, labels, ?_, ?_⟩
  · let full := endpointEquiv arity (t.closedBoundaryEquiv hn) cells labels
    let outer := endpointEquiv (label := c.graphLabel) (label' := c.graphLabel)
      arity eb (Equiv.refl c.GraphCell) (fun _ ↦ rfl)
    let es := PortNet.sigmaEndpointEquiv (Γ := fun i ↦ Unit ⊕ (c.graphFragments i).Leaf)
      arity (fun i ↦ (c.graphFragments i).label)
    have hp (p : Endpoint arity t.fragment.label (Unit ⊕ t.fragment.Leaf)) :
        full p = outer (es ⟨.inl (0 : Fin 1), p⟩) := by
      rcases p with (u | p) | ⟨d, p⟩
      · cases u; rfl
      · exact (t.noFragmentLeaf hn p).elim
      · rfl
    have hw : Wiring.Respects full.toEmbedding t.fragment.net.wiring
        (n.reboundary eb).wiring := by
      intro p
      have hf : n.wiring.partner (es ⟨.inl (0 : Fin 1), p⟩) =
          es ⟨.inl (0 : Fin 1), t.fragment.net.wiring.partner p⟩ :=
        Wiring.map_partner es (Wiring.sigma (fun i ↦ (c.graphFragments i).net.wiring))
          ⟨.inl (0 : Fin 1), p⟩
      calc
        (n.reboundary eb).wiring.partner (full p) =
            (n.reboundary eb).wiring.partner (outer (es ⟨.inl (0 : Fin 1), p⟩)) :=
          congrArg (n.reboundary eb).wiring.partner (hp p)
        _ = outer (n.wiring.partner (es ⟨.inl (0 : Fin 1), p⟩)) :=
          Wiring.map_partner outer n.wiring _
        _ = outer (es ⟨.inl (0 : Fin 1), t.fragment.net.wiring.partner p⟩) := congrArg outer hf
        _ = full (t.fragment.net.wiring.partner p) := (hp _).symm
    have hm := hw.map_eq (Wiring.respects_refl _) full (fun _ ↦ rfl)
    let first := endpointEquiv (label := t.fragment.label) (label' := t.fragment.label)
      arity (t.closedBoundaryEquiv hn) (Equiv.refl t.fragment.Cell) (fun _ ↦ rfl)
    let second := endpointEquiv arity (Equiv.refl (Fin 1)) cells labels
    have he : first.trans second = full := by
      apply Equiv.ext
      intro p
      cases p <;> rfl
    exact (Wiring.map_trans first second t.fragment.net.wiring).symm.trans
      ((congrArg (fun e ↦ t.fragment.net.wiring.map e) he).trans hm)
  · have hz (i : c.GraphRoot) : (c.graphFragments i).net.loops = 0 := by
      rw [graphFragments_term]
      exact Term.fragment_loops _
    have hs : n.loops = 0 := by
      change ((FinEnum.toList c.GraphRoot).map fun i ↦ (c.graphFragments i).net.loops).sum = 0
      simp [hz]
    exact t.fragment_loops.trans hs.symm

/-- Ordinal cell indexing preserves the singleton configuration's term-fragment isomorphism. -/
def singletonIndexedIso (t : Term arity ℕ) (next : ℕ) (hn : t.names = []) :
    (t.fragment.net.reboundary (t.closedBoundaryEquiv hn)).indexed.Iso
      ((singleton t next).toFiniteNet (singleton_closed t next hn)).2.2 :=
  (PortNet.indexedIso (t.fragment.net.reboundary (t.closedBoundaryEquiv hn))).symm.trans
    ((singletonOccurrenceIso t next hn).trans
      ((singleton t next).occurrenceIndexedIso (singleton_closed t next hn)))

/-- The actual configuration compiler's final singleton reads back its syntax constructor tree. -/
theorem singleton_readTree (tag : α → Option ℕ) (t : Term arity ℕ) (next : ℕ)
    (hn : t.names = []) :
    FiniteNet.readTree tag ((singleton t next).toFiniteNet (singleton_closed t next hn)) =
      t.constructorReadback tag := by
  let n : FiniteNet arity 1 :=
    ⟨FinEnum.card t.fragment.Cell, fun i ↦ t.fragment.label (FinEnum.equiv.symm i),
      (t.fragment.net.reboundary (t.closedBoundaryEquiv hn)).indexed⟩
  have h := FiniteNet.readTree_iso tag (n := n)
    (m := (singleton t next).toFiniteNet (singleton_closed t next hn))
    (singletonIndexedIso t next hn)
  exact h.symm.trans (t.fragment_indexed_readTree tag (t.closedBoundaryEquiv hn) rfl)

end Config

end Geb.InteractionNet

end
