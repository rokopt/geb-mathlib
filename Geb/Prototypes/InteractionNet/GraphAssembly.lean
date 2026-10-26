/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraph
public import Geb.Prototypes.InteractionNet.FiniteWiring
public import Geb.Prototypes.InteractionNet.WiringEmbedding
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Assembling term graphs by their roots and named leaves

A family of term fragments is connected by two matchings. One joins term roots to other
roots or to external root positions. The other joins named leaf occurrences to one another
or to external named positions. Gluing these matchings to the fragments produces a port
net while retaining every closed wire component. This construction serves both textual
configurations and rule bodies.

## Main definitions

* {lit}`PortNet.couple` — attach an external matching to a net's boundary.
* {lit}`TermFragment.forestOrder` — the leaves of an ordered family of fragments.
* {lit}`TermFragment.assemble` — join a family by root and leaf matchings.

## Tags

interaction net, syntax, graph, gluing, root, occurrence
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

namespace PortNet

variable {α C B Γ : Type} {arity : α → ℕ} {label : C → α}

/-- Inserting into a wire-only context leaves just the inserted cells. -/
def emptyCellEquiv (C : Type) : Fin 0 ⊕ C ≃ C where
  toFun := Sum.elim Fin.elim0 id
  invFun := Sum.inr
  left_inv p := by cases p with | inl i => exact Fin.elim0 i | inr _ => rfl
  right_inv _ := rfl

/-- Ambient endpoints before attaching a boundary matching. -/
abbrev CouplingEndpoint (arity : α → ℕ) (label : C → α) (Γ B : Type) :=
  (Γ ⊕ B) ⊕ Endpoint arity label B

/-- Pair each hole of the external matching with the corresponding boundary of the net. -/
def couplePorts (arity : α → ℕ) (label : C → α) (Γ B : Type) :
    B × Bool ↪ CouplingEndpoint arity label Γ B where
  toFun p := if p.2 then .inr (.inl p.1) else .inl (.inr p.1)
  inj' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    cases b <;> cases d <;> simp_all

/-- After boundary attachment, just the external boundary and the net's cells survive. -/
def coupleEndpointEquiv (arity : α → ℕ) (label : C → α) (Γ B : Type) :
    {p : CouplingEndpoint arity label Γ B // ∀ i b, p ≠ couplePorts arity label Γ B (i, b)} ≃
      Endpoint arity label Γ where
  toFun p := match p with
    | ⟨.inl (.inl γ), _⟩ => .inl γ
    | ⟨.inl (.inr i), h⟩ => (h i false rfl).elim
    | ⟨.inr (.inl i), h⟩ => (h i true rfl).elim
    | ⟨.inr (.inr p), _⟩ => .inr p
  invFun p := match p with
    | .inl γ => ⟨.inl (.inl γ), by intro i b; cases b <;> intro h <;> cases h⟩
    | .inr p => ⟨.inr (.inr p), by intro i b; cases b <;> intro h <;> cases h⟩
  left_inv p := match p with
    | ⟨.inl (.inl _), _⟩ => rfl
    | ⟨.inl (.inr i), h⟩ => (h i false rfl).elim
    | ⟨.inr (.inl i), h⟩ => (h i true rfl).elim
    | ⟨.inr (.inr _), _⟩ => rfl
  right_inv p := by cases p <;> rfl

/-- Locate the attached graph's live endpoints in the ambient matching and original net. -/
def coupleEmbedding (arity : α → ℕ) (label : C → α) (Γ B : Type) :
    Endpoint arity label Γ ↪ CouplingEndpoint arity label Γ B :=
  (coupleEndpointEquiv arity label Γ B).symm.toEmbedding.trans (.subtype _)

/-- Attach a matching to all boundary positions, retaining its external endpoints. -/
def couple [FinEnum C] [FinEnum Γ] [FinEnum B]
    (n : PortNet arity label B) (w : Wiring (Γ ⊕ B)) : PortNet arity label Γ :=
  let dec : DecidableEq (CouplingEndpoint arity label Γ B) := inferInstance
  let := sigmaEnum (C := fun c ↦ Fin (arity (label c) + 1))
  let : DecidableEq (CouplingEndpoint arity label Γ B) := dec
  let g := Wiring.gluedFinite (couplePorts arity label Γ B) (FinEnum.toList B)
    FinEnum.nodup_toList FinEnum.mem_toList (w.sum n.wiring, n.loops)
  ⟨g.1.map (coupleEndpointEquiv arity label Γ B), g.2⟩

/-- Boundary attachment is represented by gluing in the unchanged ambient endpoint space. -/
theorem couple_spec [FinEnum C] [FinEnum Γ] [FinEnum B]
    (n : PortNet arity label B) (w : Wiring (Γ ⊕ B)) :
    let g := Wiring.glue (couplePorts arity label Γ B) (FinEnum.toList B) (w.sum n.wiring, n.loops)
    Wiring.Respects (coupleEmbedding arity label Γ B) (n.couple w).wiring g.1 ∧
      (n.couple w).loops = g.2 := by
  simp only [couple, Wiring.gluedFinite_eq]
  constructor
  · exact (Wiring.respects_map_symm (coupleEndpointEquiv arity label Γ B) _).trans
      (Wiring.respects_glued _ _ FinEnum.nodup_toList FinEnum.mem_toList _)
  · rfl

end PortNet

namespace TermFragment

variable {α ν I R L : Type} {arity : α → ℕ}

/-- The named leaves of a family, ordered first by root and then by occurrence. -/
def forestOrder (order : List I) (f : I → TermFragment arity ν) :
    List (Σ i, (f i).Leaf) := order.flatMap fun i ↦ (f i).order.map (Sigma.mk i)

/-- Distinct roots and distinct leaves give distinct forest occurrences. -/
theorem forestOrder_unique (order : List I) (unique : order.Nodup)
    (f : I → TermFragment arity ν) : (forestOrder order f).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    exact (f i).unique.map (fun _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · apply unique.imp
    intro i j hij x hx y hy hxy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hy
    exact hij (congrArg Sigma.fst hxy)

/-- A complete root enumeration exposes every forest leaf. -/
theorem forestOrder_cover (order : List I) (cover : ∀ i, i ∈ order)
    (f : I → TermFragment arity ν) (p : Σ i, (f i).Leaf) : p ∈ forestOrder order f :=
  List.mem_flatMap.mpr ⟨p.1, cover p.1,
    List.mem_map.mpr ⟨p.2, (f p.1).cover p.2, rfl⟩⟩

/-- Forgetting occurrence positions concatenates the fragments' name lists. -/
theorem forestOrder_names (order : List I) (f : I → TermFragment arity ν) :
    (forestOrder order f).map (fun p ↦ (f p.1).name p.2) =
      order.flatMap (fun i ↦ (f i).names) := by
  simp only [forestOrder, List.map_flatMap, List.map_map, Function.comp_def, names]

/-- Root and leaf matchings together have the interface needed to attach the forest. -/
def assemblyBoundaryEquiv (f : I → TermFragment arity ν) :
    (R ⊕ I) ⊕ (L ⊕ (Σ i, (f i).Leaf)) ≃
      (R ⊕ L) ⊕ (Σ i, Unit ⊕ (f i).Leaf) where
  toFun p := match p with
    | .inl (.inl r) => .inl (.inl r)
    | .inl (.inr i) => .inr ⟨i, .inl ()⟩
    | .inr (.inl l) => .inl (.inr l)
    | .inr (.inr ⟨i, p⟩) => .inr ⟨i, .inr p⟩
  invFun p := match p with
    | .inl (.inl r) => .inl (.inl r)
    | .inl (.inr l) => .inr (.inl l)
    | .inr ⟨i, .inl _⟩ => .inl (.inr i)
    | .inr ⟨i, .inr p⟩ => .inr (.inr ⟨i, p⟩)
  left_inv p := by rcases p with (r | i) | (l | ⟨i, p⟩) <;> rfl
  right_inv p := by rcases p with (r | l) | ⟨i, u | p⟩ <;> rfl

/-- Join all fragment roots and named occurrences, preserving any resulting closed wires. -/
def assemble [FinEnum I] [FinEnum R] [FinEnum L]
    (f : I → TermFragment arity ν) (roots : Wiring (R ⊕ I))
    (leaves : Wiring (L ⊕ (Σ i, (f i).Leaf))) :
    PortNet arity (fun c : Σ i, (f i).Cell ↦ (f c.1).label c.2) (R ⊕ L) :=
  let := sigmaEnum (C := fun i ↦ (f i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (f i).Leaf)
  (PortNet.sigma (fun i ↦ (f i).net)).couple
    ((roots.sum leaves).map (assemblyBoundaryEquiv f))

end TermFragment

end Geb.InteractionNet

end
