/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphAssembly
public import Geb.Prototypes.InteractionNet.WiringSubdivision
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Attaching replacement graphs at term leaves

Graph substitution attaches one replacement root at each exposed leaf occurrence. Every
old cell and every replacement cell survives; the old leaves and replacement roots are
removed. The new boundary consists of the original root and all replacement leaves.
Assembly uses finite partner arrays and retains closed wire components.

## Main definitions

* {lit}`TermFragment.attach` — attach a family of replacement fragments at the old leaves.
* {lit}`TermFragment.attachmentEmbedding` — locate the result in the allocated endpoint space.

## Main statements

* {lit}`TermFragment.attach_spec` — attachment represents exactly the specified wire splices.

## Tags

interaction net, graph, substitution, attachment, occurrence, gluing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.TermFragment

open scoped FinEnum

variable {α ν μ : Type} {arity : α → ℕ}

/-- The original fragment's endpoints and all replacement endpoints before attachment. -/
abbrev AttachmentEndpoint (f : TermFragment arity ν)
    (g : f.Leaf → TermFragment arity μ) :=
  Endpoint arity f.label (Unit ⊕ f.Leaf) ⊕
    (Σ p, Endpoint arity (g p).label (Unit ⊕ (g p).Leaf))

/-- Structural equality of attachment endpoints uses the fragments' supplied finite indices. -/
@[instance_reducible] def attachmentDecidableEq (f : TermFragment arity ν)
    (g : f.Leaf → TermFragment arity μ) : DecidableEq (AttachmentEndpoint f g) :=
  let : DecidableEq f.Cell := f.cellEnum.decEq
  let : DecidableEq f.Leaf := f.leafEnum.decEq
  let _ (p : f.Leaf) : DecidableEq (g p).Cell := (g p).cellEnum.decEq
  let _ (p : f.Leaf) : DecidableEq (g p).Leaf := (g p).leafEnum.decEq
  inferInstanceAs (DecidableEq (Endpoint arity f.label (Unit ⊕ f.Leaf) ⊕
    (Σ p, Endpoint arity (g p).label (Unit ⊕ (g p).Leaf))))

/-- Each old leaf is paired with the corresponding replacement's root. -/
def attachmentPorts (f : TermFragment arity ν) (g : f.Leaf → TermFragment arity μ) :
    f.Leaf × Bool ↪ AttachmentEndpoint f g where
  toFun p := if p.2 then .inr ⟨p.1, .inl (.inl ())⟩ else .inl (.inl (.inr p.1))
  inj' := by
    rintro ⟨p, b⟩ ⟨q, c⟩ h
    cases b <;> cases c
    · exact Prod.ext (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h))) rfl
    · cases h
    · cases h
    · exact Prod.ext (congrArg Sigma.fst (Sum.inr.inj h)) rfl

/-- Original and occurrence-indexed replacement cells retain their symbols. -/
def attachmentLabel (f : TermFragment arity ν) (g : f.Leaf → TermFragment arity μ) :
    f.Cell ⊕ (Σ p, (g p).Cell) → α :=
  Sum.elim f.label (fun c ↦ (g c.1).label c.2)

/-- The surviving endpoint positions after every leaf-to-root splice. -/
def attachmentEndpointEquiv (f : TermFragment arity ν)
    (g : f.Leaf → TermFragment arity μ) :
    {p : AttachmentEndpoint f g // ∀ i b, p ≠ attachmentPorts f g (i, b)} ≃
      Endpoint arity (attachmentLabel f g) (Unit ⊕ (Σ i, (g i).Leaf)) where
  toFun p := match p with
    | ⟨.inl (.inl (.inl u)), _⟩ => .inl (.inl u)
    | ⟨.inl (.inl (.inr i)), h⟩ => (h i false rfl).elim
    | ⟨.inl (.inr ⟨c, p⟩), _⟩ => .inr ⟨.inl c, p⟩
    | ⟨.inr ⟨i, .inl (.inl _)⟩, h⟩ => (h i true rfl).elim
    | ⟨.inr ⟨i, .inl (.inr p)⟩, _⟩ => .inl (.inr ⟨i, p⟩)
    | ⟨.inr ⟨i, .inr ⟨c, p⟩⟩, _⟩ => .inr ⟨.inr ⟨i, c⟩, p⟩
  invFun p := match p with
    | .inl (.inl u) => ⟨.inl (.inl (.inl u)), by
        intro i b; cases b <;> intro h <;> cases h⟩
    | .inl (.inr ⟨i, p⟩) => ⟨.inr ⟨i, .inl (.inr p)⟩, by
        intro j b; cases b <;> intro h
        · cases h
        · cases Sum.inr.inj h⟩
    | .inr ⟨.inl c, p⟩ => ⟨.inl (.inr ⟨c, p⟩), by
        intro i b; cases b <;> intro h <;> cases h⟩
    | .inr ⟨.inr ⟨i, c⟩, p⟩ => ⟨.inr ⟨i, .inr ⟨c, p⟩⟩, by
        intro j b; cases b <;> intro h
        · cases h
        · cases Sum.inr.inj h⟩
  left_inv p := match p with
    | ⟨.inl (.inl (.inl _)), _⟩ => rfl
    | ⟨.inl (.inl (.inr i)), h⟩ => (h i false rfl).elim
    | ⟨.inl (.inr _), _⟩ => rfl
    | ⟨.inr ⟨i, .inl (.inl _)⟩, h⟩ => (h i true rfl).elim
    | ⟨.inr ⟨_, .inl (.inr _)⟩, _⟩ => rfl
    | ⟨.inr ⟨_, .inr _⟩, _⟩ => rfl
  right_inv p := by rcases p with (u | ⟨i, p⟩) | ⟨c | ⟨i, c⟩, p⟩ <;> rfl

/-- Locate the attached fragment's endpoints before the old leaf and new root are removed. -/
def attachmentEmbedding (f : TermFragment arity ν) (g : f.Leaf → TermFragment arity μ) :
    Endpoint arity (attachmentLabel f g) (Unit ⊕ (Σ i, (g i).Leaf)) ↪
      AttachmentEndpoint f g :=
  (attachmentEndpointEquiv f g).symm.toEmbedding.trans (.subtype _)

/-- Allocate the original and replacement matchings with their existing closed-wire count. -/
def attachmentState (f : TermFragment arity ν) (g : f.Leaf → TermFragment arity μ) :
    Wiring (AttachmentEndpoint f g) × ℕ :=
  (f.net.wiring.sum (Wiring.sigma fun i ↦ (g i).net.wiring),
    f.net.loops + (f.order.map fun i ↦ (g i).net.loops).sum)

/-- Attach one replacement at each leaf occurrence, retaining all cells and closed wires. -/
def attach (f : TermFragment arity ν) (g : f.Leaf → TermFragment arity μ) :
    TermFragment arity μ :=
  let := sigmaEnum (C := fun i ↦ (g i).Cell)
  let := sigmaEnum (C := fun i ↦ (g i).Leaf)
  let dec : DecidableEq (AttachmentEndpoint f g) := attachmentDecidableEq f g
  let := sigmaEnum (C := fun c ↦ Fin (arity (f.label c) + 1))
  let _ (i : f.Leaf) : FinEnum (CellPort arity (g i).label) := sigmaEnum
  let := sigmaEnum (C := fun i ↦ Endpoint arity (g i).label (Unit ⊕ (g i).Leaf))
  let : DecidableEq (AttachmentEndpoint f g) := dec
  let w := Wiring.gluedFinite (attachmentPorts f g) f.order f.unique f.cover
    (attachmentState f g)
  { Cell := f.Cell ⊕ (Σ i, (g i).Cell)
    cellEnum := inferInstance
    Leaf := Σ i, (g i).Leaf
    leafEnum := inferInstance
    label := attachmentLabel f g
    name p := (g p.1).name p.2
    order := forestOrder f.order g
    unique := forestOrder_unique f.order f.unique g
    cover := forestOrder_cover f.order f.cover g
    net := ⟨w.1.map (attachmentEndpointEquiv f g), w.2⟩ }

/-- Graph attachment embeds in the matching obtained by splicing every old leaf to its new root. -/
theorem attach_spec (f : TermFragment arity ν) (g : f.Leaf → TermFragment arity μ) :
    let : DecidableEq (AttachmentEndpoint f g) := attachmentDecidableEq f g
    let w := Wiring.glue (attachmentPorts f g) f.order (attachmentState f g)
    Wiring.Respects (attachmentEmbedding f g) (f.attach g).net.wiring w.1 ∧
      (f.attach g).net.loops = w.2 := by
  dsimp only
  let : DecidableEq (AttachmentEndpoint f g) := attachmentDecidableEq f g
  simp only [attach, Wiring.gluedFinite_eq]
  exact ⟨(Wiring.respects_map_symm (attachmentEndpointEquiv f g) _).trans
    (Wiring.respects_glued _ _ f.unique f.cover _), rfl⟩

/-- Attaching each replacement at just its root introduces no additional closed wire. -/
theorem attach_loops (f : TermFragment arity ν) (g : f.Leaf → TermFragment arity μ) :
    (f.attach g).net.loops = f.net.loops + (f.order.map fun i ↦ (g i).net.loops).sum := by
  let : DecidableEq (AttachmentEndpoint f g) := attachmentDecidableEq f g
  apply (f.attach_spec g).2.trans
  apply Wiring.glue_loops_of_free_right _ _ f.unique
  intro i _ j _ b
  cases b with
  | false => intro h; cases h
  | true =>
    intro h
    have hs : (⟨i, (g i).net.wiring.partner (.inl (.inl ()))⟩ :
        Σ i, Endpoint arity (g i).label (Unit ⊕ (g i).Leaf)) =
          ⟨j, .inl (.inl ())⟩ := Sum.inr.inj h
    have hij : i = j := congrArg Sigma.fst hs
    subst j
    exact (g i).net.wiring.fixedPointFree (.inl (.inl ()))
      (eq_of_heq (Sigma.mk.inj_iff.mp hs).2)

end Geb.InteractionNet.TermFragment

end
