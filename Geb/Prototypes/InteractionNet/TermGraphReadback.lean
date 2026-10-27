/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraph
public import Geb.Prototypes.InteractionNet.GraphReadback
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Constructor traversal inside term graphs

A child's root is attached to its parent's corresponding auxiliary port. Traversal inside
the child therefore agrees with traversal inside the assembled parent, with the recorded
cell positions embedded into that child's region. This correspondence holds at every fuel
bound and also preserves failed observations of variables or insufficient fuel.

## Main statements

* {lit}`TermFragment.agent_readTree_child` — attaching a parent preserves child traversal.

## Tags

interaction net, term, graph, read-back, constructor, traversal
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.TermFragment

variable {α ν : Type} {arity : α → ℕ}

/-- Parent attachment embeds a child's traversal and every cell recorded by that traversal. -/
theorem agent_readTree_child (tag : α → Option ℕ) (a : α)
    (f : Fin (arity a) → TermFragment arity ν) (i : Fin (arity a)) (fuel : ℕ)
    (p : Endpoint arity (f i).label (Unit ⊕ (f i).Leaf)) :
    (agent a f).net.readTree tag fuel (agentEndpointEquiv a f (.inr ⟨i, p⟩)) =
      ((f i).net.readTree tag fuel p).map
        (fun r ↦ (r.1, r.2.map (fun c ↦ Sum.inr (⟨i, c⟩ : Σ i, (f i).Cell)))) := by
  let n : PortNet arity (agentLabel a f) (Unit ⊕ (Σ i, (f i).Leaf)) := (agent a f).net
  change n.readTree tag fuel (agentEndpointEquiv a f (.inr ⟨i, p⟩)) = _
  refine Nat.rec (motive := fun fuel ↦ ∀ p,
    n.readTree tag fuel (agentEndpointEquiv a f (.inr ⟨i, p⟩)) =
      ((f i).net.readTree tag fuel p).map
        (fun r ↦ (r.1, r.2.map (fun c ↦ Sum.inr (⟨i, c⟩ : Σ i, (f i).Cell)))))
    (fun _ ↦ rfl) (fun fuel ih p ↦ ?_) fuel p
  have hp := Wiring.map_partner (agentEndpointEquiv a f)
    (rootWire.sum (Wiring.sigma fun i ↦ (f i).net.wiring)) (.inr ⟨i, p⟩)
  change n.wiring.partner (agentEndpointEquiv a f (.inr ⟨i, p⟩)) =
    agentEndpointEquiv a f (.inr ⟨i, (f i).net.wiring.partner p⟩) at hp
  conv_lhs => unfold PortNet.readTree; dsimp only
  rw [hp]
  cases hw : (f i).net.wiring.partner p with
  | inl b =>
    rcases b with u | b
    · simp [agentEndpointEquiv, PortNet.readTree, hw]
    · simp only [PortNet.readTree, hw]
      rfl
  | inr cp =>
    rcases cp with ⟨c, q⟩
    change (if q.val = 0 then
      PortNet.readNode (C := Unit ⊕ (Σ i, (f i).Cell)) tag ((f i).label c) (.inr ⟨i, c⟩)
        (fun j ↦ n.readTree tag fuel (.inr ⟨.inr ⟨i, c⟩, j.succ⟩)) else none) = _
    have hr : (f i).net.readTree tag (fuel + 1) p =
        if q.val = 0 then PortNet.readNode tag ((f i).label c) c
          (fun j ↦ (f i).net.readTree tag fuel (.inr ⟨c, j.succ⟩)) else none := by
      simp only [PortNet.readTree, hw]
    rw [hr]
    by_cases hq : q.val = 0
    · simp only [hq, ↓reduceIte]
      have hc (j : Fin (arity ((f i).label c))) := ih (.inr ⟨c, j.succ⟩)
      change ∀ j : Fin (arity ((f i).label c)),
        n.readTree tag fuel (.inr ⟨.inr ⟨i, c⟩, j.succ⟩) = _ at hc
      simp only [hc]
      exact PortNet.readNode_map tag ((f i).label c) c
        (fun c ↦ Sum.inr (⟨i, c⟩ : Σ i, (f i).Cell)) _
    · simp only [hq, ↓reduceIte, Option.map_none]

/-- Reading the parent root reads its children at their ordered auxiliary attachments. -/
theorem agent_readTree_root (tag : α → Option ℕ) (a : α)
    (f : Fin (arity a) → TermFragment arity ν) (fuel : ℕ) :
    (agent a f).net.readTree tag (fuel + 1) (.inl (.inl ())) =
      PortNet.readNode (C := Unit ⊕ (Σ i, (f i).Cell)) tag a (.inl ())
        (fun i ↦ ((f i).net.readTree tag fuel (.inl (.inl ()))).map
          (fun r ↦ (r.1, r.2.map (fun c ↦ Sum.inr (⟨i, c⟩ : Σ i, (f i).Cell))))) := by
  calc
    _ = PortNet.readNode (C := Unit ⊕ (Σ i, (f i).Cell)) tag a (.inl ())
        (fun i ↦ (agent a f).net.readTree tag fuel (.inr ⟨.inl (), i.succ⟩)) := rfl
    _ = _ := congrArg (PortNet.readNode tag a (Sum.inl ()))
      (funext fun i ↦ agent_readTree_child tag a f i fuel (.inl (.inl ())))

end Geb.InteractionNet.TermFragment

end
