/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.AssemblyIso
public import Geb.Prototypes.InteractionNet.ContractionCoupling
public import Geb.Prototypes.InteractionNet.GraphConfluence
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Graph reduction in boundary contexts

Attaching a boundary matching is well-defined on finite graphs modulo cell renaming.
Every contraction already enabled in the original graph remains enabled in that context,
and its result is the corresponding attachment to the contracted graph. This extends to
every finite reduction schedule. Attachment can also enable new active pairs, so it need
not preserve normal forms.

## Main definitions

* {lit}`FiniteNet.couple`, {lit}`Graph.couple` — attach a fixed finite boundary matching.

## Main statements

* {lit}`Graph.Step.couple` — every graph step is preserved in a boundary context.
* {lit}`Graph.reaches_couple` — every finite schedule is preserved in the same context.

## Tags

interaction net, graph, contraction, context, boundary, schedule
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ} {boundary outer : ℕ}

namespace FiniteNet

/-- Attach boundary wires while retaining the finite cell indices and symbols. -/
def couple (n : FiniteNet arity boundary) (w : Wiring (Fin outer ⊕ Fin boundary)) :
    FiniteNet arity outer := ⟨n.1, n.2.1, n.net.couple w⟩

/-- Attaching the same matching preserves a boundary-preserving cell isomorphism. -/
theorem Isomorphic.couple {n m : FiniteNet arity boundary} (h : n.Isomorphic m)
    (w : Wiring (Fin outer ⊕ Fin boundary)) : (n.couple w).Isomorphic (m.couple w) := by
  obtain ⟨i⟩ := h
  exact ⟨i.couple w⟩

/-- An enabled contraction remains the same contraction after attaching boundary wires. -/
theorem Step.couple {s : PortSystem arity} {n m : FiniteNet arity boundary} (h : Step s n m)
    (w : Wiring (Fin outer ⊕ Fin boundary)) : Step s (n.couple w) (m.couple w) := by
  obtain ⟨r, ⟨i⟩⟩ := h
  let r' : s.Redex (n.couple w).net :=
    { left := r.left
      right := r.right
      active := n.net.couple_active w r.active
      rhs := r.rhs
      rule_eq := r.rule_eq }
  let := r.resultEnum
  have hi := i.couple w
  have he : r.result.couple w = r'.result := n.net.contract_couple w r.active r.rhs.2.2
  rw [he] at hi
  exact ⟨r', ⟨hi⟩⟩

end FiniteNet

namespace Graph

/-- Attach a finite boundary matching independently of the graph's internal cell allocation. -/
def couple (n : Graph arity boundary) (w : Wiring (Fin outer ⊕ Fin boundary)) :
    Graph arity outer :=
  Quotient.map (fun n : FiniteNet arity boundary ↦ n.couple w)
    (fun _ _ h ↦ FiniteNet.Isomorphic.couple h w) n

/-- Boundary attachment to a graph class is represented by attachment to any finite presentation. -/
theorem couple_ofNet (n : FiniteNet arity boundary) (w : Wiring (Fin outer ⊕ Fin boundary)) :
    (ofNet n).couple w = ofNet (n.couple w) := rfl

/-- Attaching a fixed boundary context preserves each permitted contraction. -/
theorem Step.couple {s : PortSystem arity} {n m : Graph arity boundary} (h : Step s n m)
    (w : Wiring (Fin outer ⊕ Fin boundary)) : Step s (n.couple w) (m.couple w) := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  exact step_of_net (h.couple w)

/-- The same finite contraction schedule can be performed after attaching a boundary context. -/
theorem reaches_couple {s : PortSystem arity} {n m : Graph arity boundary}
    (h : Relation.ReflTransGen (Step s) n m) (w : Wiring (Fin outer ⊕ Fin boundary)) :
    Relation.ReflTransGen (Step s) (n.couple w) (m.couple w) := by
  exact Relation.ReflTransGen.head_induction_on h (Relation.ReflTransGen.refl)
    (fun h _ ih ↦ ih.head (h.couple w))

end Graph

end Geb.InteractionNet

end
