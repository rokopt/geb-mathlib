/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.ConfigGraphIso
public import Geb.Prototypes.InteractionNet.ConfigGraphPermutation
public import Geb.Prototypes.InteractionNet.CouplingWires
public import Geb.Prototypes.InteractionNet.GraphConfluence
public import Geb.Prototypes.InteractionNet.RuleGraph
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Textual agent equations expose graph redexes

An equation between two agents connects their root boundaries. Assembling the configuration
therefore joins their principal ports, independently of the auxiliary terms and other
equations. A rule for those agents selects an actual redex in the compiled graph. Finite
indexing preserves the redex and its selected replacement.

This is the progress part of the interaction simulation: a successful textual interaction
selects a graph contraction, independently of the identification of its result.

## Main statements

* {lit}`Config.occurrenceNet_head_active` — a textual head pair is graph-active.
* {lit}`Config.headRedex` — rule lookup selects the corresponding indexed graph redex.
* {lit}`System.graph_step_of_head_rule` — a textual interaction exposes a graph step.
* {lit}`System.graph_step_of_rule_mem` — equation order does not prevent this graph progress.
* {lit}`System.graph_step_of_contract_mem` — either orientation selected by the textual
  reducer exposes graph progress.

## Tags

interaction net, compiler, graph, active pair, interaction, progress
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

namespace Config

/-- A head equation between agents becomes a wire between their principal ports. -/
theorem occurrenceNet_head_active (c : Config arity) (a b : α)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    let d : Config arity :=
      { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
    ∀ closed : d.Closed, (d.occurrenceNet closed).Active
      ⟨.inr (.inl (0 : Fin (c.equations.length + 1))), .inl ()⟩
      ⟨.inr (.inr (0 : Fin (c.equations.length + 1))), .inl ()⟩ := by
  intro d closed
  let f := d.graphFragments
  let := sigmaEnum (C := fun i ↦ (f i).Cell)
  let := sigmaEnum (C := fun i ↦ Unit ⊕ (f i).Leaf)
  let n := PortNet.sigma (fun i ↦ (f i).net)
  let leaves := (d.graphLeafWiring closed).map (PortNet.emptyCellEquiv _).symm
  let w := (d.graphRootWiring.sum leaves).map (TermFragment.assemblyBoundaryEquiv f)
  let l : d.GraphCell := ⟨.inr (.inl (0 : Fin (c.equations.length + 1))), .inl ()⟩
  let r : d.GraphCell := ⟨.inr (.inr (0 : Fin (c.equations.length + 1))), .inl ()⟩
  have hl : n.wiring.partner (PortNet.principal arity d.graphLabel l) =
      .inl ⟨.inr (.inl (0 : Fin (c.equations.length + 1))), .inl ()⟩ := rfl
  have hr : n.wiring.partner (PortNet.principal arity d.graphLabel r) =
      .inl ⟨.inr (.inr (0 : Fin (c.equations.length + 1))), .inl ()⟩ := rfl
  have hw : w.partner (.inr ⟨.inr (.inl (0 : Fin (c.equations.length + 1))), .inl ()⟩) =
      .inr ⟨.inr (.inr (0 : Fin (c.equations.length + 1))), .inl ()⟩ := rfl
  have h := n.couple_boundary_wire w ⟨l, 0⟩ ⟨r, 0⟩ _ _ hl hr hw
  exact ((n.couple w).reboundary_active_iff d.graphBoundaryEquiv l r).mpr h

/-- Select the compiled redex of a head agent equation using the corresponding graph rule. -/
def headRedex (s : PortSystem arity) (c : Config arity) (a b : α)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (rhs : PortRule arity a b) (rule : s.rule a b = some rhs) :
    let d : Config arity :=
      { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
    (closed : d.Closed) → s.Redex (d.toFiniteNet closed).2.2 := by
  intro d closed
  let r : s.Redex (d.occurrenceNet closed) :=
    { left := ⟨.inr (.inl (0 : Fin (c.equations.length + 1))), .inl ()⟩
      right := ⟨.inr (.inr (0 : Fin (c.equations.length + 1))), .inl ()⟩
      active := c.occurrenceNet_head_active a b xs ys closed
      rhs := rhs
      rule_eq := rule }
  exact r.map (d.occurrenceIndexedIso closed)

end Config

/-- Every selected textual head interaction has a corresponding step of the compiled graph. -/
theorem System.graph_step_of_head_rule (s : System arity) (linear : s.Linear)
    (oriented : s.Oriented) (c : Config arity) (a b : α)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (rhs : Rule arity a b) (rule : s.rule a b = some rhs) :
    let d : Config arity :=
      { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
    ∀ closed : d.Closed, ∃ m,
      Graph.Step (s.toPortSystem linear oriented) (Graph.ofNet (d.toFiniteNet closed)) m := by
  intro d closed
  let r := c.headRedex (s.toPortSystem linear oriented) a b xs ys
    (rhs.toPortRule (linear a b rhs rule)) (s.toPortSystem_rule linear oriented rule) closed
  let := r.resultEnum
  let m := FiniteNet.pack r.result
  exact ⟨Graph.ofNet m, Graph.step_of_net ⟨r, ⟨PortNet.indexedIso r.result⟩⟩⟩

/-- Any agent equation with a forward rule exposes graph progress, regardless of equation order. -/
theorem System.graph_step_of_rule_mem (s : System arity) (linear : s.Linear)
    (oriented : s.Oriented) (c : Config arity) (closed : c.Closed) (a b : α)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (rhs : Rule arity a b) (rule : s.rule a b = some rhs)
    (mem : (Term.agent a xs, Term.agent b ys) ∈ c.equations) :
    ∃ m, Graph.Step (s.toPortSystem linear oriented) (Graph.ofNet (c.toFiniteNet closed)) m := by
  obtain ⟨before, after, he⟩ := List.mem_iff_append.mp mem
  let rest : Config arity := { c with equations := before ++ after }
  let eqn := (Term.agent a xs, Term.agent b ys)
  have hp : (eqn :: rest.equations).Perm c.equations := by
    rw [he]
    exact List.perm_middle.symm
  have hc := c.closed_perm (eqn :: rest.equations) hp closed
  obtain ⟨m, hm⟩ := s.graph_step_of_head_rule linear oriented rest a b xs ys rhs rule hc
  obtain ⟨e⟩ := c.toFiniteNet_perm (eqn :: rest.equations) hp closed
  have hg : Graph.ofNet (c.toFiniteNet closed) =
      Graph.ofNet (({ rest with equations := eqn :: rest.equations } : Config arity).toFiniteNet
        hc) := Quotient.sound ⟨e⟩
  exact ⟨m, hg ▸ hm⟩

/-- A reverse rule exposes the same graph progress after exchanging the head equation's sides. -/
theorem System.graph_step_of_head_reverse_rule (s : System arity) (linear : s.Linear)
    (oriented : s.Oriented) (c : Config arity) (a b : α)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (rhs : Rule arity b a) (rule : s.rule b a = some rhs) :
    let d : Config arity :=
      { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
    ∀ closed : d.Closed, ∃ m,
      Graph.Step (s.toPortSystem linear oriented) (Graph.ofNet (d.toFiniteNet closed)) m := by
  intro d closed
  let eqn := (Term.agent a xs, Term.agent b ys)
  let d' : Config arity := { c with equations := (eqn.2, eqn.1) :: c.equations }
  have hc := c.closed_swap eqn closed
  obtain ⟨m, hm⟩ := s.graph_step_of_head_rule linear oriented c b a ys xs rhs rule hc
  have hg : Graph.ofNet (d.toFiniteNet closed) =
      Graph.ofNet (d'.toFiniteNet hc) := Quotient.sound ⟨c.swapGraphIso eqn closed⟩
  exact ⟨m, hg ▸ hm⟩

/-- Every successful textual agent contraction exposes a graph step, in either orientation. -/
theorem System.graph_step_of_contract_mem (s : System arity) (linear : s.Linear)
    (oriented : s.Oriented) (c : Config arity) (closed : c.Closed) (a b : α)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (rest result : Config arity)
    (contract : s.contract (Term.agent a xs, Term.agent b ys) rest = some result)
    (mem : (Term.agent a xs, Term.agent b ys) ∈ c.equations) :
    ∃ m, Graph.Step (s.toPortSystem linear oriented) (Graph.ofNet (c.toFiniteNet closed)) m := by
  cases hf : s.rule a b with
  | some rhs => exact s.graph_step_of_rule_mem linear oriented c closed a b xs ys rhs hf mem
  | none =>
    cases hr : s.rule b a with
    | none =>
      change (match s.rule a b with
        | some r => some { rest with
            equations := r.instantiate rest.nextName xs ys ++ rest.equations
            nextName := rest.nextName + r.fresh }
        | none => (s.rule b a).map fun r ↦ { rest with
            equations := r.instantiate rest.nextName ys xs ++ rest.equations
            nextName := rest.nextName + r.fresh }) = some result at contract
      simp only [hf, hr, Option.map_none, reduceCtorEq] at contract
    | some rhs =>
      obtain ⟨before, after, he⟩ := List.mem_iff_append.mp mem
      let tail : Config arity := { c with equations := before ++ after }
      let eqn := (Term.agent a xs, Term.agent b ys)
      have hp : (eqn :: tail.equations).Perm c.equations := by
        rw [he]
        exact List.perm_middle.symm
      have hc := c.closed_perm (eqn :: tail.equations) hp closed
      obtain ⟨m, hm⟩ := s.graph_step_of_head_reverse_rule linear oriented tail a b xs ys rhs hr hc
      obtain ⟨e⟩ := c.toFiniteNet_perm (eqn :: tail.equations) hp closed
      have hg : Graph.ofNet (c.toFiniteNet closed) =
          Graph.ofNet (({ tail with equations := eqn :: tail.equations } : Config arity).toFiniteNet
            hc) := Quotient.sound ⟨e⟩
      exact ⟨m, hg ▸ hm⟩

end Geb.InteractionNet

end
