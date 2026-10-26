/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.TermGraph
public import Geb.Prototypes.InteractionNet.ActivePair
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Principal wires in term graphs

Each principal port in a term graph meets either the term's root or a parent's auxiliary
port. It cannot meet a variable leaf or another principal port. Consequently a term graph
has no active pair, regardless of which interaction rules will later be attached to it.

## Main statements

* {lit}`Term.fragment_principal_partner` — classify every cell's principal wire.
* {lit}`Term.fragment_no_active` — a term fragment contains no active pair.

## Tags

interaction net, term, graph, principal port, auxiliary port, normal form
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Term

open TermFragment

variable {α ν : Type} {arity : α → ℕ}

/-- A term cell's principal port meets the root boundary or a parent's auxiliary port. -/
theorem fragment_principal_partner (t : Term arity ν) (c : t.fragment.Cell) :
    t.fragment.net.wiring.partner (PortNet.principal arity t.fragment.label c) = .inl (.inl ()) ∨
      ∃ d p, p.val ≠ 0 ∧
        t.fragment.net.wiring.partner (PortNet.principal arity t.fragment.label c) =
          .inr (⟨d, p⟩ : CellPort arity t.fragment.label) := by
  refine PFunctor.FreeM.rec (motive := fun t ↦ ∀ c : (fragment t).Cell,
    (fragment t).net.wiring.partner (PortNet.principal arity (fragment t).label c) =
      .inl (.inl ()) ∨ ∃ d p, p.val ≠ 0 ∧
        (fragment t).net.wiring.partner (PortNet.principal arity (fragment t).label c) =
          .inr (⟨d, p⟩ : CellPort arity (fragment t).label))
    (fun _ c ↦ Fin.elim0 c) (fun a ts ih c ↦ ?_) t c
  rcases c with u | ⟨i, c⟩
  · exact Or.inl rfl
  · have hp := Wiring.map_partner (agentEndpointEquiv a (fun i ↦ fragment (ts i)))
      (rootWire.sum (Wiring.sigma fun i ↦ (fragment (ts i)).net.wiring))
      (.inr ⟨i, PortNet.principal arity (fragment (ts i)).label c⟩)
    rcases ih i c with h | ⟨d, p, hp0, h⟩
    · refine Or.inr ⟨.inl (), i.succ, Nat.succ_ne_zero _, ?_⟩
      exact hp.trans (congrArg (fun p ↦ agentEndpointEquiv a
        (fun i ↦ fragment (ts i)) (.inr ⟨i, p⟩)) h)
    · refine Or.inr ⟨.inr ⟨i, d⟩, p, hp0, ?_⟩
      exact hp.trans (congrArg (fun p ↦ agentEndpointEquiv a
        (fun i ↦ fragment (ts i)) (.inr ⟨i, p⟩)) h)

/-- No two principal ports are connected within a term fragment. -/
theorem fragment_no_active (t : Term arity ν) (c d : t.fragment.Cell) :
    ¬t.fragment.net.Active c d := by
  intro h
  rcases t.fragment_principal_partner c with hr | ⟨e, p, hp, he⟩
  · have bad := hr.symm.trans h
    cases bad
  · have bad := he.symm.trans h
    have hv := congrArg (fun q : CellPort arity t.fragment.label ↦ q.2.val) (Sum.inr.inj bad)
    exact hp hv

end Geb.InteractionNet.Term

end
