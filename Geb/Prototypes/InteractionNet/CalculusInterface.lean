/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Calculus
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Textual execution preserves the ordered interface size

Substitution may change the terms at the external interface, but it keeps their positions.
Every textual reduction and every finite execution therefore has the same boundary size.
This lets a complete textual execution be compared in one type of port graphs.

## Main statements

* {lit}`System.step_interface_length` — one reduction retains the interface size.
* {lit}`System.run_interface_length` — every finite run retains that size.

## Tags

interaction net, calculus, execution, interface, boundary
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ}

/-- Wire elimination substitutes interface terms without adding or removing interface positions. -/
theorem Config.eliminate_interface_length (c d : Config arity) (x : ℕ) (t : Term arity ℕ)
    (h : c.eliminate x t = some d) : d.interface.length = c.interface.length := by
  unfold Config.eliminate at h
  split at h
  · cases Option.some.inj h
    exact List.length_map ..
  · cases h

/-- Every permitted equation contraction retains the positions of the external interface. -/
theorem System.contract_interface_length (s : System arity) (e : Equation arity ℕ)
    (c d : Config arity) (h : s.contract e c = some d) :
    d.interface.length = c.interface.length := by
  obtain ⟨t, u⟩ := e
  cases t with
  | pure x =>
    cases u with
    | pure y =>
      change (c.eliminate x (Term.var y)).orElse (fun _ ↦ c.eliminate y (Term.var x)) =
        some d at h
      cases he : c.eliminate x (Term.var y) with
      | none =>
        simp only [he, Option.orElse_none] at h
        exact c.eliminate_interface_length d y (Term.var x) h
      | some v =>
        simp only [he, Option.orElse_some, Option.some.injEq] at h
        subst v
        exact c.eliminate_interface_length d x (Term.var y) he
    | liftBind b ys => exact c.eliminate_interface_length d x (.agent b ys) h
  | liftBind a xs =>
    cases u with
    | pure y => exact c.eliminate_interface_length d y (.agent a xs) h
    | liftBind b ys =>
      change (match s.rule a b with
        | some r => some { c with
            equations := r.instantiate c.nextName xs ys ++ c.equations
            nextName := c.nextName + r.fresh }
        | none => (s.rule b a).map fun r ↦
          { c with
            equations := r.instantiate c.nextName ys xs ++ c.equations
            nextName := c.nextName + r.fresh }) = some d at h
      cases hr : s.rule a b with
      | some r =>
        simp only [hr, Option.some.injEq] at h
        subst d
        rfl
      | none =>
        simp only [hr, Option.map_eq_some_iff] at h
        obtain ⟨r, _, rfl⟩ := h
        rfl

/-- Selecting any reducible equation preserves the size of the external interface. -/
theorem System.step_interface_length (s : System arity) (c d : Config arity)
    (h : s.step c = some d) : d.interface.length = c.interface.length := by
  obtain ⟨⟨e, i⟩, _, hr⟩ := List.exists_of_findSome?_eq_some h
  exact s.contract_interface_length e
    { c with equations := c.equations.take i ++ c.equations.drop (i + 1) } d hr

/-- Every finite textual execution stays at the input's fixed ordered boundary size. -/
theorem System.run_interface_length (s : System arity) (c : Config arity) (n : ℕ) :
    (s.run n c).interface.length = c.interface.length := by
  refine Nat.rec (motive := fun n ↦ (s.run n c).interface.length = c.interface.length)
    rfl (fun n ih ↦ ?_) n
  change ((s.step (s.run n c)).getD (s.run n c)).interface.length = _
  cases h : s.step (s.run n c) with
  | none => exact ih
  | some d => exact (s.step_interface_length _ d h).trans ih

end Geb.InteractionNet

end
