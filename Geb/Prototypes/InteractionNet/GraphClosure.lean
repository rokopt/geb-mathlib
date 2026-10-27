/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleGraph
public import Geb.Prototypes.InteractionNet.ConfigGraph
public import Geb.Prototypes.InteractionNet.Preservation
public import Geb.Prototypes.InteractionNet.Allocation
public import Geb.Prototypes.InteractionNet.FiniteSum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Closed-wire preservation in the textual calculus

The finite graph interpretation needs both ends of every used wire. Linear interactions
preserve existing occurrences and allocate two occurrences of each fresh name. Successful
wire elimination removes both occurrences of its eliminated name. Consequently every
configuration reached from a closed, well-formed input remains eligible for graph assembly.

## Main statements

* {lit}`Config.eliminate_closed` — wire elimination preserves closure.
* {lit}`Rule.fire_closed` — a linear interaction preserves closure.
* {lit}`System.run_closed` — every finite textual execution remains graph-representable.

## Tags

interaction net, wire, closure, preservation, compiler, graph
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α : Type} {arity : α → ℕ}

namespace Config

/-- Reversing an equation preserves the two-ended wire condition. -/
theorem closed_swap (e : Equation arity ℕ) (c : Config arity)
    (h : ({ c with equations := e :: c.equations } : Config arity).Closed) :
    ({ c with equations := (e.2, e.1) :: c.equations } : Config arity).Closed := by
  intro x hx
  have hm : x ∈ ({ c with equations := e :: c.equations } : Config arity).names := by
    simpa only [names, List.flatMap_cons, List.mem_append, or_assoc, or_left_comm] using hx
  have hc := h x hm
  simp only [names, List.flatMap_cons, List.count_append] at hc ⊢
  omega

/-- Reordering equations preserves closure. -/
theorem closed_perm (c : Config arity) (es : List (Equation arity ℕ))
    (hp : es.Perm c.equations) (hc : c.Closed) :
    ({ c with equations := es } : Config arity).Closed := by
  have hn : ({ c with equations := es } : Config arity).names.Perm c.names :=
    (List.Perm.refl _).append (hp.flatMap_right _)
  exact fun x hx ↦ (hn.count_eq x).trans (hc x (hn.mem_iff.mp hx))

/-- Eliminating a wire removes both of its ends and preserves all other names' counts. -/
theorem eliminate_closed (c d : Config arity) (x : ℕ) (t : Term arity ℕ)
    (hc : ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).Closed)
    (h : c.eliminate x t = some d) : d.Closed := by
  unfold eliminate at h
  split at h
  · rename_i hw
    obtain ⟨hnt, hcount⟩ := hw
    cases Option.some.inj h
    intro y hy
    have hp := List.count_pos_iff.mpr hy
    rw [subst_count, hcount, Nat.one_mul] at hp ⊢
    by_cases hyx : y = x
    · subst y
      simp only [List.count_eq_zero_of_not_mem hnt, ↓reduceIte, Nat.add_zero] at hp
      exact (Nat.not_lt_zero _ hp).elim
    · have he :
          ({ c with equations := (Term.var x, t) :: c.equations } : Config arity).names.count y =
            t.names.count y + c.names.count y := by
        simp only [names, List.flatMap_cons, Term.names_var, List.count_append,
          List.count_singleton, beq_iff_eq, Ne.symm hyx, ↓reduceIte, Nat.zero_add]
        omega
      have hm : y ∈ ({ c with equations := (Term.var x, t) :: c.equations } :
          Config arity).names := by
        apply List.count_pos_iff.mp
        rw [he]
        simpa only [hyx, ↓reduceIte] using hp
      simpa only [hyx, ↓reduceIte, he] using hc y hm
  · cases h

end Config

namespace Rule

/-- Each fresh name is allocated once or not at all, and contributes two ends when allocated. -/
theorem fresh_count_zero_or_two {a b : α} (r : Rule arity a b) (next z : ℕ) :
    (finSum fun k ↦ if r.allocated next k = z then 2 else 0) = 0 ∨
      (finSum fun k ↦ if r.allocated next k = z then 2 else 0) = 2 := by
  by_cases hz : next ≤ z ∧ z < next + r.fresh
  · let k : Fin r.fresh := ⟨z - next, by omega⟩
    have hk : r.allocated next k = z := by dsimp [allocated, k]; omega
    right
    rw [← hk]
    simp [(r.allocated_injective next).eq_iff]
  · left
    have hn : ∀ k, r.allocated next k ≠ z := by
      intro k hk
      apply hz
      rw [← hk]
      exact ⟨Nat.le_add_right _ _, r.allocated_lt next k⟩
    simp [hn]

/-- A well-formed linear interaction preserves both ends of every used wire. -/
theorem fire_closed {a b : α} (r : Rule arity a b) (linear : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (c : Config arity)
    (hw : ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).WellFormed)
    (hc : ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).Closed) : (r.fire xs ys c).Closed := by
  intro z hz
  have hp := List.count_pos_iff.mpr hz
  have hbound := (r.interaction_wellFormed linear xs ys c hw).1 z
  have he := r.fire_count linear xs ys c z
  rcases hc.count z with h | h <;>
    rcases r.fresh_count_zero_or_two c.nextName z with hf | hf <;> omega

end Rule

namespace System

/-- Any permitted textual contraction preserves closure. -/
theorem contract_closed (s : System arity) (linear : s.Linear)
    (e : Equation arity ℕ) (c d : Config arity)
    (hw : ({ c with equations := e :: c.equations } : Config arity).WellFormed)
    (hc : ({ c with equations := e :: c.equations } : Config arity).Closed)
    (h : s.contract e c = some d) : d.Closed := by
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
        exact c.eliminate_closed d y (Term.var x) (c.closed_swap _ hc) h
      | some v =>
        simp only [he, Option.orElse_some, Option.some.injEq] at h
        subst v
        exact c.eliminate_closed d x (Term.var y) hc he
    | liftBind b ys => exact c.eliminate_closed d x (.agent b ys) hc h
  | liftBind a xs =>
    cases u with
    | pure y => exact c.eliminate_closed d y (.agent a xs) (c.closed_swap _ hc) h
    | liftBind b ys =>
      change (match s.rule a b with
        | some r => some (r.fire xs ys c)
        | none => (s.rule b a).map (fun r ↦ r.fire ys xs c)) = some d at h
      cases hr : s.rule a b with
      | some r =>
        simp only [hr, Option.some.injEq] at h
        subst d
        exact r.fire_closed (linear a b r hr) xs ys c hw hc
      | none =>
        simp only [hr, Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        exact r.fire_closed (linear b a r hr) ys xs c (c.wellFormed_swap _ hw)
          (c.closed_swap _ hc)

/-- Selecting a reducible equation preserves the closure condition of graph assembly. -/
theorem step_closed (s : System arity) (linear : s.Linear) (c d : Config arity)
    (hw : c.WellFormed) (hc : c.Closed) (h : s.step c = some d) : d.Closed := by
  obtain ⟨⟨e, i⟩, hm, hr⟩ := List.exists_of_findSome?_eq_some h
  have hi : c.equations[i]? = some e := List.mk_mem_zipIdx_iff_getElem?.mp hm
  have he : c.equations.take i ++ e :: c.equations.drop (i + 1) = c.equations := by
    have hd := List.take_append_drop i c.equations
    rw [List.drop_eq_getElem?_toList_append, hi] at hd
    exact hd
  have hp := List.perm_middle.symm.trans (List.Perm.of_eq he)
  apply s.contract_closed linear e _ d _ _ hr
  · exact c.wellFormed_perm _ hp hw
  · exact c.closed_perm _ hp hc

/-- Every finite textual execution from a closed well-formed input remains graph-representable. -/
theorem run_closed (s : System arity) (linear : s.Linear) (c : Config arity)
    (hw : c.WellFormed) (hc : c.Closed) (n : ℕ) : (s.run n c).Closed := by
  apply Nat.rec (motive := fun n ↦ (s.run n c).Closed) hc (fun n ih ↦ ?_) n
  change ((s.step (s.run n c)).getD (s.run n c)).Closed
  cases h : s.step (s.run n c) with
  | none => exact ih
  | some d => exact s.step_closed linear _ d (s.run_wellFormed linear c hw n) ih h

end System

end Geb.InteractionNet

end
