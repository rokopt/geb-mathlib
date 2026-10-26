/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Calculus
public import Geb.Prototypes.InteractionNet.FiniteSum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Fresh allocation in an interaction

Instantiating a linear rule preserves all old wire occurrences. It adds two occurrences
of each allocated name. The allocated names are distinct, lie above every old name, and
lie below the updated supply. Thus an interaction preserves the configuration invariant.

## Main statements

* {lit}`Rule.instantiate_count` — exact wire multiplicities after instantiation.
* {lit}`Rule.fresh_count_le` — an allocated wire contributes at most two ends.
* {lit}`Rule.interaction_wellFormed` — a linear interaction preserves well-formedness.

## Tags

interaction calculus, allocation, freshness, wire, invariant
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ}

namespace Rule

private theorem perm_cons_erase {ν : Type} [BEq ν] [LawfulBEq ν]
    (a : ν) (as : List ν) (h : a ∈ as) : as.Perm (a :: as.erase a) := by
  let : DecidableEq ν := instDecidableEqOfLawfulBEq
  apply List.rec (motive := fun as ↦ a ∈ as → as.Perm (a :: as.erase a))
    (fun h ↦ False.elim (List.not_mem_nil h)) (fun b bs ih hb ↦ ?_) as h
  by_cases hab : a = b
  · subst b
    simp only [List.erase_cons_head]
    exact List.Perm.refl _
  · have hm : a ∈ bs := (List.mem_cons.mp hb).resolve_left hab
    have hn : ¬(b == a) := by simpa only [beq_iff_eq] using Ne.symm hab
    simpa only [List.erase_cons_tail hn] using
      (List.Perm.cons b (ih hm)).trans (List.Perm.swap a b (bs.erase a))

private theorem perm_of_count {ν : Type} [BEq ν] [LawfulBEq ν]
    (as bs : List ν) (h : ∀ x, as.count x = bs.count x) : as.Perm bs := by
  let : DecidableEq ν := instDecidableEqOfLawfulBEq
  apply List.rec (motive := fun as ↦ ∀ bs : List ν,
    (∀ x, as.count x = bs.count x) → as.Perm bs) (fun bs hb ↦ ?_)
    (fun a as ih bs hb ↦ ?_) as bs h
  · cases bs with
    | nil => exact List.Perm.nil
    | cons b bs =>
      have hn := hb b
      simp only [List.count_nil, List.count_cons_self] at hn
      exfalso
      omega
  · have hm : a ∈ bs := List.count_pos_iff.mp (by
      rw [← hb a, List.count_cons_self]
      omega)
    apply (List.Perm.cons a (ih (bs.erase a) ?_)).trans (perm_cons_erase a bs hm).symm
    intro b
    have he := hb b
    rw [(perm_cons_erase a bs hm).count_eq] at he
    by_cases hba : b = a
    · subst b
      simpa only [List.count_cons_self, Nat.add_right_cancel_iff] using he
    · simpa only [List.count_cons_of_ne (Ne.symm hba)] using he

/-- List the formal boundary names, once each. -/
def portNames {a b : α} (r : Rule arity a b) : List (Boundary arity a b ⊕ Fin r.fresh) :=
  (List.ofFn fun i : Fin (arity a) ↦ .inl (.inl i)) ++
    (List.ofFn fun j : Fin (arity b) ↦ .inl (.inr j))

/-- List the formal internal names, once each. -/
def internalNames {a b : α} (r : Rule arity a b) :
    List (Boundary arity a b ⊕ Fin r.fresh) := List.ofFn Sum.inr

/-- A linear rule's occurrence list is its boundary once and its internal wires twice. -/
theorem names_perm {a b : α} (r : Rule arity a b) (hr : r.Linear) :
    r.names.Perm (r.portNames ++ r.internalNames ++ r.internalNames) := by
  apply perm_of_count
  intro u
  cases u with
  | inl u =>
    cases u <;> simp [portNames, internalNames, hr.1, count_ofFn_eq_finSum]
  | inr u => simp [portNames, internalNames, hr.2, count_ofFn_eq_finSum]

/-- The occurrence list of an instantiated rule is the substitution of the port terms and
fresh names into its formal occurrence list. -/
theorem names_instantiate {a b : α} (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (r.instantiate next xs ys).flatMap (fun e ↦ e.1.names ++ e.2.names) =
      r.names.flatMap (fun u ↦
        (Sum.elim (Sum.elim xs ys) (fun i ↦ Term.var (r.allocated next i)) u).names) := by
  simp [instantiate, names, Term.names_subst, List.flatMap_map, List.flatMap_assoc,
    List.flatMap_append]

/-- The instantiated rule preserves the old port occurrences and adds two occurrences of
each fresh internal name. -/
theorem instantiate_count {a b : α} (r : Rule arity a b) (hr : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) (z : ℕ) :
    ((r.instantiate next xs ys).flatMap (fun e ↦ e.1.names ++ e.2.names)).count z =
      (finSum fun i ↦ (xs i).names.count z) + (finSum fun j ↦ (ys j).names.count z) +
        finSum (fun k ↦ if r.allocated next k = z then 2 else 0) := by
  rw [names_instantiate]
  rw [((r.names_perm hr).flatMap_right _).count_eq z]
  have hd : finSum (fun k ↦ if r.allocated next k = z then 2 else 0) =
      finSum (fun k ↦ if r.allocated next k = z then 1 else 0) +
        finSum (fun k ↦ if r.allocated next k = z then 1 else 0) := by
    rw [← finSum_add]
    apply congrArg finSum
    funext k
    by_cases h : r.allocated next k = z <;> simp [h]
  simp only [portNames, internalNames, List.flatMap_append, List.count_append,
    List.count_flatMap, List.map_ofFn, finSum_ofFn, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr, Term.names_var, List.count_singleton, beq_iff_eq, hd]
  omega

/-- A name is allocated at most once, and so receives at most two new occurrences. -/
theorem fresh_count_le {a b : α} (r : Rule arity a b) (next z : ℕ) :
    (finSum (fun k ↦ if r.allocated next k = z then 2 else 0)) ≤ 2 := by
  by_cases h : ∃ k, r.allocated next k = z
  · obtain ⟨k, rfl⟩ := h
    simp [(r.allocated_injective next).eq_iff]
  · have hn : ∀ k, r.allocated next k ≠ z := not_exists.mp h
    simp [hn]

/-- Names below the allocation supply receive no new occurrences. -/
theorem fresh_count_eq_zero_of_lt {a b : α} (r : Rule arity a b) {next z : ℕ}
    (h : z < next) : (finSum (fun k ↦ if r.allocated next k = z then 2 else 0)) = 0 := by
  have hn : ∀ k, r.allocated next k ≠ z := by
    intro k hk
    unfold allocated at hk
    omega
  simp [hn]

/-- Names at or above the updated supply receive no new occurrences. -/
theorem fresh_count_eq_zero_of_le {a b : α} (r : Rule arity a b) {next z : ℕ}
    (h : next + r.fresh ≤ z) : (finSum (fun k ↦ if r.allocated next k = z then 2 else 0)) = 0 := by
  have hn : ∀ k, r.allocated next k ≠ z := by
    intro k hk
    have hb := r.allocated_lt next k
    omega
  simp [hn]

/-- The configuration produced by an interaction, before selecting its next equation. -/
def fire {a b : α} (r : Rule arity a b)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (c : Config arity) : Config arity :=
  { c with equations := r.instantiate c.nextName xs ys ++ c.equations
           nextName := c.nextName + r.fresh }

/-- The exact occurrence counts before and after contracting an active pair. -/
theorem fire_count {a b : α} (r : Rule arity a b) (hr : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (c : Config arity) (z : ℕ) :
    (r.fire xs ys c).names.count z =
      ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
        Config arity).names.count z +
        finSum (fun k ↦ if r.allocated c.nextName k = z then 2 else 0) := by
  simp only [fire, Config.names, List.flatMap_append, List.flatMap_cons, Term.names_agent,
    List.count_append, r.instantiate_count hr, List.count_flatten, List.map_ofFn,
    finSum_ofFn, Function.comp_def]
  omega

/-- A linear interaction preserves the wire multiplicity and fresh-name invariants. -/
theorem interaction_wellFormed {a b : α} (r : Rule arity a b) (hr : r.Linear)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (c : Config arity)
    (hc : ({ c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations } :
      Config arity).WellFormed) : (r.fire xs ys c).WellFormed := by
  let before : Config arity :=
    { c with equations := (Term.agent a xs, Term.agent b ys) :: c.equations }
  have hz : ∀ z, c.nextName ≤ z → before.names.count z = 0 := by
    intro z h
    apply List.count_eq_zero_of_not_mem
    intro hm
    have hb := hc.2 z hm
    change z < c.nextName at hb
    omega
  constructor
  · intro z
    rw [r.fire_count hr]
    by_cases h : z < c.nextName
    · rw [r.fresh_count_eq_zero_of_lt h, Nat.add_zero]
      exact hc.1 z
    · rw [hz z (Nat.le_of_not_gt h), Nat.zero_add]
      exact r.fresh_count_le c.nextName z
  · intro z hm
    have hp := List.count_pos_iff.mpr hm
    rw [r.fire_count hr] at hp
    change z < c.nextName + r.fresh
    by_contra! h
    rw [hz z (by omega), r.fresh_count_eq_zero_of_le h] at hp
    omega

end Rule

end Geb.InteractionNet

end
