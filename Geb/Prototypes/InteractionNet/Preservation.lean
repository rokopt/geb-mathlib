/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.InteractionNet.Allocation
import Geb.Prototypes.InteractionNet.Substitution
public import Geb.Prototypes.InteractionNet.Calculus
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Preservation of wire invariants

An interaction preserves the interface by a linear rule. Wire elimination removes the two
ends of its named wire, transferring every name in the replacement to the remaining end.
Both operations preserve the bound of two occurrences and keep all names below the supply.

## Main statements

* {lit}`Config.subst_count` — occurrence counts after replacing one name.
* {lit}`Config.eliminate_wellFormed` — successful wire elimination preserves the invariant.
* {lit}`System.run_wellFormed` — every finite run of a linear system preserves the invariant.

## Tags

interaction calculus, substitution, invariant, preservation, wire
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ}

namespace Config

/-- Replacing a name transfers its occurrences to the replacement's names. -/
theorem subst_count (c : Config arity) (x y : ℕ) (t : Term arity ℕ) :
    (c.subst fun z ↦ if z = x then t else Term.var z).names.count y =
      c.names.count x * t.names.count y + (if y = x then 0 else c.names.count y) := by
  rw [names_subst]
  apply List.rec (motive := fun ns : List ℕ ↦
    (ns.flatMap fun z ↦ (if z = x then t else Term.var z).names).count y =
      ns.count x * t.names.count y + (if y = x then 0 else ns.count y))
    (by simp) (fun a as ih ↦ ?_) c.names
  by_cases hax : a = x <;> by_cases hay : a = y <;> by_cases hyx : y = x <;>
    simp_all [-List.count_eq_one_of_mem, Term.names_var,
      Nat.add_mul] <;> omega

/-- Reversing an equation changes neither its wire multiplicities nor its allocation bound. -/
theorem wellFormed_swap (e : Equation arity ℕ) (c : Config arity)
    (h : ({ c with equations := e :: c.equations } : Config arity).WellFormed) :
    ({ c with equations := (e.2, e.1) :: c.equations } : Config arity).WellFormed := by
  constructor
  · intro x
    have hx := h.1 x
    simp only [names, List.flatMap_cons, List.count_append] at hx ⊢
    omega
  · intro x hx
    apply h.2 x
    simpa only [names, List.flatMap_cons, List.mem_append, or_assoc, or_left_comm] using hx

/-- Reordering equations preserves the wire invariant. -/
theorem wellFormed_perm (c : Config arity) (es : List (Equation arity ℕ))
    (hp : es.Perm c.equations) (hc : c.WellFormed) :
    ({ c with equations := es } : Config arity).WellFormed := by
  have hn : ({ c with equations := es } : Config arity).names.Perm c.names :=
    (List.Perm.refl _).append (hp.flatMap_right _)
  exact ⟨fun x ↦ (hn.count_eq x) ▸ hc.1 x, fun x hx ↦ hc.2 x (hn.mem_iff.mp hx)⟩

/-- Successful wire elimination preserves the occurrence and fresh-name invariants. -/
theorem eliminate_wellFormed (c d : Config arity) (x : ℕ) (t : Term arity ℕ)
    (hc : ({ c with equations := (Term.var x, t) :: c.equations } :
      Config arity).WellFormed) (h : c.eliminate x t = some d) : d.WellFormed := by
  unfold eliminate at h
  split at h
  next hw =>
    obtain ⟨hnt, hcount⟩ := hw
    cases Option.some.inj h
    have hbefore : ∀ y, c.names.count y + t.names.count y ≤ 2 := by
      intro y
      have hb := hc.1 y
      simp only [names, List.flatMap_cons, Term.names_var, List.count_append] at hb ⊢
      omega
    have hzero : ∀ y, c.nextName ≤ y →
        c.names.count y = 0 ∧ t.names.count y = 0 := by
      intro y hy
      have hm : y ∉ ({ c with equations := (Term.var x, t) :: c.equations } :
          Config arity).names := by
        intro hm
        have hb := hc.2 y hm
        change y < c.nextName at hb
        omega
      simp only [names, List.flatMap_cons, Term.names_var, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      constructor
      · apply List.count_eq_zero_of_not_mem
        simpa only [names, List.mem_append, not_or] using And.intro hm.1 hm.2.2
      · exact List.count_eq_zero_of_not_mem hm.2.1.2
    constructor
    · intro y
      rw [subst_count, hcount, Nat.one_mul]
      by_cases hy : y = x
      · subst y
        simp [List.count_eq_zero_of_not_mem hnt]
      · simpa only [hy, ↓reduceIte, Nat.add_comm] using hbefore y
    · intro y hy
      change y < c.nextName
      by_contra! hb
      have hp := List.count_pos_iff.mpr hy
      rw [subst_count, (hzero y hb).1, (hzero y hb).2] at hp
      split at hp <;> omega
  next => simp at h

end Config

namespace System

/-- Contracting an equation preserves well-formedness when every registered rule is linear. -/
theorem contract_wellFormed (s : System arity)
    (hs : ∀ a b r, s.rule a b = some r → r.Linear)
    (e : Equation arity ℕ) (c d : Config arity)
    (hc : ({ c with equations := e :: c.equations } : Config arity).WellFormed)
    (h : s.contract e c = some d) : d.WellFormed := by
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
        exact c.eliminate_wellFormed d y (Term.var x) (c.wellFormed_swap _ hc) h
      | some v =>
        simp only [he, Option.orElse_some, Option.some.injEq] at h
        subst v
        exact c.eliminate_wellFormed d x (Term.var y) hc he
    | liftBind b ys => exact c.eliminate_wellFormed d x (.agent b ys) hc h
  | liftBind a xs =>
    cases u with
    | pure y =>
      exact c.eliminate_wellFormed d y (.agent a xs) (c.wellFormed_swap _ hc) h
    | liftBind b ys =>
      change (match s.rule a b with
        | some r => some (r.fire xs ys c)
        | none => (s.rule b a).map (fun r ↦ r.fire ys xs c)) = some d at h
      cases hr : s.rule a b with
      | some r =>
        simp only [hr, Option.some.injEq] at h
        subst d
        exact r.interaction_wellFormed (hs a b r hr) xs ys c hc
      | none =>
        simp only [hr, Option.map_eq_some_iff] at h
        obtain ⟨r, hr, rfl⟩ := h
        exact r.interaction_wellFormed (hs b a r hr) ys xs c (c.wellFormed_swap _ hc)

/-- Selecting a reducible equation and contracting it preserves well-formedness. -/
theorem step_wellFormed (s : System arity)
    (hs : ∀ a b r, s.rule a b = some r → r.Linear)
    (c d : Config arity) (hc : c.WellFormed) (h : s.step c = some d) : d.WellFormed := by
  obtain ⟨⟨e, i⟩, hm, hr⟩ := List.exists_of_findSome?_eq_some h
  have hi : c.equations[i]? = some e := List.mk_mem_zipIdx_iff_getElem?.mp hm
  have he : c.equations.take i ++ e :: c.equations.drop (i + 1) = c.equations := by
    have hd := List.take_append_drop i c.equations
    rw [List.drop_eq_getElem?_toList_append, hi] at hd
    exact hd
  apply s.contract_wellFormed hs e _ d _ hr
  apply c.wellFormed_perm _ _ hc
  exact List.perm_middle.symm.trans (List.Perm.of_eq he)

/-- Every finite sequential execution preserves well-formedness. -/
theorem run_wellFormed (s : System arity)
    (hs : ∀ a b r, s.rule a b = some r → r.Linear)
    (c : Config arity) (hc : c.WellFormed) (n : ℕ) : (s.run n c).WellFormed := by
  apply Nat.rec (motive := fun n ↦ (s.run n c).WellFormed) hc (fun n ih ↦ ?_) n
  change ((s.step (s.run n c)).getD (s.run n c)).WellFormed
  cases h : s.step (s.run n c) with
  | none => exact ih
  | some d => exact s.step_wellFormed hs _ d ih h

end System

end Geb.InteractionNet

end
