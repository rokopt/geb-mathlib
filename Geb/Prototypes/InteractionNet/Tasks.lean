/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Output
import Geb.Prototypes.InteractionNet.Substitution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Sequential composition of closed computations

A closed computation consumes one equation and delivers constructor values along its
output wires. The equation has no other free names. Its contextual normalization property
quantifies over every continuation in which those output wires have one remaining end.
Fresh names allocated while computing are retained in the resulting supply.

## Main definitions

* {lit}`ClosedTask` — an equation with its closed results and output names.
* {lit}`ClosedTask.Realizes` — contextual execution of one closed computation.
* {lit}`tasks` — computations placed before a continuation in execution order.

## Main statements

* {lit}`reaches_tasks` — contextual computations on disjoint output wires compose in order.

## Tags

interaction calculus, continuation, sequential composition, normalization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ}

/-- One equation whose only free names are its eventual result wires. -/
structure ClosedTask (arity : α → ℕ) where
  /-- The equation to reduce. -/
  equation : Equation arity ℕ
  /-- The closed value to deliver on each output wire. -/
  results : List (ℕ × Term arity ℕ)
  /-- Result terms contain no unresolved wires. -/
  closed : ∀ b ∈ results, b.2.names = []
  /-- Every free end is an output, in the same order as the result list. -/
  names_eq : equation.1.names ++ equation.2.names = results.map Prod.fst

/-- Place computations in front of a continuation configuration. -/
def tasks (ts : List (ClosedTask arity)) (c : Config arity) : Config arity :=
  { c with equations := ts.map ClosedTask.equation ++ c.equations }

/-- A computation terminates in any bounded continuation with one end per output wire. -/
def ClosedTask.Realizes (s : System arity) (t : ClosedTask arity) : Prop :=
  ∀ c : Config arity, (∀ x ∈ c.names, x < c.nextName) →
    (t.results.map Prod.fst).Nodup → (∀ b ∈ t.results, c.names.count b.1 = 1) →
    ∃ n, c.nextName ≤ n ∧
      s.Reaches (tasks [t] c) { resolve t.results c with nextName := n }

/-- The free names of pending computations are precisely their output wires. -/
theorem tasks_names (ts : List (ClosedTask arity)) (c : Config arity) :
    (tasks ts c).names = c.interface.flatMap Term.names ++
      (ts.flatMap fun t ↦ t.results.map Prod.fst) ++
      c.equations.flatMap (fun e ↦ e.1.names ++ e.2.names) := by
  simp only [tasks, Config.names, List.flatMap_append, List.flatMap_map,
    ClosedTask.names_eq, List.append_assoc]

/-- Pending computations add their output occurrences to the continuation's counts. -/
theorem tasks_count (ts : List (ClosedTask arity)) (c : Config arity) (x : ℕ) :
    (tasks ts c).names.count x =
      c.names.count x + (ts.flatMap fun t ↦ t.results.map Prod.fst).count x := by
  rw [tasks_names]
  simp only [List.count_append, Config.names]
  omega

/-- A result batch leaves computations with disjoint output wires unchanged. -/
theorem resolve_tasks (bs : List (ℕ × Term arity ℕ)) (ts : List (ClosedTask arity))
    (c : Config arity) (hc : ∀ b ∈ bs, b.2.names = [])
    (hd : ∀ x ∈ ts.flatMap (fun t ↦ t.results.map Prod.fst), x ∉ bs.map Prod.fst) :
    resolve bs (tasks ts c) = tasks ts (resolve bs c) := by
  rw [resolve_eq_subst bs _ hc, resolve_eq_subst bs _ hc]
  have he : (ts.map ClosedTask.equation).map
      (fun e ↦ (e.1.subst (deliverySubst bs), e.2.subst (deliverySubst bs))) =
      ts.map ClosedTask.equation := by
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    have hn : ∀ x ∈ t.equation.1.names ++ t.equation.2.names,
        deliverySubst bs x = Term.var x := by
      intro x hx
      apply deliverySubst_of_not_mem
      apply hd x
      exact List.mem_flatMap.mpr ⟨t, ht, t.names_eq ▸ hx⟩
    apply Prod.ext
    · exact (Term.subst_congr _ _ _ (fun x hx ↦
        hn x (List.mem_append_left _ hx))).trans (Term.subst_var_self _)
    · exact (Term.subst_congr _ _ _ (fun x hx ↦
        hn x (List.mem_append_right _ hx))).trans (Term.subst_var_self _)
  simp only [tasks, Config.subst, List.map_append, he]

/-- Contextually terminating computations on distinct wires compose in list order. -/
theorem reaches_tasks (s : System arity) (ts : List (ClosedTask arity))
    (ht : ∀ t ∈ ts, t.Realizes s) (c : Config arity)
    (hc : ∀ x ∈ c.names, x < c.nextName)
    (hn : ((ts.flatMap ClosedTask.results).map Prod.fst).Nodup)
    (hx : ∀ b ∈ ts.flatMap ClosedTask.results, c.names.count b.1 = 1) :
    ∃ n, c.nextName ≤ n ∧ s.Reaches (tasks ts c)
      { resolve (ts.flatMap ClosedTask.results) c with nextName := n } := by
  apply List.rec (motive := fun ts ↦ (∀ t ∈ ts, t.Realizes s) → ∀ c : Config arity,
    (∀ x ∈ c.names, x < c.nextName) →
    ((ts.flatMap ClosedTask.results).map Prod.fst).Nodup →
    (∀ b ∈ ts.flatMap ClosedTask.results, c.names.count b.1 = 1) →
    ∃ n, c.nextName ≤ n ∧ s.Reaches (tasks ts c)
      { resolve (ts.flatMap ClosedTask.results) c with nextName := n })
    (fun _ c _ _ _ ↦ ⟨c.nextName, Nat.le_refl _, s.reaches_refl c⟩)
    (fun t ts ih ht c hc hn hx ↦ ?_) ts ht c hc hn hx
  have hn' := List.nodup_append.mp (show
    (t.results.map Prod.fst ++ (ts.flatMap ClosedTask.results).map Prod.fst).Nodup by
      simpa only [List.flatMap_cons, List.map_append] using hn)
  have hxt : ∀ b ∈ t.results, c.names.count b.1 = 1 :=
    fun b hb ↦ hx b (List.mem_append_left _ hb)
  have hxs : ∀ b ∈ ts.flatMap ClosedTask.results, c.names.count b.1 = 1 :=
    fun b hb ↦ hx b (List.mem_append_right _ hb)
  have hdis : ∀ x ∈ ts.flatMap (fun t ↦ t.results.map Prod.fst),
      x ∉ t.results.map Prod.fst := by
    intro x hs hh
    have hs' : x ∈ (ts.flatMap ClosedTask.results).map Prod.fst := by
      simpa only [List.map_flatMap] using hs
    exact hn'.2.2 x hh x hs' rfl
  have hbound : ∀ x ∈ (tasks ts c).names, x < (tasks ts c).nextName := by
    intro x hm
    rw [tasks_names] at hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact hc x (List.mem_append_left _ hm)
      · have hm' : x ∈ (ts.flatMap ClosedTask.results).map Prod.fst := by
          simpa only [List.map_flatMap] using hm
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm'
        exact hc b.1 (List.count_pos_iff.mp (by rw [hxs b hb]; omega))
    · exact hc x (List.mem_append_right _ hm)
  have hcount : ∀ b ∈ t.results, (tasks ts c).names.count b.1 = 1 := by
    intro b hb
    rw [tasks_count, hxt b hb]
    have hnot : b.1 ∉ ts.flatMap (fun t ↦ t.results.map Prod.fst) :=
      fun hm ↦ hdis b.1 hm (List.mem_map_of_mem hb)
    rw [List.count_eq_zero_of_not_mem hnot, Nat.add_zero]
  obtain ⟨n, hn, hs⟩ := ht t (List.mem_cons_self ..) (tasks ts c) hbound hn'.1 hcount
  rw [resolve_tasks t.results ts c t.closed hdis] at hs
  let d : Config arity := { resolve t.results c with nextName := n }
  have hdc : ∀ x ∈ d.names, x < d.nextName := by
    intro x hm
    exact Nat.lt_of_lt_of_le (hc x (names_resolve_subset t.results c t.closed hm)) hn
  have hdx : ∀ b ∈ ts.flatMap ClosedTask.results, d.names.count b.1 = 1 := by
    intro b hb
    change (resolve t.results c).names.count b.1 = 1
    rw [resolve_count_of_not_mem t.results c t.closed b.1]
    · exact hxs b hb
    · apply hdis b.1
      simpa only [List.map_flatMap] using
        (List.mem_map_of_mem hb : b.1 ∈ (ts.flatMap ClosedTask.results).map Prod.fst)
  obtain ⟨m, hm, hs'⟩ := ih (fun u hu ↦ ht u (List.mem_cons_of_mem _ hu)) d hdc hn'.2.1 hdx
  refine ⟨m, Nat.le_trans hn hm, ?_⟩
  have hclosed : ∀ b ∈ ts.flatMap ClosedTask.results, b.2.names = [] := by
    intro b hb
    obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp hb
    exact u.closed b hu
  have hf := s.reaches_trans hs hs'
  have he : { resolve (ts.flatMap ClosedTask.results) d with nextName := m } =
      { resolve (t.results ++ ts.flatMap ClosedTask.results) c with nextName := m } := by
    dsimp only [d]
    rw [resolve_with_nextName _ _ _ hclosed, resolve_append]
  rw [he] at hf
  exact hf

end Geb.InteractionNet

end
