/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Erasure
public import Geb.Prototypes.InteractionNet.Tasks
import Geb.Prototypes.InteractionNet.FiniteSum
import Geb.Prototypes.InteractionNet.Substitution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Contextual copying of constructor values

Copying a constructor allocates a rectangular array of wires: one row for each field,
and one column for each requested copy. Child computations fill those rows before the
parent constructors are delivered. The fresh array is disjoint from the continuation's
names, so the closed child substitutions affect only their intended fields.

## Main definitions

* {lit}`copyTask` — a fan on a closed constructor value, with its expected copies.

## Main statements

* {lit}`copy_realizes` — every finite constructor value can be copied in a continuation.
* {lit}`reaches_copy` — contextual copying terminates with the requested closed deliveries.

## Tags

interaction net, constructor, copying, continuation, normalization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- Copy a closed constructor value to the listed output ports. -/
def copyTask (v : Value dataArity) {k : ℕ} (outs : Fin k → ℕ) :
    ClosedTask (netArity (φ := φ) dataArity) where
  equation := (Term.agent (fan dataArity k) (fun j ↦ Term.var (outs j)),
    Value.embed dataArity v)
  results := List.ofFn fun j ↦ (outs j, Value.embed dataArity v)
  closed := by simp
  names_eq := by
    simp only [Term.names_agent, Term.names_var, Value.embed_names, List.append_nil,
      List.map_ofFn, Function.comp_def]
    simpa only [List.flatMap, List.map_ofFn, Function.comp_def] using
      List.flatMap_singleton' (List.ofFn outs)

/-- The fresh wire joining one copied field to one parent constructor. -/
def copyWire {m k : ℕ} (next : ℕ) (i : Fin m) (j : Fin k) : ℕ :=
  next + (finProdFinEquivC (i, j)).val

/-- The fresh rectangle has distinct entries. -/
theorem copyWire_eq_iff {m k : ℕ} (next : ℕ) (i i' : Fin m) (j j' : Fin k) :
    copyWire next i j = copyWire next i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    have he := finProdFinEquivC.injective (Fin.ext (Nat.add_left_cancel h))
    exact Prod.mk.inj he
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every copied field wire is below the supply after the constructor interaction. -/
theorem copyWire_lt {m k : ℕ} (next : ℕ) (i : Fin m) (j : Fin k) :
    copyWire next i j < next + m * k := Nat.add_lt_add_left (finProdFinEquivC (i, j)).isLt _

/-- One constructor interaction schedules its child copies before its parent deliveries. -/
theorem copy_step (p : Program (φ := φ) dataArity) (a : δ ⊕ ℕ)
    (vs : Fin (constructorArity dataArity a) → Value dataArity)
    {k : ℕ} (outs : Fin k → ℕ) (c : Config (netArity dataArity)) :
    (system dataArity p).step (tasks [copyTask dataArity (Term.agent a vs) outs] c) =
      some (tasks (List.ofFn fun i ↦ copyTask dataArity (vs i) (copyWire (k := k) c.nextName i))
        (deliveries (List.ofFn fun j ↦ (outs j, Term.agent (.inl a)
          (fun i ↦ Term.var (copyWire c.nextName i j))))
          { c with nextName := c.nextName + constructorArity dataArity a * k })) := by
  apply System.step_cons
  change some { c with
    equations := (fanRule dataArity k a).instantiate c.nextName
      (fun j ↦ Term.var (outs j)) (fun i ↦ Value.embed dataArity (vs i)) ++ c.equations
    nextName := c.nextName + (fanRule dataArity k a).fresh } = _
  simp only [fanRule, Rule.instantiate, List.map_append, List.map_ofFn, Function.comp_def,
    Term.subst_agent, Term.subst_var, Sum.elim_inl, Sum.elim_inr, Rule.allocated,
    copyWire, tasks, deliveries, copyTask, List.append_assoc]

private theorem copy_constructor_realizes (p : Program (φ := φ) dataArity) (a : δ ⊕ ℕ)
    (vs : Fin (constructorArity dataArity a) → Value dataArity)
    (ih : ∀ i {k : ℕ} (outs : Fin k → ℕ), (copyTask dataArity (vs i) outs).Realizes
      (system dataArity p)) {k : ℕ} (outs : Fin k → ℕ) :
    (copyTask dataArity (Term.agent a vs) outs).Realizes (system dataArity p) := by
  intro c hc hn hx
  let w : Fin (constructorArity dataArity a) → Fin k → ℕ := copyWire c.nextName
  let ts := List.ofFn fun i ↦ copyTask (φ := φ) dataArity (vs i) (w i)
  let bs := ts.flatMap ClosedTask.results
  let pending := List.ofFn fun j ↦
    (outs j, Term.agent (arity := netArity (φ := φ) dataArity) (.inl a)
      (fun i ↦ Term.var (w i j)))
  let next := c.nextName + constructorArity dataArity a * k
  let d := deliveries pending { c with nextName := next }
  have hold : ∀ j, outs j < c.nextName := by
    intro j
    apply hc
    apply List.count_pos_iff.mp
    rw [hx (outs j, Value.embed dataArity (Term.agent a vs))
      (List.mem_ofFn.mpr ⟨j, rfl⟩)]
    omega
  have hw : ∀ i i' j j', w i j = w i' j' ↔ i = i' ∧ j = j' :=
    copyWire_eq_iff c.nextName
  have hlow : ∀ i j, c.nextName ≤ w i j := fun i j ↦ Nat.le_add_right _ _
  have hhigh : ∀ i j, w i j < next := copyWire_lt c.nextName
  have hkeys : bs.map Prod.fst = (List.ofFn fun i ↦ List.ofFn (w i)).flatten := by
    simp only [bs, ts, List.flatMap, copyTask, List.map_flatten,
      List.map_ofFn, Function.comp_def]
  have hnodup : (bs.map Prod.fst).Nodup := by
    rw [hkeys]
    exact nodup_matrix w hw
  have hclosed : ∀ b ∈ bs, b.2.names = [] := by
    intro b hb
    obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hb
    exact t.closed b ht
  have hbound : ∀ x ∈ d.names, x < d.nextName := by
    intro x h
    change x < next
    change x ∈ c.interface.flatMap Term.names ++
      (pending.map (fun b : ℕ × Term (netArity dataArity) ℕ ↦ (Term.var b.1, b.2)) ++
        c.equations).flatMap
        (fun e : Equation (netArity dataArity) ℕ ↦ e.1.names ++ e.2.names) at h
    rw [List.flatMap_append] at h
    rcases List.mem_append.mp h with h | h
    · exact Nat.lt_of_lt_of_le (hc x (List.mem_append_left _ h)) (Nat.le_add_right _ _)
    · rcases List.mem_append.mp h with h | h
      · rw [List.flatMap_map] at h
        obtain ⟨b, hb, hh⟩ := List.mem_flatMap.mp h
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
        rcases List.mem_append.mp hh with hh | hh
        · have he : x = outs j := List.mem_singleton.mp hh
          subst x
          exact Nat.lt_of_lt_of_le (hold j) (Nat.le_add_right _ _)
        · obtain ⟨ns, hns, hmem⟩ := List.mem_flatten.mp hh
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hns
          have he : x = w i j := List.mem_singleton.mp hmem
          exact he ▸ hhigh i j
      · exact Nat.lt_of_lt_of_le (hc x (List.mem_append_right _ h)) (Nat.le_add_right _ _)
  have hcount : ∀ b ∈ bs, d.names.count b.1 = 1 := by
    intro b hb
    obtain ⟨t, ht, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    have hc0 : c.names.count (w i j) = 0 := List.count_eq_zero_of_not_mem (by
      intro hm
      have hl := hc (w i j) hm
      have hh := hlow i j
      omega)
    have ho0 : ∀ l, outs l ≠ w i j := by
      intro l he
      have hl := hold l
      have hh := hlow i j
      omega
    have hsum : ∀ l, (finSum fun r ↦ if w r l = w i j then 1 else 0) =
        if l = j then 1 else 0 := by
      intro l
      simp only [hw]
      by_cases he : l = j <;> simp [he]
    have he : d.names.count (w i j) = c.names.count (w i j) + 1 := by
      simp only [d, pending, deliveries, Config.names, List.flatMap_append,
        List.count_append, List.count_flatMap, List.map_ofFn,
        Function.comp_def, Term.names_var, Term.names_agent, List.count_flatten,
        List.count_singleton, beq_iff_eq, finSum_ofFn]
      simp only [ho0, ↓reduceIte, Nat.zero_add, hsum, finSum_ite_eq]
      omega
    rw [he, hc0]
  obtain ⟨n, hnext, hs⟩ := reaches_tasks (system dataArity p) ts
    (by intro t ht; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht; exact ih i (w i))
    d hbound hnodup hcount
  let σ := deliverySubst bs
  have hσold : ∀ x, x < c.nextName → σ x = Term.var x := by
    intro x hx
    apply deliverySubst_of_not_mem
    rw [hkeys]
    intro hm
    obtain ⟨row, hr, hm⟩ := List.mem_flatten.mp hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
    have hh := hlow i j
    omega
  have hσwire : ∀ i j, σ (w i j) = Value.embed dataArity (vs i) := by
    intro i j
    apply deliverySubst_of_mem bs hnodup (w i j, Value.embed dataArity (vs i))
    exact List.mem_flatMap.mpr ⟨copyTask dataArity (vs i) (w i),
      List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_ofFn.mpr ⟨j, rfl⟩⟩
  have hσc : ({ c with nextName := next } : Config (netArity dataArity)).subst σ =
      { c with nextName := next } :=
    (Config.subst_congr σ Term.var { c with nextName := next }
      (fun x hx ↦ hσold x (hc x hx))).trans
      (Config.subst_var_self _)
  have hr : resolve bs d = deliveries (copyTask dataArity (Term.agent a vs) outs).results
      { c with nextName := next } := by
    rw [resolve_eq_subst bs d hclosed]
    change (deliveries pending _).subst σ = _
    rw [subst_deliveries_of_fixed pending _ σ
      (by intro b hb; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb; exact hσold (outs j) (hold j)),
      hσc]
    simp only [pending, List.map_ofFn, Function.comp_def, Term.subst_agent,
      Term.subst_var, hσwire, copyTask, Value.embed_agent]
  rw [hr] at hs
  have hstep := System.reaches_of_step _ (copy_step dataArity p a vs outs c)
  have hcopies := System.reaches_trans _ hstep hs
  have hfinish := reaches_resolve (system dataArity p)
    (copyTask dataArity (Term.agent a vs) outs).results { c with nextName := n }
    (copyTask dataArity (Term.agent a vs) outs).closed hn hx
  refine ⟨n, Nat.le_trans (Nat.le_add_right _ _) hnext, ?_⟩
  rw [resolve_with_nextName _ c n (copyTask dataArity (Term.agent a vs) outs).closed]
    at hfinish
  exact System.reaches_trans _ hcopies hfinish

/-- Every finite constructor value can be copied any finite number of times in a bounded
continuation with one remaining end on each distinct output wire. -/
theorem copy_realizes (p : Program (φ := φ) dataArity) (v : Value dataArity)
    {k : ℕ} (outs : Fin k → ℕ) :
    (copyTask dataArity v outs).Realizes (system dataArity p) := by
  apply PFunctor.FreeM.rec (motive := fun v ↦ ∀ {k : ℕ} (outs : Fin k → ℕ),
    (copyTask dataArity v outs).Realizes (system dataArity p))
    (fun x ↦ x.elim) (fun a vs ih _ outs ↦ ?_) v outs
  exact copy_constructor_realizes dataArity p a vs ih outs

/-- The sequential reducer delivers copies of an arbitrary constructor value, preserving
the continuation except for the output substitutions and its increased allocation supply. -/
theorem reaches_copy (p : Program (φ := φ) dataArity) (v : Value dataArity)
    {k : ℕ} (outs : Fin k → ℕ) (hi : Function.Injective outs)
    (c : Config (netArity dataArity)) (hc : ∀ x ∈ c.names, x < c.nextName)
    (hx : ∀ j, c.names.count (outs j) = 1) :
    ∃ n, c.nextName ≤ n ∧ (system dataArity p).Reaches
      { c with equations := (Term.agent (fan dataArity k) (fun j ↦ Term.var (outs j)),
        Value.embed dataArity v) :: c.equations }
      { resolve (List.ofFn fun j ↦ (outs j, Value.embed dataArity v)) c with nextName := n } := by
  apply copy_realizes dataArity p v outs c hc
  · simp only [copyTask, List.map_ofFn, Function.comp_def]
    apply List.nodup_iff_count_of_mem.mpr
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    simp only [count_ofFn_eq_finSum, hi.eq_iff, finSum_ite_eq]
  · intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    exact hx j

end Geb.InteractionNet.FirstOrder

end
