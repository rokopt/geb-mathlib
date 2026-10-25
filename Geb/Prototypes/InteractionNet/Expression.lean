/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.CopyingNormalization
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Contextual expression evaluation

An expression evaluator consumes a closed environment and delivers one closed value.
Its local rules first copy the environment, then evaluate the children, and finally
construct a value or invoke a named call. Contextual execution composes these computations
in the same order as the sequential reducer.

## Main definitions

* {lit}`evalTask` — evaluate an expression against a closed environment.
* {lit}`returnTask` — deliver a computed value on its result wire.
* {lit}`Evaluates`, {lit}`Calls` — contextual normalization of expressions and named calls.

## Main statements

* {lit}`evaluates_var` — variable evaluation consumes the unused environment entries.
* {lit}`finish_con_realizes` — constructor assembly delivers its closed result.

## Tags

interaction net, expression, evaluation, continuation, normalization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- Deliver one closed value to its output wire. -/
def returnTask (v : Value dataArity) (out : ℕ) :
    ClosedTask (netArity (φ := φ) dataArity) where
  equation := (Term.var out, Value.embed dataArity v)
  results := [(out, Value.embed dataArity v)]
  closed := by simp
  names_eq := by simp

/-- A computed value is delivered in one wire-elimination step. -/
theorem return_realizes (p : Program (φ := φ) dataArity) (v : Value dataArity) (out : ℕ) :
    (returnTask dataArity v out).Realizes (system dataArity p) := by
  intro c _ _ hx
  refine ⟨c.nextName, Nat.le_refl _, ?_⟩
  exact reaches_delivery _ c out (Value.embed dataArity v) (Value.embed_names dataArity v)
    (hx _ (List.mem_singleton_self _))

/-- Evaluate an expression against a closed finite environment, with its expected result. -/
def evalTask {n : ℕ} (e : Expr (φ := φ) dataArity n) (ρ : Fin n → Value dataArity)
    (out : ℕ) (v : Value dataArity) : ClosedTask (netArity (φ := φ) dataArity) where
  equation := (Term.agent (ev dataArity e) (fun _ ↦ Term.var out),
    Term.agent (env dataArity n) (fun i ↦ Value.embed dataArity (ρ i)))
  results := [(out, Value.embed dataArity v)]
  closed := by simp
  names_eq := by simp

/-- Contextual evaluation for every choice of the result wire. -/
def Evaluates (p : Program (φ := φ) dataArity) {n : ℕ} (e : Expr (φ := φ) dataArity n)
    (ρ : Fin n → Value dataArity) (v : Value dataArity) : Prop :=
  ∀ out, (evalTask dataArity e ρ out v).Realizes (system dataArity p)

private theorem flatten_ofFn_ite {β : Type} {n : ℕ} (i : Fin n) (f : Fin n → β) :
    (List.ofFn fun j ↦ if j = i then [f j] else []).flatten = [f i] := by
  apply Nat.rec (motive := fun n ↦ ∀ (i : Fin n) (f : Fin n → β),
    (List.ofFn fun j ↦ if j = i then [f j] else []).flatten = [f i])
    (fun i ↦ i.elim0) (fun n ih i f ↦ ?_) n i f
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp [List.ofFn_succ]
  · simpa [List.ofFn_succ, Ne.symm (Fin.succ_ne_zero i)] using ih i (fun j ↦ f j.succ)

/-- A variable retains its selected environment entry and erases every other entry. -/
def variableTasks {n : ℕ} (i : Fin n) (ρ : Fin n → Value dataArity) (out : ℕ) :
    List (ClosedTask (netArity (φ := φ) dataArity)) :=
  List.ofFn fun j ↦ if j = i then returnTask dataArity (ρ j) out
    else copyTask dataArity (ρ j) (Fin.elim0 : Fin 0 → ℕ)

/-- The selected environment entry is the variable computation's only result. -/
theorem variableTasks_results {n : ℕ} (i : Fin n) (ρ : Fin n → Value dataArity) (out : ℕ) :
    (variableTasks (φ := φ) dataArity i ρ out).flatMap ClosedTask.results =
      [(out, Value.embed dataArity (ρ i))] := by
  simp only [variableTasks, List.flatMap, List.map_ofFn, Function.comp_def]
  have he : (fun j : Fin n ↦
      (if j = i then returnTask dataArity (ρ j) out else
        copyTask (φ := φ) dataArity (ρ j) (Fin.elim0 : Fin 0 → ℕ)).results) =
      (fun j ↦ if j = i then [(out, Value.embed dataArity (ρ j))] else []) := by
    funext j
    by_cases h : j = i <;> simp [h, returnTask, copyTask]
  rw [he]
  exact flatten_ofFn_ite i _

/-- A variable evaluator exposes the selected delivery and the unused-entry erasures. -/
theorem eval_var_step (p : Program (φ := φ) dataArity) {n : ℕ} (i : Fin n)
    (ρ : Fin n → Value dataArity) (out : ℕ) (v : Value dataArity)
    (c : Config (netArity dataArity)) :
    (system dataArity p).step (tasks [evalTask dataArity (Term.var i) ρ out v] c) =
      some (tasks (variableTasks dataArity i ρ out) c) := by
  apply System.step_cons
  simp only [System.contract, evalTask, Term.agent, system, ev, env]
  change some { c with
    equations := (evalRule dataArity (Term.var i)).instantiate c.nextName
      (fun _ ↦ Term.var out) (fun j ↦ Value.embed dataArity (ρ j)) ++ c.equations
    nextName := c.nextName + (evalRule dataArity (Term.var i)).fresh } = _
  simp only [evalRule, Term.var, Rule.instantiate, List.map_ofFn, Function.comp_def,
    tasks, variableTasks, Nat.add_zero]
  congr 1
  congr 1
  apply congrArg (fun es ↦ es ++ c.equations)
  apply congrArg List.ofFn
  funext j
  by_cases h : j = i
  · simp only [h, ↓reduceIte, returnTask]
    rfl
  · simp only [h, ↓reduceIte, copyTask]
    apply Prod.ext
    · apply congrArg (Term.agent (fan dataArity 0))
      funext z
      exact z.elim0
    · rfl

/-- A variable evaluates to its environment entry, consuming every unused entry. -/
theorem evaluates_var (p : Program (φ := φ) dataArity) {n : ℕ} (i : Fin n)
    (ρ : Fin n → Value dataArity) :
    Evaluates dataArity p (Term.var i) ρ (ρ i) := by
  intro out c hc hn hx
  have ht : ∀ t ∈ variableTasks dataArity i ρ out,
      t.Realizes (system dataArity p) := by
    intro t ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ht
    by_cases h : j = i
    · simp only [h, ↓reduceIte]
      exact return_realizes dataArity p (ρ i) out
    · simp only [h, ↓reduceIte]
      exact copy_realizes dataArity p (ρ j) Fin.elim0
  obtain ⟨m, hm, hs⟩ := reaches_tasks (system dataArity p)
    (variableTasks dataArity i ρ out) ht c hc
    (by simpa only [variableTasks_results, evalTask] using hn)
    (by simpa only [variableTasks_results, evalTask] using hx)
  refine ⟨m, hm, ?_⟩
  rw [variableTasks_results] at hs
  exact System.reaches_trans _
    (System.reaches_of_step _ (eval_var_step dataArity p i ρ out (ρ i) c)) hs

/-- Finish an expression root whose child computations have supplied closed values. -/
def finishTask (a : Symbol (δ := δ) (φ := φ))
    (vs : Fin (exprArity dataArity a) → Value dataArity) (out : ℕ) (v : Value dataArity) :
    ClosedTask (netArity (φ := φ) dataArity) where
  equation := finish dataArity a (Term.var out) (fun i ↦ Value.embed dataArity (vs i))
  results := [(out, Value.embed dataArity v)]
  closed := by simp
  names_eq := by
    cases a with
    | inl a => simp [finish]
    | inr fk => rcases fk with ⟨f, k⟩; simp [finish, List.ofFn_succ]

/-- Finishing a data constructor delivers the constructor applied to its computed fields. -/
theorem finish_con_realizes (p : Program (φ := φ) dataArity) (a : δ)
    (vs : Fin (dataArity a) → Value dataArity) (out : ℕ) :
    (finishTask dataArity (.inl a) vs out (Term.agent (.inl a) vs)).Realizes
      (system dataArity p) := by
  simpa only [finishTask, finish, returnTask, Value.embed_agent] using
    return_realizes dataArity p (Term.agent (.inl a) vs) out

/-- Contextual execution of a named call on closed arguments. -/
def Calls (p : Program (φ := φ) dataArity) (f : φ) (v : Value dataArity)
    (args : List (Value dataArity)) (result : Value dataArity) : Prop :=
  ∀ out, (finishTask dataArity (.inr (f, args.length)) (Fin.cases v args.get) out result).Realizes
    (system dataArity p)

/-- Reindexing a call's auxiliary arguments along an arity equality leaves its task unchanged. -/
theorem finishTask_call_congr (f : φ) {k l : ℕ} (h : k = l) (v : Value dataArity)
    (xs : Fin k → Value dataArity) (ys : Fin l → Value dataArity)
    (he : ∀ i, xs i = ys (Fin.cast h i)) (out : ℕ) (result : Value dataArity) :
    finishTask dataArity (.inr (f, k)) (Fin.cases v xs) out result =
      finishTask dataArity (.inr (f, l)) (Fin.cases v ys) out result := by
  subst l
  have hs : xs = ys := funext he
  rw [hs]

end Geb.InteractionNet.FirstOrder

end
