/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Program
public import Geb.Prototypes.InteractionNet.FiniteSum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Wire invariants of the first-order translation

The translation preserves the interface of each interacting pair. Every auxiliary port
appears once in the replacement, and every newly allocated wire has two ends. In particular,
duplication in a source expression is implemented by fans rather than repeated port names.

## Main statements

* {lit}`fanRule_linear` — constructor copying preserves the interface.
* {lit}`finish_count` — finishing an expression uses its output and child results once.
* {lit}`callRule_linear` — a call transfers its fields and arguments once.
* {lit}`system_rule_linear` — every rule of the generated system is linear.

## Tags

interaction net, compilation, linearity, wire, interface
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- Copying uses each boundary port once and each internal wire twice. -/
theorem fanRule_linear (k : ℕ) (a : δ ⊕ ℕ) :
    (fanRule (φ := φ) dataArity k a).Linear := by
  dsimp [-List.count_eq_one_of_mem, Rule.Linear, Rule.names, fanRule]
  constructor
  · intro i
    cases i <;>
      simp [-List.count_eq_one_of_mem, Term.names_agent, Term.names_var,
      List.count_flatMap, List.count_flatten,
        List.map_ofFn, finSum_ofFn, List.count_singleton, Function.comp_def]
  · intro j
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquivC.surjective j
    simp [-List.count_eq_one_of_mem, Term.names_agent, Term.names_var,
      List.count_flatMap, List.count_flatten,
      List.map_ofFn, finSum_ofFn, List.count_singleton, Function.comp_def, ite_and]

/-- Finishing an expression uses the output and every child's result exactly once. -/
theorem finish_count {ν : Type} [BEq ν] (a : Symbol (δ := δ) (φ := φ))
    (out : Term (netArity (φ := φ) dataArity) ν)
    (rs : Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ν) (x : ν) :
    (finish dataArity a out rs).1.names.count x + (finish dataArity a out rs).2.names.count x =
      out.names.count x + finSum (fun i ↦ (rs i).names.count x) := by
  cases a with
  | inl a =>
    simp [-List.count_eq_one_of_mem, finish, Term.names_agent,
      List.count_flatten, List.map_ofFn, finSum_ofFn,
      Function.comp_def]
  | inr a =>
    obtain ⟨f, n⟩ := a
    simp only [finish, Term.names_agent, List.ofFn_succ, Fin.cases_zero, Fin.cases_succ,
      List.flatten_cons, List.count_append, finSum_succ, List.count_flatten,
      List.map_ofFn, finSum_ofFn, Function.comp_def]
    omega

/-- A call transfers its result port, the constructor fields, and its further arguments once. -/
theorem callRule_linear (f : φ) (others : ℕ) (a : δ)
    (body : Expr (φ := φ) dataArity (dataArity a + others)) :
    (callRule dataArity f others a body).Linear := by
  dsimp [-List.count_eq_one_of_mem, Rule.Linear, Rule.names, callRule]
  constructor
  · intro i
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Term.names_agent,
      Term.names_var,
      List.count_append, List.count_flatten, List.map_ofFn, finSum_ofFn,
      Function.comp_def, finSum_append]
    cases i with
    | inl j =>
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp [-List.count_eq_one_of_mem]
      · simp [-List.count_eq_one_of_mem, List.count_singleton, Ne.symm (Fin.succ_ne_zero j)]
    | inr j =>
      simp [-List.count_eq_one_of_mem, List.count_singleton]
  · intro i
    exact i.elim0

/-- Evaluating a variable sends its selected environment entry to the output and erases
every other entry. The rule preserves the interface. -/
theorem evalRule_var_linear {n : ℕ} (i : Fin n) :
    (evalRule (φ := φ) dataArity (Term.var i)).Linear := by
  change (evalRule (φ := φ) dataArity (PFunctor.FreeM.pure i)).Linear
  dsimp only [Rule.Linear, Rule.names, evalRule]
  constructor
  · intro j
    cases j with
    | inl j =>
      have h : j = 0 := by
        apply Fin.ext
        have hj : j.val < 1 := j.isLt
        change j.val = 0
        omega
      subst j
      simp [-List.count_eq_one_of_mem, List.count_flatMap, List.map_ofFn,
        finSum_ofFn, Function.comp_def,
        apply_ite, Term.names_agent, Term.names_var]
    | inr j =>
      simp [-List.count_eq_one_of_mem, List.count_flatMap, List.map_ofFn,
        finSum_ofFn, Function.comp_def,
        apply_ite, Term.names_agent, Term.names_var, List.count_singleton]
  · intro j
    exact j.elim0

private theorem castAdd_ne_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  change i.val = m + j.val at hv
  omega

private theorem natAdd_ne_castAdd {m n : ℕ} (i : Fin n) (j : Fin m) :
    Fin.natAdd m i ≠ Fin.castAdd n j := Ne.symm (castAdd_ne_natAdd j i)

private theorem natAdd_inj {m n : ℕ} (i j : Fin n) :
    Fin.natAdd m i = Fin.natAdd m j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have he := congrArg Fin.val h
    change m + i.val = m + j.val at he
    omega
  · exact congrArg (Fin.natAdd m)

/-- Evaluating a constructor or call allocates a separate wire for every environment copy
and every child result; each allocated wire has exactly two ends. -/
theorem evalRule_agent_linear {n : ℕ} (a : Symbol (δ := δ) (φ := φ))
    (es : Fin (exprArity dataArity a) → Expr dataArity n) :
    (evalRule dataArity (Term.agent a es)).Linear := by
  change (evalRule dataArity (PFunctor.FreeM.liftBind a es)).Linear
  dsimp only [Rule.Linear, Rule.names, evalRule]
  constructor
  · intro j
    cases j with
    | inl j =>
      have h : j = 0 := by
        apply Fin.ext
        have hj : j.val < 1 := j.isLt
        change j.val = 0
        omega
      subst j
      simp [-List.count_eq_one_of_mem, List.count_flatMap, List.map_ofFn, Function.comp_def,
        finish_count, Term.names_agent, Term.names_var, List.count_flatten]
    | inr j =>
      simp [-List.count_eq_one_of_mem, List.count_flatMap, List.map_ofFn,
        finSum_ofFn, Function.comp_def,
        finish_count, Term.names_agent, Term.names_var, List.count_flatten,
        List.count_singleton]
  · intro j
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquivC.surjective j
      simp [-List.count_eq_one_of_mem, List.count_flatMap, List.map_ofFn,
        finSum_ofFn, Function.comp_def,
        finish_count, Term.names_agent, Term.names_var, List.count_flatten,
        List.count_singleton, ite_and, natAdd_ne_castAdd]
    · simp [-List.count_eq_one_of_mem, List.count_flatMap, List.map_ofFn,
        finSum_ofFn, Function.comp_def,
        finish_count, Term.names_agent, Term.names_var, List.count_flatten,
        List.count_singleton, castAdd_ne_natAdd, -Fin.natAdd_inj, natAdd_inj]

/-- Every expression-evaluation rule preserves the interface of its active pair. -/
theorem evalRule_linear {n : ℕ} (e : Expr (φ := φ) dataArity n) :
    (evalRule dataArity e).Linear :=
  PFunctor.FreeM.rec (evalRule_var_linear dataArity)
    (fun a es _ ↦ evalRule_agent_linear dataArity a es) e

/-- Every registered rule of a translated first-order program is a linear interaction rule. -/
theorem system_rule_linear (p : Program (φ := φ) dataArity)
    (a b : Agent (φ := φ) dataArity) (r : Rule (netArity dataArity) a b)
    (h : (system dataArity p).rule a b = some r) : r.Linear := by
  cases a with
  | inl a => simp [-List.count_eq_one_of_mem, system] at h
  | inr a =>
    cases a with
    | inl k =>
      cases b with
      | inl b =>
        simp only [system, Option.some.injEq] at h
        subst r
        exact fanRule_linear dataArity k b
      | inr b => simp [-List.count_eq_one_of_mem, system] at h
    | inr a =>
      cases a with
      | inl e =>
        obtain ⟨n, e⟩ := e
        cases b with
        | inr b => simp [-List.count_eq_one_of_mem, system] at h
        | inl b =>
          cases b with
          | inl b => simp [-List.count_eq_one_of_mem, system] at h
          | inr m =>
            by_cases heq : n = m
            · subst m
              simp only [system, ↓reduceDIte, Option.some.injEq] at h
              subst r
              exact evalRule_linear dataArity e
            · simp [-List.count_eq_one_of_mem, system, heq] at h
      | inr f =>
        obtain ⟨f, k⟩ := f
        cases b with
        | inr b => simp [-List.count_eq_one_of_mem, system] at h
        | inl b =>
          cases b with
          | inr m => simp [-List.count_eq_one_of_mem, system] at h
          | inl b =>
            simp only [system, Option.map_eq_some_iff] at h
            obtain ⟨body, _, rfl⟩ := h
            exact callRule_linear dataArity f k b body

end Geb.InteractionNet.FirstOrder

end
