/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Expression
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Constructor dispatch and contextual calls

A named call inspects its principal constructor and transfers that constructor's fields,
followed by its further arguments, to the rule body's evaluator. No fields are inspected
or copied during this transfer. Contextual normalization of the body therefore supplies
contextual normalization of the call.

## Main statements

* {lit}`call_step` — a registered rule transfers closed arguments to its body evaluator.
* {lit}`calls_of_rewrite` — normalization of a rule body implies normalization of its call.

## Tags

interaction net, call, constructor dispatch, evaluation, normalization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- A registered constructor rule transfers the call's closed arguments to its evaluator. -/
theorem call_step (p : Program (φ := φ) dataArity) (f : φ) (a : δ)
    (vs : Fin (dataArity a) → Value dataArity) (args : List (Value dataArity))
    (body : Expr (φ := φ) dataArity (dataArity a + args.length))
    (h : p.rewrite f args.length a = some body) (out : ℕ) (result : Value dataArity)
    (c : Config (netArity dataArity)) :
    (system dataArity p).step (tasks [finishTask dataArity (.inr (f, args.length))
      (Fin.cases (Term.agent (.inl a) vs) args.get) out result] c) =
      some (tasks [evalTask dataArity body (Fin.addCases vs args.get) out result] c) := by
  apply System.step_cons
  simp only [finishTask, finish, Fin.cases_zero, Fin.cases_succ, Value.embed_agent]
  simp only [System.contract, Term.agent, system, app, h, Option.map_some]
  change some { c with
    equations := (callRule dataArity f args.length a body).instantiate c.nextName
      (Fin.cases (Term.var out) (fun i ↦ Value.embed dataArity (args.get i)))
      (fun i ↦ Value.embed dataArity (vs i)) ++ c.equations
    nextName := c.nextName + (callRule dataArity f args.length a body).fresh } = _
  simp only [callRule, Rule.instantiate, List.map_cons, List.map_nil, List.singleton_append,
    Term.subst_agent, Term.subst_var, Sum.elim_inl, Fin.cases_zero,
    Nat.add_zero, tasks, evalTask]
  congr 1
  congr 1
  congr 1
  apply Prod.ext
  · rfl
  · apply congrArg (Term.agent (env dataArity (dataArity a + args.length)))
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.addCases_left, Term.subst_var, Sum.elim_inl, Sum.elim_inr]
    · simp only [Fin.addCases_right, Term.subst_var, Sum.elim_inl, Fin.cases_succ]

/-- A constructor-dispatch call normalizes whenever its selected rule body does. -/
theorem calls_of_rewrite (p : Program (φ := φ) dataArity) (f : φ) (a : δ)
    (vs : Fin (dataArity a) → Value dataArity) (args : List (Value dataArity))
    (body : Expr (φ := φ) dataArity (dataArity a + args.length))
    (h : p.rewrite f args.length a = some body) (result : Value dataArity)
    (hb : Evaluates dataArity p body (Fin.addCases vs args.get) result) :
    Calls dataArity p f (Term.agent (.inl a) vs) args result := by
  intro out c hc hn hx
  obtain ⟨N, hN, hs⟩ := hb out c hc
    (by simpa only [evalTask, finishTask] using hn)
    (by simpa only [evalTask, finishTask] using hx)
  exact ⟨N, hN, System.reaches_trans _
    (System.reaches_of_step _ (call_step dataArity p f a vs args body h out result c)) hs⟩

end Geb.InteractionNet.FirstOrder

end
