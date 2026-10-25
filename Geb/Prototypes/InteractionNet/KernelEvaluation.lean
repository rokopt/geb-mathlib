/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelApplication
import Geb.Prototypes.InteractionNet.KernelControl
import Geb.Prototypes.InteractionNet.KernelPrimitives
import Geb.Prototypes.InteractionNet.KernelRules
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Simulation of kernel source evaluation

The source compiler preserves every successful evaluator step in represented environments.
The proof follows source syntax, using the preceding evaluator level for function
application and global references. Captured environments and conditional thunks retain
their source paths through compilation.

## Tags

interaction net, kernel, compiler, evaluation, simulation, environment
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Kernel

open Geb.Kernel FirstOrder

/-- A successful lookup in a represented environment has a represented expression entry. -/
theorem evaluatesTo_lookup (P : List Tree) {n : ℕ} (ρ : Fin n → Value dataArity)
    (es : List (E n)) (env : List Tree) (h : List.Forall₂ (EvaluatesTo P ρ) es env)
    (i : ℕ) (v : Tree) (hv : env[i]? = some v) :
    ∃ e, es[i]? = some e ∧ EvaluatesTo P ρ e v := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hv
  have hi' : i < es.length := by simpa only [h.length_eq] using hi
  exact ⟨es[i], List.getElem?_eq_getElem hi', h.get hi' hi⟩

private theorem projection_simulation (P : List Tree) (second : Bool) (v result : Tree)
    (h : (match v.label, v.children with
      | Label.pair, [a, b] => some (if second then b else a)
      | _, _ => none) = some result) : CallsTo P (.project second) v [] result := by
  split at h
  next a b hl hcs =>
    obtain rfl := Option.some.inj h
    have hv : v = Eval.Val.pair a b :=
      (RoseTree.node_eq_iff.mpr ⟨hl.symm, hcs.symm⟩).symm
    rw [hv]
    exact callsTo_project P second a b
  next => cases h

/-- One source-evaluation layer is simulated when references and applications at the
preceding layer are simulated. Structural child evaluation remains in the current layer. -/
theorem evaluation_step_simulation (P : List Tree) (p : Eval.Fns)
    (hev : EvaluationSimulation P p.1) (hap : ApplicationSimulation P p.2) :
    EvaluationSimulation P (fun env t ↦ RoseTree.para (Eval.evStep P p) t env) := by
  intro env t result h n ρ site es hen
  refine RoseTree.ind (P := fun t ↦ ∀ env result,
    RoseTree.para (Eval.evStep P p) t env = some result →
    ∀ {n : ℕ} (ρ : Fin n → Value dataArity) (site : List ℕ) (es : List (E n)),
      List.Forall₂ (EvaluatesTo P ρ) es env →
      ∃ e, compileAt t site es = some e ∧ EvaluatesTo P ρ e result)
    (fun l ts ih env result h n ρ site es hen ↦ ?_) t env result h ρ site es hen
  rw [RoseTree.para_node] at h
  generalize hF : RoseTree.para (Eval.evStep P p) = F at h
  unfold Eval.evStep at h
  split at h <;> subst hF
  case h_1 i _ heq =>
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain ⟨e, he, hr⟩ := evaluatesTo_lookup P ρ es env hen i.label result h
    refine ⟨e, ?_, hr⟩
    unfold compileAt
    rw [RoseTree.para_node]
    exact he
  case h_2 A _ b _ heq =>
    obtain ⟨rfl, _, _⟩ := Eval.map_pair_eq_two heq
    obtain rfl := Option.some.inj h
    refine ⟨con (.closure (site ++ [1]) A b es.length) es rfl, ?_,
      evaluatesTo_closure P ρ (site ++ [1]) A b es env hen⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_3 cf f cx x heq =>
    obtain ⟨rfl, rfl, rfl⟩ := Eval.map_pair_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨vf, hvf, vx, hvx, hr⟩ := h
    obtain ⟨ef, hf, hrf⟩ := ih cf (by simp) env vf hvf ρ (site ++ [0]) es hen
    obtain ⟨ex, hx, hrx⟩ := ih cx (by simp) env vx hvx ρ (site ++ [1]) es hen
    refine ⟨apply ef ex, ?_, evaluatesTo_apply P ρ ef ex vf vx result hrf hrx (hap _ _ _ hr)⟩
    unfold compileAt
    rw [RoseTree.para_node]
    change (do
      let f ← compileAt cf (site ++ [0]) es
      let x ← compileAt cx (site ++ [1]) es
      return apply f x) = _
    simp only [hf, hx, Option.bind_eq_bind, Option.bind_some, pure]
  case h_4 heq =>
    obtain rfl := List.map_eq_nil_iff.mp heq
    obtain rfl := Option.some.inj h
    refine ⟨unit, ?_, evaluatesTo_unit P ρ⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_5 ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl⟩ := Eval.map_pair_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨va, hva, vb, hvb, rfl⟩ := h
    obtain ⟨ea, ha, hra⟩ := ih ca (by simp) env va hva ρ (site ++ [0]) es hen
    obtain ⟨eb, hb, hrb⟩ := ih cb (by simp) env vb hvb ρ (site ++ [1]) es hen
    refine ⟨pair ea eb, ?_, evaluatesTo_pair P ρ ea eb va vb hra hrb⟩
    unfold compileAt
    rw [RoseTree.para_node]
    change (do
      let a ← compileAt ca (site ++ [0]) es
      let b ← compileAt cb (site ++ [1]) es
      return pair a b) = _
    simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, pure]
  case h_6 cp fp heq =>
    obtain ⟨rfl, rfl⟩ := Eval.map_pair_eq_one heq
    obtain ⟨vp, hvp, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, he, hre⟩ := ih cp (by simp) env vp hvp ρ (site ++ [0]) es hen
    refine ⟨call (.project false) e, ?_,
      evaluatesTo_call P ρ (.project false) e [] vp result [] hre .nil
        (projection_simulation P false vp result hr)⟩
    unfold compileAt
    rw [RoseTree.para_node]
    change (compileAt cp (site ++ [0]) es).map (call (.project false) ·) = _
    simp only [he, Option.map_some]
  case h_7 cp fp heq =>
    obtain ⟨rfl, rfl⟩ := Eval.map_pair_eq_one heq
    obtain ⟨vp, hvp, hr⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, he, hre⟩ := ih cp (by simp) env vp hvp ρ (site ++ [0]) es hen
    refine ⟨call (.project true) e, ?_,
      evaluatesTo_call P ρ (.project true) e [] vp result [] hre .nil
        (projection_simulation P true vp result hr)⟩
    unfold compileAt
    rw [RoseTree.para_node]
    change (compileAt cp (site ++ [0]) es).map (call (.project true) ·) = _
    simp only [he, Option.map_some]
  case h_8 t _ heq =>
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain rfl := Option.some.inj h
    refine ⟨literal t, ?_, evaluatesTo_literal P ρ t⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_9 cc c ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Eval.map_pair_eq_three heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨vc, hvc, t, ht, hr⟩ := h
    obtain rfl := eq_quote_of_unquote vc t ht
    obtain ⟨ec, hc, hrc⟩ := ih cc (by simp) env (Eval.Val.quote t) hvc ρ (site ++ [0]) es hen
    have hb : ∀ {m : ℕ} (σ : Fin m → Value dataArity) (fs : List (E m)),
        List.Forall₂ (EvaluatesTo P σ) fs env →
        ∃ e, compileAt (if t.label = 0 then cb else ca)
          (if t.label = 0 then site ++ [2] else site ++ [1]) fs = some e ∧
            EvaluatesTo P σ e result := by
      intro m σ fs hfs
      by_cases ht : t.label = 0
      · have he : RoseTree.para (Eval.evStep P p) cb env = some result := by simpa [ht] using hr
        simpa only [ht, ↓reduceIte] using ih cb (by simp) env result he σ (site ++ [2]) fs hfs
      · have he : RoseTree.para (Eval.evStep P p) ca env = some result := by simpa [ht] using hr
        simpa only [ht, ↓reduceIte] using ih ca (by simp) env result he σ (site ++ [1]) fs hfs
    refine ⟨call .choose ec [con (.thunk (site ++ [1]) ca es.length) es rfl,
      con (.thunk (site ++ [2]) cb es.length) es rfl], ?_,
      evaluatesTo_choose_thunks P ρ ec t hrc es env hen (site ++ [1]) (site ++ [2])
        ca cb result hb⟩
    unfold compileAt
    rw [RoseTree.para_node]
    change (do let e ← compileAt cc (site ++ [0]) es
               return call .choose e [con (.thunk (site ++ [1]) ca es.length) es rfl,
                 con (.thunk (site ++ [2]) cb es.length) es rfl]) = _
    simp only [hc, Option.bind_eq_bind, Option.bind_some, pure]
  case h_10 A _ heq =>
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain rfl := Option.some.inj h
    refine ⟨nil A, ?_, evaluatesTo_nil P ρ A⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_11 cx x cxs xs heq =>
    obtain ⟨rfl, rfl, rfl⟩ := Eval.map_pair_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨vx, hvx, vxs, hvxs, rfl⟩ := h
    obtain ⟨ex, hx, hrx⟩ := ih cx (by simp) env vx hvx ρ (site ++ [0]) es hen
    obtain ⟨exs, hxs, hrxs⟩ := ih cxs (by simp) env vxs hvxs ρ (site ++ [1]) es hen
    refine ⟨cons ex exs, ?_, evaluatesTo_cons P ρ ex exs vx vxs hrx hrxs⟩
    unfold compileAt
    rw [RoseTree.para_node]
    change (do
      let x ← compileAt cx (site ++ [0]) es
      let xs ← compileAt cxs (site ++ [1]) es
      return cons x xs) = _
    simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, pure]
  case h_12 A _ heq =>
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain rfl := Option.some.inj h
    refine ⟨con (.partialApp site (RoseTree.node Label.fold [A]) 0) [] rfl, ?_,
      evaluatesTo_partial P ρ site (RoseTree.node Label.fold [A])
        (by simp [ConstantHead]) [] [] .nil⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_13 A _ heq =>
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain rfl := Option.some.inj h
    refine ⟨con (.partialApp site (RoseTree.node Label.para [A]) 0) [] rfl, ?_,
      evaluatesTo_partial P ρ site (RoseTree.node Label.para [A])
        (by simp [ConstantHead]) [] [] .nil⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_14 A _ heq =>
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain rfl := Option.some.inj h
    refine ⟨con (.partialApp site (RoseTree.node Label.iter [A]) 0) [] rfl, ?_,
      evaluatesTo_partial P ρ site (RoseTree.node Label.iter [A])
        (by simp [ConstantHead]) [] [] .nil⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_15 A _ B _ heq =>
    obtain ⟨rfl, _, _⟩ := Eval.map_pair_eq_two heq
    obtain rfl := Option.some.inj h
    refine ⟨con (.partialApp site (RoseTree.node Label.foldr [A, B]) 0) [] rfl, ?_,
      evaluatesTo_partial P ρ site (RoseTree.node Label.foldr [A, B])
        (by simp [ConstantHead]) [] [] .nil⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_16 A _ B _ heq =>
    obtain ⟨rfl, _, _⟩ := Eval.map_pair_eq_two heq
    obtain rfl := Option.some.inj h
    refine ⟨con (.partialApp site (RoseTree.node Label.lcase [A, B]) 0) [] rfl, ?_,
      evaluatesTo_partial P ρ site (RoseTree.node Label.lcase [A, B])
        (by simp [ConstantHead]) [] [] .nil⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_17 k _ heq =>
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain rfl := Option.some.inj h
    refine ⟨con (.partialApp site (RoseTree.node Label.prim [leaf k.label]) 0) [] rfl, ?_,
      evaluatesTo_partial P ρ site (RoseTree.node Label.prim [leaf k.label])
        (by simp [ConstantHead]) [] [] .nil⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_18 i _ heq =>
    obtain ⟨rfl, _⟩ := Eval.map_pair_eq_one heq
    obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp h
    have hcall := callsTo_reference P i.label t result ht
      (fun σ ↦ hev [] t result hr σ [i.label + 1] [] .nil)
    refine ⟨call (.reference i.label) unit, ?_,
      evaluatesTo_call P ρ (.reference i.label) unit [] Eval.Val.unit result []
        (evaluatesTo_unit P ρ) .nil hcall⟩
    unfold compileAt
    rw [RoseTree.para_node]
    rfl
  case h_19 => cases h

end Geb.InteractionNet.Kernel

end
