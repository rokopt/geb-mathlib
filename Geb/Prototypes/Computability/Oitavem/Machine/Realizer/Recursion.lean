/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Compile
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Loop
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Retained

set_option doc.verso true in
/-!
# Realizing recursion over generated inputs

The indexed loop streams concatenation recursion. Safe recursion retains only
the logarithmic prefix observable by its steps, then emits the complete final
step. Both constructions regenerate their virtual normal arguments and preserve
the caller's environment. The syntax recursor combines all constructor rules.

## Main statements

* {lit}`Expr.Realized.concatRec` closes realization under concatenation recursion.
* {lit}`Expr.Realized.safeRec` realizes the bounded-prefix implementation of safe recursion.
* {lit}`Expr.realized` realizes every expression over generated arguments.
* {lit}`Expr.computable_polytime_logspace` proves unary machine soundness.

## Implementation notes

All calls preserve the caller environment and clear their private tapes. The
machine contracts inherit {lit}`Classical.choice` from CSLib.

## Tags

logspace, function algebra, soundness, safe recursion, Turing machine
-/

set_option doc.verso true

namespace Geb.Oitavem

open Turing MultiTapeTM
open Geb.SizeBounded
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine
open Machine

public section

/-- A canonical binary query selects a suffix without storing the generated word. -/
@[expose] def Machine.Generator.dropCounter {m : ℕ}
    {Pre : List Bool → (Fin m → List Bool) → Prop}
    {W : List Bool → (Fin m → List Bool) → List Bool}
    (G : Generator m Pre W) (Q : Fin m) (N : ℕ → ℕ) (C : ℕ)
    (hq : ∀ input σ, Pre input σ →
      ∃ q, σ Q = counterWord q ∧ q ≤ N input.length)
    (hw : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n + 1).size ≤ C * (n.size + 1)) :
    Generator m Pre (fun input σ ↦ (W input σ).drop (counterValue (σ Q))) :=
  ((Generator.unaryCounter m Pre Q N hq).iterPred G N C (by
    intro input σ hp
    obtain ⟨q, he, hn⟩ := hq input σ hp
    simp only [List.length_replicate, he, counterValue_counterWord]
    exact max_le hn (hw input σ hp)) hsize).congr (by
      intro input σ _
      simp only [List.length_replicate])

/-- Select a generator by the first emitted digit, defaulting to false on empty output. -/
@[expose] def Machine.Generator.condBit {m : ℕ}
    {Pre : List Bool → (Fin m → List Bool) → Prop}
    {W : List Bool → (Fin m → List Bool) → List Bool}
    {U : Bool → List Bool → (Fin m → List Bool) → List Bool}
    (G : Generator m Pre W) (P : (b : Bool) → Generator m Pre (U b)) :
    Generator m Pre (fun input σ ↦ U ((W input σ).headD false) input σ) :=
  (G.last.numericPred.cond (fun b ↦ P (!b)) 2 (by
    intro input σ _
    refine (size_le_size (Nat.add_le_add_right
      (length_numericPred_le [(W input σ).headD false]) 1)).trans ?_
    exact (show (2 : ℕ).size ≤ 2 by decide).trans (by omega))).congr (by
    intro input σ _
    cases (W input σ).headD false <;> rfl)

/-- Concatenation recursion streams one indexed step digit per recursion digit,
then emits the base case, with a fixed reusable workspace. -/
theorem Expr.Realized.concatRec {n : ℕ} {g : Expr n 0} {h : Bool → Expr (n + 1) 0}
    (hg : g.Realized) (hh : ∀ b, (h b).Realized) : (Expr.concatRec g h).Realized := by
  intro m Pre X Y GX _ N hN hx _
  obtain ⟨C, hC⟩ := logarithmic_size_of_polyBounded hN
  let X' (i : Fin (n + 1)) (input : List Bool) (σ : Fin (m + 1) → List Bool) :=
    X i input (fun j ↦ σ j.castSucc)
  let G' (i : Fin (n + 1)) : Generator (m + 1) (QueryPre Pre N) (X' i) :=
    (GX i).rename Fin.castSucc (fun _ _ hp ↦ hp.1)
  let V input (σ : Fin (m + 1) → List Bool) :=
    (X' 0 input σ).drop (counterValue (σ (Fin.last m)))
  let GV : Generator (m + 1) (QueryPre Pre N) V :=
    (G' 0).dropCounter (Fin.last m) N C (fun _ _ hp ↦ hp.2)
      (fun input σ hp ↦ hx input _ hp.1 0) hC
  have hb (b : Bool) : Nonempty (Generator (m + 1) (QueryPre Pre N)
      (fun input σ ↦ (h b).eval
        (Fin.cons (V input σ).tail (fun i ↦ X' i.succ input σ)) Fin.elim0)) := by
    obtain ⟨P⟩ := hh b (m + 1) (QueryPre Pre N)
      (Fin.cons (fun input σ ↦ (V input σ).tail) (fun i ↦ X' i.succ))
      (fun i _ _ ↦ i.elim0) (Fin.cases GV.pred (fun i ↦ G' i.succ))
      (fun i ↦ i.elim0) N hN (by
        intro input σ hp
        refine Fin.cases ?_ (fun i ↦ hx input _ hp.1 i.succ)
        change (V input σ).tail.length ≤ N input.length
        simp only [V, List.length_tail, List.length_drop]
        exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (hx input _ hp.1 0)))
      (fun _ _ _ i ↦ i.elim0)
    refine ⟨P.congr ?_⟩
    intro input σ _
    congr 1
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  obtain ⟨P₀⟩ := hb false
  obtain ⟨P₁⟩ := hb true
  let P (b : Bool) : Generator (m + 1) (QueryPre Pre N)
      (fun input σ ↦ [((h b).eval
        (Fin.cons (V input σ).tail (fun i ↦ X' i.succ input σ)) Fin.elim0).headD false]) := by
    cases b
    · exact P₀.last
    · exact P₁.last
  let F input (σ : Fin m → List Bool) (j : ℕ) :=
    ((h ((X 0 input σ)[j]?.getD false)).eval
      (Fin.cons ((X 0 input σ).drop (j + 1)) (fun i ↦ X i.succ input σ)) Fin.elim0).headD false
  have hp : Nonempty (Generator (m + 1) (QueryPre Pre N)
      (fun input σ ↦ [F input (fun i ↦ σ i.castSucc) (counterValue (σ (Fin.last m)))])) := by
    refine ⟨(GV.condBit P).congr ?_⟩
    intro input σ _
    simp only [V, X', F, List.tail_drop, List.headD_eq_head?_getD, List.head?_drop]
  obtain ⟨P⟩ := hp
  let D input σ := concatDigits (fun b ↦ (h b).eval) (X 0 input σ)
    (fun i ↦ X i.succ input σ)
  let GD := (GX 0).indexed P D C (fun input σ hp ↦ hx input σ hp 0) hC
    (fun _ _ _ ↦ length_concatDigits ..) (by
      intro input σ _ j hj
      dsimp only [D] at hj ⊢
      rw [length_concatDigits] at hj
      simp only [F, getElem?_concatDigits, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some])
  obtain ⟨GB⟩ := hg m Pre (fun i ↦ X i.succ) (fun i _ _ ↦ i.elim0)
    (fun i ↦ GX i.succ) (fun i ↦ i.elim0) N hN
    (fun input σ hp i ↦ hx input σ hp i.succ) (fun _ _ _ i ↦ i.elim0)
  refine ⟨(GD.append GB).congr ?_⟩
  intro input σ _
  have hy : (fun i : Fin 0 ↦ Y i input σ) = Fin.elim0 := funext (fun i ↦ i.elim0)
  have hnil : (fun i : Fin 0 ↦ (i.elim0 : List Bool)) = Fin.elim0 :=
    funext (fun i ↦ i.elim0)
  simpa only [D, Expr.concatRec, Expr.eval_node, evalNode, Fin.tail_def, hy, hnil] using
    (concatRec_eq_concatDigits g.eval (fun b ↦ (h b).eval) (X 0 input σ)
      (fun i ↦ X i.succ input σ)).symm

/-- Safe recursion captures only the logarithmic prefix observable by its steps.
Its last step emits the full result, so polynomial outputs need no extra storage. -/
theorem Expr.Realized.safeRec {n : ℕ} {g : Expr n 0} {h : Bool → Expr (n + 1) 1}
    (hg : g.Realized) (hh : ∀ b, (h b).Realized) : (Expr.safeRec g h).Realized := by
  intro m Pre X Y GX _ N hN hx _
  obtain ⟨A, hA⟩ := Expr.recursionCutoff_le_log_of_polyBounded h hN
  obtain ⟨Mask, ⟨GM⟩, hmLower, D, hmSize⟩ := Generator.exists_prefixMask m Pre A
  obtain ⟨C, hC⟩ := logarithmic_size_of_polyBounded hN
  let M := Fin.last m
  let PreM := LengthPre Pre Mask
  let X' (i : Fin (n + 1)) (input : List Bool) (σ : Fin (m + 1) → List Bool) :=
    X i input (fun j ↦ σ j.castSucc)
  let G' (i : Fin (n + 1)) : Generator (m + 1) PreM (X' i) :=
    (GX i).rename Fin.castSucc (fun _ _ hp ↦ hp.1)
  have hx' input σ (hp : PreM input σ) i : (X' i input σ).length ≤ N input.length :=
    hx input _ hp.1 i
  have hmask input σ (hp : PreM input σ) : (σ M).length ≤ D * (input.length.size + 1) := by
    rw [hp.2, length_counterWord]
    exact (size_le_size (Nat.le_succ _)).trans (hmSize input _ hp.1)
  have hcut input σ (hp : PreM input σ) :
      Expr.recursionCutoff h (N input.length) ≤ (σ M).length := by
    rw [hp.2, length_counterWord]
    exact (hA input.length).trans (hmLower input _ hp.1)
  obtain ⟨GB⟩ := hg (m + 1) PreM (fun i ↦ X' i.succ) (fun i _ _ ↦ i.elim0)
    (fun i ↦ G' i.succ) (fun i ↦ i.elim0) N hN
    (fun input σ hp i ↦ hx' input σ hp i.succ) (fun _ _ _ i ↦ i.elim0)
  let StepPre := RetainedPre PreM M N
  let R : Fin (m + 1 + 2) := Fin.natAdd (m + 1) 0
  let Q : Fin (m + 1 + 2) := Fin.natAdd (m + 1) 1
  let X'' (i : Fin (n + 1)) (input : List Bool) (σ : Fin (m + 1 + 2) → List Bool) :=
    X' i input (fun j ↦ σ (j.castAdd 2))
  let G'' (i : Fin (n + 1)) : Generator (m + 1 + 2) StepPre (X'' i) :=
    (G' i).rename (Fin.castAdd 2) (fun _ _ hp ↦ hp.1)
  let V input (σ : Fin (m + 1 + 2) → List Bool) :=
    (X'' 0 input σ).drop (counterValue (σ Q))
  let GV : Generator (m + 1 + 2) StepPre V :=
    (G'' 0).dropCounter Q N C (fun _ _ hp ↦ hp.2.2)
      (fun input σ hp ↦ hx' input _ hp.1 0) hC
  let Bound (n : ℕ) := max (N n) (D * (n + 1))
  have hBound : IsPolyBounded Bound := isPolyBounded_max hN
    (isPolyBounded_mul (isPolyBounded_const D) isPolyBounded_succ)
  have hb (b : Bool) : Nonempty (Generator (m + 1 + 2) StepPre
      (fun input σ ↦ (h b).eval
        (Fin.cons (V input σ).tail (fun i ↦ X'' i.succ input σ)) ![σ R])) := by
    obtain ⟨P⟩ := hh b (m + 1 + 2) StepPre
      (Fin.cons (fun input σ ↦ (V input σ).tail) (fun i ↦ X'' i.succ))
      (fun _ _ σ ↦ σ R) (Fin.cases GV.pred (fun i ↦ G'' i.succ))
      (fun _ ↦ Generator.stored _ StepPre R) Bound hBound (by
        intro input σ hp
        refine Fin.cases ?_ (fun i ↦ (hx' input _ hp.1 i.succ).trans (Nat.le_max_left _ _))
        change (V input σ).tail.length ≤ Bound input.length
        simp only [V, List.length_tail, List.length_drop]
        exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans
          ((hx' input _ hp.1 0).trans (Nat.le_max_left _ _)))) (by
        intro input σ hp i
        exact hp.2.1.trans ((hmask input _ hp.1).trans
          ((Nat.mul_le_mul_left D (Nat.add_le_add_right (size_le_self _) 1)).trans
            (Nat.le_max_right _ _))))
    refine ⟨P.congr ?_⟩
    intro input σ _
    simp only [Matrix.cons_fin_one]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  obtain ⟨P₀⟩ := hb false
  obtain ⟨P₁⟩ := hb true
  let Ps (b : Bool) : Generator (m + 1 + 2) StepPre
      (fun input σ ↦ (h b).eval
        (Fin.cons (V input σ).tail (fun i ↦ X'' i.succ input σ)) ![σ R]) := by
    cases b
    · exact P₀
    · exact P₁
  let H input (σ : Fin (m + 1) → List Bool) (v : List Bool) (q : ℕ) :=
    (h ((X' 0 input σ)[q]?.getD false)).eval
      (Fin.cons ((X' 0 input σ).drop (q + 1)) (fun i ↦ X' i.succ input σ)) ![v]
  let P : Generator (m + 1 + 2) StepPre (fun input σ ↦
      H input (fun i ↦ σ (i.castAdd 2)) (σ R) (counterValue (σ Q))) :=
    (GV.condBit Ps).congr (by
      intro input σ _
      simp only [H, V, X'', List.tail_drop, List.headD_eq_head?_getD, List.head?_drop])
  let Value input σ := prefixLoop (σ M).length g.eval (fun b ↦ (h b).eval)
    (X' 0 input σ).tail (fun i ↦ X' i.succ input σ)
  let Out input σ := H input σ (Value input σ (X' 0 input σ).tail.length) 0
  let GR := (G' 0).pred.retained GB M P Value Out C
    (fun input σ hp ↦ by simpa only [List.length_tail] using
      (Nat.sub_le (X' 0 input σ).length 1).trans (hx' input σ hp 0)) hC
    (fun _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ prefixLoop_length_le ..) (by
      intro input σ hp j hj
      dsimp only [H, Value, prefixLoop]
      rw [List.getElem?_tail]
      have he : (X' 0 input σ).tail.length - (j + 1) + 1 =
          (X' 0 input σ).tail.length - j := by omega
      rw [he]
      rw [List.drop_tail])
    (fun _ _ _ ↦ rfl)
  let Branch (b : Bool) : Generator (m + 1) PreM (fun input σ ↦
      if b then g.eval (fun i ↦ X' i.succ input σ) Fin.elim0 else Out input σ) := by
    cases b
    · exact GR
    · exact GB
  have hfinal : Nonempty (Generator (m + 1) PreM (fun input σ ↦
      BellantoniCook.evalRec g.eval (h false).eval (h true).eval (X' 0 input σ)
        (fun i ↦ X' i.succ input σ) Fin.elim0)) := by
    refine ⟨((G' 0).cond Branch C (fun input σ hp ↦
      (size_le_size (Nat.add_le_add_right (hx' input σ hp 0) 1)).trans (hC _))).congr ?_⟩
    intro input σ hp
    have hobs (b : Bool) (v : List Bool) (hv : v.length ≤ N input.length) (r : List Bool) :
        (h b).eval (Fin.cons v (fun i ↦ X' i.succ input σ)) ![r] =
          (h b).eval (Fin.cons v (fun i ↦ X' i.succ input σ)) ![r.take (σ M).length] := by
      have hk : (h b).prefixCutoff (N input.length) ≤ (σ M).length := by
        apply le_trans _ (hcut input σ hp)
        cases b
        · exact Nat.le_max_left _ _
        · exact Nat.le_max_right _ _
      simpa only [Matrix.cons_fin_one] using (h b).eval_take_prefixCutoff
        (Fin.cons v (fun i ↦ X' i.succ input σ)) (N input.length)
        (Fin.cases hv (fun i ↦ hx' input σ hp i.succ)) ![r] hk
    cases hw : X' 0 input σ with
    | nil => simp only [List.isEmpty_nil, ↓reduceIte, BellantoniCook.evalRec]
    | cons b v =>
      have hv : v.length ≤ N input.length := by
        have := hx' input σ hp 0
        rw [hw, List.length_cons] at this
        omega
      simpa only [Out, H, Value, hw, List.isEmpty_cons, ↓reduceIte, List.tail_cons,
        List.getElem?_cons_zero, Option.getD_some, Nat.zero_add, List.drop_succ_cons,
        List.drop_zero, Bool.false_eq_true] using
        (evalRec_cons_prefixLoop (σ M).length (N input.length) g.eval (fun b ↦ (h b).eval)
          (fun i ↦ X' i.succ input σ) hobs b v hv).symm
  obtain ⟨GF⟩ := hfinal
  refine ⟨(GM.withLength
    (V := fun input σ ↦ BellantoniCook.evalRec g.eval (h false).eval (h true).eval
      (X 0 input σ) (fun i ↦ X i.succ input σ) Fin.elim0) GF D hmSize).congr ?_⟩
  intro input σ _
  have hy : (fun i : Fin 0 ↦ Y i input σ) = Fin.elim0 := funext (fun i ↦ i.elim0)
  simp only [Expr.safeRec, Expr.eval_node, evalNode, Fin.tail_def, hy]

/-- Every well-formed Logs expression admits substitution of polynomially bounded
generated arguments over a protected environment. -/
theorem Expr.realized {n s : ℕ} (e : Expr n s) : e.Realized := by
  refine Expr.induction (P := fun _ e ↦ e.Realized) ?_ e
  intro a c ih
  cases a with
  | initial p =>
    have hc : c = (fun i ↦ i.elim0) := funext (fun i ↦ i.elim0)
    rw [hc]
    exact Expr.Realized.initial p
  | comp n k safe =>
    have he : Expr.node (.comp n k safe) c =
        Expr.comp (safe := safe) (c (.inl ())) (fun i ↦ c (.inr i)) := by
      unfold Expr.comp
      congr 1
      funext i
      rcases i with ⟨⟩ | i <;> rfl
    rw [he]
    exact Expr.Realized.comp (ih (.inl ())) (fun i ↦ ih (.inr i))
  | safeRec n =>
    have he : Expr.node (.safeRec n) c =
        Expr.safeRec (c (.inl ())) (fun b ↦ c (.inr b)) := by
      unfold Expr.safeRec
      congr 1
      funext i
      rcases i with ⟨⟩ | i <;> rfl
    rw [he]
    exact Expr.Realized.safeRec (ih (.inl ())) (fun b ↦ ih (.inr b))
  | concatRec n =>
    have he : Expr.node (.concatRec n) c =
        Expr.concatRec (c (.inl ())) (fun b ↦ c (.inr b)) := by
      unfold Expr.concatRec
      congr 1
      funext i
      rcases i with ⟨⟩ | i <;> rfl
    rw [he]
    exact Expr.Realized.concatRec (ih (.inl ())) (fun b ↦ ih (.inr b))
  | logTransition n =>
    have he : Expr.node (.logTransition n) c = Expr.logTransition (c ()) := by
      unfold Expr.logTransition
      congr 1
    rw [he]
    exact Expr.Realized.logTransition (ih ())

/-- Direct machine soundness for Oitavem's Logs: every fixed unary expression has
one finite deterministic transducer with polynomial time and logarithmic work space. -/
theorem Expr.computable_polytime_logspace (e : Expr 1 0) :
    ∃ C d : ℕ, ComputableInTimeAndSpaceOfLength (fun w ↦ e.eval ![w] Fin.elim0)
      (.refl _) (.refl _) (fun n ↦ C * (n + 1) ^ d) (fun n ↦ C * (n.size + 1)) :=
  e.realized.computes

end

end Geb.Oitavem
