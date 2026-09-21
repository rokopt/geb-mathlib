/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Truncation
public import Geb.Prototypes.Computability.Oitavem.Length
public import Geb.Prototypes.Computability.Oitavem.Derived
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Safe recursion with a logarithmic retained state

The safe-input truncation lemma of {cite}`Oitavem2010` permits replacing a
recursive value by a bounded numerical state between steps. Its bound is
polynomial in the normal input lengths, so its binary representation is
logarithmic. Alternatively, the indexed loop can retain an output prefix directly.
Both representations are proved correct.

## Main definitions

* {lit}`cappedRank` computes a truncated enumeration index with saturated arithmetic.
* {lit}`cappedRec` keeps only that index between safe-recursion steps.
* {lit}`prefixLoop` traverses the input by an index, retaining only an output prefix.
* {lit}`Expr.prefixCutoff` computes the required prefix length from the syntax.
* {lit}`Expr.recursionCutoff` takes a common cutoff for both recursion branches.

## Main statements

* {lit}`cappedRank_eq` identifies saturated arithmetic with truncation of the full index.
* {lit}`cappedRank_take_size` needs only logarithmically many output digits.
* {lit}`Expr.exists_uniform_truncation` gives a polynomial cutoff from normal lengths.
* {lit}`Expr.exists_logarithmic_prefix` replaces safe words by logarithmic prefixes.
* {lit}`cappedRec_correct` proves the retained state is the capped recursive result.
* {lit}`cappedRec_length_le` bounds the state's binary representation.
* {lit}`prefixLoop_eq` verifies the indexed loop under the prefix observation property.
* {lit}`Expr.exists_logarithmic_loop` supplies that property for every safe recursion.
* {lit}`Expr.eval_take_prefixCutoff` verifies the executable prefix cutoff.
* {lit}`Expr.eval_safeRec_cons_prefixCutoff` uses that cutoff in the indexed loop.

## Implementation notes

These are denotational and representation theorems. They do not bound the memory
used by Lean's evaluator or establish a Turing-machine time or space bound for
the subcalls. A machine must compute the truncated result without storing the
full output of each subcall.

## References

* {cite}`Oitavem2010`, Lemma 3.3 and Theorem 3.4.

## Tags

logspace, safe recursion, saturated arithmetic, binary state
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Oitavem

open BellantoniCook (Sem)
open Geb.SizeBounded (IsPolyBounded)

/-- The step digits of concatenation recursion, in their final output order. -/
def concatDigits {n : ℕ} (h : Bool → Sem (n + 1, 0)) :
    List Bool → (Fin n → List Bool) → List Bool :=
  List.rec (fun _ ↦ []) fun b w ih x ↦ (h b (Fin.cons w x) Fin.elim0).headD false :: ih x

/-- Concatenation recursion contributes exactly one step digit per input digit. -/
theorem length_concatDigits {n : ℕ} (h : Bool → Sem (n + 1, 0))
    (w : List Bool) (x : Fin n → List Bool) : (concatDigits h w x).length = w.length := by
  revert w
  refine List.rec ?_ ?_
  · rfl
  · intro b w ih
    exact congrArg Nat.succ ih

/-- Each step digit uses the suffix following its corresponding input digit. -/
theorem getElem?_concatDigits {n : ℕ} (h : Bool → Sem (n + 1, 0))
    (w : List Bool) (x : Fin n → List Bool) (j : ℕ) :
    (concatDigits h w x)[j]? =
      (w[j]?).map (fun b ↦ (h b (Fin.cons (w.drop (j + 1)) x) Fin.elim0).headD false) := by
  revert w j
  refine List.rec ?_ ?_
  · intro j
    rfl
  · intro b w ih j
    cases j with
    | zero => rfl
    | succ j => exact ih j

/-- Concatenation recursion streams its indexed step digits before its base output. -/
theorem concatRec_eq_concatDigits {n : ℕ} (g : Sem (n, 0)) (h : Bool → Sem (n + 1, 0))
    (w : List Bool) (x : Fin n → List Bool) :
    concatRec g h w x Fin.elim0 = concatDigits h w x ++ g x Fin.elim0 := by
  revert w
  refine List.rec ?_ ?_
  · rfl
  · intro b w ih
    simpa only [concatRec, concatDigits, List.cons_append] using congrArg
        ((h b (Fin.cons w x) Fin.elim0).headD false :: ·) ih

/-- Decode an index with saturation after each digit, never retaining a value above the cap. -/
def cappedRank (B : ℕ) : List Bool → ℕ :=
  List.foldr (fun b v ↦ min (2 * v + b.toNat + 1) B) 0

/-- Digitwise saturation agrees with truncating the complete enumeration index. -/
theorem cappedRank_eq (B : ℕ) (w : List Bool) : cappedRank B w = min (rank w) B := by
  apply List.rec (motive := fun w ↦ cappedRank B w = min (rank w) B) ?_ ?_ w
  · simp [cappedRank]
  · intro b v ih
    change min (2 * cappedRank B v + b.toNat + 1) B = min (rank (b :: v)) B
    rw [ih, rank_cons]
    omega

/-- Every retained index is at most its cap. -/
theorem cappedRank_le (B : ℕ) (w : List Bool) : cappedRank B w ≤ B := by
  rw [cappedRank_eq]
  exact Nat.min_le_right _ _

/-- The first binary-size-of-cap digits suffice: any longer word already saturates.
The list order is least significant digit first, so these are the first emitted digits. -/
theorem cappedRank_take_size (B : ℕ) (w : List Bool) :
    cappedRank B (w.take B.size) = cappedRank B w := by
  by_cases hw : w.length ≤ B.size
  · rw [List.take_of_length_le hw]
  · have ht : (w.take B.size).length = B.size := by simp; omega
    have hpow := pow_length_le_rank_add_one (w.take B.size)
    rw [ht] at hpow
    have hB := Geb.BitTree.Counter.lt_pow_size B
    have hcap : B ≤ rank (w.take B.size) := by omega
    rw [cappedRank_eq, cappedRank_eq, Nat.min_eq_right hcap,
      Nat.min_eq_right (hcap.trans (rank_take_le w B.size))]

/-- Any longer prefix also suffices to decode the capped numerical value. -/
theorem cappedRank_take {B k : ℕ} (hk : B.size ≤ k) (w : List Bool) :
    cappedRank B (w.take k) = cappedRank B w := by
  rw [← cappedRank_take_size B (w.take k), List.take_take, Nat.min_eq_left hk,
    cappedRank_take_size]

/-- A truncation property remains true with any larger pointwise cutoff. -/
theorem Truncates.mono {n s : ℕ} {f : Sem (n, s)} {a : (Fin n → List Bool) → ℕ}
    (hf : Truncates f a) (x : Fin n → List Bool) (B : ℕ) (hB : a x ≤ B)
    (y : Fin s → List Bool) :
    f x y = f x (fun j ↦ unrank (cappedRank B (y j))) := by
  rw [hf x y, hf x (fun j ↦ unrank (cappedRank B (y j)))]
  congr 1
  funext j
  simp only [rank_unrank, cappedRank_eq]
  congr 1
  omega

/-- A single polynomial in normal lengths suffices to truncate every safe input. -/
theorem Expr.exists_uniform_truncation {n s : ℕ} (e : Expr n s) :
    ∃ p : ℕ → ℕ, IsPolyBounded p ∧ ∀ x m, (∀ j, (x j).length ≤ m) → ∀ y,
      e.eval x y = e.eval x (fun j ↦ unrank (cappedRank (p m) (y j))) := by
  obtain ⟨b, hb⟩ := e.exists_truncation
  exact ⟨lengthPoly b.1.1, lengthPoly_isPolyBounded b.1.1,
    fun x m hx y ↦ hb.mono x _ (b.length_le x Fin.elim0 m hx) y⟩

/-- Safe recursion retaining only the capped numerical value of each recursive result. -/
def cappedRec {n : ℕ} (B : ℕ) (g : Sem (n, 0)) (h : Bool → Sem (n + 1, 1)) :
    List Bool → (Fin n → List Bool) → ℕ :=
  List.rec (fun x ↦ cappedRank B (g x Fin.elim0)) fun b v ih x ↦
    cappedRank B (h b (Fin.cons v x) ![unrank (ih x)])

/-- A retained recursion state is within its cap after every step. -/
theorem cappedRec_le {n : ℕ} (B : ℕ) (g : Sem (n, 0)) (h : Bool → Sem (n + 1, 1))
    (w : List Bool) (x : Fin n → List Bool) : cappedRec B g h w x ≤ B := by
  cases w with
  | nil => exact cappedRank_le _ _
  | cons b v => exact cappedRank_le _ _

/-- The retained state needs no more digits than the binary size of the cap plus one. -/
theorem cappedRec_length_le {n : ℕ} (B : ℕ) (g : Sem (n, 0)) (h : Bool → Sem (n + 1, 1))
    (w : List Bool) (x : Fin n → List Bool) :
    (unrank (cappedRec B g h w x)).length ≤ (B + 1).size :=
  length_unrank_le (cappedRec_le B g h w x)

/-- If every step observes only the capped safe value, the capped evaluator agrees
with ordinary safe recursion, at every prefix within the input-length bound. -/
theorem cappedRec_correct {n : ℕ} (B N : ℕ) (g : Sem (n, 0))
    (h : Bool → Sem (n + 1, 1)) (x : Fin n → List Bool)
    (hh : ∀ b v, v.length ≤ N → ∀ r,
      h b (Fin.cons v x) ![r] = h b (Fin.cons v x) ![unrank (cappedRank B r)])
    (w : List Bool) (hw : w.length ≤ N) :
    cappedRec B g h w x =
      cappedRank B (BellantoniCook.evalRec g (h false) (h true) w x Fin.elim0) := by
  apply List.rec (motive := fun w ↦ w.length ≤ N → cappedRec B g h w x =
    cappedRank B (BellantoniCook.evalRec g (h false) (h true) w x Fin.elim0)) ?_ ?_ w hw
  · intro _
    rfl
  · intro b v ih hv
    have hv' : v.length ≤ N := by simp only [List.length_cons] at hv; omega
    change cappedRank B (h b (Fin.cons v x) ![unrank (cappedRec B g h v x)]) = _
    rw [ih hv']
    cases b <;> exact congrArg (cappedRank B) (hh _ v hv' _).symm

/-- The last step may emit its entire answer from the capped penultimate state.
Only intermediate recursive results need to be truncated. -/
theorem evalRec_cons_capped {n : ℕ} (B N : ℕ) (g : Sem (n, 0))
    (h : Bool → Sem (n + 1, 1)) (x : Fin n → List Bool)
    (hh : ∀ b v, v.length ≤ N → ∀ r,
      h b (Fin.cons v x) ![r] = h b (Fin.cons v x) ![unrank (cappedRank B r)])
    (b : Bool) (v : List Bool) (hv : v.length ≤ N) :
    BellantoniCook.evalRec g (h false) (h true) (b :: v) x Fin.elim0 =
      h b (Fin.cons v x) ![unrank (cappedRec B g h v x)] := by
  rw [cappedRec_correct B N g h x hh v hv]
  cases b <;> exact hh _ v hv _

/-- Polynomially bounded numerical values have logarithmic binary size. -/
theorem logarithmic_size_of_polyBounded {p : ℕ → ℕ} (hp : IsPolyBounded p) :
    ∃ C : ℕ, ∀ m, (p m + 1).size ≤ C * (m.size + 1) := by
  obtain ⟨c, d, hp⟩ := hp
  refine ⟨c.size + d + 1, fun m ↦ ?_⟩
  have hc := Geb.BitTree.Counter.lt_pow_size c
  have hm := Geb.BitTree.Counter.lt_pow_size m
  have hpow : c * (m + 1) ^ d < 2 ^ (c.size + m.size * d) := by
    calc
      c * (m + 1) ^ d < 2 ^ c.size * (m + 1) ^ d :=
        Nat.mul_lt_mul_of_pos_right hc (Nat.pow_pos (by omega))
      _ ≤ 2 ^ c.size * (2 ^ m.size) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d)
      _ = 2 ^ (c.size + m.size * d) := by rw [Nat.pow_add, Nat.pow_mul]
  have hpm : p m + 1 < 2 ^ (c.size + m.size * d + 1) := by
    have hp' := hp m
    have hpos := Nat.two_pow_pos (c.size + m.size * d)
    rw [Nat.pow_succ]
    omega
  have hs := Geb.BitTree.Counter.size_le_of_lt_pow _ _ hpm
  have hd : m.size * d ≤ (c.size + d + 1) * m.size := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_succ]
  omega

/-- The power of two selected by binary size is at most twice the successor. -/
theorem pow_size_le (n : ℕ) : 2 ^ n.size ≤ 2 * (n + 1) := by
  by_cases hs : n.size = 0
  · simp only [hs, Nat.pow_zero]
    omega
  · have hl : 2 ^ (n.size - 1) ≤ n := by
      by_cases h : n < 2 ^ (n.size - 1)
      · have := Geb.BitTree.Counter.size_le_of_lt_pow _ _ h
        omega
      · omega
    have he : n.size = (n.size - 1) + 1 := by omega
    rw [he, Nat.pow_succ]
    omega

/-- Exponentiating a logarithmic binary-size bound gives a polynomial bound. -/
theorem isPolyBounded_pow_size (a : ℕ) :
    IsPolyBounded (fun n ↦ 2 ^ (a * (n.size + 1))) := by
  refine ⟨4 ^ a, a, fun n ↦ ?_⟩
  have h : 2 ^ (n.size + 1) ≤ 4 * (n + 1) := by
    rw [Nat.pow_succ]
    have := pow_size_le n
    omega
  calc
    2 ^ (a * (n.size + 1)) = (2 ^ (n.size + 1)) ^ a := by
      rw [← Nat.pow_mul, Nat.mul_comm a]
    _ ≤ (4 * (n + 1)) ^ a := Nat.pow_le_pow_left h a
    _ = 4 ^ a * (n + 1) ^ a := Nat.mul_pow _ _ _

/-- An executable safe-input prefix length, computed from the inferred polynomial
bound on the truncation expression. -/
def Expr.prefixCutoff {n s : ℕ} (e : Expr n s) (N : ℕ) : ℕ :=
  (lengthPoly e.truncationBound.1.1 N).size

/-- Every prefix at least as long as the inferred cutoff preserves the result. -/
theorem Expr.eval_take_prefixCutoff {n s : ℕ} (e : Expr n s)
    (x : Fin n → List Bool) (N : ℕ) (hx : ∀ j, (x j).length ≤ N)
    (y : Fin s → List Bool) {k : ℕ} (hk : e.prefixCutoff N ≤ k) :
    e.eval x y = e.eval x (fun j ↦ (y j).take k) := by
  have he := e.truncates_truncationBound.mono x (lengthPoly e.truncationBound.1.1 N)
    (e.truncationBound.length_le x Fin.elim0 N hx)
  rw [he y, he (fun j ↦ (y j).take k)]
  simp only [cappedRank_take hk]

/-- The computed cutoff is logarithmic even when the normal arguments themselves
have lengths bounded by a polynomial in the physical input length. -/
theorem Expr.prefixCutoff_le_log_of_polyBounded {n s : ℕ} (e : Expr n s)
    {p : ℕ → ℕ} (hp : IsPolyBounded p) :
    ∃ C : ℕ, ∀ m, e.prefixCutoff (p m) ≤ C * (m.size + 1) := by
  obtain ⟨C, hC⟩ := logarithmic_size_of_polyBounded
    (isPolyBounded_comp (lengthPoly_isPolyBounded e.truncationBound.1.1) hp)
  exact ⟨C, fun m ↦ (Geb.BitTree.Counter.size_mono (Nat.le_succ _)).trans (hC m)⟩

/-- A safe argument can be replaced by its first logarithmically many digits.
Thus a streamed recursive output need retain only that prefix, including when the
full output is polynomially long. -/
theorem Expr.exists_logarithmic_prefix {n s : ℕ} (e : Expr n s) :
    ∃ C : ℕ, ∀ x N, (∀ j, (x j).length ≤ N) → ∀ y,
      e.eval x y = e.eval x (fun j ↦ (y j).take (C * (N.size + 1))) := by
  obtain ⟨C, hC⟩ := e.prefixCutoff_le_log_of_polyBounded Geb.SizeBounded.isPolyBounded_id
  exact ⟨C, fun x N hx y ↦ e.eval_take_prefixCutoff x N hx y (hC N)⟩

/-- An indexed recursion loop retaining only the first k emitted digits of each
subcall. A transducer can collect these digits directly, without numerical decoding. -/
def prefixLoop {n : ℕ} (k : ℕ) (g : Sem (n, 0)) (h : Bool → Sem (n + 1, 1))
    (w : List Bool) (x : Fin n → List Bool) : ℕ → List Bool :=
  Nat.rec ((g x Fin.elim0).take k) fun j r ↦
    (h (w[w.length - (j + 1)]?.getD false)
      (Fin.cons (w.drop (w.length - j)) x) ![r]).take k

/-- The retained prefix has at most k digits after every iteration. -/
theorem prefixLoop_length_le {n : ℕ} (k : ℕ) (g : Sem (n, 0))
    (h : Bool → Sem (n + 1, 1)) (w : List Bool) (x : Fin n → List Bool) (t : ℕ) :
    (prefixLoop k g h w x t).length ≤ k := by
  cases t <;> exact List.length_take_le _ _

/-- The length example's retained value after processing {lit}`t` digits is {lit}`unrank t`.
A cutoff large enough for the final numerical length also suffices at every earlier step. -/
theorem prefixLoop_lengthByRec (K : ℕ) (w : List Bool)
    (hK : (unrank w.length).length ≤ K) (t : ℕ) (ht : t ≤ w.length) :
    prefixLoop K (Expr.initial (.zero 0)).eval (fun _ ↦ lengthByRecStep.eval)
      w Fin.elim0 t = unrank t := by
  revert t
  refine Nat.rec ?_ ?_
  · intro ht
    simp [prefixLoop, Expr.eval_initial, Initial.eval, unrank_zero]
  · intro j ih ht
    change (lengthByRecStep.eval (Fin.cons (w.drop (w.length - j)) Fin.elim0)
      ![prefixLoop K (Expr.initial (.zero 0)).eval (fun _ ↦ lengthByRecStep.eval)
        w Fin.elim0 j]).take K = unrank (j + 1)
    rw [ih (by omega)]
    change (lengthByRecStep.eval ![w.drop (w.length - j)] ![unrank j]).take K = _
    rw [eval_lengthByRecStep, rank_unrank, List.length_drop,
      Nat.sub_sub_self (by omega : j ≤ w.length), Nat.min_self]
    exact List.take_of_length_le ((length_unrank_mono ht).trans hK)

/-- If steps cannot distinguish a value from its k-digit prefix, the loop retains
exactly the prefix of the recursive value for the digits processed so far. -/
theorem prefixLoop_eq {n : ℕ} (k N : ℕ) (g : Sem (n, 0))
    (h : Bool → Sem (n + 1, 1)) (x : Fin n → List Bool)
    (hh : ∀ b v, v.length ≤ N → ∀ r,
      h b (Fin.cons v x) ![r] = h b (Fin.cons v x) ![r.take k])
    (w : List Bool) (hw : w.length ≤ N) (t : ℕ) (ht : t ≤ w.length) :
    prefixLoop k g h w x t =
      (BellantoniCook.evalRec g (h false) (h true)
        (w.drop (w.length - t)) x Fin.elim0).take k := by
  apply Nat.rec (motive := fun t ↦ t ≤ w.length → prefixLoop k g h w x t =
    (BellantoniCook.evalRec g (h false) (h true)
      (w.drop (w.length - t)) x Fin.elim0).take k) ?_ ?_ t ht
  · intro _
    simp [prefixLoop, BellantoniCook.evalRec]
  · intro j ih hj
    have hidx : w.length - (j + 1) < w.length := by omega
    have hnext : w.length - (j + 1) + 1 = w.length - j := by omega
    have hd := List.drop_eq_getElem_cons (l := w) hidx
    rw [hnext] at hd
    have hv : (w.drop (w.length - j)).length ≤ N := by
      rw [List.length_drop]
      omega
    change (h (w[w.length - (j + 1)]?.getD false)
      (Fin.cons (w.drop (w.length - j)) x) ![prefixLoop k g h w x j]).take k = _
    rw [ih (by omega), hd, List.getElem?_eq_getElem hidx]
    cases w[w.length - (j + 1)] <;> exact congrArg (List.take k) (hh _ _ hv _).symm

/-- The final step emits its full answer using the retained penultimate prefix. -/
theorem evalRec_cons_prefixLoop {n : ℕ} (k N : ℕ) (g : Sem (n, 0))
    (h : Bool → Sem (n + 1, 1)) (x : Fin n → List Bool)
    (hh : ∀ b v, v.length ≤ N → ∀ r,
      h b (Fin.cons v x) ![r] = h b (Fin.cons v x) ![r.take k])
    (b : Bool) (v : List Bool) (hv : v.length ≤ N) :
    BellantoniCook.evalRec g (h false) (h true) (b :: v) x Fin.elim0 =
      h b (Fin.cons v x) ![prefixLoop k g h v x v.length] := by
  rw [prefixLoop_eq k N g h x hh v hv _ (Nat.le_refl _), Nat.sub_self, List.drop_zero]
  cases b <;> exact hh _ v hv _

/-- A common executable prefix length for both branches of a safe recursion. -/
def Expr.recursionCutoff {n : ℕ} (h : Bool → Expr (n + 1) 1) (N : ℕ) : ℕ :=
  max ((h false).prefixCutoff N) ((h true).prefixCutoff N)

/-- The full recursive output can be obtained by a final step after an indexed
loop retaining only the syntax-derived prefix. -/
theorem Expr.eval_safeRec_cons_prefixCutoff {n : ℕ} (g : Expr n 0)
    (h : Bool → Expr (n + 1) 1) (x : Fin n → List Bool) (N : ℕ)
    (hx : ∀ j, (x j).length ≤ N) (b : Bool) (v : List Bool) (hv : v.length ≤ N) :
    (safeRec g h).eval (Fin.cons (b :: v) x) Fin.elim0 =
      (h b).eval (Fin.cons v x)
        ![prefixLoop (recursionCutoff h N) g.eval (fun bit ↦ (h bit).eval) v x v.length] := by
  apply evalRec_cons_prefixLoop _ N g.eval (fun bit ↦ (h bit).eval) x _ b v hv
  intro bit w hw r
  have henv : ∀ j, ((Fin.cons w x : Fin (n + 1) → List Bool) j).length ≤ N :=
    Fin.cases hw hx
  have hk : (h bit).prefixCutoff N ≤ recursionCutoff h N := by
    cases bit
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  simpa only [Matrix.cons_fin_one] using (h bit).eval_take_prefixCutoff _ N henv ![r] hk

/-- The common cutoff remains logarithmic under polynomial growth of virtual inputs. -/
theorem Expr.recursionCutoff_le_log_of_polyBounded {n : ℕ}
    (h : Bool → Expr (n + 1) 1) {p : ℕ → ℕ} (hp : IsPolyBounded p) :
    ∃ C : ℕ, ∀ m, recursionCutoff h (p m) ≤ C * (m.size + 1) := by
  obtain ⟨C₀, h₀⟩ := (h false).prefixCutoff_le_log_of_polyBounded hp
  obtain ⟨C₁, h₁⟩ := (h true).prefixCutoff_le_log_of_polyBounded hp
  refine ⟨max C₀ C₁, fun m ↦ max_le ?_ ?_⟩
  · exact (h₀ m).trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  · exact (h₁ m).trans (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))

/-- Every safe recursion has an indexed loop retaining a logarithmic output prefix.
The size bound counts the index and retained word, not the subcalls' workspace. -/
theorem Expr.exists_logarithmic_loop {n : ℕ} (g : Expr n 0)
    (h : Bool → Expr (n + 1) 1) :
    ∃ C : ℕ, ∀ (x : Fin n → List Bool) N, (∀ j, (x j).length ≤ N) →
      ∀ w, w.length ≤ N → ∀ t, t ≤ w.length →
        let k := C * (N.size + 1)
        prefixLoop k g.eval (fun b ↦ (h b).eval) w x t =
          ((Expr.safeRec g h).eval (Fin.cons (w.drop (w.length - t)) x) Fin.elim0).take k ∧
        t.size + (prefixLoop k g.eval (fun b ↦ (h b).eval) w x t).length ≤
          (C + 1) * (N.size + 1) := by
  obtain ⟨C₀, h₀⟩ := (h false).exists_logarithmic_prefix
  obtain ⟨C₁, h₁⟩ := (h true).exists_logarithmic_prefix
  refine ⟨max C₀ C₁, ?_⟩
  intro x N hx w hw t ht
  dsimp only
  constructor
  · apply prefixLoop_eq _ N g.eval (fun b ↦ (h b).eval) x _ w hw t ht
    intro bit v hv r
    have henv : ∀ j, ((Fin.cons v x : Fin (n + 1) → List Bool) j).length ≤ N :=
      Fin.cases hv hx
    have expand {C : ℕ} (hc : C ≤ max C₀ C₁) (f : Sem (n + 1, 1))
        (hf : ∀ y, f (Fin.cons v x) y =
          f (Fin.cons v x) (fun j ↦ (y j).take (C * (N.size + 1)))) :
        f (Fin.cons v x) ![r] =
          f (Fin.cons v x) ![r.take (max C₀ C₁ * (N.size + 1))] := by
      rw [hf ![r], hf ![r.take (max C₀ C₁ * (N.size + 1))]]
      simp only [Matrix.cons_fin_one, List.take_take,
        Nat.min_eq_left (Nat.mul_le_mul_right _ hc)]
    cases bit
    · exact expand (Nat.le_max_left _ _) (h false).eval (h₀ _ N henv)
    · exact expand (Nat.le_max_right _ _) (h true).eval (h₁ _ N henv)
  · have hi := Geb.BitTree.Counter.size_mono (ht.trans hw)
    have hr := prefixLoop_length_le (max C₀ C₁ * (N.size + 1))
      g.eval (fun b ↦ (h b).eval) w x t
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Every safe recursion admits a polynomial cap for which its retained state is
correct and its binary representation is logarithmic in the normal length bound. -/
theorem Expr.exists_logarithmic_state {n : ℕ} (g : Expr n 0)
    (h : Bool → Expr (n + 1) 1) :
    ∃ p : ℕ → ℕ, IsPolyBounded p ∧ ∃ C : ℕ,
      ∀ (x : Fin n → List Bool) N, (∀ j, (x j).length ≤ N) →
      ∀ w, w.length ≤ N →
        cappedRec (p N) g.eval (fun b ↦ (h b).eval) w x =
          cappedRank (p N) ((Expr.safeRec g h).eval (Fin.cons w x) Fin.elim0) ∧
        (unrank (cappedRec (p N) g.eval (fun b ↦ (h b).eval) w x)).length ≤
          C * (N.size + 1) := by
  obtain ⟨b₀, hb₀⟩ := (h false).exists_truncation
  obtain ⟨b₁, hb₁⟩ := (h true).exists_truncation
  let p : ℕ → ℕ := fun N ↦ max (lengthPoly b₀.1.1 N) (lengthPoly b₁.1.1 N)
  have hp : IsPolyBounded p := Geb.SizeBounded.isPolyBounded_max
    (lengthPoly_isPolyBounded b₀.1.1) (lengthPoly_isPolyBounded b₁.1.1)
  obtain ⟨C, hC⟩ := logarithmic_size_of_polyBounded hp
  refine ⟨p, hp, C, ?_⟩
  intro x N hx w hw
  constructor
  · apply cappedRec_correct (p N) N g.eval (fun b ↦ (h b).eval) x _ w hw
    intro bit v hv r
    have henv : ∀ j, ((Fin.cons v x : Fin (n + 1) → List Bool) j).length ≤ N :=
      Fin.cases hv hx
    cases bit
    · simpa only [Matrix.cons_fin_one] using
        hb₀.mono _ (p N) ((b₀.length_le _ Fin.elim0 N henv).trans (Nat.le_max_left _ _)) ![r]
    · simpa only [Matrix.cons_fin_one] using
        hb₁.mono _ (p N) ((b₁.length_le _ Fin.elim0 N henv).trans (Nat.le_max_right _ _)) ![r]
  · exact (cappedRec_length_le _ _ _ _ _).trans (hC N)

end Geb.Oitavem
