/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Subtraction
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Contract
public import Geb.Prototypes.Computability.Oitavem.Machine.Recursion
public import Geb.Prototypes.Computability.Oitavem.Machine.Compose
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Branch
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Sigma

set_option doc.verso true in
/-!
# Streaming subtraction of virtual words

Length and digit readers supply two virtual words. A first scan determines the sign
and last significant position of their difference. A second scan recomputes exactly
the required digits. The signed carry occupies one cell; lengths and positions are
binary counters. Neither argument nor the difference is stored on a work tape.

## Main definitions

* {lit}`subBitStep` performs one digit of signed-carry subtraction.
* {lit}`subScan` emits raw difference digits while saving the carry and significant index.
* {lit}`numericSubGenerator` initializes and runs both scans, then clears its working ports.

## Main statements

* {lit}`subBitStep_transformsIn` verifies the transition and preservation of all other tapes.
* {lit}`numericSubGenerator_emitsIn` verifies exact shortlex subtraction, termination,
  caller preservation, and the common work-space bound of the argument readers.

## Implementation notes

Seven caller-assigned ports hold two input digits, the carry, one result digit,
the countdown, the query, and the significant index. The argument readers restore
their separate scratch space after every call. Their sentinel encodings are queried
at arbitrary canonical indices, including positions beyond the shorter argument.
The machine contracts inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, subtraction, finite carry, logarithmic space
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- A parked optional singleton exposes exactly its optional digit. -/
theorem tapeOf_toList_zero (b : Option Bool) : tapeOf b.toList 0 = b := by
  cases b <;> simp [tapeOf]

/-- Replacing the only possible occupied cell replaces its optional singleton word. -/
theorem tapeOf_update_zero {w : List Bool} (hw : w.length ≤ 1) (b : Option Bool) :
    Function.update (tapeOf w) 0 b = tapeOf b.toList := by
  funext z
  by_cases hz : z = 0
  · subst z
    cases b <;> simp [tapeOf]
  · rw [Function.update_of_ne hz]
    by_cases hneg : z < 0
    · rw [tapeOf_neg _ _ hneg, tapeOf_neg _ _ hneg]
    · rw [tapeOf_of_le _ _ (by omega), tapeOf_of_le _ _ ?_]
      have := Option.length_toList_le (o := b)
      omega

/-- One arithmetic transition. The ports are minuend digit, subtrahend digit, carry, result. -/
@[expose] def subBitStep {k : ℕ} (r : Fin 4 → Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    let v := subBit ((work (r 0)).getD false) ((work (r 1)).getD false) (work (r 2))
    { inputTape := 0
      workTapes := fun i ↦
        if i = r 2 then (some v.1, 0)
        else if i = r 3 then (some (some v.2), 0) else (none, 0)
      output := none
      state := none }

/-- Update the optional carry and result words with one finite arithmetic transition. -/
@[expose] def subBitVal {k : ℕ} (r : Fin 4 → Fin k) (σ : Fin k → List Bool) :=
  let v := subBit ((tapeOf (σ (r 0)) 0).getD false)
    ((tapeOf (σ (r 1)) 0).getD false) (tapeOf (σ (r 2)) 0)
  Function.update (Function.update σ (r 2) v.1.toList) (r 3) [v.2]

/-- The arithmetic transition writes at most one cell on each output port
and preserves all heads. -/
theorem subBitStep_transformsIn {k : ℕ} (r : Fin 4 → Fin k) (hr : Function.Injective r)
    (B : ℕ → ℕ) (hB1 : ∀ n, 1 ≤ B n) :
    TransformsIn (subBitStep r)
      (fun _ σ ↦ (σ (r 2)).length ≤ 1 ∧ (σ (r 3)).length ≤ 1)
      (fun _ σ ↦ subBitVal r σ) (fun _ ↦ 1) B := by
  intro input cfg σ hq hpark _ hσ hp hB
  have hw (i : Fin k) : cfg.workTapeSymbols i = tapeOf (σ i) 0 := by
    change cfg.workTapes i (cfg.workTapePos i) = _
    rw [hpark i, hσ i]
  have hs : (subBitStep r).step cfg = after cfg (subBitVal r σ) := by
    rw [step_of_state _ _ () hq]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext i
      by_cases hi2 : i = r 2
      · subst i
        simp only [subBitStep, ite_true, after, subBitVal,
          Function.update_of_ne (hr.ne (by decide : (2 : Fin 4) ≠ 3)), Function.update_self]
        rw [hpark, hσ, hw, hw, hw, tapeOf_update_zero hp.1]
      · by_cases hi3 : i = r 3
        · subst i
          simp only [subBitStep, hi2, ite_false, ite_true, after, subBitVal,
            Function.update_self]
          rw [hpark, hσ, hw, hw, hw, tapeOf_update_zero hp.2]
          rfl
        · simp [subBitStep, hi2, hi3, after, subBitVal, hσ i]
    · funext i
      simp only [subBitStep, after]
      split_ifs <;> simp
    · simp [subBitStep, after]
  refine ⟨(hB.update (Option.length_toList_le.trans (hB1 _))).update (hB1 _),
    1, le_rfl, ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩⟩
  · intro s hs'
    have : s = 0 := by omega
    simpa only [this, runFrom_zero, hq] using Option.some_ne_none ()
  · simpa only [runFrom_succ_eq_step', runFrom_zero] using hs
  · intro s hs' i
    have hpos : -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
      rw [hpark i]
      constructor <;> omega
    have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl
    · exact hpos
    · simpa only [runFrom_succ_eq_step', runFrom_zero, hs, after] using hpos
  · simp only [outputString_succ, runFrom_zero, outputSymbol, hq]
    rfl

/-- Save the current index when the result digit is one. -/
@[expose] def saveLastOne {k : ℕ} (Q R L : Fin k) :=
  caseProbe (some R) idle (copy Q L)

/-- Saving the index preserves the source digit and every other register. -/
theorem saveLastOne_transformsIn {k : ℕ} (Q R L : Fin k) (hQL : Q ≠ L) (B : ℕ → ℕ) :
    TransformsIn (saveLastOne Q R L) (fun _ _ ↦ True)
      (fun _ σ ↦ if (σ R).getLast? = some true then Function.update σ L (σ Q) else σ)
      (fun n ↦ 5 * B n + 14) B := by
  have hc := Transforms.toIn_of (fun n ↦ copy_transforms Q L hQL (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (hB Q))
  exact ((TransformsIn.idle B).caseReg R hc).mono_pre (fun _ _ _ _ ↦ by split <;> trivial)
    |>.mono_time (fun _ ↦ by omega)

/-- One subtraction digit, recording its index, emitting it, and clearing digit ports.
The ports are minuend digit, subtrahend digit, carry, result, countdown, query, and last one. -/
@[expose] def subDigit {k : ℕ} (r : Fin 7 → Fin k) :=
  seq (subBitStep (r ∘ Fin.castAdd 3))
    (seq (saveLastOne (r 5) (r 3) (r 6))
      (seq (emitBit (r 3)) (seq (const [] (r 0)) (seq (const [] (r 1)) (const [] (r 3))))))

/-- The arithmetic result and finite carry read from the parked digit ports. -/
@[expose] def subDigitValue {k : ℕ} (r : Fin 7 → Fin k) (σ : Fin k → List Bool) :=
  subBit ((tapeOf (σ (r 0)) 0).getD false) ((tapeOf (σ (r 1)) 0).getD false)
    (tapeOf (σ (r 2)) 0)

/-- The valuation after emitting one subtraction digit. -/
@[expose] def subDigitVal {k : ℕ} (r : Fin 7 → Fin k) (σ : Fin k → List Bool) :=
  let v := subDigitValue r σ
  let τ := Function.update σ (r 2) v.1.toList
  let τ := if v.2 then Function.update τ (r 6) (σ (r 5)) else τ
  Function.update (Function.update (Function.update τ (r 0) []) (r 1) []) (r 3) []

/-- One scan body records and emits exactly its arithmetic bit, keeping only a finite carry. -/
theorem subDigit_emitsIn {k : ℕ} (r : Fin 7 → Fin k) (hr : Function.Injective r)
    (B : ℕ → ℕ) (hB1 : ∀ n, 1 ≤ B n) :
    EmitsIn (subDigit r)
      (fun _ σ ↦ (σ (r 2)).length ≤ 1 ∧ (σ (r 3)).length ≤ 1)
      (fun _ σ ↦ subDigitVal r σ) (fun _ σ ↦ [(subDigitValue r σ).2])
      (fun n ↦ 17 * B n + 43) B := by
  have hc (i : Fin k) := Transforms.toIn_of (fun n ↦ const_transforms [] i (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hb := subBitStep_transformsIn (r ∘ Fin.castAdd 3)
    (hr.comp (Fin.castAdd_injective 4 3)) B hB1
  have hs := hb.seqEmitsIn ((saveLastOne_transformsIn (r 5) (r 3) (r 6)
    (hr.ne (by decide)) B).seqEmitsIn ((emitBit_emitsIn (r 3) B).seqTransformsIn
      ((hc (r 0)).seq ((hc (r 1)).seq (hc (r 3))))))
  have hm := hs.mono_pre (Pre' := fun _ σ ↦
      (σ (r 2)).length ≤ 1 ∧ (σ (r 3)).length ≤ 1) (fun _ _ _ hp ↦
    ⟨hp, trivial, trivial, trivial, trivial, trivial⟩)
  have hf : ∀ σ, (subBitVal (r ∘ Fin.castAdd 3) σ (r 3)).getLast? =
      some (subDigitValue r σ).2 := by
    intro σ
    change (Function.update (Function.update σ (r 2) (subDigitValue r σ).1.toList)
      (r 3) [(subDigitValue r σ).2] (r 3)).getLast? = _
    rw [Function.update_self]
    rfl
  refine ((hm.congr ?_).congr_output ?_).mono_time (fun _ ↦ by omega)
  · intro input σ _
    rw [hf]
    simp only [Option.some.injEq, subBitVal, Function.comp_apply, subDigitVal, subDigitValue]
    split_ifs <;> (funext i; by_cases h0 : i = r 0 <;> by_cases h1 : i = r 1 <;>
      by_cases h2 : i = r 2 <;> by_cases h3 : i = r 3 <;> by_cases h6 : i = r 6 <;>
      simp_all [hr.eq_iff])
  · intro input σ _
    rw [hf]
    split <;> simp [subBitVal, Function.comp_apply, subDigitValue, tapeOf, hr.eq_iff]

/-- The counters, carry, and last significant index after a prefix of a subtraction scan. -/
@[expose] def subScanVal {k : ℕ} (σ : Fin k → List Bool) (r : Fin 7 → Fin k)
    (ps : List (Bool × Bool)) (c j : ℕ) :=
  Function.update
    (Function.update (concatVal σ (r 4) (r 5) c j) (r 2)
      (subCarry (ps.take j) (some true)).toList)
    (r 6) (counterWord ((trim (subDigits (ps.take j) 1).2).length - 1))

/-- Reading the next pair, processing it, and advancing the counters
preserves the scan invariant. -/
theorem subScanVal_step {k : ℕ} (r : Fin 7 → Fin k) (hr : Function.Injective r)
    (σ : Fin k → List Bool) (ps : List (Bool × Bool)) (c j : ℕ) (hj : j < ps.length)
    (hclear : σ (r 0) = [] ∧ σ (r 1) = [] ∧ σ (r 3) = [])
    (a b : Option Bool) (ha : a.getD false = ps[j].1) (hb : b.getD false = ps[j].2) :
    let τ := Function.update (Function.update (subScanVal σ r ps c j) (r 0) a.toList)
      (r 1) b.toList
    Function.update (Function.update (subDigitVal r τ) (r 5) (counterWord (j + 1)))
      (r 4) (counterWord (c - (j + 1))) = subScanVal σ r ps c (j + 1) := by
  let v := subBit ps[j].1 ps[j].2 (subCarry (ps.take j) (some true))
  have ht : ps.take j ++ [ps[j]] = ps.take (j + 1) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]
    rfl
  have hc : subCarry (ps.take (j + 1)) (some true) = v.1 := by
    rw [← ht, subCarry_append_one]
  have ho : (subDigits (ps.take (j + 1)) 1).2 =
      (subDigits (ps.take j) 1).2 ++ [v.2] := by
    rw [← ht]
    exact congrArg Prod.snd (subDigits_append_one (ps.take j) ps[j].1 ps[j].2 (some true))
  have hl : (trim (subDigits (ps.take (j + 1)) 1).2).length - 1 =
      if v.2 then j else (trim (subDigits (ps.take j) 1).2).length - 1 := by
    rw [ho]
    cases hv : v.2
    · simp [trim_append_false]
    · simp [trim_append_true, subDigits_length, List.length_take, Nat.min_eq_left hj.le]
  have hv : subDigitValue r
      (Function.update (Function.update (subScanVal σ r ps c j) (r 0) a.toList)
        (r 1) b.toList) = v := by
    simp [subDigitValue, subScanVal, concatVal, hr.eq_iff, tapeOf_toList_zero, ha, hb, v]
  dsimp only
  simp only [subDigitVal]
  rw [hv]
  simp only [subScanVal, concatVal, hc, hl]
  cases hv2 : v.2
  all_goals
    funext i
    by_cases hi : ∃ s, i = r s
    · obtain ⟨s, rfl⟩ := hi
      fin_cases s <;> simp_all [hr.eq_iff]
    · have hn (s) : i ≠ r s := fun h ↦ hi ⟨s, h⟩
      simp [Function.update_of_ne, hn]

/-- Scan a saved number of paired virtual digits, retaining the carry and significant length. -/
@[expose] def subScan {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (r : Fin 7 → Fin k) :=
  concatLoop (seq P (subDigit r)) (r 4) (r 5)

/-- A paired reader supplies the subtraction scan. The result consists of its raw digits,
finite carry, and the binary index of its last significant digit. -/
theorem subScan_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (r : Fin 7 → Fin k) (hr : Function.Injective r)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {F : List Bool → (Fin k → List Bool) → Fin k → List Bool} {T B N : ℕ → ℕ}
    (hP : TransformsIn P Pre F T B)
    (Pre₀ : List Bool → (Fin k → List Bool) → Prop)
    (D : List Bool → (Fin k → List Bool) → List (Bool × Bool))
    (hlen : ∀ input σ, Pre₀ input σ → (D input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) (hB1 : ∀ n, 1 ≤ B n)
    (hcall : ∀ input σ, Pre₀ input σ → ∀ c ≤ (D input σ).length, ∀ j < c,
      let τ := subScanVal σ r (D input σ) c j
      Pre input τ ∧ ∃ a b : Option Bool,
        F input τ = Function.update (Function.update τ (r 0) a.toList) (r 1) b.toList ∧
        a.getD false = ((D input σ)[j]?.getD (false, false)).1 ∧
        b.getD false = ((D input σ)[j]?.getD (false, false)).2) :
    EmitsIn (subScan P r)
      (fun input σ ↦ Pre₀ input σ ∧ ∃ c, σ (r 4) = counterWord c ∧
        c ≤ (D input σ).length ∧ σ (r 2) = [true] ∧
        ∀ i : Fin 7, i ≠ 2 → i ≠ 4 → σ (r i) = [])
      (fun input σ ↦ subScanVal σ r (D input σ) (counterValue (σ (r 4)))
        (counterValue (σ (r 4))))
      (fun input σ ↦ (subDigits ((D input σ).take (counterValue (σ (r 4)))) 1).2)
      (fun n ↦ N n * (T n + 21 * B n + 54) + 1) B := by
  have hi := Transforms.toIn_of (fun n ↦ inc_transforms (r 5) (B n))
    (fun input σ ↦ ∃ q, σ (r 5) = counterWord q ∧ q < N input.length) (by
      intro input σ hB ⟨q, hq, hqn⟩
      refine hB.update ?_
      rw [hq, incL_counterWord, length_counterWord]
      exact (size_le_size (by omega : q + 1 ≤ N input.length)).trans (hsize _))
  have hd := Transforms.toIn_of (fun n ↦ dec_transforms (r 4) (B n))
    (fun _ _ ↦ True) (fun _ σ hB _ ↦ hB.update (by
      rw [List.length_reverse]
      exact (length_decL_le _).trans (by simpa only [List.length_reverse] using hB (r 4))))
  have hbody := (hP.seqEmitsIn (subDigit_emitsIn r hr B hB1)).seqTransformsIn (hi.seq hd)
  have hw := hbody.whileReg (r 4)
    (fun input σ ↦ Pre₀ input σ ∧ ∃ c, σ (r 4) = counterWord c ∧
      c ≤ (D input σ).length ∧ σ (r 2) = [true] ∧
      ∀ i : Fin 7, i ≠ 2 → i ≠ 4 → σ (r i) = [])
    (fun _ σ ↦ counterValue (σ (r 4))) N
    (fun input σ j ↦ subScanVal σ r (D input σ) (counterValue (σ (r 4))) j)
    (fun input σ j ↦ (subDigits ((D input σ).take j) 1).2)
    (by
      rintro input σ ⟨hp, c, hc, hcD, _⟩
      rw [hc, counterValue_counterWord]
      exact hcD.trans (hlen input σ hp))
    (by
      rintro input σ ⟨_, c, hc, _, hK, hz⟩
      rw [hc, counterValue_counterWord]
      refine ⟨?_, rfl⟩
      change Function.update (Function.update (Function.update
        (Function.update σ (r 4) (counterWord c)) (r 5) []) (r 2) [true]) (r 6) [] = σ
      have hQ : Function.update σ (r 5) [] = σ := by
        rw [← hz 5 (by decide) (by decide), Function.update_eq_self]
      have hL : Function.update σ (r 6) [] = σ := by
        rw [← hz 6 (by decide) (by decide), Function.update_eq_self]
      rw [← hc, Function.update_eq_self, hQ, ← hK, Function.update_eq_self, hL])
    (by
      rintro input σ ⟨hp, c, hc, hcD, hK, hz⟩ j hj
      rw [hc, counterValue_counterWord] at hj ⊢
      have hjD : j < (D input σ).length := hj.trans_le hcD
      have hN := hlen input σ hp
      obtain ⟨hpP, a, b, hF, ha, hb⟩ := hcall input σ hp c hcD j hj
      rw [List.getElem?_eq_getElem hjD] at ha hb
      have hquery : subDigitVal r (F input (subScanVal σ r (D input σ) c j)) (r 5) =
          counterWord j := by
        rw [hF]
        simp only [subDigitVal]
        split <;> simp [subScanVal, concatVal, hr.eq_iff]
      have hcount : subDigitVal r (F input (subScanVal σ r (D input σ) c j)) (r 4) =
          counterWord (c - j) := by
        rw [hF]
        simp only [subDigitVal]
        split <;> simp [subScanVal, concatVal, hr.eq_iff]
      have hcarry : F input (subScanVal σ r (D input σ) c j) (r 2) =
          (subCarry ((D input σ).take j) (some true)).toList := by
        rw [hF]
        simp [subScanVal, hr.eq_iff]
      have hresult : F input (subScanVal σ r (D input σ) c j) (r 3) = [] := by
        rw [hF]
        simp [subScanVal, concatVal, hr.eq_iff, hz 3 (by decide) (by decide)]
      refine ⟨?_, ⟨⟨hpP, ?_, ?_⟩, ⟨j, hquery, by omega⟩, trivial⟩, ?_, ?_⟩
      · simpa [subScanVal, concatVal, hr.eq_iff, counterWord_eq_nil_iff] using
          (by omega : c - j ≠ 0)
      · rw [hcarry]
        exact Option.length_toList_le
      · rw [hresult]
        decide
      · rw [hquery, incL_counterWord,
          Function.update_of_ne (hr.ne (by decide : (4 : Fin 7) ≠ 5)), hcount,
          decL_counterWord, Nat.sub_sub, hF]
        exact subScanVal_step r hr σ (D input σ) c j hjD
          ⟨hz 0 (by decide) (by decide), hz 1 (by decide) (by decide),
            hz 3 (by decide) (by decide)⟩ a b ha hb
      · have hv : subDigitValue r (F input (subScanVal σ r (D input σ) c j)) =
            subBit (D input σ)[j].1 (D input σ)[j].2
              (subCarry ((D input σ).take j) (some true)) := by
          rw [hF]
          simp [subDigitValue, subScanVal, concatVal, hr.eq_iff, tapeOf_toList_zero, ha, hb]
        rw [hv]
        have he := congrArg Prod.snd
          (subDigits_append_one ((D input σ).take j) (D input σ)[j].1 (D input σ)[j].2
            (some true))
        have ht : (D input σ).take j ++ [(D input σ)[j]] = (D input σ).take (j + 1) := by
          rw [List.take_add_one, List.getElem?_eq_getElem hjD]
          rfl
        rw [ht] at he
        exact he.symm)
    (by
      intro input σ _
      simp [subScanVal, concatVal, hr.eq_iff, show counterWord 0 = [] from rfl])
  exact hw.mono_time (fun _ ↦ Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1)

/-- A negative carry suppresses the entire output by selecting length zero. -/
@[expose] def subSelectLength {k : ℕ} (K L : Fin k) :=
  chooseEmpty (S := fun b ↦ if b then StateOf (const [] L) else Unit) K
    (fun b ↦ match b with | false => idle | true => const [] L)

/-- Only a negative carry changes the selected output length. -/
theorem subSelectLength_transformsIn {k : ℕ} (K L : Fin k) (B : ℕ → ℕ) :
    TransformsIn (subSelectLength K L) (fun _ _ ↦ True)
      (fun _ σ ↦ if (σ K).isEmpty then Function.update σ L [] else σ)
      (fun n ↦ 4 * B n + 10) B := by
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] L (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hp : ∀ b : Bool,
      EmitsIn (S := if b then StateOf (const [] L) else Unit)
        (match b with | false => idle | true => const [] L) (fun _ _ ↦ True)
        (fun _ σ ↦ if b then Function.update σ L [] else σ) (fun _ _ ↦ [])
        (fun n ↦ 4 * B n + 9) B := by
    intro b
    cases b
    · exact (TransformsIn.idle B).toEmitsIn.mono_time (fun _ ↦ by omega)
    · exact hc.toEmitsIn
  simpa only [subSelectLength, max_self, Nat.add_comm 1] using
    (chooseEmpty_emitsIn K hp).toTransformsIn

/-- Prepare the second scan from the saved sign and significant index. -/
@[expose] def subRestart {k : ℕ} (r : Fin 7 → Fin k) :=
  seq (subSelectLength (r 2) (r 6))
    (seq (copy (r 6) (r 4)) (seq (const [] (r 5)) (seq (const [true] (r 2)) (const [] (r 6)))))

/-- The valuation at the beginning of the second scan. -/
@[expose] def subRestartVal {k : ℕ} (r : Fin 7 → Fin k) (σ : Fin k → List Bool) :=
  Function.update (Function.update (Function.update (Function.update σ (r 4)
    (if (σ (r 2)).isEmpty then [] else σ (r 6))) (r 5) []) (r 2) [true]) (r 6) []

/-- Restarting clears the query and last-index counters and restores the initial carry. -/
theorem subRestart_transformsIn {k : ℕ} (r : Fin 7 → Fin k) (hr : Function.Injective r)
    (B : ℕ → ℕ) (hB1 : ∀ n, 1 ≤ B n) :
    TransformsIn (subRestart r) (fun _ _ ↦ True) (fun _ σ ↦ subRestartVal r σ)
      (fun n ↦ 21 * B n + 49) B := by
  have hc (i : Fin k) (w : List Bool) (hw : ∀ n, w.length ≤ B n) :=
    Transforms.toIn_of (fun n ↦ const_transforms w i (B n)) (fun _ _ ↦ True)
      (fun _ _ hB _ ↦ hB.update (hw _))
  have hcopy := Transforms.toIn_of
    (fun n ↦ copy_transforms (r 6) (r 4) (hr.ne (by decide)) (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (hB (r 6)))
  have hs := (subSelectLength_transformsIn (r 2) (r 6) B).seq
    (hcopy.seq ((hc (r 5) [] (fun _ ↦ Nat.zero_le _)).seq
      ((hc (r 2) [true] hB1).seq (hc (r 6) [] (fun _ ↦ Nat.zero_le _)))))
  have hm := hs.mono_pre (Pre' := fun _ _ ↦ True)
    (fun _ _ _ _ ↦ ⟨trivial, trivial, trivial, trivial, trivial⟩)
  refine (hm.congr ?_).mono_time (fun _ ↦ by omega)
  intro input σ _
  dsimp only [subRestartVal]
  split_ifs
  all_goals
    funext i
    by_cases hi : ∃ s, i = r s
    · obtain ⟨s, rfl⟩ := hi
      fin_cases s <;> simp [hr.eq_iff]
    · have hn (s) : i ≠ r s := fun h ↦ hi ⟨s, h⟩
      simp [Function.update_of_ne, hn]

/-- The scan overwrites exactly its four saved state registers. -/
theorem subScanVal_idem {k : ℕ} (r : Fin 7 → Fin k) (hr : Function.Injective r)
    (σ : Fin k → List Bool) (ps qs : List (Bool × Bool)) (c j d l : ℕ) :
    subScanVal (subScanVal σ r ps c j) r qs d l = subScanVal σ r qs d l := by
  funext i
  by_cases hi : ∃ s, i = r s
  · obtain ⟨s, rfl⟩ := hi
    fin_cases s <;> simp [subScanVal, concatVal, hr.eq_iff]
  · have hn (s) : i ≠ r s := fun h ↦ hi ⟨s, h⟩
    simp [subScanVal, concatVal, Function.update_of_ne, hn]

/-- A complete first scan supplies precisely the canonical second-scan length. -/
theorem subRestartVal_afterScan {k : ℕ} (r : Fin 7 → Fin k) (hr : Function.Injective r)
    (σ : Fin k → List Bool) (ps : List (Bool × Bool)) :
    subRestartVal r (subScanVal σ r ps ps.length ps.length) =
      subScanVal σ r ps (subOutputLength ps) 0 := by
  have he (b : Option Bool) : b.toList.isEmpty = b.isNone := by cases b <;> rfl
  funext i
  by_cases hi : ∃ s, i = r s
  · obtain ⟨s, rfl⟩ := hi
    fin_cases s <;> simp [subRestartVal, subScanVal, concatVal, hr.eq_iff, subOutputLength,
      he, subCarry, subDigits, trim, show counterWord 0 = [] from rfl]
    split <;> rfl
  · have hn (s) : i ≠ r s := fun h ↦ hi ⟨s, h⟩
    simp [subRestartVal, subScanVal, concatVal, Function.update_of_ne, hn]

/-- Clearing the scan state leaves every caller register intact. -/
@[expose] def subDoneVal {k : ℕ} (r : Fin 7 → Fin k) (σ : Fin k → List Bool) :=
  Function.update (Function.update (Function.update (Function.update σ (r 4) [])
    (r 5) []) (r 2) []) (r 6) []

/-- Clearing the final carry, index, and significant length clears all scan state. -/
theorem subDoneVal_afterScan {k : ℕ} (r : Fin 7 → Fin k) (hr : Function.Injective r)
    (σ : Fin k → List Bool) (ps : List (Bool × Bool)) (c : ℕ) :
    Function.update (Function.update (Function.update (subScanVal σ r ps c c) (r 2) [])
      (r 5) []) (r 6) [] = subDoneVal r σ := by
  funext i
  by_cases hi : ∃ s, i = r s
  · obtain ⟨s, rfl⟩ := hi
    fin_cases s <;> simp [subScanVal, concatVal, subDoneVal, hr.eq_iff,
      show counterWord 0 = [] from rfl]
  · have hn (s) : i ≠ r s := fun h ↦ hi ⟨s, h⟩
    simp [subScanVal, concatVal, subDoneVal, Function.update_of_ne, hn]

/-- Determine the sign and significant length, then recompute exactly the required digits. -/
@[expose] def subtractionCore {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S)
    (r : Fin 7 → Fin k) :=
  seq (seq (mute (subScan P r)) (subRestart r)) (seq (subScan P r)
    (seq (const [] (r 2)) (seq (const [] (r 5)) (const [] (r 6)))))

/-- Two scans emit the canonical signed difference without storing the generated digits.
The paired source and its precondition are independent of the seven scan registers. -/
theorem subtractionCore_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (r : Fin 7 → Fin k) (hr : Function.Injective r)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {D : List Bool → (Fin k → List Bool) → List (Bool × Bool)} {T B : ℕ → ℕ}
    (hscan : EmitsIn (subScan P r)
      (fun input σ ↦ Pre input σ ∧ ∃ c, σ (r 4) = counterWord c ∧
        c ≤ (D input σ).length ∧ σ (r 2) = [true] ∧
        ∀ i : Fin 7, i ≠ 2 → i ≠ 4 → σ (r i) = [])
      (fun input σ ↦ subScanVal σ r (D input σ) (counterValue (σ (r 4)))
        (counterValue (σ (r 4))))
      (fun input σ ↦ (subDigits ((D input σ).take (counterValue (σ (r 4)))) 1).2) T B)
    (hpre : ∀ input σ i w, Pre input σ → Pre input (Function.update σ (r i) w))
    (hword : ∀ input σ i w, D input (Function.update σ (r i) w) = D input σ)
    (hB1 : ∀ n, 1 ≤ B n) :
    EmitsIn (subtractionCore P r)
      (fun input σ ↦ Pre input σ ∧ σ (r 4) = counterWord (D input σ).length ∧
        σ (r 2) = [true] ∧ ∀ i : Fin 7, i ≠ 2 → i ≠ 4 → σ (r i) = [])
      (fun _ σ ↦ subDoneVal r σ)
      (fun input σ ↦ if 0 ≤ (subDigits (D input σ) 1).1 then
        (trim (subDigits (D input σ) 1).2).dropLast else [])
      (fun n ↦ 2 * T n + 33 * B n + 77) B := by
  let Start := fun input σ ↦ Pre input σ ∧ σ (r 4) = counterWord (D input σ).length ∧
    σ (r 2) = [true] ∧ ∀ i : Fin 7, i ≠ 2 → i ≠ 4 → σ (r i) = []
  have hpreV input σ ps c j (hp : Pre input σ) : Pre input (subScanVal σ r ps c j) :=
    hpre input _ 6 _ (hpre input _ 2 _ (hpre input _ 5 _ (hpre input _ 4 _ hp)))
  have hwordV input σ ps c j : D input (subScanVal σ r ps c j) = D input σ := by
    simp only [subScanVal, concatVal, hword]
  have hcountV σ ps c j : subScanVal σ r ps c j (r 4) = counterWord (c - j) := by
    simp [subScanVal, concatVal, hr.eq_iff]
  have hfirst := ((mute_emitsIn hscan).toTransformsIn.mono_pre (Pre' := Start)
    (fun input σ _ hp ↦ ⟨hp.1, (D input σ).length, hp.2.1, le_rfl, hp.2.2⟩)).congr
    (F' := fun input σ ↦ subScanVal σ r (D input σ) (D input σ).length (D input σ).length)
    (fun _ _ hp ↦ by rw [hp.2.1, counterValue_counterWord])
  have hstart := ((hfirst.seq (subRestart_transformsIn r hr B hB1)).mono_pre
    (Pre' := Start) (fun _ _ _ hp ↦ ⟨hp, trivial⟩)).congr
      (F' := fun input σ ↦ subScanVal σ r (D input σ) (subOutputLength (D input σ)) 0)
      (fun _ _ _ ↦ subRestartVal_afterScan r hr _ _)
  have hready input σ (hp : Start input σ) :
      let τ := subScanVal σ r (D input σ) (subOutputLength (D input σ)) 0
      Pre input τ ∧ ∃ c, τ (r 4) = counterWord c ∧ c ≤ (D input τ).length ∧
        τ (r 2) = [true] ∧ ∀ i : Fin 7, i ≠ 2 → i ≠ 4 → τ (r i) = [] := by
    refine ⟨hpreV _ _ _ _ _ hp.1, subOutputLength (D input σ), ?_, ?_, ?_, ?_⟩
    · rw [hcountV, Nat.sub_zero]
    · rw [hwordV]
      exact subOutputLength_le _
    · simp [subScanVal, hr.eq_iff, subCarry]
    · intro i hi2 hi4
      have hz := hp.2.2.2
      fin_cases i <;> simp_all [subScanVal, concatVal, hr.eq_iff, subDigits, trim,
        show counterWord 0 = [] from rfl]
  have hc (i : Fin k) := Transforms.toIn_of (fun n ↦ const_transforms [] i (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hcleanup := (hc (r 2)).seq ((hc (r 5)).seq (hc (r 6)))
  have hs := (hstart.seqEmitsIn (hscan.seqTransformsIn hcleanup)).mono_pre (Pre' := Start)
    (fun input σ _ hp ↦ ⟨hp, hready input σ hp, trivial, trivial, trivial⟩)
  refine ((hs.congr ?_).congr_output ?_).mono_time (fun _ ↦ by omega)
  · intro input σ _
    rw [hwordV, hcountV, Nat.sub_zero, counterValue_counterWord, subScanVal_idem r hr]
    exact subDoneVal_afterScan r hr σ (D input σ) _
  · intro input σ _
    rw [hwordV, hcountV, Nat.sub_zero, counterValue_counterWord]
    exact subDigits_take_subOutputLength _

/-- Subtraction of two virtual shortlex words, given readers for their sentinel encodings.
The countdown is initialized to the larger argument length plus one. -/
theorem subtractionCore_numericSub_emitsIn {k : ℕ} {S₁ S₂ : Type}
    {P₁ : MultiTapeTM k Bool S₁} {P₂ : MultiTapeTM k Bool S₂}
    (r : Fin 7 → Fin k) (hr : Function.Injective r)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {V W : List Bool → (Fin k → List Bool) → List Bool} {T₁ T₂ B N : ℕ → ℕ}
    (hA : ReadsAtAll P₁ (r 5) (r 0) Pre (fun input σ ↦ W input σ ++ [true]) T₁ B)
    (hB : ReadsAtAll P₂ (r 5) (r 1) Pre (fun input σ ↦ V input σ ++ [true]) T₂ B)
    (hpre : ∀ input σ i w, Pre input σ → Pre input (Function.update σ (r i) w))
    (hV : ∀ input σ i w, V input (Function.update σ (r i) w) = V input σ)
    (hW : ∀ input σ i w, W input (Function.update σ (r i) w) = W input σ)
    (hlen : ∀ input σ, Pre input σ →
      max (V input σ).length (W input σ).length + 1 ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    EmitsIn (subtractionCore (seq P₁ P₂) r)
      (fun input σ ↦ Pre input σ ∧
        σ (r 4) = counterWord (max (V input σ).length (W input σ).length + 1) ∧
        σ (r 2) = [true] ∧ ∀ i : Fin 7, i ≠ 2 → i ≠ 4 → σ (r i) = [])
      (fun _ σ ↦ subDoneVal r σ) (fun input σ ↦ numericSub (V input σ) (W input σ))
      (fun n ↦ 2 * (N n * (T₁ n + T₂ n + 21 * B n + 54) + 1) + 33 * B n + 77) B := by
  have hpreV input σ ps c j (hp : Pre input σ) : Pre input (subScanVal σ r ps c j) :=
    hpre input _ 6 _ (hpre input _ 2 _ (hpre input _ 5 _ (hpre input _ 4 _ hp)))
  have hVV input σ ps c j : V input (subScanVal σ r ps c j) = V input σ := by
    simp only [subScanVal, concatVal, hV]
  have hWV input σ ps c j : W input (subScanVal σ r ps c j) = W input σ := by
    simp only [subScanVal, concatVal, hW]
  have hq σ ps c j : subScanVal σ r ps c j (r 5) = counterWord j := by
    simp [subScanVal, concatVal, hr.eq_iff]
  have hs := subScan_emitsIn r hr (hA.seq hB) Pre
    (fun input σ ↦ bitPairs (V input σ) (W input σ))
    (fun input σ hp ↦ by simpa only [length_bitPairs] using hlen input σ hp)
    hsize hB1 (by
      intro input σ hp c hc j hj
      have hjD : j < (bitPairs (V input σ) (W input σ)).length := hj.trans_le hc
      have ht := hpreV input σ (bitPairs (V input σ) (W input σ)) c j hp
      refine ⟨⟨⟨ht, j, hq ..⟩, hpre input _ 0 _ ht, j, ?_⟩,
        (W input σ ++ [true])[j]?, (V input σ ++ [true])[j]?, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne (hr.ne (by decide : (5 : Fin 7) ≠ 0)), hq]
      · simp only [hV, hWV, hVV, Function.update_of_ne
          (hr.ne (by decide : (5 : Fin 7) ≠ 0)), hq, counterValue_counterWord]
      · rw [List.getElem?_eq_getElem hjD, Option.getD_some, bitPairs_getElem]
      · rw [List.getElem?_eq_getElem hjD, Option.getD_some, bitPairs_getElem])
  have h := subtractionCore_emitsIn r hr hs hpre
    (fun input σ i w ↦ by rw [hV, hW]) hB1
  simpa only [length_bitPairs] using h.congr_output
    (fun input σ _ ↦ shortlexSub_eq_numericSub (V input σ) (W input σ))

/-- Count both arguments and initialize a subtraction scan, including its sentinel position. -/
@[expose] def subInit {k : ℕ} {S₁ S₂ : Type}
    (L₁ : MultiTapeTM k Bool S₁) (L₂ : MultiTapeTM k Bool S₂) (r : Fin 7 → Fin k) :=
  seq (seq L₁ L₂) (seq (maxCounter (r 4) (r 5) (r 6))
    (seq (inc (r 4)) (const [true] (r 2))))

/-- Length readers initialize the countdown using logarithmic binary counters. -/
theorem subInit_transformsIn {k : ℕ} {S₁ S₂ : Type}
    {L₁ : MultiTapeTM k Bool S₁} {L₂ : MultiTapeTM k Bool S₂}
    (r : Fin 7 → Fin k) (hr : Function.Injective r)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {V W : List Bool → (Fin k → List Bool) → List Bool} {T₁ T₂ B N : ℕ → ℕ}
    (h₁ : ReadsLength L₁ (r 4) Pre V T₁ B) (h₂ : ReadsLength L₂ (r 5) Pre W T₂ B)
    (hpre : ∀ input σ i w, Pre input σ → Pre input (Function.update σ (r i) w))
    (hW : ∀ input σ i w, W input (Function.update σ (r i) w) = W input σ)
    (hlen : ∀ input σ, Pre input σ →
      max (V input σ).length (W input σ).length + 1 ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    TransformsIn (subInit L₁ L₂ r) Pre
      (fun input σ ↦ subScanVal σ r (bitPairs (V input σ) (W input σ))
        (max (V input σ).length (W input σ).length + 1) 0)
      (fun n ↦ T₁ n + T₂ n + N n * (8 * B n + 24) + 11 * B n + 27) B := by
  have hl := ((h₁.seq h₂).mono_pre (Pre' := Pre)
    (fun input σ _ hp ↦ ⟨hp, hpre input σ 4 _ hp⟩)).congr
    (F' := fun input σ ↦ Function.update (Function.update σ (r 4)
      (counterWord (V input σ).length)) (r 5) (counterWord (W input σ).length))
    (fun input σ _ ↦ by rw [hW])
  have hm := maxCounter_transformsIn (r 4) (r 5) (r 6)
    (hr.ne (by decide)) (hr.ne (by decide)) (hr.ne (by decide)) N B hsize
  have hi := Transforms.toIn_of (fun n ↦ inc_transforms (r 4) (B n))
    (fun input σ ↦ ∃ c, σ (r 4) = counterWord c ∧ c + 1 ≤ N input.length) (by
      rintro input σ hB ⟨c, hc, hcn⟩
      refine hB.update ?_
      rw [hc, incL_counterWord, length_counterWord]
      exact (size_le_size hcn).trans (hsize _))
  have hk := Transforms.toIn_of (fun n ↦ const_transforms [true] (r 2) (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (hB1 _))
  have hs := (hl.seq (hm.seq (hi.seq hk))).mono_pre (Pre' := Pre) (by
    intro input σ _ hp
    have hn := hlen input σ hp
    refine ⟨hp, ⟨(V input σ).length, (W input σ).length, ?_, ?_, by omega, by omega⟩,
      ⟨max (V input σ).length (W input σ).length, ?_, hn⟩, trivial⟩
    · simp [hr.eq_iff]
    · simp
    · simp [hr.eq_iff, counterValue_counterWord])
  refine (hs.congr ?_).mono_time (fun _ ↦ by omega)
  intro input σ _
  funext i
  by_cases hi : ∃ s, i = r s
  · obtain ⟨s, rfl⟩ := hi
    fin_cases s <;> simp [subScanVal, concatVal, hr.eq_iff, counterValue_counterWord,
      incL_counterWord, subCarry, subDigits, trim, show counterWord 0 = [] from rfl]
  · have hn (s) : i ≠ r s := fun h ↦ hi ⟨s, h⟩
    simp [subScanVal, concatVal, Function.update_of_ne, hn]

/-- Numerical subtraction from length readers and sentinel-digit readers. -/
@[expose] def numericSubGenerator {k : ℕ} {S₁ S₂ S₃ S₄ : Type}
    (L₁ : MultiTapeTM k Bool S₁) (L₂ : MultiTapeTM k Bool S₂)
    (P₁ : MultiTapeTM k Bool S₃) (P₂ : MultiTapeTM k Bool S₄) (r : Fin 7 → Fin k) :=
  seq (subInit L₁ L₂ r) (subtractionCore (seq P₁ P₂) r)

/-- The subtraction constructor has finite control whenever its argument routines do. -/
theorem numericSubGenerator_finite {k : ℕ} {S₁ S₂ S₃ S₄ : Type}
    [Finite S₁] [Finite S₂] [Finite S₃] [Finite S₄]
    (L₁ : MultiTapeTM k Bool S₁) (L₂ : MultiTapeTM k Bool S₂)
    (P₁ : MultiTapeTM k Bool S₃) (P₂ : MultiTapeTM k Bool S₄) (r : Fin 7 → Fin k) :
    Finite (StateOf (numericSubGenerator L₁ L₂ P₁ P₂ r)) := by
  let := Fintype.ofFinite S₁
  let := Fintype.ofFinite S₂
  let := Fintype.ofFinite S₃
  let := Fintype.ofFinite S₄
  let (b : Bool) : Fintype (if b then StateOf (const [] (r 6)) else Unit) := by
    cases b
    · change Fintype Unit
      infer_instance
    · change Fintype (StateOf (const [] (r 6)))
      unfold const
      infer_instance
  let : Fintype (StateOf (subInit L₁ L₂ r)) := by
    unfold subInit maxCounter
    infer_instance
  let : Fintype (StateOf (subScan (seq P₁ P₂) r)) := by
    unfold subScan concatLoop subDigit saveLastOne
    infer_instance
  let : Fintype (StateOf (subRestart r)) := by
    unfold subRestart subSelectLength chooseEmpty chooseSymbol
    infer_instance
  unfold numericSubGenerator subtractionCore mute
  infer_instance

/-- The finite execution bound for initialization, both scans, and cleanup. -/
@[expose] def numericSubTime (L₁ L₂ T₁ T₂ B N : ℕ) : ℕ :=
  (L₁ + L₂ + N * (8 * B + 24) + 11 * B + 27) +
    (2 * (N * (T₁ + T₂ + 21 * B + 54) + 1) + 33 * B + 77)

/-- Length and digit routines compose into numerical subtraction on virtual arguments.
The four counter and carry registers may initially contain old data; all seven ports
are blank on return. -/
theorem numericSubGenerator_emitsIn {k : ℕ} {S₁ S₂ S₃ S₄ : Type}
    {L₁ : MultiTapeTM k Bool S₁} {L₂ : MultiTapeTM k Bool S₂}
    {P₁ : MultiTapeTM k Bool S₃} {P₂ : MultiTapeTM k Bool S₄}
    (r : Fin 7 → Fin k) (hr : Function.Injective r)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {V W : List Bool → (Fin k → List Bool) → List Bool} {TL₁ TL₂ T₁ T₂ B N : ℕ → ℕ}
    (hl₁ : ReadsLength L₁ (r 4) Pre V TL₁ B) (hl₂ : ReadsLength L₂ (r 5) Pre W TL₂ B)
    (hA : ReadsAtAll P₁ (r 5) (r 0) Pre (fun input σ ↦ W input σ ++ [true]) T₁ B)
    (hB : ReadsAtAll P₂ (r 5) (r 1) Pre (fun input σ ↦ V input σ ++ [true]) T₂ B)
    (hpre : ∀ input σ i w, Pre input σ → Pre input (Function.update σ (r i) w))
    (hV : ∀ input σ i w, V input (Function.update σ (r i) w) = V input σ)
    (hW : ∀ input σ i w, W input (Function.update σ (r i) w) = W input σ)
    (hlen : ∀ input σ, Pre input σ →
      max (V input σ).length (W input σ).length + 1 ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    EmitsIn (numericSubGenerator L₁ L₂ P₁ P₂ r)
      (fun input σ ↦ Pre input σ ∧ σ (r 0) = [] ∧ σ (r 1) = [] ∧ σ (r 3) = [])
      (fun _ σ ↦ subDoneVal r σ) (fun input σ ↦ numericSub (V input σ) (W input σ))
      (fun n ↦ numericSubTime (TL₁ n) (TL₂ n) (T₁ n) (T₂ n) (B n) (N n)) B := by
  have hi := subInit_transformsIn r hr hl₁ hl₂ hpre hW hlen hsize hB1
  have hs := subtractionCore_numericSub_emitsIn r hr hA hB hpre hV hW hlen hsize hB1
  have hv input σ ps c j : V input (subScanVal σ r ps c j) = V input σ := by
    simp only [subScanVal, concatVal, hV]
  have hw input σ ps c j : W input (subScanVal σ r ps c j) = W input σ := by
    simp only [subScanVal, concatVal, hW]
  have hpv input σ ps c j (hp : Pre input σ) : Pre input (subScanVal σ r ps c j) :=
    hpre input _ 6 _ (hpre input _ 2 _ (hpre input _ 5 _ (hpre input _ 4 _ hp)))
  have h := (hi.seqEmitsIn hs).mono_pre (Pre' := fun input σ ↦
      Pre input σ ∧ σ (r 0) = [] ∧ σ (r 1) = [] ∧ σ (r 3) = []) (by
    intro input σ _ hp
    refine ⟨hp.1, hpv _ _ _ _ _ hp.1, ?_, ?_, ?_⟩
    · rw [hv, hw]
      simp [subScanVal, concatVal, hr.eq_iff]
    · simp [subScanVal, hr.eq_iff, subCarry]
    · intro i hi2 hi4
      fin_cases i <;> simp_all [subScanVal, concatVal, hr.eq_iff, subDigits, trim,
        show counterWord 0 = [] from rfl])
  refine (h.congr ?_).congr_output ?_
  · intro input σ _
    funext i
    by_cases hi : ∃ s, i = r s
    · obtain ⟨s, rfl⟩ := hi
      fin_cases s <;> simp [subDoneVal, subScanVal, concatVal, hr.eq_iff]
    · have hn (s) : i ≠ r s := fun h ↦ hi ⟨s, h⟩
      simp [subDoneVal, subScanVal, concatVal, Function.update_of_ne, hn]
  · intro input σ _
    rw [hv, hw]

end

end Geb.Oitavem.Machine
