/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Recursion
public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Reader

set_option doc.verso true in
/-!
# Generators retaining logarithmic prefixes

A polynomially long virtual word supplies a binary length large enough to serve
as a logarithmic capture mask. The word itself is streamed, so its length is the
only value that needs storage. A retained-prefix machine captures the base and
intermediate outputs, then emits the full final step and clears its work tapes.

## Main statements

* {lit}`Generator.exists_prefixMask` supplies a mask for any fixed logarithmic
  coefficient.
* {lit}`Generator.retained` assembles a machine from a saved-prefix invariant.

## Implementation notes

The mask is constructed from fixed products of the physical input. All machine
contracts inherit {lit}`Classical.choice` from CSLib.

## Tags

logspace, retained prefix, recursion, Turing machine
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- A virtual polynomial-length word has a binary length exceeding any fixed
logarithmic cutoff, while the binary length itself remains logarithmic. -/
theorem Generator.exists_prefixMask (m : ℕ)
    (Pre : List Bool → (Fin m → List Bool) → Prop) (A : ℕ) :
    ∃ W : List Bool → (Fin m → List Bool) → List Bool,
      Nonempty (Generator m Pre W) ∧
      (∀ input σ, Pre input σ → A * (input.length.size + 1) ≤ (W input σ).length.size) ∧
      ∃ C : ℕ, ∀ input σ, Pre input σ →
        ((W input σ).length + 1).size ≤ C * (input.length.size + 1) := by
  let G : Generator m Pre (fun input _ ↦ input) :=
    Generator.input.rename (fun i ↦ i.elim0) (fun _ _ _ ↦ trivial)
  let four := ((((Generator.empty m Pre).succ false).succ false).succ false).succ false
  let Base := (G.succ false).product four (fun _ ↦ 4) 3 (fun _ _ _ ↦ le_rfl) (by
    intro n
    have hn : 3 ≤ 3 * (n.size + 1) := by omega
    exact (show (4 + 1).size ≤ 3 by decide).trans hn)
  have hb (input : List Bool) (_σ : Fin m → List Bool) :
      ((List.replicate 4 (false :: input)).flatten : List Bool).length =
      4 * (input.length + 1) := by
    simp only [List.length_flatten, List.map_replicate, List.sum_replicate,
      List.length_cons, nsmul_eq_mul, Nat.cast_id]
  have hpoly : IsPolyBounded (fun n ↦ 4 * (n + 1)) :=
    isPolyBounded_mul (isPolyBounded_const 4) isPolyBounded_succ
  obtain ⟨C, hC⟩ := logarithmic_size_of_polyBounded hpoly
  have hp (a : ℕ) : ∃ W : List Bool → (Fin m → List Bool) → List Bool,
      Nonempty (Generator m Pre W) ∧
        ∀ input σ, (W input σ).length = (4 * (input.length + 1)) ^ a := by
    refine Nat.rec ?_ ?_ a
    · exact ⟨fun _ _ ↦ [false], ⟨(Generator.empty m Pre).succ false⟩, fun _ _ ↦ rfl⟩
    · intro a ih
      obtain ⟨W, ⟨P⟩, hP⟩ := ih
      refine ⟨_, ⟨P.product Base (fun n ↦ 4 * (n + 1)) C
        (fun input σ _ ↦ (hb input σ).le) hC⟩, ?_⟩
      intro input σ
      simp only [List.length_flatten, List.map_replicate, List.sum_replicate,
        List.length_cons, List.length_nil, nsmul_eq_mul, Nat.cast_id, hP, Nat.pow_succ,
        Nat.mul_comm]
  obtain ⟨W, hG, hW⟩ := hp A
  refine ⟨W, hG, ?_, ?_⟩
  · intro input σ _
    rw [hW]
    have hpow : 2 ^ (A * (input.length.size + 1)) ≤ (4 * (input.length + 1)) ^ A := by
      rw [Nat.mul_comm A, Nat.pow_mul]
      apply Nat.pow_le_pow_left
      rw [Nat.pow_succ]
      have := pow_size_le input.length
      omega
    have hs := size_le_size hpow
    rw [Nat.size_pow] at hs
    omega
  · have hpA : IsPolyBounded (fun n ↦ (4 * (n + 1)) ^ A) :=
      ⟨4 ^ A, A, fun n ↦ (Nat.mul_pow 4 (n + 1) A).le⟩
    obtain ⟨D, hD⟩ := logarithmic_size_of_polyBounded hpA
    exact ⟨D, fun input σ _ ↦ by rw [hW]; exact hD _⟩

/-- A recursive step receives a bounded saved prefix and a canonical countdown.
The mask is one of the original protected registers. -/
@[expose] def RetainedPre {m : ℕ} (Pre : List Bool → (Fin m → List Bool) → Prop)
    (M : Fin m) (N : ℕ → ℕ) (input : List Bool) (σ : Fin (m + 2) → List Bool) : Prop :=
  Pre input (fun i ↦ σ (i.castAdd 2)) ∧
    (σ (Fin.natAdd m 0)).length ≤ (σ (M.castAdd 2)).length ∧
      ∃ q, σ (Fin.natAdd m 1) = counterWord q ∧ q ≤ N input.length

/-- Updating an old tape commutes with reserving the mask and capture buffer. -/
theorem update_tapeCase_oldTape {k : ℕ} (c b w : List Bool) (σ : Fin k → List Bool)
    (R : Fin k) : Function.update (tapeCase c b σ) (oldTape R) w =
      tapeCase c b (Function.update σ R w) := by
  funext i
  rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
  · simp [Function.update_of_ne (oldTape_ne_countTape R).symm]
  · simp [Function.update_of_ne (oldTape_ne_resultTape R).symm]
  · by_cases hi : i = R
    · subst i
      simp
    · have hi' : oldTape i ≠ oldTape R := fun he ↦
        hi (Fin.succ_injective _ (Fin.succ_injective _ he))
      simp [hi, hi']

namespace Generator

variable {m : ℕ} {Pre : List Bool → (Fin m → List Bool) → Prop}
  {W V : List Bool → (Fin m → List Bool) → List Bool} {N : ℕ → ℕ}
  {H : List Bool → (Fin m → List Bool) → List Bool → ℕ → List Bool}

/-- Initialize a capture mask and countdown, retain the base and intermediate
outputs, and emit the final step before clearing the saved prefix and mask. -/
@[expose] def retainedProgram (G : Generator m Pre W) (Base : Generator m Pre V) (M : Fin m)
    (P : Generator (m + 2) (RetainedPre Pre M N) (fun input σ ↦
      H input (fun i ↦ σ (i.castAdd 2)) (σ (Fin.natAdd m 0))
        (counterValue (σ (Fin.natAdd m 1))))) :=
  let K := G.tapes + Base.tapes + P.tapes + 1
  let L := onTapes (G.lengthReader (Fin.castAdd 2) (Fin.natAdd m (1 : Fin 2)))
    (padLayout (m + 2) (G.tapes + 1) K (by omega))
  let B := onTapes (Base.call (Fin.castAdd 2))
    (padLayout (m + 2) Base.tapes K (by omega))
  let S := (P.pad K (by omega)).program
  let r (j : Fin 2) : Fin (m + 2 + K) := (j.natAdd m).castAdd K
  let e := reserveTwo (m + 2 + K)
  seq (copy (oldTape ((M.castAdd 2).castAdd K)) countTape)
    (seq (onTapes L e) (seq (generatedPrefix B (r 0))
      (seq (retainedLoop S (r 0) (r 1)) (seq (onTapes S e)
        (seq (const [] (oldTape (r 0))) (const [] countTape))))))

/-- The saved-prefix program has finite control. -/
theorem retainedProgram_finite (G : Generator m Pre W) (Base : Generator m Pre V) (M : Fin m)
    (P : Generator (m + 2) (RetainedPre Pre M N) (fun input σ ↦
      H input (fun i ↦ σ (i.castAdd 2)) (σ (Fin.natAdd m 0))
        (counterValue (σ (Fin.natAdd m 1))))) :
    Finite (StateOf (G.retainedProgram Base M P)) := by
  let := G.lengthReader_finite (Fin.castAdd 2) (Fin.natAdd m (1 : Fin 2))
  let := Fintype.ofFinite (StateOf (G.lengthReader (Fin.castAdd 2) (Fin.natAdd m (1 : Fin 2))))
  let := Base.call_finite (Fin.castAdd 2 : Fin m → Fin (m + 2))
  let := Fintype.ofFinite (StateOf (Base.call (Fin.castAdd 2 : Fin m → Fin (m + 2))))
  let := P.call_finite id
  let := Fintype.ofFinite (StateOf (P.call id))
  have hcapture {k : ℕ} {S : Type} [Finite S] (Q : MultiTapeTM k Bool S) (R : Fin k) :
      Finite (StateOf (generatedPrefix Q R)) := by
    let := Fintype.ofFinite S
    unfold generatedPrefix capturePrefix
    infer_instance
  have hloop {k : ℕ} {S : Type} [Finite S] (Q : MultiTapeTM k Bool S) (R C : Fin k) :
      Finite (StateOf (retainedLoop Q R C)) := by
    let := hcapture Q R
    let := Fintype.ofFinite (StateOf (generatedPrefix Q R))
    unfold retainedLoop
    infer_instance
  let K := G.tapes + Base.tapes + P.tapes + 1
  let r (j : Fin 2) : Fin (m + 2 + K) := (j.natAdd m).castAdd K
  let B := onTapes (Base.call (Fin.castAdd 2 : Fin m → Fin (m + 2)))
    (padLayout (m + 2) Base.tapes K (by dsimp [K]; omega))
  let S := (P.pad K (by dsimp [K]; omega)).program
  let := hcapture B (r 0)
  let := Fintype.ofFinite (StateOf (generatedPrefix B (r 0)))
  let := hloop S (r 0) (r 1)
  let := Fintype.ofFinite (StateOf (retainedLoop S (r 0) (r 1)))
  unfold retainedProgram
  infer_instance

/-- Realize a saved-prefix invariant. The final step emits its full output,
and only the bounded intermediate prefixes are stored. -/
@[expose] def retained (G : Generator m Pre W) (Base : Generator m Pre V) (M : Fin m)
    (P : Generator (m + 2) (RetainedPre Pre M N) (fun input σ ↦
      H input (fun i ↦ σ (i.castAdd 2)) (σ (Fin.natAdd m 0))
        (counterValue (σ (Fin.natAdd m 1)))))
    (Value : List Bool → (Fin m → List Bool) → ℕ → List Bool)
    (D : List Bool → (Fin m → List Bool) → List Bool) (C : ℕ)
    (hlen : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n + 1).size ≤ C * (n.size + 1))
    (hzero : ∀ input σ, Pre input σ → Value input σ 0 = (V input σ).take (σ M).length)
    (hval : ∀ input σ, Pre input σ → ∀ j ≤ (W input σ).length,
      (Value input σ j).length ≤ (σ M).length)
    (hstep : ∀ input σ, Pre input σ → ∀ j < (W input σ).length,
      (H input σ (Value input σ j) ((W input σ).length - j)).take (σ M).length =
        Value input σ (j + 1))
    (hdone : ∀ input σ, Pre input σ →
      H input σ (Value input σ (W input σ).length) 0 = D input σ) : Generator m Pre D :=
  ⟨m + 2 + (G.tapes + Base.tapes + P.tapes + 1) + 2,
    StateOf (G.retainedProgram Base M P),
    { finite := G.retainedProgram_finite Base M P
      env := fun i ↦ oldTape ((i.castAdd 2).castAdd (G.tapes + Base.tapes + P.tapes + 1))
      env_injective := (Fin.succ_injective _).comp ((Fin.succ_injective _).comp
        ((Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)))
      program := G.retainedProgram Base M P
      space := G.space + Base.space + P.space + C
      correct B hB := by
        let K := G.tapes + Base.tapes + P.tapes + 1
        let k := m + 2 + K
        let r (j : Fin 2) : Fin k := (j.natAdd m).castAdd K
        let env (i : Fin m) : Fin k := (i.castAdd 2).castAdd K
        let Pre₁ input (σ : Fin k → List Bool) :=
          Pre input (fun i ↦ σ (env i)) ∧ Initialized (Fin.castAdd K : Fin (m + 2) → _) σ
        let Pre₀ input σ (L : ℕ) := Pre₁ input σ ∧ L = (σ (env M)).length
        have hr : Function.Injective r :=
          (Fin.castAdd_injective _ _).comp (Fin.natAdd_injective _ _)
        have h01 : r 0 ≠ r 1 := hr.ne (by decide)
        have hsep (i : Fin m) (j : Fin 2) : env i ≠ r j := by
          apply Fin.ne_of_val_ne
          simp only [env, r, Fin.val_castAdd, Fin.val_natAdd]
          omega
        have henv (σ : Fin k → List Bool) (j : Fin 2) (w : List Bool) :
            (fun i ↦ Function.update σ (r j) w (env i)) = fun i ↦ σ (env i) :=
          funext (fun i ↦ Function.update_of_ne (hsep i j) _ _)
        have hpre input σ j w (hp : Pre₁ input σ) :
            Pre₁ input (Function.update σ (r j) w) :=
          ⟨by simpa only [henv] using hp.1, hp.2.update (j.natAdd m) w⟩
        have hG (n) : G.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _
            (by omega : G.space ≤ G.space + Base.space + P.space + C)).trans (hB n)
        have hBase (n) : Base.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _
            (by omega : Base.space ≤ G.space + Base.space + P.space + C)).trans (hB n)
        have hP (n) : P.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _
            (by omega : P.space ≤ G.space + Base.space + P.space + C)).trans (hB n)
        have hN (n) : (N n + 1).size ≤ B n := (hsize n).trans
          ((Nat.mul_le_mul_right _
            (by omega : C ≤ G.space + Base.space + P.space + C)).trans (hB n))
        obtain ⟨TL, hl⟩ :=
          G.lengthReader_readsLength (Fin.castAdd 2) (Fin.natAdd m (1 : Fin 2)) B hG
            (fun input σ hp ↦
              (size_le_size (Nat.add_le_add_right (hlen input σ hp) 1)).trans (hN _))
        have hl' := hl.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (i.castAdd 2)))
          (W := fun input σ ↦ W input (fun i ↦ σ (i.castAdd 2)))
          (padLayout (m + 2) (G.tapes + 1) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        change ReadsLength _ (r 1) Pre₁ (fun input σ ↦ W input (fun i ↦ σ (env i))) TL B at hl'
        have hl'' := hl'.onTapes (reserveTwo k)
        have he (i : Fin k) : (reserveTwo k).symm (.inl i) = oldTape i := rfl
        simp only [he] at hl''
        let Base' := (Base.rename (Fin.castAdd 2 : Fin m → Fin (m + 2))
          (fun _ _ hp ↦ hp)).allocate
            (padLayout (m + 2) Base.tapes K (by dsimp [K]; omega))
        obtain ⟨TB, hb⟩ := Base'.correct B hBase
        have hbenv : Base'.env = Fin.castAdd K := funext (fun i ↦ padLayout_env ..)
        simp only [hbenv] at hb
        change EmitsIn _ Pre₁ (fun _ σ ↦ σ) (fun input σ ↦ V input (fun i ↦ σ (env i)))
          TB B at hb
        obtain ⟨TP, hp⟩ := (P.pad K (by dsimp [K]; omega)).correct B hP
        simp only [pad_env] at hp
        have loop := retainedLoop_transformsIn (r 0) (r 1) h01 hp Pre₀
          (fun input σ ↦ (W input (fun i ↦ σ (env i))).length)
          (fun input σ _ j ↦ Value input (fun i ↦ σ (env i)) j)
          (fun input σ _ h ↦ hlen input _ h.1.1)
          (fun input σ _ h j hj ↦ (hval input _ h.1.1 j hj).trans_eq h.2.symm) (by
            intro input σ L h j hj
            have hp' := hpre input _ 1
              (counterWord ((W input (fun i ↦ σ (env i))).length - j))
              (hpre input σ 0 (Value input (fun i ↦ σ (env i)) j) h.1)
            have he : (fun i ↦ retainedVal σ (r 0) (r 1)
                ((W input (fun i ↦ σ (env i))).length - j)
                (Value input (fun i ↦ σ (env i)) j) (env i)) = fun i ↦ σ (env i) := by
              simp only [retainedVal, henv]
            refine ⟨⟨⟨?_, ?_, (W input (fun i ↦ σ (env i))).length - j,
              Function.update_self .., ?_⟩, hp'.2⟩, ?_⟩
            · change Pre input (fun i ↦ retainedVal σ (r 0) (r 1) _ _ (env i))
              rw [he]
              exact h.1.1
            · change (retainedVal σ (r 0) (r 1) _ _ (r 0)).length ≤
                (retainedVal σ (r 0) (r 1) _ _ (env M)).length
              simp only [retainedVal, Function.update_of_ne h01,
                Function.update_self, Function.update_of_ne (hsep M 1),
                Function.update_of_ne (hsep M 0)]
              exact hval input _ h.1.1 j (by omega)
            · exact (Nat.sub_le _ _).trans (hlen input _ h.1.1)
            · change (H input (fun i ↦ retainedVal σ (r 0) (r 1) _ _ (env i))
                (retainedVal σ (r 0) (r 1) _ _ (r 0))
                (counterValue (retainedVal σ (r 0) (r 1) _ _ (r 1)))).take L = _
              rw [he]
              simp only [retainedVal, Function.update_self,
                Function.update_of_ne h01, counterValue_counterWord, h.2]
              exact hstep input _ h.1.1 j hj)
        have final := (hp.onTapes (reserveTwo k)).congr
          (fun _ σ _ ↦ onTapesVal_self (reserveTwo k) σ)
        change EmitsIn _ (fun input σ ↦
          (Pre input (fun i ↦ σ (oldTape (env i))) ∧
            (σ (oldTape (r 0))).length ≤ (σ (oldTape (env M))).length ∧
            ∃ q, σ (oldTape (r 1)) = counterWord q ∧ q ≤ N input.length) ∧
            Initialized (Fin.castAdd K) (fun i ↦ σ (oldTape i)))
          (fun _ σ ↦ σ) (fun input σ ↦ H input (fun i ↦ σ (oldTape (env i)))
            (σ (oldTape (r 0))) (counterValue (σ (oldTape (r 1))))) TP B at final
        have init := Transforms.toIn_of (fun n ↦ copy_transforms
          (oldTape (env M)) countTape (oldTape_ne_countTape _) (B n))
          (fun _ _ ↦ True) (fun _ _ h _ ↦ h.update (h (oldTape (env M))))
        have clearR := Transforms.toIn_of (fun n ↦ const_transforms [] (oldTape (r 0)) (B n))
          (fun _ _ ↦ True) (fun _ _ h _ ↦ h.update (Nat.zero_le _))
        have clearM := Transforms.toIn_of (fun n ↦ const_transforms [] (countTape : Fin (k + 2))
          (B n)) (fun _ _ ↦ True) (fun _ _ h _ ↦ h.update (Nat.zero_le _))
        have hs := init.seqEmitsIn (hl''.seqEmitsIn
          ((generatedPrefix_transformsIn hb (r 0)).seqEmitsIn
            (loop.seqEmitsIn (final.seqTransformsIn (clearR.seq clearM)))))
        dsimp only [Base', allocate, rename, program] at hs
        have hσtape (σ : Fin (k + 2) → List Bool)
            (hσ : Initialized (fun i ↦ oldTape (env i)) σ) :
            σ = tapeCase [] [] (fun i ↦ σ (oldTape i)) := by
          funext i
          rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
          · exact hσ countTape (fun i ↦ (oldTape_ne_countTape (env i)).symm)
          · exact hσ resultTape (fun i ↦ (oldTape_ne_resultTape (env i)).symm)
          · rfl
        have hinj : Function.Injective (oldTape : Fin k → Fin (k + 2)) :=
          (Fin.succ_injective _).comp (Fin.succ_injective _)
        refine ⟨_, ((hs.mono_pre ?_).congr ?_).congr_output ?_⟩
        · intro input σ _ hσ
          rw [hσtape σ hσ.2]
          simp only [update_tapeCase_countTape, update_tapeCase_oldTape, tapeCase_oldTape,
            tapeCase_countTape, tapeCase_resultTape, henv, Pre₀, retainedVal,
            Function.update_of_ne h01, Function.update_of_ne h01.symm, Function.update_self,
            Function.update_of_ne (hsep M 0), Function.update_of_ne (hsep M 1)]
          have hi : Pre₁ input (fun i ↦ σ (oldTape i)) := ⟨hσ.1,
            fun i h ↦ hσ.2 (oldTape i) (fun j he ↦ h (j.castAdd 2) (hinj he))⟩
          have hiL := hpre input (fun i ↦ σ (oldTape i)) 1
            (counterWord (W input (fun i ↦ σ (oldTape (env i)))).length) hi
          have hiB := hpre input _ 0
            ((V input (fun i ↦ σ (oldTape (env i)))).take (σ (oldTape (env M))).length) hiL
          refine ⟨trivial, hi, hiL,
            ⟨⟨hiB, trivial⟩, trivial, trivial, (hzero input _ hσ.1).symm⟩,
            ⟨⟨hσ.1, hval input _ hσ.1 _ le_rfl, 0, rfl, Nat.zero_le _⟩, ?_⟩,
            trivial, trivial⟩
          exact (hiB.2.update (Fin.natAdd m (0 : Fin 2)) _).update
            (Fin.natAdd m (1 : Fin 2)) _
        · intro input σ hσ
          rw [hσtape σ hσ.2]
          simp only [update_tapeCase_countTape, update_tapeCase_oldTape, tapeCase_oldTape,
            tapeCase_countTape, henv, retainedVal]
          have hu (j) : Function.update (fun i ↦ σ (oldTape i)) (r j) [] =
              fun i ↦ σ (oldTape i) := by
            rw [← hσ.2 (oldTape (r j)) (fun i he ↦ (hsep i j).symm (hinj he))]
            exact Function.update_eq_self ..
          simp only [Function.update_idem, Function.update_comm h01,
            show counterWord 0 = [] from rfl, hu]
        · intro input σ hσ
          rw [hσtape σ hσ.2]
          simp only [update_tapeCase_countTape, update_tapeCase_oldTape, tapeCase_oldTape,
            tapeCase_countTape, henv, retainedVal, Function.update_of_ne h01,
            Function.update_self, counterValue_counterWord]
          exact hdone input _ hσ.1
    }⟩

end Generator

end

end Geb.Oitavem.Machine
