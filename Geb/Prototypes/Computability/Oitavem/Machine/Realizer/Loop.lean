/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Reader
public import Geb.Prototypes.Computability.Oitavem.Machine.Recursion

set_option doc.verso true in
/-!
# Indexed generators with reusable work tapes

An indexed step receives the caller's environment and one canonical binary
query. A generated length initializes the loop, which emits one step digit per
position. The query and countdown are cleared on return, and every step reuses
the same private tapes.

## Main definitions

* {lit}`QueryPre` extends a protected environment by a bounded binary query.
* {lit}`Generator.indexed` streams a word from its length and indexed digits.
* {lit}`Generator.withLength` lends a generated binary length to a continuation.

## Implementation notes

The programs use the existing generated length reader and emitting loop. Their
contracts inherit {lit}`Classical.choice` from CSLib.

## Tags

Turing machine, logarithmic space, indexed loop, generator
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Extend a protected environment by a canonical binary query with a uniform bound. -/
@[expose] def QueryPre {m : ℕ} (Pre : List Bool → (Fin m → List Bool) → Prop)
    (N : ℕ → ℕ) (input : List Bool) (σ : Fin (m + 1) → List Bool) : Prop :=
  Pre input (fun i ↦ σ i.castSucc) ∧
    ∃ q, σ (Fin.last m) = counterWord q ∧ q ≤ N input.length

/-- Extend an environment by the canonical binary length of a generated word. -/
@[expose] def LengthPre {m : ℕ} (Pre : List Bool → (Fin m → List Bool) → Prop)
    (W : List Bool → (Fin m → List Bool) → List Bool)
    (input : List Bool) (σ : Fin (m + 1) → List Bool) : Prop :=
  Pre input (fun i ↦ σ i.castSucc) ∧
    σ (Fin.last m) = counterWord (W input (fun i ↦ σ i.castSucc)).length

namespace Generator

variable {m : ℕ} {Pre : List Bool → (Fin m → List Bool) → Prop}
  {W : List Bool → (Fin m → List Bool) → List Bool} {N : ℕ → ℕ}
  {F : List Bool → (Fin m → List Bool) → ℕ → Bool}

/-- Initialize a countdown, emit indexed digits, and clear the query. -/
@[expose] def indexedProgram (G : Generator m Pre W)
    (P : Generator (m + 1) (QueryPre Pre N)
      (fun input σ ↦ [F input (fun i ↦ σ i.castSucc) (counterValue (σ (Fin.last m)))])) :=
  let K := G.tapes + P.tapes + 1
  let L := onTapes (G.lengthReader (Fin.castAdd 2) (Fin.natAdd m (1 : Fin 2)))
    (padLayout (m + 2) (G.tapes + 1) K (by omega))
  let S := onTapes (P.call (Fin.castSucc : Fin (m + 1) → Fin (m + 2)))
    (padLayout (m + 2) P.tapes K (by omega))
  let r (j : Fin 2) : Fin (m + 2 + K) := (j.natAdd m).castAdd K
  seq L (seq (concatLoop S (r 1) (r 0)) (const [] (r 0)))

/-- Indexed assembly has finite control when the length source and step do. -/
theorem indexedProgram_finite (G : Generator m Pre W)
    (P : Generator (m + 1) (QueryPre Pre N)
      (fun input σ ↦ [F input (fun i ↦ σ i.castSucc) (counterValue (σ (Fin.last m)))])) :
    Finite (StateOf (G.indexedProgram P)) := by
  let := G.lengthReader_finite (Fin.castAdd 2) (Fin.natAdd m (1 : Fin 2))
  let := P.call_finite (Fin.castSucc : Fin (m + 1) → Fin (m + 2))
  let := Fintype.ofFinite (StateOf (G.lengthReader (Fin.castAdd 2) (Fin.natAdd m (1 : Fin 2))))
  let := Fintype.ofFinite (StateOf (P.call (Fin.castSucc : Fin (m + 1) → Fin (m + 2))))
  unfold indexedProgram concatLoop
  infer_instance

/-- A generated length and a restoring indexed step stream the specified word.
The step's behavior past the word's end is immaterial to this loop. -/
@[expose] def indexed (G : Generator m Pre W)
    (P : Generator (m + 1) (QueryPre Pre N)
      (fun input σ ↦ [F input (fun i ↦ σ i.castSucc) (counterValue (σ (Fin.last m)))]))
    (D : List Bool → (Fin m → List Bool) → List Bool) (C : ℕ)
    (hlen : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n + 1).size ≤ C * (n.size + 1))
    (hD : ∀ input σ, Pre input σ → (D input σ).length = (W input σ).length)
    (hdigit : ∀ input σ, Pre input σ → ∀ j < (D input σ).length,
      F input σ j = (D input σ)[j]?.getD false) : Generator m Pre D :=
  ⟨m + 2 + (G.tapes + P.tapes + 1), StateOf (G.indexedProgram P),
    { finite := G.indexedProgram_finite P
      env := fun i ↦ (i.castAdd 2).castAdd (G.tapes + P.tapes + 1)
      env_injective := (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)
      program := G.indexedProgram P
      space := G.space + P.space + C
      correct B hB := by
        let K := G.tapes + P.tapes + 1
        let r (j : Fin 2) : Fin (m + 2 + K) := (j.natAdd m).castAdd K
        let env (j : Fin m) : Fin (m + 2 + K) := (j.castAdd 2).castAdd K
        let Pre₀ input (σ : Fin (m + 2 + K) → List Bool) :=
          Pre input (fun i ↦ σ (env i)) ∧ Initialized (Fin.castAdd K : Fin (m + 2) → _) σ
        have hr : Function.Injective r :=
          (Fin.castAdd_injective _ _).comp (Fin.natAdd_injective _ _)
        have hsep (i : Fin m) (j : Fin 2) : env i ≠ r j := by
          apply Fin.ne_of_val_ne
          simp only [env, r, Fin.val_castAdd, Fin.val_natAdd]
          omega
        have henv (σ : Fin (m + 2 + K) → List Bool) (j : Fin 2) (w : List Bool) :
            (fun i ↦ Function.update σ (r j) w (env i)) = fun i ↦ σ (env i) :=
          funext (fun i ↦ Function.update_of_ne (hsep i j) _ _)
        have hpre input σ j w (hp : Pre₀ input σ) :
            Pre₀ input (Function.update σ (r j) w) :=
          ⟨by simpa only [henv] using hp.1, hp.2.update (j.natAdd m) w⟩
        have hG (n) : G.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by omega : G.space ≤ G.space + P.space + C)).trans (hB n)
        have hP (n) : P.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by omega : P.space ≤ G.space + P.space + C)).trans (hB n)
        have hN (n) : (N n + 1).size ≤ B n := (hsize n).trans
          ((Nat.mul_le_mul_right _ (by omega : C ≤ G.space + P.space + C)).trans (hB n))
        obtain ⟨TL, hl⟩ :=
          G.lengthReader_readsLength (Fin.castAdd 2) (Fin.natAdd m (1 : Fin 2)) B hG
          (fun input σ hp ↦ (size_le_size (Nat.add_le_add_right (hlen input σ hp) 1)).trans (hN _))
        have hl' := hl.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (i.castAdd 2)))
          (W := fun input σ ↦ W input (fun i ↦ σ (i.castAdd 2)))
          (padLayout (m + 2) (G.tapes + 1) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        let S := (P.rename (Fin.castSucc : Fin (m + 1) → Fin (m + 2))
          (fun _ _ hp ↦ hp)).allocate (padLayout (m + 2) P.tapes K (by dsimp [K]; omega))
        have hSenv : S.env = Fin.castAdd K := funext (fun i ↦ padLayout_env ..)
        obtain ⟨TS, hs⟩ := S.correct B hP
        simp only [hSenv] at hs
        have hloop := concatLoop_emitsIn (r 1) (r 0) (hr.ne (by decide)) hs Pre₀
          (fun input σ ↦ D input (fun i ↦ σ (env i)))
          (fun input σ hp ↦ (hD input _ hp.1).trans_le (hlen input _ hp.1))
          (fun n ↦ (size_le_size (Nat.le_succ (N n))).trans (hN n)) (by
            intro input σ hp j hj
            have hp' := hpre input _ 0 (counterWord j)
              (hpre input σ 1 (counterWord ((D input (fun i ↦ σ (env i))).length - j)) hp)
            have he : (fun i ↦ concatVal σ (r 1) (r 0)
                (D input (fun i ↦ σ (env i))).length j (env i)) = fun i ↦ σ (env i) := by
              simp only [concatVal, henv]
            refine ⟨⟨⟨?_, j, ?_, ?_⟩, hp'.2⟩, ?_⟩
            · change Pre input (fun i ↦ concatVal σ (r 1) (r 0) _ j (env i))
              rw [he]
              exact hp.1
            · exact Function.update_self ..
            · have := hlen input (fun i ↦ σ (env i)) hp.1
              rw [hD input _ hp.1] at hj
              omega
            · change [F input (fun i ↦ concatVal σ (r 1) (r 0) _ j (env i))
                (counterValue (concatVal σ (r 1) (r 0) _ j (r 0)))] = _
              rw [he, concatVal, Function.update_self, counterValue_counterWord,
                hdigit input _ hp.1 j hj])
        have hc := Transforms.toIn_of (fun n ↦ const_transforms [] (r 0) (B n))
          (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (Nat.zero_le _))
        have h := hl'.seqEmitsIn (hloop.seqTransformsIn hc)
        dsimp only [S, allocate, rename, program] at h
        refine ⟨_, ((h.mono_pre ?_).congr ?_).congr_output ?_⟩
        · intro input σ _ hp
          have hp₀ : Pre₀ input σ := ⟨hp.1,
            fun i hi ↦ hp.2 i (fun j he ↦ hi (j.castAdd 2) he)⟩
          refine ⟨hp₀, ⟨hpre input σ 1 _ hp₀, ?_, ?_⟩, trivial⟩
          · rw [Function.update_self, henv, hD input _ hp.1]
          · rw [Function.update_of_ne (hr.ne (by decide))]
            exact hp.2 (r 0) (fun i ↦ (hsep i 0).symm)
        · intro input σ hp
          have hu (j) : Function.update σ (r j) [] = σ := by
            rw [← hp.2 (r j) (fun i ↦ (hsep i j).symm)]
            exact Function.update_eq_self ..
          dsimp only [r] at hu ⊢
          simp only [concatVal, Nat.sub_self, Function.update_idem,
            show counterWord 0 = [] from rfl, hu]
        · intro input σ _
          exact congrArg (D input) (henv σ 1 _)
    }⟩

/-- Count a generated word, run a continuation with that count, then clear it. -/
@[expose] def withLengthProgram {V : List Bool → (Fin m → List Bool) → List Bool}
    (G : Generator m Pre W)
    (P : Generator (m + 1) (LengthPre Pre W) (fun input σ ↦ V input (fun i ↦ σ i.castSucc))) :=
  let K := G.tapes + P.tapes + 1
  let L := onTapes (G.lengthReader Fin.castSucc (Fin.last m))
    (padLayout (m + 1) (G.tapes + 1) K (by omega))
  seq L (seq (P.pad K (by omega)).program (const [] ((Fin.last m).castAdd K)))

/-- A generated-length continuation has finite control. -/
theorem withLengthProgram_finite {V : List Bool → (Fin m → List Bool) → List Bool}
    (G : Generator m Pre W)
    (P : Generator (m + 1) (LengthPre Pre W) (fun input σ ↦ V input (fun i ↦ σ i.castSucc))) :
    Finite (StateOf (G.withLengthProgram P)) := by
  let := G.lengthReader_finite Fin.castSucc (Fin.last m)
  let := Fintype.ofFinite (StateOf (G.lengthReader Fin.castSucc (Fin.last m)))
  let := P.call_finite id
  let := Fintype.ofFinite (StateOf (P.call id))
  unfold withLengthProgram pad allocate rename program
  infer_instance

/-- A continuation may use a generated binary length in one additional protected
register. The register is cleared before returning to the original caller. -/
@[expose] def withLength {V : List Bool → (Fin m → List Bool) → List Bool}
    (G : Generator m Pre W)
    (P : Generator (m + 1) (LengthPre Pre W) (fun input σ ↦ V input (fun i ↦ σ i.castSucc)))
    (C : ℕ) (hsize : ∀ input σ, Pre input σ →
      ((W input σ).length + 1).size ≤ C * (input.length.size + 1)) : Generator m Pre V :=
  ⟨m + 1 + (G.tapes + P.tapes + 1), StateOf (G.withLengthProgram P),
    { finite := G.withLengthProgram_finite P
      env := fun i ↦ i.castSucc.castAdd (G.tapes + P.tapes + 1)
      env_injective := (Fin.castAdd_injective _ _).comp (Fin.castSucc_injective _)
      program := G.withLengthProgram P
      space := G.space + P.space + C
      correct B hB := by
        let K := G.tapes + P.tapes + 1
        let R := (Fin.last m).castAdd K
        let env (i : Fin m) := i.castSucc.castAdd K
        have hsep (i : Fin m) : env i ≠ R := fun he ↦
          Fin.castSucc_ne_last i ((Fin.castAdd_injective _ _) he)
        have henv (σ : Fin (m + 1 + K) → List Bool) (w : List Bool) :
            (fun i ↦ Function.update σ R w (env i)) = fun i ↦ σ (env i) :=
          funext (fun i ↦ Function.update_of_ne (hsep i) _ _)
        have hG (n) : G.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by omega : G.space ≤ G.space + P.space + C)).trans (hB n)
        have hP (n) : P.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by omega : P.space ≤ G.space + P.space + C)).trans (hB n)
        obtain ⟨TL, hl⟩ := G.lengthReader_readsLength Fin.castSucc (Fin.last m) B hG
          (fun input σ hp ↦ (hsize input σ hp).trans ((Nat.mul_le_mul_right _
            (by omega : C ≤ G.space + P.space + C)).trans (hB _)))
        have hl' := hl.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ i.castSucc))
          (W := fun input σ ↦ W input (fun i ↦ σ i.castSucc))
          (padLayout (m + 1) (G.tapes + 1) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        obtain ⟨TP, hp⟩ := (P.pad K (by dsimp [K]; omega)).correct B hP
        simp only [pad_env] at hp
        have hc := Transforms.toIn_of (fun n ↦ const_transforms [] R (B n))
          (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (Nat.zero_le _))
        have hs := hl'.seqEmitsIn (hp.seqTransformsIn hc)
        refine ⟨_, ((hs.mono_pre ?_).congr ?_).congr_output ?_⟩
        · intro input σ _ hσ
          have hi : Initialized (Fin.castAdd K : Fin (m + 1) → _) σ :=
            fun i h ↦ hσ.2 i (fun j he ↦ h j.castSucc he)
          refine ⟨⟨hσ.1, hi⟩, ⟨⟨?_, ?_⟩, hi.update (Fin.last m) _⟩, trivial⟩
          · change Pre input (fun i ↦ Function.update σ R _ (env i))
            rw [henv]
            exact hσ.1
          · change Function.update σ R _ R =
              counterWord (W input (fun i ↦ Function.update σ R _ (env i))).length
            rw [Function.update_self, henv]
        · intro input σ hσ
          rw [Function.update_idem, ← hσ.2 R (fun i ↦ (hsep i).symm)]
          exact Function.update_eq_self ..
        · intro input σ _
          exact congrArg (V input) (henv σ _)
    }⟩

end Generator

end

end Geb.Oitavem.Machine
