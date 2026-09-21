/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Realizer.Reader
public import Geb.Prototypes.Computability.Oitavem.Machine.Segment
public import Geb.Prototypes.Computability.Oitavem.Machine.Subtraction

set_option doc.verso true in
/-!
# Initial functions of generated arguments

The arithmetic and segment constructors call restoring readers of independently
compiled arguments. Those readers share one private workspace, because every
call returns it blank. Only the constructor's fixed ports remain live between
calls.

## Main definitions

* {lit}`Generator.numericSubProgram` assembles the four subtraction readers.
* {lit}`Generator.numericSub` realizes numerical subtraction of generated words.
* {lit}`Generator.iterPred` streams an iterated string predecessor.
* {lit}`Generator.cond` chooses between two independently generated branches.

## Main statements

* {lit}`Initial.realize` realizes every initial function on polynomially bounded
  generated arguments over a shared protected environment.

## Implementation notes

The programs use executable copies and explicit tape layouts. Their machine
contracts inherit {lit}`Classical.choice` from CSLib.

## Tags

Turing machine, logarithmic space, generator, subtraction
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine.Generator

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

variable {m : ℕ} {Pre : List Bool → (Fin m → List Bool) → Prop}
  {V W : List Bool → (Fin m → List Bool) → List Bool}

/-- Assemble length and sentinel-digit readers for a streaming subtraction.
All four readers reuse the same private tapes after the environment and seven ports. -/
@[expose] def numericSubProgram (G : Generator m Pre V) (H : Generator m Pre W) :=
  let K := G.tapes + H.tapes + 2
  let src : Fin m → Fin (m + 7) := Fin.castAdd 7
  let L₁ := onTapes (G.lengthReader src (Fin.natAdd m 4))
    (padLayout (m + 7) (G.tapes + 1) K (by omega))
  let L₂ := onTapes (H.lengthReader src (Fin.natAdd m 5))
    (padLayout (m + 7) (H.tapes + 1) K (by omega))
  let P₁ := onTapes ((H.appendBit true).atReader src (Fin.natAdd m 5) (Fin.natAdd m 0))
    (padLayout (m + 7) (H.tapes + 2) K (by omega))
  let P₂ := onTapes ((G.appendBit true).atReader src (Fin.natAdd m 5) (Fin.natAdd m 1))
    (padLayout (m + 7) (G.tapes + 2) K (by omega))
  numericSubGenerator L₁ L₂ P₁ P₂ (fun j ↦ (j.natAdd m).castAdd K)

/-- The assembled subtraction program has finite control. -/
theorem numericSubProgram_finite (G : Generator m Pre V) (H : Generator m Pre W) :
    Finite (StateOf (G.numericSubProgram H)) := by
  let src : Fin m → Fin (m + 7) := Fin.castAdd 7
  let := G.lengthReader_finite src (Fin.natAdd m 4)
  let := H.lengthReader_finite src (Fin.natAdd m 5)
  let := (H.appendBit true).atReader_finite src (Fin.natAdd m 5) (Fin.natAdd m 0)
  let := (G.appendBit true).atReader_finite src (Fin.natAdd m 5) (Fin.natAdd m 1)
  exact numericSubGenerator_finite _ _ _ _ _

/-- Numerical subtraction of independently generated words needs only their
length and digit readers, even when the words are too long to store. -/
@[expose] def numericSub (G : Generator m Pre V) (H : Generator m Pre W)
    (N : ℕ → ℕ) (C : ℕ)
    (hlen : ∀ input σ, Pre input σ →
      max (V input σ).length (W input σ).length + 1 ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ C * (n.size + 1)) :
    Generator m Pre (fun input σ ↦ Oitavem.numericSub (V input σ) (W input σ)) :=
  ⟨m + 7 + (G.tapes + H.tapes + 2), StateOf (G.numericSubProgram H),
    { finite := G.numericSubProgram_finite H
      env := fun i ↦ (i.castAdd 7).castAdd (G.tapes + H.tapes + 2)
      env_injective := (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)
      program := G.numericSubProgram H
      space := G.space + H.space + C + 1
      correct B hB := by
        let K := G.tapes + H.tapes + 2
        let src : Fin m → Fin (m + 7) := Fin.castAdd 7
        let r (j : Fin 7) : Fin (m + 7 + K) := (j.natAdd m).castAdd K
        let env (j : Fin m) : Fin (m + 7 + K) := (j.castAdd 7).castAdd K
        have hr : Function.Injective r :=
          (Fin.castAdd_injective _ _).comp (Fin.natAdd_injective _ _)
        have hsep (i : Fin m) (j : Fin 7) : env i ≠ r j := by
          apply Fin.ne_of_val_ne
          simp only [env, r, Fin.val_castAdd, Fin.val_natAdd]
          omega
        have hG (n) : G.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by omega : G.space ≤ G.space + H.space + C + 1)).trans (hB n)
        have hH (n) : H.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by omega : H.space ≤ G.space + H.space + C + 1)).trans (hB n)
        have hN (n) : (N n).size ≤ B n := (hsize n).trans
          ((Nat.mul_le_mul_right _ (by omega : C ≤ G.space + H.space + C + 1)).trans (hB n))
        have hB1 (n) : 1 ≤ B n :=
          (Nat.mul_le_mul (by omega : 1 ≤ G.space + H.space + C + 1)
            (by omega : 1 ≤ n.size + 1)).trans (hB n)
        have hsizeV input σ (hp : Pre input σ) :
            ((V input σ).length + 1).size ≤ B input.length :=
          (size_le_size ((Nat.add_le_add_right (Nat.le_max_left _ _) 1).trans
            (hlen input σ hp))).trans (hN _)
        have hsizeW input σ (hp : Pre input σ) :
            ((W input σ).length + 1).size ≤ B input.length :=
          (size_le_size ((Nat.add_le_add_right (Nat.le_max_right _ _) 1).trans
            (hlen input σ hp))).trans (hN _)
        obtain ⟨TL₁, hl₁⟩ := G.lengthReader_readsLength src (Fin.natAdd m 4) B hG hsizeV
        obtain ⟨TL₂, hl₂⟩ := H.lengthReader_readsLength src (Fin.natAdd m 5) B hH hsizeW
        obtain ⟨T₁, ha⟩ := (H.appendBit true).atReader_readsAtAll src
          (Fin.natAdd m 5) (Fin.natAdd m 0) B hH hB1
        obtain ⟨T₂, hb⟩ := (G.appendBit true).atReader_readsAtAll src
          (Fin.natAdd m 5) (Fin.natAdd m 1) B hG hB1
        have hl₁' := hl₁.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (src i)))
          (W := fun input σ ↦ V input (fun i ↦ σ (src i)))
          (padLayout (m + 7) (G.tapes + 1) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        have hl₂' := hl₂.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (src i)))
          (W := fun input σ ↦ W input (fun i ↦ σ (src i)))
          (padLayout (m + 7) (H.tapes + 1) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        have ha' := ha.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (src i)))
          (W := fun input σ ↦ W input (fun i ↦ σ (src i)) ++ [true])
          (padLayout (m + 7) (H.tapes + 2) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        have hb' := hb.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (src i)))
          (W := fun input σ ↦ V input (fun i ↦ σ (src i)) ++ [true])
          (padLayout (m + 7) (G.tapes + 2) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        have henv (σ : Fin (m + 7 + K) → List Bool) (j : Fin 7) (w : List Bool) :
            (fun i ↦ Function.update σ (r j) w (env i)) = fun i ↦ σ (env i) := by
          funext i
          exact Function.update_of_ne (hsep i j) _ _
        have hp input σ j w
            (h : Pre input (fun i ↦ σ (env i)) ∧ Initialized (Fin.castAdd K : Fin (m + 7) → _) σ) :
            Pre input (fun i ↦ Function.update σ (r j) w (env i)) ∧
              Initialized (Fin.castAdd K : Fin (m + 7) → _) (Function.update σ (r j) w) :=
          ⟨by simpa only [henv] using h.1, h.2.update (j.natAdd m) w⟩
        have h := numericSubGenerator_emitsIn r hr hl₁' hl₂' ha' hb' hp
          (fun input σ j w ↦ congrArg (V input) (henv σ j w))
          (fun input σ j w ↦ congrArg (W input) (henv σ j w))
          (fun input σ hp ↦ hlen input _ hp.1) hN hB1
        refine ⟨_, (h.mono_pre ?_).congr ?_⟩
        · intro input σ _ hp
          have hz (j) : σ (r j) = [] := hp.2 (r j) (fun i ↦ (hsep i j).symm)
          refine ⟨⟨hp.1, ?_⟩, hz 0, hz 1, hz 3⟩
          intro i hi
          exact hp.2 i (fun j he ↦ hi (j.castAdd 7) he)
        · intro input σ hp
          have hz (j) : σ (r j) = [] := hp.2 (r j) (fun i ↦ (hsep i j).symm)
          have hu (j) : Function.update σ (r j) [] = σ := by
            rw [← hz j]
            exact Function.update_eq_self ..
          simp only [subDoneVal, hu]
    }⟩

/-- Assemble the length and digit readers for iterated string predecessor. -/
@[expose] def iterPredProgram (G : Generator m Pre V) (H : Generator m Pre W) :=
  let K := G.tapes + H.tapes + 2
  let src : Fin m → Fin (m + 6) := Fin.castAdd 6
  let L₁ := onTapes (G.lengthReader src (Fin.natAdd m 0))
    (padLayout (m + 6) (G.tapes + 1) K (by omega))
  let L₂ := onTapes (H.lengthReader src (Fin.natAdd m 5))
    (padLayout (m + 6) (H.tapes + 1) K (by omega))
  let P := onTapes (H.atReader src (Fin.natAdd m 2) (Fin.natAdd m 4))
    (padLayout (m + 6) (H.tapes + 2) K (by omega))
  iterPredGenerator L₁ L₂ P (fun j ↦ (j.castSucc.natAdd m).castAdd K)
    ((Fin.natAdd m 5).castAdd K)

/-- The iterated-predecessor program has finite control. -/
theorem iterPredProgram_finite (G : Generator m Pre V) (H : Generator m Pre W) :
    Finite (StateOf (G.iterPredProgram H)) := by
  let src : Fin m → Fin (m + 6) := Fin.castAdd 6
  let := G.lengthReader_finite src (Fin.natAdd m 0)
  let := H.lengthReader_finite src (Fin.natAdd m 5)
  let := H.atReader_finite src (Fin.natAdd m 2) (Fin.natAdd m 4)
  exact iterPredGenerator_finite _ _ _ _ _

/-- Iterated string predecessor streams the surviving segment of its second
argument, after counting the first argument. -/
@[expose] def iterPred (G : Generator m Pre V) (H : Generator m Pre W)
    (N : ℕ → ℕ) (C : ℕ)
    (hlen : ∀ input σ, Pre input σ →
      max (V input σ).length (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n + 1).size ≤ C * (n.size + 1)) :
    Generator m Pre (fun input σ ↦ (W input σ).drop (V input σ).length) :=
  ⟨m + 6 + (G.tapes + H.tapes + 2), StateOf (G.iterPredProgram H),
    { finite := G.iterPredProgram_finite H
      env := fun i ↦ (i.castAdd 6).castAdd (G.tapes + H.tapes + 2)
      env_injective := (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)
      program := G.iterPredProgram H
      space := G.space + H.space + C + 1
      correct B hB := by
        let K := G.tapes + H.tapes + 2
        let src : Fin m → Fin (m + 6) := Fin.castAdd 6
        let r (j : Fin 6) : Fin (m + 6 + K) := (j.natAdd m).castAdd K
        let env (j : Fin m) : Fin (m + 6 + K) := (j.castAdd 6).castAdd K
        have hr : Function.Injective r :=
          (Fin.castAdd_injective _ _).comp (Fin.natAdd_injective _ _)
        have hsep (i : Fin m) (j : Fin 6) : env i ≠ r j := by
          apply Fin.ne_of_val_ne
          simp only [env, r, Fin.val_castAdd, Fin.val_natAdd]
          omega
        have hG (n) : G.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by omega : G.space ≤ G.space + H.space + C + 1)).trans (hB n)
        have hH (n) : H.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by omega : H.space ≤ G.space + H.space + C + 1)).trans (hB n)
        have hN (n) : (N n + 1).size ≤ B n := (hsize n).trans
          ((Nat.mul_le_mul_right _ (by omega : C ≤ G.space + H.space + C + 1)).trans (hB n))
        have hB1 (n) : 1 ≤ B n :=
          (Nat.mul_le_mul (by omega : 1 ≤ G.space + H.space + C + 1)
            (by omega : 1 ≤ n.size + 1)).trans (hB n)
        have hsizeV input σ (hp : Pre input σ) :
            ((V input σ).length + 1).size ≤ B input.length :=
          (size_le_size (Nat.add_le_add_right ((Nat.le_max_left _ _).trans
            (hlen input σ hp)) 1)).trans (hN _)
        have hsizeW input σ (hp : Pre input σ) :
            ((W input σ).length + 1).size ≤ B input.length :=
          (size_le_size (Nat.add_le_add_right ((Nat.le_max_right _ _).trans
            (hlen input σ hp)) 1)).trans (hN _)
        obtain ⟨TL₁, hl₁⟩ := G.lengthReader_readsLength src (Fin.natAdd m 0) B hG hsizeV
        obtain ⟨TL₂, hl₂⟩ := H.lengthReader_readsLength src (Fin.natAdd m 5) B hH hsizeW
        obtain ⟨T, ha⟩ := H.atReader_readsAtAll src
          (Fin.natAdd m 2) (Fin.natAdd m 4) B hH hB1
        have hl₁' := hl₁.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (src i)))
          (W := fun input σ ↦ V input (fun i ↦ σ (src i)))
          (padLayout (m + 6) (G.tapes + 1) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        have hl₂' := hl₂.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (src i)))
          (W := fun input σ ↦ W input (fun i ↦ σ (src i)))
          (padLayout (m + 6) (H.tapes + 1) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        have ha' := ha.onEnvironment
          (Pre := fun input σ ↦ Pre input (fun i ↦ σ (src i)))
          (W := fun input σ ↦ W input (fun i ↦ σ (src i)))
          (padLayout (m + 6) (H.tapes + 2) K (by dsimp [K]; omega)) (fun i ↦ padLayout_env ..)
        have henv (σ : Fin (m + 6 + K) → List Bool) (j : Fin 6) (w : List Bool) :
            (fun i ↦ Function.update σ (r j) w (env i)) = fun i ↦ σ (env i) := by
          funext i
          exact Function.update_of_ne (hsep i j) _ _
        have hp input σ j w
            (h : Pre input (fun i ↦ σ (env i)) ∧ Initialized (Fin.castAdd K : Fin (m + 6) → _) σ) :
            Pre input (fun i ↦ Function.update σ (r j) w (env i)) ∧
              Initialized (Fin.castAdd K : Fin (m + 6) → _) (Function.update σ (r j) w) :=
          ⟨by simpa only [henv] using h.1, h.2.update (j.natAdd m) w⟩
        have h := iterPredGenerator_emitsIn (fun j ↦ r j.castSucc)
          (hr.comp (Fin.castSucc_injective _)) (r 5)
          (fun j ↦ hr.ne (by apply Fin.ne_of_val_ne; change (5 : ℕ) ≠ j.val; omega))
          hl₁' hl₂' ha'.readsAt (fun input σ j w ↦ hp input σ j.castSucc w)
          (fun input σ w ↦ hp input σ 5 w)
          (fun input σ j w ↦ congrArg (W input) (henv σ j.castSucc w))
          (fun input σ w ↦ congrArg (W input) (henv σ 5 w))
          (fun input σ hp ↦ (Nat.le_max_left _ _).trans (hlen input _ hp.1))
          (fun input σ hp ↦ (Nat.le_max_right _ _).trans (hlen input _ hp.1))
          (fun n ↦ (size_le_size (Nat.le_succ (N n))).trans (hN n)) hB1
        refine ⟨_, (h.mono_pre ?_).congr ?_⟩
        · intro input σ _ hp
          refine ⟨⟨hp.1, ?_⟩, hp.2 (r 2) (fun i ↦ (hsep i 2).symm)⟩
          intro i hi
          exact hp.2 i (fun j he ↦ hi (j.castAdd 6) he)
        · intro input σ hp
          have hu (j) : Function.update σ (r j) [] = σ := by
            rw [← hp.2 (r j) (fun i ↦ (hsep i j).symm)]
            exact Function.update_eq_self ..
          simp only [hu]
    }⟩

/-- Test one generated word and run the selected generated branch in shared scratch. -/
@[expose] def condProgram (Q : Generator m Pre W)
    {U : Bool → List Bool → (Fin m → List Bool) → List Bool}
    (P : (b : Bool) → Generator m Pre (U b)) :=
  let K := Q.tapes + (P false).tapes + (P true).tapes
  let hP (b : Bool) : (P b).tapes ≤ K := by cases b <;> dsimp [K] <;> omega
  condGenerator (Q.pad K (by omega)).program (fun b ↦ ((P b).pad K (hP b)).program)

/-- Conditional assembly preserves finite control. -/
theorem condProgram_finite (Q : Generator m Pre W)
    {U : Bool → List Bool → (Fin m → List Bool) → List Bool}
    (P : (b : Bool) → Generator m Pre (U b)) :
    Finite (StateOf (Q.condProgram P)) := by
  let := Q.call_finite (id : Fin m → Fin m)
  let (b : Bool) : Finite (StateOf ((P b).call (id : Fin m → Fin m))) := (P b).call_finite id
  exact condGenerator_finite _ _

/-- Conditional selection uses only a logarithmic counter for its generated test word. -/
@[expose] def cond (Q : Generator m Pre W)
    {U : Bool → List Bool → (Fin m → List Bool) → List Bool}
    (P : (b : Bool) → Generator m Pre (U b)) (C : ℕ)
    (hsize : ∀ input σ, Pre input σ →
      ((W input σ).length + 1).size ≤ C * (input.length.size + 1)) :
    Generator m Pre (fun input σ ↦ U (W input σ).isEmpty input σ) :=
  ⟨m + (Q.tapes + (P false).tapes + (P true).tapes) + 1, StateOf (Q.condProgram P),
    { finite := Q.condProgram_finite P
      env := fun i ↦ (i.castAdd (Q.tapes + (P false).tapes + (P true).tapes)).succ
      env_injective := (Fin.succ_injective _).comp (Fin.castAdd_injective _ _)
      program := Q.condProgram P
      space := Q.space + (P false).space + (P true).space + C
      correct B hB := by
        let K := Q.tapes + (P false).tapes + (P true).tapes
        have hkQ : Q.tapes ≤ K := by dsimp [K]; omega
        have hkP (b : Bool) : (P b).tapes ≤ K := by cases b <;> dsimp [K] <;> omega
        have hQ (n) : Q.space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _
            (by omega : Q.space ≤ Q.space + (P false).space + (P true).space + C)).trans (hB n)
        have hP (b : Bool) (n) : (P b).space * (n.size + 1) ≤ B n :=
          (Nat.mul_le_mul_right _ (by cases b <;> omega :
            (P b).space ≤ Q.space + (P false).space + (P true).space + C)).trans (hB n)
        obtain ⟨TQ, hq⟩ := (Q.pad K hkQ).correct B hQ
        obtain ⟨T₀, h₀⟩ := ((P false).pad K (hkP false)).correct B (hP false)
        obtain ⟨T₁, h₁⟩ := ((P true).pad K (hkP true)).correct B (hP true)
        simp only [pad_env] at hq h₀ h₁
        have hp (b : Bool) : EmitsIn ((P b).pad K (hkP b)).program
            (fun input σ ↦ Pre input (fun i ↦ σ (i.castAdd K)) ∧ Initialized (Fin.castAdd K) σ)
            (fun _ σ ↦ σ) (fun input σ ↦ U b input (fun i ↦ σ (i.castAdd K)))
            (Bool.rec T₀ T₁ b) B := by
          cases b
          · exact h₀
          · exact h₁
        have h := condGenerator_emitsIn hq hp (fun input σ hp _ ↦
          (hsize input _ hp.1).trans ((Nat.mul_le_mul_right _
            (by omega : C ≤ Q.space + (P false).space + (P true).space + C)).trans (hB _)))
        refine ⟨_, (h.mono_pre ?_).congr ?_⟩
        · intro input σ _ hp
          exact ⟨⟨hp.1, hp.2.succ⟩, ⟨hp.1, hp.2.succ⟩⟩
        · intro input σ hp
          rw [← hp.2.zero]
          exact Function.update_eq_self ..
    }⟩

/-- Every initial function can be applied to independently generated arguments
whose lengths have a common polynomial bound in the physical input. -/
theorem _root_.Geb.Oitavem.Initial.realize (p : Initial) {m : ℕ}
    {Pre : List Bool → (Fin m → List Bool) → Prop}
    {X : Fin p.arity → List Bool → (Fin m → List Bool) → List Bool}
    (G : (i : Fin p.arity) → Generator m Pre (X i)) (N : ℕ → ℕ)
    (hN : Geb.SizeBounded.IsPolyBounded N)
    (hlen : ∀ input σ, Pre input σ → ∀ i, (X i input σ).length ≤ N input.length) :
    Nonempty (Generator m Pre (fun input σ ↦ p.eval (fun i ↦ X i input σ))) := by
  obtain ⟨C, hC⟩ := logarithmic_size_of_polyBounded hN
  have hs input σ (hp : Pre input σ) (i : Fin p.arity) :
      ((X i input σ).length + 1).size ≤ C * (input.length.size + 1) :=
    (size_le_size (Nat.add_le_add_right (hlen input σ hp i) 1)).trans (hC _)
  cases p with
  | zero n => exact ⟨empty m Pre⟩
  | proj n i => exact ⟨G i⟩
  | succ b => exact ⟨(G 0).succ b⟩
  | pred => exact ⟨(G 0).pred⟩
  | numericSucc => exact ⟨(G 0).numericSucc⟩
  | numericPred => exact ⟨(G 0).numericPred⟩
  | last => exact ⟨(G 0).last⟩
  | length => exact ⟨(G 0).length C (fun input σ hp ↦ hs input σ hp 0)⟩
  | product =>
    exact ⟨(G 0).product (G 1) N C (fun input σ hp ↦ hlen input σ hp 1) hC⟩
  | numericSub =>
    exact ⟨(G 0).numericSub (G 1) (fun n ↦ N n + 1) C
      (fun input σ hp ↦ Nat.add_le_add_right
        (max_le (hlen input σ hp 0) (hlen input σ hp 1)) 1) hC⟩
  | iterPred =>
    exact ⟨(G 0).iterPred (G 1) N C
      (fun input σ hp ↦ max_le (hlen input σ hp 0) (hlen input σ hp 1)) hC⟩
  | cond =>
    let P : (b : Bool) → Generator m Pre
        (fun input σ ↦ if b then X 1 input σ else X 2 input σ) := fun b ↦ by
      cases b
      · exact G 2
      · exact G 1
    exact ⟨(G 0).cond P C (fun input σ hp ↦ hs input σ hp 0)⟩

end

end Geb.Oitavem.Machine.Generator
