/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineModel
public import Geb.Prototypes.Computability.BitTree.Elias.MachineConfig

set_option doc.verso true

/-!
# Normalization of counter and cleanup configurations

Counter subroutines replace one finite field while retaining the other tapes. Cleanup
removes both fields and completes one pending subtree. These identities express their
results in the common configuration used at input boundaries.

## Tags

Elias delta code, Turing machine, simulation
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Replacing the length counter preserves the payload counter and both unary counters. -/
theorem counterCfg_scanCfg_false (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (q q' : Control) (pending zeros : ℕ) (bs cs ds : List Bool) :
    counterCfg (scanCfg input pos q pending zeros bs cs) false ds q' (ds.length + 1) =
      scanCfg input pos q' pending zeros ds cs := by
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦
      Fin.cases rfl (fun i ↦ Fin.cases rfl (fun j ↦ Fin.elim0 j) i) i) i) i
  · funext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦
      Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) i) i) i) i <;>
      dsimp only [counterCfg, scanCfg, counterTape] <;>
      simp only [Nat.cast_add, Nat.cast_one] <;> rfl

/-- Replacing the payload counter preserves the length counter and both unary counters. -/
theorem counterCfg_scanCfg_true (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (q q' : Control) (pending zeros : ℕ) (bs cs ds : List Bool) :
    counterCfg (scanCfg input pos q pending zeros bs cs) true ds q' (ds.length + 1) =
      scanCfg input pos q' pending zeros bs ds := by
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦
      Fin.cases rfl (fun i ↦ Fin.cases rfl (fun j ↦ Fin.elim0 j) i) i) i) i
  · funext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦
      Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) i) i) i) i <;>
      dsimp only [counterCfg, scanCfg, counterTape] <;>
      simp only [Nat.cast_add, Nat.cast_one] <;> rfl

/-- Cleanup starts at the two right-hand blank cells of the stored fields. -/
theorem clearingCfg_scanCfg (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (q : Control) (pending zeros : ℕ) (bs cs : List Bool) :
    clearingCfg (scanCfg input pos q pending zeros bs cs) bs cs
        (bs.length + 1) (cs.length + 1) =
      scanCfg input pos stClear pending zeros bs cs := by
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦
      Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) i) i) i) i <;>
      dsimp only [clearingCfg, scanCfg] <;>
      simp only [prefixTape_full bs (Nat.le_succ _), prefixTape_full cs (Nat.le_succ _)] <;>
      rfl
  · funext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦
      Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) i) i) i) i <;>
      dsimp only [clearingCfg, scanCfg] <;> simp only [Nat.cast_add, Nat.cast_one] <;> rfl

/-- The empty marked tape recognizes completion precisely at pending count one. -/
theorem wordTape_pending_marker (pending : ℕ) (hp : 0 < pending) :
    (wordTape [] ((pending : ℤ) - 1) == some 2) = decide (pending = 1) := by
  by_cases he : pending = 1
  · subst pending
    rfl
  · have hn : (pending : ℤ) - 1 ≠ 0 := by omega
    have hpos : 0 < (pending : ℤ) - 1 := by omega
    simp only [wordTape, hn, hpos, ↓reduceIte, List.reverse_nil, List.getElem?_nil,
      Option.map_none, he, decide_false]
    rfl

/-- Completed cleanup agrees with the scalar leaf-completion operation. -/
theorem completedCfg_scanCfg (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (q : Control) (pending : ℕ) (bs cs : List Bool) (hp : 0 < pending) :
    completedCfg (scanCfg input pos q pending 0 bs cs) =
      modelCfg input pos (Scanner.finish pending) [] [] := by
  have hs : (pending : ℤ) - 1 = (pending - 1 : ℕ) := by omega
  have hm := wordTape_pending_marker pending hp
  by_cases he : pending = 1
  · subst pending
    refine Cfg.ext rfl rfl ?_ ?_
    · funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦
        Fin.cases rfl (fun i ↦ Fin.cases rfl (fun j ↦ Fin.elim0 j) i) i) i) i
    · funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦
        Fin.cases rfl (fun i ↦ Fin.cases rfl (fun j ↦ Fin.elim0 j) i) i) i) i
  · have hf : Scanner.finish pending = (.tree, pending - 1) :=
      ite_eq_right he
    rw [hf]
    refine Cfg.ext ?_ rfl ?_ ?_
    · change some (if wordTape [] ((pending : ℤ) - 1) == some 2 then _ else _) = _
      rw [hm]
      simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
      rfl
    · funext i
      exact Fin.cases rfl (fun i ↦ Fin.cases rfl (fun i ↦
        Fin.cases rfl (fun i ↦ Fin.cases rfl (fun j ↦ Fin.elim0 j) i) i) i) i
    · funext i
      refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦
        Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) i) i) i) i
      · exact hs
      · rfl
      · rfl
      · rfl

end Geb.BitTree.Elias.Machine
