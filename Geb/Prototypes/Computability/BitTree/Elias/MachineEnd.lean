/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineModel
public import Geb.Prototypes.Computability.TreeScanner.Steps

set_option doc.verso true

/-!
# Reading the input and emitting the final verdict

At normalized scanner boundaries the next input symbol is either the next bit
or the right end marker. The end marker causes one output bit and halting.

## Main statements

* {lit}`inputSymbol_at` identifies the next input bit.
* {lit}`step_end` and {lit}`outputSymbol_end` specify the final transition.

## Tags

Elias delta code, Turing machine, input, halting
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Initialization installs the four origin markers and leaves one pending root. -/
theorem configs_start (input : List (Fin 3)) :
    machine.configs (machine.initCfg input) 1 =
      modelCfg input 1 (.tree, 1) [] [] := by
  rw [configs_succ_eq_step']
  rw [Geb.TreeScanner.step_of_state _ _ stInit rfl]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (1 : Fin (input.length + 2)) 0 = 1
    rw [moveInputPos_zero]
  · funext i z
    change (Function.update (fun _ : ℤ ↦ (none : Option (Fin 3))) 0 (some 2)) z = _
    by_cases hz : z = 0
    · subst z
      simp [modelCfg, scanCfg, wordTape]
    · simp [modelCfg, scanCfg, wordTape, hz]
  · funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j ↦ Fin.elim0 j)))) i

/-- Initialization does not emit output. -/
theorem outputString_start (input : List (Fin 3)) :
    machine.outputString (machine.initCfg input) 1 = [] := rfl

/-- Initialization visits only the origin and its immediate right neighbor. -/
theorem headBound_start (input : List (Fin 3)) (width : ℕ) (hw : 1 ≤ width) :
    ∀ t ≤ 1, HeadBound width (machine.configs (machine.initCfg input) t) := by
  intro t ht
  cases t with
  | zero =>
    intro i
    change 0 ≤ (0 : ℤ) ∧ 0 ≤ (width : ℤ)
    exact ⟨Int.le_refl _, Int.natCast_nonneg _⟩
  | succ t =>
    have he : t = 0 := by omega
    subst t
    rw [configs_start]
    exact scanCfg_headBound input 1 stTree 1 0 [] [] width hw (Nat.zero_le _) hw hw

/-- The input symbol at an interior position is the corresponding encoded boolean. -/
theorem inputSymbol_at (w : List Bool) (t : ℕ) (ht : t < w.length)
    (cfg : Cfg 4 (Fin 3) Control (w.map boolEmb)) (hp : cfg.inputPos.val = t + 1) :
    cfg.inputSymbol = some (boolEmb w[t]) := by
  rw [inputSymbolInner t (by omega) (by simpa only [List.length_map] using ht),
    List.getElem_map]

/-- The right end marker is read as a blank input symbol. -/
theorem inputSymbol_end {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (hp : cfg.inputPos.val = input.length + 1) : cfg.inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs <;> rfl

/-- Reading the end marker in a normalized mode halts without changing any tape or head. -/
theorem step_end {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (m : Scanner.Mode) (hq : cfg.state = some (modeState m)) (hi : cfg.inputSymbol = none) :
    machine.step cfg = { cfg with state := none } := by
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, hi, tr_end _ _ (modeState_read m)]
  apply Cfg.ext <;> simp [finish, jump]

/-- The final output bit says exactly whether the scanner completed its root. -/
theorem outputSymbol_end {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (m : Scanner.Mode) (hq : cfg.state = some (modeState m)) (hi : cfg.inputSymbol = none) :
    machine.outputSymbol cfg = some (boolEmb (decide (m = .done))) := by
  unfold outputSymbol
  rw [hq]
  dsimp only
  rw [hi, tr_end _ _ (modeState_read m)]
  cases m <;> rfl

end Geb.BitTree.Elias.Machine
