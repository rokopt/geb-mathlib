/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Machine
public import Geb.Prototypes.Computability.TreeScanner.Steps

set_option doc.verso true

/-!
# Input transitions of the binary-counter recognizer

Reading a bit advances the input head and selects the next scan mode or a
counter-increment phase. The work tapes are unchanged during this transition.

## Main statements

* {lit}`step_read` realizes one input transition without changing work tapes.
* {lit}`step_end` and {lit}`outputSymbol_end` describe the final emitting transition.
* {lit}`headBound_add` combines bounds on consecutive execution segments.

## Tags

Turing machine, simulation, binary tree, binary counter
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM
open Geb.TreeScanner (step_of_state)

/-- An input transition has the closed form given by {name}`consumeCfg`. -/
theorem step_read {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (m : Mode) (b : Bool) (hq : cfg.state = some (modeState m))
    (hi : cfg.inputSymbol = some (boolEmb b)) :
    machine.step cfg = consumeCfg cfg (postReadState m b) := by
  rw [step_of_state _ _ _ hq, hi, tr_read]
  apply Cfg.ext <;> simp [consume, consumeCfg]

/-- Input transitions emit nothing. -/
theorem outputSymbol_read {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (m : Mode) (b : Bool) (hq : cfg.state = some (modeState m))
    (hi : cfg.inputSymbol = some (boolEmb b)) : machine.outputSymbol cfg = none := by
  unfold outputSymbol
  rw [hq]
  dsimp only
  rw [hi, tr_read]
  rfl

/-- The symbol at an interior input position is its next bit. -/
theorem inputSymbol_at (w : List Bool) (t : ℕ) (ht : t < w.length)
    (cfg : Cfg 3 (Fin 4) (Fin 10) (w.map boolEmb)) (hp : cfg.inputPos.val = t + 1) :
    cfg.inputSymbol = some (boolEmb w[t]) := by
  rw [inputSymbolInner t (by omega) (by simpa only [List.length_map] using ht),
    List.getElem_map]

/-- The input symbol at the right end marker is blank. -/
theorem inputSymbol_end {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (hp : cfg.inputPos.val = input.length + 1) : cfg.inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs <;> rfl

/-- At the right end marker only the finite control changes to the halting state. -/
theorem step_end {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (m : Mode) (hq : cfg.state = some (modeState m)) (hi : cfg.inputSymbol = none) :
    machine.step cfg = { cfg with state := none } := by
  rw [step_of_state _ _ _ hq, hi, tr_end]
  apply Cfg.ext <;> simp [finish]

/-- The final transition emits exactly the accepting-mode decision. -/
theorem outputSymbol_end {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (m : Mode) (hq : cfg.state = some (modeState m)) (hi : cfg.inputSymbol = none) :
    machine.outputSymbol cfg = some (boolEmb (decide (m = .done))) := by
  unfold outputSymbol
  rw [hq]
  dsimp only
  rw [hi, tr_end]
  rfl

/-- Bounds on consecutive execution segments combine into a bound on their concatenation. -/
theorem headBound_add {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (width a b : ℕ)
    (ha : ∀ t ≤ a, HeadBound width (machine.configs cfg t))
    (hb : ∀ t ≤ b, HeadBound width (machine.configs (machine.configs cfg a) t)) :
    ∀ t ≤ a + b, HeadBound width (machine.configs cfg t) := by
  intro t ht
  by_cases h : t ≤ a
  · exact ha t h
  · rw [show t = a + (t - a) by omega, configs_add]
    exact hb (t - a) (by omega)

end Geb.BitTree.BinaryMachine
