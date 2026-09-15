/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Simple
public import Geb.Prototypes.Computability.BitTree.EliasBinary.Zeros
public import Geb.Prototypes.Computability.BitTree.EliasBinary.SizeRead
public import Geb.Prototypes.Computability.BitTree.EliasBinary.LengthRead
public import Geb.Prototypes.Computability.BitTree.EliasBinary.Payload
public import Geb.Prototypes.Computability.MultiTape.OutputString

set_option doc.verso true in
/-!
# One input bit of the second pass

The phase statements are combined by a case analysis on the scanner phase of the account.

## Main statements

* {lit}`runFrom_bit` realizes one bit at any boundary in its macro cost.

## Tags

Turing machine, simulation, Elias delta code
-/

set_option doc.verso true

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb)

/-- One input bit at a boundary realizes its account update within its macro cost. -/
theorem runFrom_bit (w : List Bool) (t : ℕ) (ht : t < w.length)
    (cfg : Cfg 9 (Fin 4) Control (w.map boolEmb)) (hp : cfg.inputPos.val = t + 1)
    (a : Account) (hv : AccountValid w.length a) (h : Represents (widthOf w.length) cfg a)
    (hw1 : a.forks.size + 1 ≤ widthOf w.length)
    (hw2 : (a.forks + 1).size + 1 ≤ widthOf w.length)
    (hw3 : (a.leaves + 1).size ≤ widthOf w.length) :
    let cost := macroCost a w[t]
    Represents (widthOf w.length) (machine.runFrom cfg cost) (accountStep a w[t]) ∧
      (machine.runFrom cfg cost).inputPos.val = t + 2 ∧
      machine.outputString cfg cost = [] ∧
      ∀ u ≤ cost, HeadBound (widthOf w.length) (machine.runFrom cfg u) := by
  have hi := inputSymbol_at w t ht cfg hp
  have hspec : BitSpec cfg a w[t] (widthOf w.length) := by
    rcases hs : a.state with ⟨m, k⟩
    cases m with
    | tree => exact runFrom_bit_tree cfg a w[t] w.length _ hv h hi hw1 hw2 k hs
    | zeros z => exact runFrom_bit_zeros cfg a w[t] w.length _ hv h hi hw1 hw3 z k hs
    | size r v => exact runFrom_bit_size cfg a w[t] w.length _ hv h hi hw1 r v k hs
    | length r v => exact runFrom_bit_length cfg a w[t] w.length _ hv h hi hw1 r v k hs
    | payload r => exact runFrom_bit_payload cfg a w[t] w.length _ hv h hi hw1 hw3 r k hs
    | done => exact runFrom_bit_done cfg a w[t] _ h hi k hs
    | dead => exact runFrom_bit_dead cfg a w[t] _ h hi k hs
  obtain ⟨hr, hin, ho, hb⟩ := hspec
  refine ⟨hr, ?_, ho, hb⟩
  rw [hin, moveInputPos_pos_val _ (by rw [hp, List.length_map]; omega), hp]

end Geb.BitTree.EliasBinary
