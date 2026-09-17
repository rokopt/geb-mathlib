/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Counter
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return
public import Geb.Prototypes.Computability.SizeBounded.Machine.Seq

set_option doc.verso true in
/-!
# The decrement phase

A counter register holds the reverse of its digit list, so that cell
{lit}`z` holds digit {lit}`z`, least significant first. The decrement of
{name}`Geb.SizeBounded.Logspace.decL` sets the run of zeros from cell
{lit}`0`, clears the one above it, and erases that one when it is the most
significant digit. {lit}`decWalk` does exactly that from a parked head, in
three states. Borrowing, it sets each zero it reads and moves right, and halts
on a blank, which is the case of the number zero. On a one it clears it,
moves right and checks the next cell: reading a digit it halts; reading a
blank it steps back and erases the cleared digit. {lit}`dec` returns the head
to cell {lit}`0` afterwards, and its contract transforms the register by the
decrement of its digit list.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`decAct` — an action on one tape.
* {lit}`decWalk` — decrement the digit list rightwards from cell {lit}`0`.
* {lit}`dec` — decrement a counter register from a parked head.
* {lit}`borrowCfg` — the closed form of the borrowing configurations.

# Main statements

* {lit}`length_decL_le` — the decrement is no longer than the digit list.
* {lit}`decL_replicate_false_append`, {lit}`exists_replicate_false_append` —
  the decrement past a run of zeros, and the split of a digit list at its
  first one.
* {lit}`read_tapeOf_reverse`, {lit}`update_tapeOf_reverse` — reading and
  writing a cell of a counter register, as its digit list.
* {lit}`Reaches.ofStep`, {lit}`RunsTo.ofStep` — one step as a reach and as a
  run.
* {lit}`decWalk_step` — a step of the walk, given its action.
* {lit}`decWalk_borrow` — the borrowing sweep.
* {lit}`decWalk_runsTo` — the run of the walk, naming the halted
  configuration and the step count.
* {lit}`dec_transforms` — the contract of the decrement.

# Tags

Turing machine, binary counter, decrement, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine

public section

/-- The decrement is no longer than the digit list. -/
theorem length_decL_le : ∀ d : List Bool, (decL d).length ≤ d.length :=
  List.rec (Nat.le_refl 0) fun b d ih ↦ by
    cases b
    · rw [decL_cons_false, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ ih
    · cases d with
      | nil => exact Nat.zero_le _
      | cons c d' =>
        rw [decL_cons_true_cons]
        exact Nat.le_refl _

/-- The decrement past a run of zeros sets them and decrements the rest. -/
theorem decL_replicate_false_append (d : List Bool) :
    ∀ c : ℕ, decL (List.replicate c false ++ d) = List.replicate c true ++ decL d :=
  Nat.rec (by rw [List.replicate_zero, List.replicate_zero, List.nil_append, List.nil_append])
    fun c ih ↦ by
      rw [List.replicate_succ, List.replicate_succ, List.cons_append, List.cons_append,
        decL_cons_false, ih]

/-- A digit list is a run of zeros followed by nothing or by a one. -/
theorem exists_replicate_false_append : ∀ d : List Bool, ∃ (c : ℕ) (d' : List Bool),
    d = List.replicate c false ++ d' ∧ (d' = [] ∨ ∃ rest, d' = true :: rest) :=
  List.rec ⟨0, [], rfl, Or.inl rfl⟩ fun b d ih ↦ by
    cases b
    · obtain ⟨c, d', hd, h⟩ := ih
      exact ⟨c + 1, d', by rw [List.replicate_succ, List.cons_append, ← hd], h⟩
    · exact ⟨0, true :: d, rfl, Or.inr ⟨d, rfl⟩⟩

/-- A cell of a register holding the reverse of a digit list holds the
corresponding digit. -/
theorem read_tapeOf_reverse (d : List Bool) (n : ℕ) : tapeOf d.reverse (n : ℤ) = d[n]? := by
  unfold tapeOf
  rw [List.reverse_reverse, ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]

/-- Writing a digit at a cell of such a register sets that digit. -/
theorem update_tapeOf_reverse (d : List Bool) (n : ℕ) (hn : n < d.length) (b : Bool) :
    Function.update (tapeOf d.reverse) (n : ℤ) (some b) = tapeOf (d.set n b).reverse := by
  funext z
  by_cases hz : z = (n : ℤ)
  · subst hz
    rw [Function.update_self, read_tapeOf_reverse, List.getElem?_set_self hn]
  · rw [Function.update_of_ne hz]
    unfold tapeOf
    rw [List.reverse_reverse, List.reverse_reverse]
    split_ifs with h0
    · rw [List.getElem?_set_ne (by omega)]
    · rfl

/-- Setting the digit at the end of a run of ones. -/
theorem set_replicate_true_append (n : ℕ) (x y : Bool) (T : List Bool) :
    (List.replicate n true ++ x :: T).set n y = List.replicate n true ++ y :: T := by
  rw [List.set_append_right _ _ (by rw [List.length_replicate]), List.length_replicate,
    Nat.sub_self, List.set_cons_zero]

/-- A single step whose target is live is a reach. -/
theorem Reaches.ofStep {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (cfg cfg' : Cfg k Bool State input) (B : ℕ)
    (hlive : cfg.state ≠ none) (hstep : tm.step cfg = cfg') (hout : tm.outputSymbol cfg = none)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B)
    (hpos' : ∀ i, -1 ≤ cfg'.workTapePos i ∧ cfg'.workTapePos i ≤ B) :
    Reaches tm cfg cfg' 1 B :=
  Reaches.ofFamily tm (Nat.rec cfg fun _ _ ↦ cfg') 1 B
    (fun s hs ↦ by
      obtain rfl : s = 0 := by omega
      exact hlive)
    (fun s hs ↦ by
      obtain rfl : s = 0 := by omega
      exact hstep)
    (fun s hs ↦ by
      obtain rfl : s = 0 := by omega
      exact hout)
    (fun s hs ↦ by
      cases s with
      | zero => exact hpos
      | succ s =>
        obtain rfl : s = 0 := by omega
        exact hpos')

/-- A single step to a halted configuration is a run. -/
theorem RunsTo.ofStep {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (cfg cfg' : Cfg k Bool State input) (B : ℕ)
    (hlive : cfg.state ≠ none) (hstep : tm.step cfg = cfg') (hhalt : cfg'.state = none)
    (hout : tm.outputSymbol cfg = none)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B)
    (hpos' : ∀ i, -1 ≤ cfg'.workTapePos i ∧ cfg'.workTapePos i ≤ B) :
    RunsTo tm cfg cfg' 1 B :=
  ⟨Reaches.ofStep tm cfg cfg' B hlive hstep hout hpos hpos', hhalt⟩

/-- An action on tape {lit}`i` alone: write {lit}`w`, move {lit}`m`, continue
as {lit}`s`. -/
@[expose] def decAct {k : ℕ} (i : Fin k) (w : Option (Option Bool)) (m : SignType)
    (s : Option (Fin 3)) : Action k Bool (Fin 3) where
  inputTape := 0
  workTapes j := if j = i then (w, m) else (none, 0)
  output := none
  state := s

/-- Decrement the digit list on tape {lit}`i` rightwards from its head. State
{lit}`0` borrows: reading a zero, set it and move right; reading a one, clear
it, move right and go to state {lit}`1`; reading a blank, halt. State
{lit}`1` checks for a leading zero: reading a blank, move left and go to
state {lit}`2`; reading a digit, halt. State {lit}`2` erases the cell and
halts. -/
@[expose] def decWalk {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Fin 3) where
  q₀ := 0
  tr q _ work :=
    match q.val, work i with
    | 0, some false => decAct i (some (some true)) 1 (some 0)
    | 0, some true => decAct i (some (some false)) 1 (some 1)
    | 0, none => decAct i none 0 none
    | 1, none => decAct i none (-1) (some 2)
    | 1, some _ => decAct i none 0 none
    | _, _ => decAct i (some none) 0 none

/-- Decrement the counter on tape {lit}`i` from a parked head: borrow, clear,
erase, park. -/
@[expose] def dec {k : ℕ} (i : Fin k) := seq (decWalk i) (returnTape i)

/-- {name}`decWalk` emits nothing. -/
theorem decWalk_outputSymbol {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Fin 3) input) : (decWalk i).outputSymbol cfg = none := by
  unfold outputSymbol
  cases cfg.state with
  | none => rfl
  | some q =>
    change (match q.val, cfg.workTapeSymbols i with
      | 0, some false => decAct i (some (some true)) 1 (some 0)
      | 0, some true => decAct i (some (some false)) 1 (some 1)
      | 0, none => decAct i none 0 none
      | 1, none => decAct i none (-1) (some 2)
      | 1, some _ => decAct i none 0 none
      | _, _ => decAct i (some none) 0 none).output = none
    split <;> rfl

/-- A step of {name}`decWalk` whose transition is a {name}`decAct`: tape
{lit}`i` is written at the head as the action's write says and its head moved
by the action's move. -/
theorem decWalk_step {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool (Fin 3) input)
    (q : Fin 3) (hq : cfg.state = some q) (w : Option (Option Bool)) (m : SignType)
    (s : Option (Fin 3))
    (htr : (decWalk i).tr q cfg.inputSymbol cfg.workTapeSymbols = decAct i w m s) :
    (decWalk i).step cfg =
      { cfg with
        state := s
        workTapes := Function.update cfg.workTapes i
          (w.elim (cfg.workTapes i) (Function.update (cfg.workTapes i) (cfg.workTapePos i)))
        workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i + m) } := by
  rw [step_of_state _ _ q hq, htr]
  apply Cfg.ext
  · rfl
  · change moveInputPos cfg.inputPos 0 = cfg.inputPos
    rw [moveInputPos_zero]
  · funext j
    dsimp only [decAct]
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, ite_eq_left rfl]
      cases w <;> rfl
    · rw [Function.update_of_ne hj, ite_eq_right hj]
  · funext j
    dsimp only [decAct]
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne hj, ite_eq_right hj, SignType.coe_zero, add_zero]
  · exact List.append_nil _

/-- The transition of state {lit}`0` at a zero. -/
theorem decWalk_tr_zero_false {k : ℕ} (i : Fin k) (inp : Option Bool) (work : Fin k → Option Bool)
    (h : work i = some false) :
    (decWalk i).tr 0 inp work = decAct i (some (some true)) 1 (some 0) := by
  simp only [decWalk, h]
  rfl

/-- The transition of state {lit}`0` at a one. -/
theorem decWalk_tr_zero_true {k : ℕ} (i : Fin k) (inp : Option Bool) (work : Fin k → Option Bool)
    (h : work i = some true) :
    (decWalk i).tr 0 inp work = decAct i (some (some false)) 1 (some 1) := by
  simp only [decWalk, h]
  rfl

/-- The transition of state {lit}`0` at a blank. -/
theorem decWalk_tr_zero_none {k : ℕ} (i : Fin k) (inp : Option Bool) (work : Fin k → Option Bool)
    (h : work i = none) : (decWalk i).tr 0 inp work = decAct i none 0 none := by
  simp only [decWalk, h]
  rfl

/-- The transition of state {lit}`1` at a blank. -/
theorem decWalk_tr_one_none {k : ℕ} (i : Fin k) (inp : Option Bool) (work : Fin k → Option Bool)
    (h : work i = none) : (decWalk i).tr 1 inp work = decAct i none (-1) (some 2) := by
  simp only [decWalk, h]
  rfl

/-- The transition of state {lit}`1` at a digit. -/
theorem decWalk_tr_one_some {k : ℕ} (i : Fin k) (inp : Option Bool) (work : Fin k → Option Bool)
    (b : Bool) (h : work i = some b) : (decWalk i).tr 1 inp work = decAct i none 0 none := by
  simp only [decWalk, h]
  rfl

/-- The transition of state {lit}`2`. -/
theorem decWalk_tr_two {k : ℕ} (i : Fin k) (inp : Option Bool) (work : Fin k → Option Bool) :
    (decWalk i).tr 2 inp work = decAct i (some none) 0 none := rfl

/-- A step of {name}`decWalk` from a configuration whose tape {lit}`i` and
head are updates of {lit}`cfg`'s, given the transition at the cell read. -/
theorem decWalk_step_update {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Fin 3) input) (q : Fin 3) (T : ℤ → Option Bool) (n : ℤ)
    (w : Option (Option Bool)) (m : SignType) (s : Option (Fin 3))
    (htr : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work i = T n →
      (decWalk i).tr q inp work = decAct i w m s) :
    (decWalk i).step
      { cfg with
        state := some q
        workTapes := Function.update cfg.workTapes i T
        workTapePos := Function.update cfg.workTapePos i n } =
      { cfg with
        state := s
        workTapes := Function.update cfg.workTapes i (w.elim T (Function.update T n))
        workTapePos := Function.update cfg.workTapePos i (n + m) } := by
  rw [decWalk_step i _ q rfl w m s (htr _ _ (by
    change Function.update cfg.workTapes i T i (Function.update cfg.workTapePos i n i) = T n
    rw [Function.update_self, Function.update_self]))]
  apply Cfg.ext
  · rfl
  · rfl
  · dsimp only
    rw [Function.update_idem, Function.update_self, Function.update_self]
  · dsimp only
    rw [Function.update_idem, Function.update_self]
  · rfl

/-- {name}`decWalk_step_update` for an action writing nothing. -/
theorem decWalk_step_keep {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Fin 3) input) (q : Fin 3) (T : ℤ → Option Bool) (n : ℤ)
    (m : SignType) (s : Option (Fin 3))
    (htr : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work i = T n →
      (decWalk i).tr q inp work = decAct i none m s) :
    (decWalk i).step
      { cfg with
        state := some q
        workTapes := Function.update cfg.workTapes i T
        workTapePos := Function.update cfg.workTapePos i n } =
      { cfg with
        state := s
        workTapes := Function.update cfg.workTapes i T
        workTapePos := Function.update cfg.workTapePos i (n + m) } :=
  decWalk_step_update i cfg q T n none m s htr

/-- {name}`decWalk_step_update` for an action writing {lit}`b`. -/
theorem decWalk_step_write {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Fin 3) input) (q : Fin 3) (T : ℤ → Option Bool) (n : ℤ)
    (b : Option Bool) (m : SignType) (s : Option (Fin 3))
    (htr : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work i = T n →
      (decWalk i).tr q inp work = decAct i (some b) m s) :
    (decWalk i).step
      { cfg with
        state := some q
        workTapes := Function.update cfg.workTapes i T
        workTapePos := Function.update cfg.workTapePos i n } =
      { cfg with
        state := s
        workTapes := Function.update cfg.workTapes i (Function.update T n b)
        workTapePos := Function.update cfg.workTapePos i (n + m) } :=
  decWalk_step_update i cfg q T n (some b) m s htr

/-- A cell past a run of ones holds the corresponding element of the rest. -/
theorem getElem?_replicate_true_append (n m : ℕ) (T : List Bool) :
    (List.replicate n true ++ T)[n + m]? = T[m]? := by
  rw [List.getElem?_append_right (by rw [List.length_replicate]; omega), List.length_replicate,
    Nat.add_sub_cancel_left]

/-- The configuration of {name}`decWalk` after {lit}`s` borrowing steps from
a parked start holding the digit list {lit}`d`: the first {lit}`s` digits
set, the head at cell {lit}`s`. -/
@[expose] def borrowCfg {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool (Fin 3) input)
    (d : List Bool) (s : ℕ) : Cfg k Bool (Fin 3) input :=
  { cfg with
    state := some 0
    workTapes := Function.update cfg.workTapes i
      (tapeOf (List.replicate s true ++ d.drop s).reverse)
    workTapePos := Function.update cfg.workTapePos i (s : ℤ) }

/-- The borrowing sweep: from a parked start holding {lit}`d` whose first
{lit}`c` digits are zeros, {name}`decWalk` reaches the configuration with
those digits set and its head at cell {lit}`c` in {lit}`c` steps. -/
theorem decWalk_borrow {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool (Fin 3) input)
    (hq : cfg.state = some 0) (d : List Bool) (hw : cfg.workTapes i = tapeOf d.reverse)
    (hp : cfg.workTapePos i = 0) (B : ℕ) (hB : d.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B)
    (c : ℕ) (hc : ∀ s < c, d[s]? = some false) (hcd : c ≤ d.length) :
    Reaches (decWalk i) cfg
      { cfg with
        state := some 0
        workTapes := Function.update cfg.workTapes i
          (tapeOf (List.replicate c true ++ d.drop c).reverse)
        workTapePos := Function.update cfg.workTapePos i (c : ℤ) }
      c B := by
  have hstep : ∀ s < c, (decWalk i).step (borrowCfg i cfg d s) = borrowCfg i cfg d (s + 1) := by
    intro s hs
    have hread : tapeOf (List.replicate s true ++ d.drop s).reverse (s : ℤ) = some false := by
      have h := getElem?_replicate_true_append s 0 (d.drop s)
      rw [Nat.add_zero] at h
      rw [read_tapeOf_reverse, h, List.getElem?_drop, Nat.add_zero]
      exact hc s hs
    have hset : (List.replicate s true ++ d.drop s).set s true =
        List.replicate (s + 1) true ++ d.drop (s + 1) := by
      rw [List.drop_eq_getElem_cons (by omega), set_replicate_true_append, List.replicate_succ',
        List.append_assoc, List.singleton_append]
    have hlen : s < (List.replicate s true ++ d.drop s).length := by
      rw [List.length_append, List.length_replicate, List.length_drop]
      omega
    unfold borrowCfg
    rw [decWalk_step_write i cfg 0 _ _ (some true) 1 (some 0)
      (fun inp work h ↦ decWalk_tr_zero_false i inp work (by rw [h, hread])),
      update_tapeOf_reverse _ _ hlen, hset, SignType.coe_one, Nat.cast_succ]
  have hzero : borrowCfg i cfg d 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · change Function.update cfg.workTapes i (tapeOf (List.replicate 0 true ++ d.drop 0).reverse) =
        cfg.workTapes
      rw [List.replicate_zero, List.drop_zero, List.nil_append, ← hw, Function.update_eq_self]
    · change Function.update cfg.workTapePos i ((0 : ℕ) : ℤ) = cfg.workTapePos
      rw [show (((0 : ℕ) : ℤ)) = cfg.workTapePos i by omega, Function.update_eq_self]
    · rfl
  have key := Reaches.ofFamily (decWalk i) (borrowCfg i cfg d) c B
    (fun _ _ ↦ Option.some_ne_none _) hstep (fun s _ ↦ decWalk_outputSymbol i _)
    (fun s hs j ↦ update_workTapePos_bounds i hpos (s : ℤ) (by omega) (by omega) j)
  rwa [hzero] at key

/-- {name}`decWalk` from a parked counter register holding the digit list
{lit}`d` runs at most {lit}`d.length + 3` steps and leaves it holding the
decrement, its head at a cell of the decrement or at the blank after it. -/
theorem decWalk_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool (Fin 3) input)
    (hq : cfg.state = some 0) (d : List Bool) (hw : cfg.workTapes i = tapeOf d.reverse)
    (hp : cfg.workTapePos i = 0) (B : ℕ) (hB : d.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    ∃ (p t : ℕ), p ≤ (decL d).length ∧ t ≤ d.length + 3 ∧
      RunsTo (decWalk i) cfg
        { cfg with
          state := none
          workTapes := Function.update cfg.workTapes i (tapeOf (decL d).reverse)
          workTapePos := Function.update cfg.workTapePos i (p : ℤ) } t B := by
  obtain ⟨c, d', rfl, hd'⟩ := exists_replicate_false_append d
  have hlen : (List.replicate c false ++ d').length = c + d'.length := by
    rw [List.length_append, List.length_replicate]
  have hc : ∀ s < c, (List.replicate c false ++ d')[s]? = some false := fun s hs ↦ by
    rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hs),
      List.getElem?_replicate_of_lt hs]
  have hborrow := decWalk_borrow i cfg hq _ hw hp B hB hpos c hc (by omega)
  rw [List.drop_left' List.length_replicate] at hborrow
  rw [decL_replicate_false_append]
  have hread : ∀ T : List Bool, tapeOf (List.replicate c true ++ T).reverse (c : ℤ) = T[0]? := by
    intro T
    have h := getElem?_replicate_true_append c 0 T
    rw [Nat.add_zero] at h
    rw [read_tapeOf_reverse, h]
  have hbnd : ∀ n : ℕ, n ≤ B → ∀ j, -1 ≤ Function.update cfg.workTapePos i (n : ℤ) j ∧
      Function.update cfg.workTapePos i (n : ℤ) j ≤ B :=
    fun n hn j ↦ update_workTapePos_bounds i hpos (n : ℤ) (by omega) (by omega) j
  rcases hd' with rfl | ⟨rest, rfl⟩
  · have hA := decWalk_step_keep i cfg 0 (tapeOf (List.replicate c true ++ []).reverse) (c : ℤ) 0
      none (fun inp work h ↦ decWalk_tr_zero_none i inp work (by rw [h, hread, List.getElem?_nil]))
    rw [SignType.coe_zero, add_zero] at hA
    have hl : (List.replicate c true ++ decL []).length = c := by
      rw [decL_nil, List.append_nil, List.length_replicate]
    refine ⟨c, c + 1, by omega, by omega, ?_⟩
    rw [decL_nil]
    exact ⟨hborrow.trans (RunsTo.ofStep (decWalk i) _ _ B (Option.some_ne_none _) hA rfl
      (decWalk_outputSymbol i _) (hbnd c (by omega)) (hbnd c (by omega))).toReaches, rfl⟩
  · rw [List.length_cons] at hlen
    have hB1 := decWalk_step_write i cfg 0 (tapeOf (List.replicate c true ++ true :: rest).reverse)
      (c : ℤ) (some false) 1 (some 1)
      (fun inp work h ↦ decWalk_tr_zero_true i inp work (by rw [h, hread, List.getElem?_cons_zero]))
    rw [update_tapeOf_reverse _ _
        (by rw [List.length_append, List.length_replicate, List.length_cons]; omega),
      set_replicate_true_append, SignType.coe_one, ← Nat.cast_succ] at hB1
    have r₁ := Reaches.ofStep (decWalk i) _ _ B (Option.some_ne_none _) hB1
      (decWalk_outputSymbol i _) (hbnd c (by omega)) (hbnd (c + 1) (by omega))
    have hread2 : tapeOf (List.replicate c true ++ false :: rest).reverse ((c + 1 : ℕ) : ℤ) =
        rest[0]? := by
      rw [read_tapeOf_reverse, getElem?_replicate_true_append, List.getElem?_cons_succ]
    rcases rest with _ | ⟨e, rest'⟩
    · have hB2 := decWalk_step_keep i cfg 1 (tapeOf (List.replicate c true ++ [false]).reverse)
        ((c + 1 : ℕ) : ℤ) (-1) (some 2)
        (fun inp work h ↦ decWalk_tr_one_none i inp work (by rw [h, hread2, List.getElem?_nil]))
      rw [SignType.coe_neg_one, show ((c + 1 : ℕ) : ℤ) + -1 = (c : ℤ) by omega] at hB2
      have r₂ := Reaches.ofStep (decWalk i) _ _ B (Option.some_ne_none _) hB2
        (decWalk_outputSymbol i _) (hbnd (c + 1) (by omega)) (hbnd c (by omega))
      have herase : Function.update (tapeOf (List.replicate c true ++ [false]).reverse) (c : ℤ)
          none = tapeOf (List.replicate c true ++ []).reverse := by
        rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.append_nil,
          show (c : ℤ) = ((List.replicate c true).reverse.length : ℕ) by
            rw [List.length_reverse, List.length_replicate],
          tapeOf_update_none]
      have hB3 := decWalk_step_write i cfg 2 (tapeOf (List.replicate c true ++ [false]).reverse)
        (c : ℤ) none 0 none (fun inp work _ ↦ decWalk_tr_two i inp work)
      rw [SignType.coe_zero, add_zero, herase] at hB3
      have hl : (List.replicate c true ++ decL [true]).length = c := by
        rw [decL_singleton_true, List.append_nil, List.length_replicate]
      refine ⟨c, c + 1 + 1 + 1, by omega, by omega, ?_⟩
      rw [decL_singleton_true]
      exact ⟨((hborrow.trans r₁).trans r₂).trans (RunsTo.ofStep (decWalk i) _ _ B
        (Option.some_ne_none _) hB3 rfl (decWalk_outputSymbol i _) (hbnd c (by omega))
        (hbnd c (by omega))).toReaches, rfl⟩
    · have hB2 := decWalk_step_keep i cfg 1
        (tapeOf (List.replicate c true ++ false :: e :: rest').reverse) ((c + 1 : ℕ) : ℤ) 0 none
        (fun inp work h ↦ decWalk_tr_one_some i inp work e
          (by rw [h, hread2, List.getElem?_cons_zero]))
      rw [SignType.coe_zero, add_zero] at hB2
      have hl : (List.replicate c true ++ decL (true :: e :: rest')).length =
          c + rest'.length + 2 := by
        rw [decL_cons_true_cons, List.length_append, List.length_replicate, List.length_cons,
          List.length_cons]
        omega
      rw [List.length_cons] at hlen
      refine ⟨c + 1, c + 1 + 1, by omega, by omega, ?_⟩
      rw [decL_cons_true_cons]
      exact ⟨(hborrow.trans r₁).trans (RunsTo.ofStep (decWalk i) _ _ B (Option.some_ne_none _)
        hB2 rfl (decWalk_outputSymbol i _) (hbnd (c + 1) (by omega))
        (hbnd (c + 1) (by omega))).toReaches, rfl⟩

/-- {name}`dec` transforms the valuation by decrementing the digit list of
register {lit}`i`, in {lit}`2 * B + 6` steps. -/
theorem dec_transforms {k : ℕ} (i : Fin k) (B : ℕ) :
    Transforms (dec i) (fun σ ↦ Function.update σ i (decL (σ i).reverse).reverse)
      (2 * B + 6) B := by
  intro _ cfg σ hq hpark hσ hB _
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hself : Function.update cfg.workTapePos i (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos i from (hpark i).symm, Function.update_eq_self]
  have hlenB : (σ i).reverse.length ≤ B := by
    rw [List.length_reverse]
    exact hB i
  obtain ⟨p, t, hp, ht, r₁⟩ := decWalk_runsTo i { cfg with state := some (decWalk i).q₀ } rfl
    (σ i).reverse
    (by rw [List.reverse_reverse]; exact hσ i) (hpark i) B hlenB hpos
  have hpB : p ≤ B := le_trans hp (le_trans (length_decL_le _) hlenB)
  have r₂ := returnTape_runsTo i
    { cfg with
      state := some (returnTape i).q₀
      workTapes := Function.update cfg.workTapes i (tapeOf (decL (σ i).reverse).reverse)
      workTapePos := Function.update cfg.workTapePos i (p : ℤ) }
    rfl (decL (σ i).reverse).reverse
    (by change Function.update cfg.workTapes i (tapeOf (decL (σ i).reverse).reverse) i = _
        rw [Function.update_self])
    (p : ℤ)
    (by change Function.update cfg.workTapePos i (p : ℤ) i = (p : ℤ)
        rw [Function.update_self])
    (by omega) (by rw [List.length_reverse]; omega) B
    (fun l ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) l)
  rw [Function.update_idem, hself, show ((p : ℤ) + 2).toNat = p + 2 from by omega] at r₂
  have hall := r₁.seq r₂
  rw [← liftL_start (decWalk i) (returnTape i) cfg hq] at hall
  rw [show after cfg (Function.update σ i (decL (σ i).reverse).reverse) =
      liftR { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (decL (σ i).reverse).reverse) }
      from ?_]
  · exact ⟨_, by omega, hall⟩
  · apply Cfg.ext
    · rfl
    · rfl
    · funext l
      change tapeOf (Function.update σ i (decL (σ i).reverse).reverse l) =
        Function.update cfg.workTapes i (tapeOf (decL (σ i).reverse).reverse) l
      by_cases hl : l = i
      · rw [hl, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hl, Function.update_of_ne hl, hσ l]
    · rfl
    · rfl

end

end Geb.SizeBounded.Logspace.Machine
