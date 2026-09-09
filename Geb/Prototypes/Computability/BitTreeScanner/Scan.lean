/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Encoding

set_option doc.verso true

/-!
# The left-to-right scan recognizing spelled trees

A single left-to-right pass over a bitstring carrying a mode and a counter,
which accepts exactly the spellings of {name}`Geb.BitTreeScanner.spell`. The mode
records whether the scan expects a tree, is inside a leaf, has completed the
one tree it expects, or has failed; the counter is the number of trees pending
beyond the one in progress. A pair bit raises the counter; a leaf's closing bit
lowers it, or completes the scan when nothing is pending.

The counter is the pending count of {lit}`RankedAlphabet.Binary.depth` less
one, so that it is never negative and the completed scan is a mode rather
than a count. Validity is one condition on the final state, that its mode is
the completed one, and {lit}`Geb.BitTreeScanner.valid_iff_exists_spell` identifies
the words satisfying it with the spellings.

## Main definitions

* {lit}`Geb.BitTreeScanner.Mode`, {lit}`Geb.BitTreeScanner.Scan` — the scan's modes and its
  state.
* {lit}`Geb.BitTreeScanner.close` — the state a completed tree leaves at a pending
  count.
* {lit}`Geb.BitTreeScanner.scanStep`, {lit}`Geb.BitTreeScanner.scanFrom`,
  {lit}`Geb.BitTreeScanner.init`, {lit}`Geb.BitTreeScanner.scanFinal` — the scan.
* {lit}`Geb.BitTreeScanner.validBool`, {lit}`Geb.BitTreeScanner.Valid` — what it accepts.

## Main statements

* {lit}`Geb.BitTreeScanner.scanFrom_spell` — a spelling scanned from the expecting
  mode at any pending count completes that count.
* {lit}`Geb.BitTreeScanner.valid_spell` — every spelling is valid.
* {lit}`Geb.BitTreeScanner.exists_spell_of_valid` — every valid word is a spelling.
* {lit}`Geb.BitTreeScanner.valid_iff_exists_spell` — the valid words are exactly the
  spellings.
* {lit}`Geb.BitTreeScanner.eq_nil_of_spell_eq_spell_append` — no spelling is a
  proper prefix of another: the encoding is a prefix code.
* {lit}`Geb.BitTreeScanner.scanFinal_take_succ` — the scan of a prefix extended by
  one bit, the form a machine step against the scan consumes.

## Implementation notes

The scan reads from the list's head, so {lit}`scanFrom` is a {name}`List.foldl`
and a step on a prefix extended at its end is {name}`List.foldl_append`. The
right-to-left scan of {lit}`RankedAlphabet.scanFrom` reads a word's last bit
first because a prefix code is read in preorder from the left; here the
machine also reads from the left, in one pass, so nothing reverses.

{lit}`exists_spell_of_valid` recurses on a bound on the word's length rather
than on the word: the pair case applies its hypothesis to the remainder the
left child leaves, which is not a structural subterm. The leaf case is
{lit}`exists_leafBody_append`, whose recursion on the word carries both
in-leaf modes at once, since the two alternate bit by bit.

A {lit}`scanStep` equation at a mode whose row of the match is a catch-all in
the bit column is proved by cases on the bit: the compiled matcher inspects
the bit there, so the equation is not {lit}`rfl` at a variable bit.

## Tags

binary tree, prefix code, scan, recognizer, counter automaton
-/

@[expose] public section

namespace Geb.BitTreeScanner

/-- The scan's mode. -/
inductive Mode where
  /-- Expecting a tree. -/
  | term
  /-- Inside a leaf, expecting a payload bit's prefix or the closing bit. -/
  | leafOpen
  /-- Inside a leaf, expecting a payload bit. -/
  | leafBit
  /-- The one expected tree complete, nothing pending. -/
  | done
  /-- Failed: a bit read after completion. -/
  | dead
  deriving DecidableEq, Repr, Inhabited

/-- The scan's state: its mode, and the count of trees pending beyond the one
in progress. -/
@[ext] structure Scan where
  /-- The mode. -/
  mode : Mode
  /-- The count of trees pending beyond the one in progress. -/
  count : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The state a completed tree leaves at a pending count: complete when
nothing is pending, else expecting the next tree with one fewer pending. -/
def close : ℕ → Scan
  | 0 => ⟨.done, 0⟩
  | c + 1 => ⟨.term, c⟩

/-- One step of the scan, reading one bit. A pair bit raises the count and a
leaf bit opens a leaf; inside a leaf, {lit}`true` announces a payload bit and
{lit}`false` closes the leaf; after completion any bit fails, and failure
absorbs. -/
def scanStep (s : Scan) (b : Bool) : Scan :=
  match s.mode, b with
  | .term, true => ⟨.term, s.count + 1⟩
  | .term, false => ⟨.leafOpen, s.count⟩
  | .leafOpen, true => ⟨.leafBit, s.count⟩
  | .leafOpen, false => close s.count
  | .leafBit, _ => ⟨.leafOpen, s.count⟩
  | .done, _ => ⟨.dead, s.count⟩
  | .dead, _ => s

/-- The scan of a word from a state, reading the word's head first. -/
def scanFrom (w : List Bool) (s : Scan) : Scan := w.foldl scanStep s

/-- The initial state: expecting one tree, nothing pending. -/
def init : Scan := ⟨.term, 0⟩

/-- The scan of a word from the initial state. -/
def scanFinal (w : List Bool) : Scan := scanFrom w init

/-- Whether a word spells a tree: the scan completes. -/
def validBool (w : List Bool) : Bool := decide ((scanFinal w).mode = .done)

/-- A word spells a tree. -/
def Valid (w : List Bool) : Prop := validBool w = true

/-- {name}`Valid` is a {lit}`Bool` equation, so membership is decidable.
Instance search does not unfold the {lit}`def`, so the instance is
supplied. -/
instance : DecidablePred Valid := fun _ ↦ inferInstanceAs (Decidable (_ = true))

section Equations

/-- Nothing pending: completion. -/
@[simp] theorem close_zero : close 0 = ⟨.done, 0⟩ := rfl

/-- Something pending: the next tree is expected. -/
@[simp] theorem close_succ (c : ℕ) : close (c + 1) = ⟨.term, c⟩ := rfl

/-- A pair bit raises the pending count. -/
@[simp] theorem scanStep_term_true (c : ℕ) : scanStep ⟨.term, c⟩ true = ⟨.term, c + 1⟩ := rfl

/-- A leaf bit opens a leaf. -/
@[simp] theorem scanStep_term_false (c : ℕ) : scanStep ⟨.term, c⟩ false = ⟨.leafOpen, c⟩ := rfl

/-- Inside a leaf, {lit}`true` announces a payload bit. -/
@[simp] theorem scanStep_leafOpen_true (c : ℕ) :
    scanStep ⟨.leafOpen, c⟩ true = ⟨.leafBit, c⟩ := rfl

/-- Inside a leaf, {lit}`false` closes it. -/
@[simp] theorem scanStep_leafOpen_false (c : ℕ) : scanStep ⟨.leafOpen, c⟩ false = close c := rfl

/-- A payload bit returns to the leaf's open mode. -/
@[simp] theorem scanStep_leafBit (c : ℕ) (b : Bool) :
    scanStep ⟨.leafBit, c⟩ b = ⟨.leafOpen, c⟩ := by
  cases b <;> rfl

/-- A bit after completion fails. -/
@[simp] theorem scanStep_done (c : ℕ) (b : Bool) : scanStep ⟨.done, c⟩ b = ⟨.dead, c⟩ := by
  cases b <;> rfl

/-- Failure absorbs. -/
@[simp] theorem scanStep_dead (c : ℕ) (b : Bool) : scanStep ⟨.dead, c⟩ b = ⟨.dead, c⟩ := by
  cases b <;> rfl

/-- The empty word leaves the state. -/
@[simp] theorem scanFrom_nil (s : Scan) : scanFrom [] s = s := rfl

/-- The scan of the empty word is the initial state. -/
@[simp] theorem scanFinal_nil : scanFinal [] = init := rfl

/-- The scan reads the head bit first. -/
@[simp] theorem scanFrom_cons (b : Bool) (w : List Bool) (s : Scan) :
    scanFrom (b :: w) s = scanFrom w (scanStep s b) := rfl

/-- The scan of a concatenation reads the earlier part first. -/
theorem scanFrom_append (u v : List Bool) (s : Scan) :
    scanFrom (u ++ v) s = scanFrom v (scanFrom u s) := List.foldl_append

/-- A failed scan reads no further. -/
theorem scanFrom_dead (w : List Bool) (c : ℕ) : scanFrom w ⟨.dead, c⟩ = ⟨.dead, c⟩ :=
  List.rec (motive := fun w ↦ scanFrom w ⟨.dead, c⟩ = ⟨.dead, c⟩) rfl
    (fun b _ ih ↦ by rw [scanFrom_cons, scanStep_dead]; exact ih) w

/-- The scan of a prefix extended by one bit is the scan of the prefix followed
by that bit. -/
theorem scanFinal_take_succ (w : List Bool) (k : ℕ) (h : k < w.length) :
    scanFinal (w.take (k + 1)) = scanStep (scanFinal (w.take k)) w[k] := by
  rw [List.take_succ_eq_append_getElem h, scanFinal, scanFinal, scanFrom_append]
  rfl

end Equations

section Soundness

/-- A leaf body read in the leaf's open mode completes the pending count. -/
theorem scanFrom_leafBody (s : List Bool) (c : ℕ) :
    scanFrom (leafBody s) ⟨.leafOpen, c⟩ = close c :=
  List.rec (motive := fun s ↦ scanFrom (leafBody s) ⟨.leafOpen, c⟩ = close c) rfl
    (fun b _ ih ↦ by
      rw [leafBody_cons, scanFrom_cons, scanStep_leafOpen_true, scanFrom_cons, scanStep_leafBit]
      exact ih) s

/-- A spelling read in the expecting mode completes the pending count. -/
theorem scanFrom_spell (t : BitTree) : ∀ c, scanFrom (spell t) ⟨.term, c⟩ = close c :=
  PFunctor.FreeM.rec (motive := fun t ↦ ∀ c, scanFrom (spell t) ⟨.term, c⟩ = close c)
    (fun s c ↦ scanFrom_leafBody s c)
    (fun a k ih c ↦ by
      rw [spell_liftBind, scanFrom_cons, scanStep_term_true, scanFrom_append, ih false,
        close_succ, ih true]) t

/-- Every spelling is valid. -/
theorem valid_spell (t : BitTree) : Valid (spell t) := by
  unfold Valid validBool scanFinal init
  rw [scanFrom_spell t 0]
  rfl

end Soundness

section Completeness

/-- A word completing the scan from inside a leaf begins with the rest of a leaf
body, the remainder completing the scan from the state the leaf leaves. The
two in-leaf modes alternate bit by bit, so the recursion carries both: in the
open mode the word begins with a body, in payload bit and then
a body. -/
theorem exists_leafBody_append (w : List Bool) :
    (∀ c, (scanFrom w ⟨.leafOpen, c⟩).mode = .done →
      ∃ s v, w = leafBody s ++ v ∧ (scanFrom v (close c)).mode = .done) ∧
    (∀ c, (scanFrom w ⟨.leafBit, c⟩).mode = .done →
      ∃ b s v, w = (b :: leafBody s) ++ v ∧ (scanFrom v (close c)).mode = .done) :=
  List.rec
    (motive := fun w ↦
      (∀ c, (scanFrom w ⟨.leafOpen, c⟩).mode = .done →
        ∃ s v, w = leafBody s ++ v ∧ (scanFrom v (close c)).mode = .done) ∧
      (∀ c, (scanFrom w ⟨.leafBit, c⟩).mode = .done →
        ∃ b s v, w = (b :: leafBody s) ++ v ∧ (scanFrom v (close c)).mode = .done))
    ⟨fun _ h ↦ (nomatch h), fun _ h ↦ (nomatch h)⟩
    (fun b w ih ↦ by
      refine ⟨fun c h ↦ ?_, fun c h ↦ ?_⟩
      · cases b with
        | false => exact ⟨[], w, rfl, h⟩
        | true =>
          obtain ⟨b', s, v, hw, hv⟩ := ih.2 c h
          exact ⟨b' :: s, v, by rw [hw, leafBody_cons]; simp only [List.cons_append], hv⟩
      · rw [scanFrom_cons, scanStep_leafBit] at h
        obtain ⟨s, v, hw, hv⟩ := ih.1 c h
        exact ⟨b, s, v, by rw [hw, List.cons_append], hv⟩) w

/-- A word of bounded length completing the scan from the expecting mode begins
with a spelling, the remainder completing the scan from the state the tree
leaves. The recursion is on the bound: the pair case applies its hypothesis
to the remainder the left child leaves, which is not a structural subterm of
the word. -/
theorem exists_spell_append_of_length_le (n : ℕ) :
    ∀ w : List Bool, w.length ≤ n → ∀ c, (scanFrom w ⟨.term, c⟩).mode = .done →
      ∃ t v, w = spell t ++ v ∧ (scanFrom v (close c)).mode = .done :=
  Nat.rec
    (motive := fun n ↦ ∀ w : List Bool, w.length ≤ n → ∀ c,
      (scanFrom w ⟨.term, c⟩).mode = .done →
        ∃ t v, w = spell t ++ v ∧ (scanFrom v (close c)).mode = .done)
    (fun w hw c h ↦ by
      cases w with
      | nil => exact nomatch h
      | cons b w => exact absurd hw (by simp))
    (fun n ih w hw c h ↦ by
      cases w with
      | nil => exact nomatch h
      | cons b w =>
        rw [List.length_cons] at hw
        cases b with
        | false =>
          obtain ⟨s, v, hw', hv⟩ := (exists_leafBody_append w).1 c h
          exact ⟨leaf s, v, by rw [hw', spell_leaf, List.cons_append], hv⟩
        | true =>
          obtain ⟨l, v₁, hw₁, hv₁⟩ := ih w (by omega) (c + 1) h
          have hv₁len : v₁.length ≤ n := by
            have := congrArg List.length hw₁
            rw [List.length_append] at this
            omega
          obtain ⟨r, v, hv, hvv⟩ := ih v₁ hv₁len c hv₁
          exact ⟨pair l r, v, by rw [hw₁, hv, spell_pair, List.cons_append, List.append_assoc],
            hvv⟩) n

/-- A word completing the scan from the completed mode is empty: a bit read
after completion fails, and failure absorbs. -/
theorem eq_nil_of_mode_scanFrom_done_eq_done (w : List Bool) (c : ℕ)
    (h : (scanFrom w ⟨.done, c⟩).mode = .done) : w = [] := by
  cases w with
  | nil => rfl
  | cons b w =>
    rw [scanFrom_cons, scanStep_done, scanFrom_dead] at h
    exact nomatch h

/-- Every valid word is a spelling. -/
theorem exists_spell_of_valid {w : List Bool} (h : Valid w) : ∃ t, spell t = w := by
  have h' : (scanFrom w ⟨.term, 0⟩).mode = .done := of_decide_eq_true h
  obtain ⟨t, v, hw, hv⟩ := exists_spell_append_of_length_le w.length w le_rfl 0 h'
  rw [close_zero] at hv
  rw [eq_nil_of_mode_scanFrom_done_eq_done v 0 hv, List.append_nil] at hw
  exact ⟨t, hw.symm⟩

/-- The valid words are exactly the spellings. -/
theorem valid_iff_exists_spell (w : List Bool) : Valid w ↔ ∃ t, spell t = w :=
  ⟨exists_spell_of_valid, fun ⟨t, ht⟩ ↦ ht ▸ valid_spell t⟩

/-- No spelling is a proper prefix of another: the scan completes at the end
of the shorter and fails on any bit after it. -/
theorem eq_nil_of_spell_eq_spell_append (t t' : BitTree) (v : List Bool)
    (h : spell t = spell t' ++ v) : v = [] := by
  have hv : (scanFrom v (close 0)).mode = .done := by
    rw [← scanFrom_spell t' 0, ← scanFrom_append, ← h, scanFrom_spell t 0]
    rfl
  exact eq_nil_of_mode_scanFrom_done_eq_done v 0 hv

end Completeness

end Geb.BitTreeScanner
