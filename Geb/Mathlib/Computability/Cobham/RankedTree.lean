/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Cases
public import Geb.Mathlib.Data.Tree.Ranked.Preorder

/-!
# The generic ranked recognizer

The validity scan of `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`, at an
arbitrary ranked alphabet, as an expression of Cobham's class.

## Main definitions

* `Cobham.bufBits` — the incomplete block in a slot of the alphabet's width.
* `Cobham.stateWord` — the scan state as a bitstring.
* `Cobham.dispatchWidth` — the number of state bits a step dispatches on.
* `Cobham.decodeState` — the inverse of the state layout.
* `Cobham.dropCount`, `Cobham.nextPrefix` — the bits a step drops and
  prepends.
* `Cobham.rankedStep`, `Cobham.rankedSem` — the recognizer's step and the
  meaning of its scan.
* `Cobham.ranked`, `Cobham.rankedOf` — the scan as an expression of `C`, and
  at its declared arity.

## Main statements

* `Cobham.length_bufBits_of_lt`, `Cobham.length_stateWord_of_lt` — the slot's
  and the state word's lengths.
* `Cobham.dropWhile_bufBits` — the slot past its padding.
* `Cobham.ofFn_bits_stateWord` — the state word truncated to a window and
  zero-padded.
* `Cobham.decodeState_stateWord_of_lt` — the decoder inverts the layout up to
  capping the pending count at the depth window.
* `Cobham.dropCount_min_depth`, `Cobham.nextPrefix_min_depth` — capping the
  pending count at the depth window changes neither.
* `Cobham.stateWord_scanStep_of_lt` — a step rewrites a bounded prefix and
  drops a bounded number of bits.
* `Cobham.stepWord_rankedStep_of_lt`, `Cobham.rankedSem_eq` — the expression
  computes the scan, one step and then on every input.
* `Cobham.length_rankedSem_le` — the recursion bound the scanner asks for.
* `Cobham.rankedSem_eq_eval` — the meaning read at the raw tree is the meaning
  the expression carries.

## Implementation notes

`RankedAlphabet.Scan` carries an incomplete block, a count of pending
subterms, and a liveness flag. The count is unbounded and the other two are
not, and an expression of the class reaches only a bounded prefix of a word,
so the count is the tail and the layout admits no alternative.

The block cannot be delimited by its own length, since the fields after it
would then stand at a position not statically known. It occupies a slot of
exactly `R.width` bits, delimited by a `true` sentinel preceded by `false`
padding: reading from offset one, past the flag, the first `true` is the
sentinel and the block is what follows it, the padding being all `false`. The
slot's length is invariant under accumulation — the padding shrinks as the
block grows — which is why the fields after it never move. This costs
`R.width` bits rather than the `2 * R.width` a separate fill counter would.

`length_bufBits_of_lt`'s hypothesis is consumed rather than decorative. `Nat`
subtraction being truncated, a block of length `R.width` or more yields a slot
of length one past the block, and `stateWord` is then not injective: at
`R.width = 2` the states `⟨[false, true], 0, true⟩` and `⟨[false], 1, true⟩`
share the word `[true, true, false, true]`. The invariant excluding this is
`RankedAlphabet.length_buf_scanFinal_lt`.

The pending count is unary. Binary would need a truncated subtraction
definable in the class, and `Cobham/Tree.lean`'s recognizer represents its own
depth in unary already.

`ofFn_bits_stateWord` is stated at an arbitrary window rather than at
`dispatchWidth`.

The branch family's domain is `Fin (dispatchWidth R) → Bool` at a symbolic
width, so recovering the fields index by index would carry a bound proof at
every step. `decodeState` avoids that by passing through `List.ofFn` and
reading the fields with the `List` API. This also keeps the module clear of
`DecidableEq (Fin n → Bool)`, which resolves through
`Fintype.decidablePiFintype`, measured as depending on `Classical.choice`,
while `DecidableEq (List Bool)` measures clean.

The run of `false` past the slot is cleared by a two-case reduction rather
than by `List.takeWhile_replicate`, which was measured to depend on
`Classical.choice` through `List.filter_replicate`. A proof shortened back
onto that lemma fails `lake lint`.

The dispatch reads the flag and the slot together with the low
`R.maxArity + 1` bits of the pending count, which give
`min depth (R.maxArity + 1)`. Those bits decide `r ≤ depth` for every symbol:
if the count is at least `R.maxArity + 1` then every arity is below it, and
otherwise those bits are the count itself.
`RankedAlphabet.le_maxArity_of_arOf_eq_some` is what makes the window
sufficient, and it is what `dropCount_min_depth` and `nextPrefix_min_depth`
consume.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, ranked alphabet, preorder, scan
-/

namespace Cobham

open RankedAlphabet

public section

/-- The incomplete block in a slot of the alphabet's width: `false` padding,
a `true` sentinel, then the block. -/
@[expose] def bufBits (R : RankedAlphabet) (buf : List Bool) : List Bool :=
  List.replicate (R.width - 1 - buf.length) false ++ true :: buf

/-- The scan state as a bitstring: the liveness flag, the block slot, then the
pending count in unary. -/
@[expose] def stateWord (R : RankedAlphabet) (s : Scan) : List Bool :=
  s.live :: bufBits R s.buf ++ List.replicate s.depth true

/-- The number of state bits a step dispatches on: the flag, the slot, and
enough of the pending count to decide `r ≤ depth` for every arity `r`. -/
@[expose] def dispatchWidth (R : RankedAlphabet) : ℕ := R.width + R.maxArity + 2

/-- The slot holds the alphabet's width, the padding shrinking as the block
grows. `Nat` subtraction being truncated, the hypothesis is consumed. -/
theorem length_bufBits_of_lt (R : RankedAlphabet) (buf : List Bool)
    (h : buf.length < R.width) : (bufBits R buf).length = R.width := by
  rw [bufBits, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The state word's length: the flag, the slot, and the pending count. -/
theorem length_stateWord_of_lt (R : RankedAlphabet) (s : Scan)
    (h : s.buf.length < R.width) :
    (stateWord R s).length = 1 + R.width + s.depth := by
  rw [stateWord, List.cons_append, List.length_cons, List.length_append,
    length_bufBits_of_lt R s.buf h, List.length_replicate]
  omega

/-- The slot past its padding is the sentinel followed by the block. -/
theorem dropWhile_bufBits (R : RankedAlphabet) (buf : List Bool) :
    (bufBits R buf).dropWhile (fun b ↦ !b) = true :: buf := by
  rw [bufBits, List.dropWhile_append_of_pos
    (fun a ha ↦ by rw [List.eq_of_mem_replicate ha]; rfl)]
  rfl

/-- The state word truncated to a window past the slot and zero-padded: the
flag, the slot, and the pending count capped at the window. Stated at an
arbitrary window rather than at `dispatchWidth`. -/
theorem ofFn_bits_stateWord (R : RankedAlphabet) (s : Scan) (p m : ℕ)
    (hp : p = 1 + R.width + m) (h : s.buf.length < R.width) :
    List.ofFn (bits p (stateWord R s)) =
      s.live :: (bufBits R s.buf ++
        (List.replicate (min m s.depth) true ++
          List.replicate (m - s.depth) false)) := by
  subst hp
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hdw : 1 + R.width + m = (bufBits R s.buf).length + m + 1 := by
    rw [hbuf]
    omega
  have hpad : 1 + R.width + m - (stateWord R s).length = m - s.depth := by
    rw [length_stateWord_of_lt R s h]
    omega
  rw [ofFn_bits, hpad, stateWord, List.cons_append, hdw, List.take_succ_cons,
    List.take_length_add_append, List.take_replicate, List.cons_append,
    List.append_assoc]

/-- The inverse of the state layout, read off `List.ofFn` of the bit family:
the flag is the head, the block is the slot past its padding and sentinel, and
the pending count is the run of `true` that follows the slot. Every operation
is structural, so no `Fin` arithmetic and no `Fintype`-derived decidability
arises. -/
@[expose] def decodeState (R : RankedAlphabet)
    (v : Fin (dispatchWidth R) → Bool) : Scan :=
  ⟨(((List.ofFn v).tail.take R.width).dropWhile (fun b ↦ !b)).tail,
    (((List.ofFn v).tail.drop R.width).takeWhile id).length,
    (List.ofFn v).headD false⟩

/-- The decoder inverts the layout, up to capping the pending count at the
depth window `R.maxArity + 1`. -/
theorem decodeState_stateWord_of_lt (R : RankedAlphabet) (s : Scan)
    (h : s.buf.length < R.width) :
    decodeState R (bits (dispatchWidth R) (stateWord R s)) =
      { s with depth := min s.depth (R.maxArity + 1) } := by
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hword := ofFn_bits_stateWord R s (dispatchWidth R) (R.maxArity + 1)
    (by rw [dispatchWidth]; omega) h
  have hslot : ((List.ofFn (bits (dispatchWidth R) (stateWord R s))).tail.take
      R.width) = bufBits R s.buf := by
    rw [hword, List.tail_cons, List.take_left' hbuf]
  have htail : ((List.ofFn (bits (dispatchWidth R) (stateWord R s))).tail.drop
      R.width) = List.replicate (min (R.maxArity + 1) s.depth) true ++
        List.replicate (R.maxArity + 1 - s.depth) false := by
    rw [hword, List.tail_cons, List.drop_left' hbuf]
  refine Scan.ext ?_ ?_ ?_
  · rw [decodeState, hslot, dropWhile_bufBits]
    rfl
  · have hfalse : ∀ j : ℕ, (List.replicate j false).takeWhile id = [] := fun j ↦
      match j with
      | 0 => rfl
      | _ + 1 => rfl
    rw [decodeState, htail,
      List.takeWhile_append_of_pos (fun a ha ↦ by rw [List.eq_of_mem_replicate ha]; rfl),
      hfalse, List.append_nil, List.length_replicate]
    exact Nat.min_comm _ _
  · rw [decodeState, hword, List.headD_cons]

/-- The bits a step drops from the state word: the flag and the slot, together
with the popped subterms where a completed block's symbol pops. -/
@[expose] def dropCount (R : RankedAlphabet) (b : Bool) (s : Scan) : ℕ :=
  match s.live with
  | false => 1 + R.width
  | true =>
    match decide ((b :: s.buf).length = R.width) with
    | false => 1 + R.width
    | true =>
      match R.arOf (decodeBits (b :: s.buf)) with
      | none => 1 + R.width
      | some r =>
        match decide (r ≤ s.depth) with
        | false => 1 + R.width
        | true => 1 + R.width + r

/-- The bits a step prepends to the state word: the rebuilt flag and slot,
together with the pushed subterm where a completed block's symbol pops. -/
@[expose] def nextPrefix (R : RankedAlphabet) (b : Bool) (s : Scan) :
    List Bool :=
  match s.live with
  | false => false :: bufBits R s.buf
  | true =>
    match decide ((b :: s.buf).length = R.width) with
    | false => true :: bufBits R (b :: s.buf)
    | true =>
      match R.arOf (decodeBits (b :: s.buf)) with
      | none => false :: bufBits R []
      | some r =>
        match decide (r ≤ s.depth) with
        | false => false :: bufBits R []
        | true => true :: bufBits R [] ++ [true]

/-- Capping the pending count at the depth window `R.maxArity + 1` leaves the
bits dropped unchanged: the only test reading the count compares it with an
arity, which is at most the largest. -/
theorem dropCount_min_depth (R : RankedAlphabet) (b : Bool) (s : Scan) :
    dropCount R b { s with depth := min s.depth (R.maxArity + 1) } =
      dropCount R b s := by
  obtain ⟨buf, depth, live⟩ := s
  rw [dropCount, dropCount]
  dsimp only
  cases live
  · rfl
  · cases har : R.arOf (decodeBits (b :: buf))
    · rfl
    · rename_i r
      have hr : r ≤ R.maxArity := le_maxArity_of_arOf_eq_some R har
      dsimp only
      rcases Nat.le_total depth (R.maxArity + 1) with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [decide_eq_true (by omega : r ≤ min depth (R.maxArity + 1)),
          decide_eq_true (by omega : r ≤ depth)]

/-- Capping the pending count leaves the bits prepended unchanged, as
`dropCount_min_depth`. -/
theorem nextPrefix_min_depth (R : RankedAlphabet) (b : Bool) (s : Scan) :
    nextPrefix R b { s with depth := min s.depth (R.maxArity + 1) } =
      nextPrefix R b s := by
  obtain ⟨buf, depth, live⟩ := s
  rw [nextPrefix, nextPrefix]
  dsimp only
  cases live
  · rfl
  · cases har : R.arOf (decodeBits (b :: buf))
    · rfl
    · rename_i r
      have hr : r ≤ R.maxArity := le_maxArity_of_arOf_eq_some R har
      dsimp only
      rcases Nat.le_total depth (R.maxArity + 1) with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [decide_eq_true (by omega : r ≤ min depth (R.maxArity + 1)),
          decide_eq_true (by omega : r ≤ depth)]

/-- A step of the scan rewrites a bounded prefix of the state word and drops a
bounded number of its bits: the flag and the slot are rebuilt, and the pending
count in the tail is popped by the arity of a completed block's symbol. -/
theorem stateWord_scanStep_of_lt (R : RankedAlphabet) (b : Bool) (s : Scan)
    (h : s.buf.length < R.width) :
    stateWord R (R.scanStep b s) =
      nextPrefix R b s ++ (stateWord R s).drop (dropCount R b s) := by
  have hpre : (s.live :: bufBits R s.buf).length = 1 + R.width := by
    rw [List.length_cons, length_bufBits_of_lt R s.buf h]
    omega
  have hdrop : (stateWord R s).drop (1 + R.width) =
      List.replicate s.depth true := List.drop_left' hpre
  have hdropr : ∀ r : ℕ, (stateWord R s).drop (1 + R.width + r) =
      List.replicate (s.depth - r) true := fun r ↦ by
    rw [← List.drop_drop, hdrop, List.drop_replicate]
  obtain ⟨buf, depth, live⟩ := s
  rw [scanStep, dropCount, nextPrefix]
  dsimp only
  cases live
  · dsimp only
    rw [hdrop]
    rfl
  · cases hc : decide ((b :: buf).length = R.width)
    · dsimp only
      rw [hdrop]
      rfl
    · dsimp only
      cases har : R.arOf (decodeBits (b :: buf))
      · dsimp only
        rw [hdrop]
        rfl
      · rename_i r
        dsimp only
        cases hle : decide (r ≤ depth)
        · dsimp only
          rw [hdrop]
          rfl
        · dsimp only
          rw [hdropr r, stateWord, List.replicate_succ, List.append_assoc]
          rfl

/-- One step of the recognizer: dispatch on the state's leading bits, prepend
the rebuilt prefix and drop the consumed bits. Every branch has that one
shape. -/
@[expose] def rankedStep (R : RankedAlphabet) (b : Bool) : COf 1 :=
  diagOf (casesOf (dispatchWidth R) fun v ↦
    prependOf (nextPrefix R b (decodeState R v))
      (predIterOf (dropCount R b (decodeState R v))))

/-- The recognizer's scan, at the two steps and the growth the state layout
allows. -/
@[expose] def rankedSem (R : RankedAlphabet) : Sem 1 :=
  scanSem (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1)

/-- A step of the expression computes a step of the scan, on a state whose
incomplete block is short of the width. This is where the decoder, the two
capping lemmas and the step lemma meet. -/
theorem stepWord_rankedStep_of_lt (R : RankedAlphabet) (b : Bool) (s : Scan)
    (h : s.buf.length < R.width) :
    stepWord (rankedStep R b) (stateWord R s) = stateWord R (R.scanStep b s) := by
  rw [rankedStep, stepWord_diagOf]
  change casesSem (dispatchWidth R) _ ![stateWord R s, stateWord R s] = _
  rw [casesSem_eq, stepWord_prependOf, stepWord_predIterOf,
    decodeState_stateWord_of_lt R s h, nextPrefix_min_depth, dropCount_min_depth,
    stateWord_scanStep_of_lt R b s h]

/-- The expression computes the scan's state word on every input. -/
theorem rankedSem_eq (R : RankedAlphabet) (w : List Bool) :
    rankedSem R ![w] = stateWord R (R.scanFinal w) := by
  rw [rankedSem, scanSem_eq]
  refine List.rec ?_ ?_ w
  · rw [List.foldr_nil, baseWord_constAtOf, scanFinal_nil]
  · intro b v ih
    rw [List.foldr_cons, ih, scanFinal_cons]
    cases b
    · exact stepWord_rankedStep_of_lt R false _ (length_buf_scanFinal_lt R v)
    · exact stepWord_rankedStep_of_lt R true _ (length_buf_scanFinal_lt R v)

/-- The value never exceeds the input by more than the state's fixed part, so
the scanner's recursion bound holds at growth `R.width + 1`. Stated at
`scanSem`, which is the form `Cobham.scan` consumes. At the empty word the
bound is tight. -/
theorem length_rankedSem_le (R : RankedAlphabet) (w : List Bool) :
    (scanSem (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
      (rankedStep R true) (R.width + 1) ![w]).length ≤ w.length + (R.width + 1) := by
  have hlen := length_stateWord_of_lt R (R.scanFinal w) (length_buf_scanFinal_lt R w)
  have hdepth := depth_scanFinal_le_length R w
  rw [← rankedSem, rankedSem_eq, hlen]
  omega

/-- The scan as an expression of the class, its recursion bound discharged by
`length_rankedSem_le`. -/
@[expose] def ranked (R : RankedAlphabet) : C :=
  scan (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)

/-- `ranked` at its declared arity. -/
@[expose] def rankedOf (R : RankedAlphabet) : COf 1 :=
  scanOf (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)

/-- The meaning `rankedSem` reads at the raw tree is the meaning `ranked`
carries. -/
theorem rankedSem_eq_eval (R : RankedAlphabet) :
    transport (rankedOf R).2 (rankedOf R).1.eval = rankedSem R :=
  scanSem_eq_eval (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)

end

end Cobham
