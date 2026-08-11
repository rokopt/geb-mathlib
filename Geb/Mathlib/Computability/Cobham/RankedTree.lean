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

The state of the validity scan of
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`, at an arbitrary ranked alphabet,
laid out as a bitstring.

## Main definitions

* `Cobham.bufBits` — the incomplete block in a slot of the alphabet's width.
* `Cobham.stateWord` — the scan state as a bitstring.
* `Cobham.dispatchWidth` — the number of state bits a step dispatches on.

## Main statements

* `Cobham.length_bufBits_of_lt`, `Cobham.length_stateWord_of_lt` — the slot's
  and the state word's lengths.
* `Cobham.dropWhile_bufBits` — the slot past its padding.
* `Cobham.ofFn_bits_stateWord` — the state word truncated to a window and
  zero-padded.

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

end

end Cobham
