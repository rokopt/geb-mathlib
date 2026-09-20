# Reducing the W-tree recognizer's cost — measurements and handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Three cost models, kept apart](#three-cost-models-kept-apart)
- [Measurements](#measurements)
  - [Reproducing them](#reproducing-them)
- [The floor](#the-floor)
- [Where the present expression spends its time](#where-the-present-expression-spends-its-time)
- [The expression to write](#the-expression-to-write)
- [What to measure, and what to expect](#what-to-measure-and-what-to-expect)
- [Risks](#risks)
- [Order of work](#order-of-work)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

The recognizer of the spellings of the size-bounded algebra's expressions,
`Geb.SizeBounded.Logspace.WTree.SigCheck.sigRecognizer`, is correct and
carries its machine bound, but evaluating it is slow enough that the tests
exercise it on one ten-bit word. This document records what the cost is,
where it comes from, what the floor is, and how to rewrite the numeral
arithmetic to approach that floor. It covers
`Geb/Prototypes/Computability/SizeBounded/Logspace/WTree/`, chiefly
`BitFold.lean`, `NumArith.lean`, `NumSum.lean` and `NumScanExpr.lean`.

This document is a transient process artifact in the sense of
`CONTRIBUTING.md` § Concern shape: remove it in the final commits of the
branch. What is permanent belongs in the module docstrings, `docs/index.md`
and `TODO.md`.

## Three cost models, kept apart

- The specification, `CodedSig.recognize`, is plain Lean. Its counters are
  natural numbers, so a comparison is one machine operation.
- The expression under the evaluator with sharing, `SOf.semVec`
  (`Geb/Prototypes/Computability/SizeBounded/Sharing.lean`), interprets the
  denotational semantics. Its counters are end segments of the input, and
  every comparison of counters is itself a recursion over the input.
- The compiled machine's proven step bound,
  `Geb.SizeBounded.Logspace.Machine.time`, is computable and can be
  evaluated. It bounds the machine that
  `Machine.computableInTimeAndSpace_sem` builds.

None of the three is the machine's actual step count. Simulating the machine
is impractical as the configuration stands: `Turing.MultiTapeTM.Cfg` holds
each work tape as a function from the integers, so a few thousand steps
build a chain of closures that is quadratic to read back. A two-bit input on
the tail expression did not finish in ten minutes. Measuring the real
machine needs a simulator over array or map tapes with a proof that it
agrees with the step function.

## Measurements

All timings are from the Lean interpreter under `lake env lean` on one
machine, so only the ratios carry information. The slope is the log-log
slope between the two largest lengths measured.

Evaluator with sharing, on arbitrary words of the stated bit length:

| expression | bit lengths | times | slope |
| --- | --- | --- | --- |
| `dropBy` | 200, 400, 800, 1600 | 18, 47, 179, 681 ms | 1.9 |
| `dbl` | 25, 50, 100, 200 | 10, 41, 195, 1182 ms | 2.6 |
| `NumExpr.numOk` | 10, 20, 40, 80 | 109, 303, 1290, 6445 ms | 2.3 |
| `NumArith.natEq` | 6, 9, 12, 18 | 112, 280, 638, 2090 ms | 2.9 |
| `NumArith.natValue` | 6, 9, 12, 18 | 55, 156, 328, 1033 ms | 2.8 |
| `EliasTree.isEliasTree` | 20, 40, 80, 160 | 366, 1412, 6454, 38509 ms | 2.6 |

The recognizer on accepted spellings, which is the case where nothing
short-circuits. The spellings are of `const 0 w` leaves with `w` of growing
length:

| bit length | time |
| --- | --- |
| 10 | 37.1 s |
| 11 | 58.8 s |
| 12 | 99.9 s |
| 16 | 234.3 s |

Over that range the slope reads between 3.9 and 6.1. The range of lengths is
a factor of 1.6, so the estimate is crude.

The specification, for contrast:

| function | input | time |
| --- | --- | --- |
| `Elias.Scanner.validBool` | 10000 bits | 1 ms |
| `sigCoded.recognize` | 154-bit spelling | 1 ms |
| `sigCoded.recognize` | 298-bit spelling | 4 ms |

The compiled machine's proven step bound:

| expression | bit lengths | bound | slope |
| --- | --- | --- | --- |
| `dropBy` | 10, 20, 40, 80 | 5.4e4, 3.1e5, 2.1e6, 1.6e7 | 2.9 |
| `dbl` | 10, 20, 40, 80 | 7.7e6, 8.3e7, 1.1e9, 1.6e10 | 3.9 |
| `isEliasTree` | 10, 20, 40, 80 | 1.1e14, 1.5e15, 3.1e16, 7.9e17 | 4.7 |

`time sigRecognizer n` did not finish within fifteen minutes at any length,
which is itself a datum about the size of the compiled expression.

### Reproducing them

Write a scratch file outside the repository and run it with
`lake env lean`. The shape that worked:

```lean
import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree
import Geb.Prototypes.Computability.SizeBounded.Sharing
open Geb.SizeBounded.Logspace Geb.SizeBounded.Logspace.WTree

def word (n : ℕ) : List Bool := (List.range n).map fun i ↦ decide (i % 3 = 0)

def bench (label : String) (n : ℕ) (f : Unit → List Bool) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  let k := r.length
  let t1 ← IO.monoMsNow
  IO.println s!"{label} n={n} len={k} {t1 - t0} ms"

#eval bench "isEliasTree" 40 fun _ ↦ EliasTree.isEliasTree.1.semVec ![word 40]
```

Force the result before reading the clock, as `bench` does with `r.length`.
A timing taken around `pure (...)` measures nothing, because the value is
not demanded.

For the machine's bound, `Geb.SizeBounded.Logspace.Machine.time e n`
evaluates directly. For accepted spellings, build raw trees with `WType.mk`
and spell them with `Sig.sigCoded.spell`.

## The floor

The language embeds distant equality by a projection. A substitution node
whose label codes arity `N`, with a large head subtree and one argument
whose label codes output arity `M`, lies in the language exactly when
`N = M`, and the bits of `N` and `M` occupy fixed positions of a word of
proportional length. Distant equality carries a time-space product lower
bound of order `n²` on offline Turing machines, which is the model
`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength` uses: a read-only
two-way input head with work tapes counted for space. At logarithmic space
that forces time of order `n² / log n`.

The bound is attributed to Cobham's 1966 paper on perfect squares and
palindromes. It was not verified against a primary source, and the theorem
search tooling available did not carry it. Verify it before repeating the
claim in a permanent document, per `AGENTS.md` § Verify agent claims. The
supporting evidence short of that: the matching upper bound holds at both
ends, since storing `S` bits of one side and re-scanning gives time of order
`n² / S`.

So the quadratic re-scanning the specification performs is near-optimal, and
the target for the expression is a degree near the specification's, not
linear time. Under the evaluator the target is one power higher again: a
bare recursion over the word already measures a slope near 1.9 there, so an
expression whose algorithm is quadratic cannot measure better than about 3
until the evaluator question below is settled.

## Where the present expression spends its time

Two causes, independent of each other.

The first is the numeral arithmetic. `BitFold.bitFold` folds over bit
indices, and its step reads one bit of each numeral by `NumExpr.numHit`,
which runs a whole numeral scan from the numeral's position. So a comparison
of two numerals is a scan inside a fold, one nesting level deeper than it
needs to be. `NumArith.natEq`, `natLt`, `natValue` and `NumSum.natSum` all
have this shape.

`NumArith.updValue` compounds it: it doubles the power register at every
level of the fold, by `dblApp`, rather than only at the levels inside the
numeral's payload. The doubling is itself a recursion, so the count of
doublings should be the field's length and is instead the word's.

The second is the evaluator. A bare recursion over the word, `dropBy`, whose
step is a tail, measures a slope of 1.9 where the algebra prescribes one
step per level. Whether `Sharing.lean` costs more than a constant per level,
and if so why, was not determined. If it does, every expression loses a
power to the evaluator alone, and fixing it would improve every measurement
above without touching any expression.

## The expression to write

Replace index-based bit access with lockstep suffix pointers. A recursion
over the word can hold one register per numeral, each the word dropped by
that numeral's position plus the level, advanced by a tail at every step.
Reading the current bit of each numeral is then a dispatch on a register's
head, not a scan. The node and child scans in `NodeExpr.lean` and
`ChildExpr.lean` already work this way and are the model to follow.

- Equality. The code is canonical and injective, `Numeral.natCode_injective`,
  so two numbers are equal exactly when their codes agree as strings. Run
  both numeral scanners in lockstep, require both to accept, require the
  same end offset, and require every bit to agree. One pass.
- Order. The payload bits arrive least significant first, so the running
  verdict rule the present `NumArith.ltBits` uses carries over unchanged:
  at each index, when the bits differ, the verdict becomes the second
  number's bit. Sizes differing decides the comparison outright, and both
  scanners already hold the size in a register, so that case is a comparison
  of two counters rather than of bits.
- Bits past the end. The index-based reading pads with `false` beyond a
  numeral's payload, by `List.getD`. A lockstep scan must do the same
  explicitly: once one scanner reaches its end position its bit stream
  contributes zeros while the other continues. The order and the sum both
  depend on that padding, so state it once and reuse it.
- The sum. Ripple carry runs from the least significant bit upward, which is
  the order the lockstep scan delivers. The invariant in `NumSum.sum_inv`,
  which relates the registers to the remainders modulo powers of two, should
  carry over with the index replaced by the lockstep step count.
- Reading a numeral into a counter. Keep the doubling, but make it
  conditional on being inside the payload, so the number of doublings is the
  field's length rather than the word's. The conditional must be one the
  evaluator can short-circuit, which `cond4L` is.

The correctness statement should follow `NumScanExpr.regsNS_eq`: an
invariant giving each register's value after a prefix of the word in terms
of the two or three numerals' remaining codes, proved by the recursor over
the prefix, with the end-to-end statements derived from it as
`NumExpr.num_natCode` and `num_of_ok` are.

Keep `Numeral.lean`, `NumScan.lean` and `NumScanExpr.lean`: the scanner and
its soundness and completeness are what the lockstep version builds on.
Keep the generic recognizer and the shape of `Sig.lean`, `SigLabel.lean` and
`SigEdge.lean`; only the four numeral operations change, and their
statements, `natEq_natCode` and its siblings, should keep their present
signatures so the callers do not move.

## What to measure, and what to expect

Measure before and after, at the same lengths, with the harness above.

- `natEq` at 6, 9, 12 and 18 bits. It is 112 to 2090 ms now with a slope
  near 2.9. One pass should put the slope near the bare recursion's, which
  is 1.9 today, and the absolute times below the `numOk` line, since the
  work per level becomes a dispatch rather than a scan.
- `natValue` at the same lengths. It is 55 to 1033 ms now with a slope near
  2.8. Making the doubling conditional should show there on its own, before
  the lockstep rewrite lands, so run that change first and measure it
  separately.
- `sigRecognizer` on accepted spellings at 10, 11, 12 and 16 bits. It is
  37 to 234 s now. Removing one nesting level from the numeral operations
  should remove about one power. Whether the second power follows depends on
  the evaluator question above.
- The machine's bound for `dropBy`, `dbl` and `isEliasTree`, unchanged by
  this work, as a control that the compiler's cost model has not shifted.

Treat a slope estimate over a length range narrower than a factor of four as
indicative only. The recognizer's accepted spellings are sparse at small
lengths, so consider generating longer accepted words, for instance nests of
substitutions, and accept that each measurement will take minutes.

## Risks

- The lockstep scan needs both numerals' scanners running in one recursion,
  so the register count grows. `ChildExpr.lean` already carries twelve
  registers and four parameters and its step lemmas are proved one mode at a
  time; the same method applies, but the case analysis grows with the
  product of the two scanners' modes. Consider proving the two scanners'
  steps separately and combining them, rather than casing on pairs.
- The saturating counter in `NumScan.lean` saturates at the word's length.
  Two numerals compared in lockstep may both saturate, in which case
  equality of the saturated values is not equality of the numbers. The
  present proofs avoid this by bounding the numbers through
  `NumBits.lt_two_pow_of_size_le`; check that the lockstep version keeps a
  comparable bound.
- Short-circuiting through `cond4L` makes timings depend on whether the
  input is accepted. Measure accepted inputs when comparing.

## Order of work

1. Settle the evaluator question first, since it is cheap and it changes how
   to read every other measurement. Instrument or reason about
   `Sharing.lean` to find whether a recursion costs more than a constant per
   level, and record the answer here.
2. Make the doubling in `natValue` conditional, which touches one register
   step, and measure it on its own before anything else moves.
3. Write the lockstep numeral scanner and prove it against `NumScan.lean`.
4. Rebuild `natEq`, `natLt` and `natSum` on it, keeping their statements, so
   that `SigLabel.lean` and `SigEdge.lean` need no change.
5. Rebuild `natValue` on it as well, now that its doubling count is already
   bounded by the field.
6. Measure, and record the before and after in this document.
7. Remove this document in the branch's final commits, moving whatever
   proves permanent into the module docstrings and `docs/index.md`.
