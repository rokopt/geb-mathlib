# Reducing the W-tree recognizer's cost — measurements and handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Three cost models, kept apart](#three-cost-models-kept-apart)
- [Measurements before](#measurements-before)
  - [Reproducing them](#reproducing-them)
- [The floor](#the-floor)
- [Where the cost was, and the evaluator](#where-the-cost-was-and-the-evaluator)
- [The expression written](#the-expression-written)
- [Measurements after](#measurements-after)
- [What remains](#what-remains)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

The recognizer of the spellings of the size-bounded algebra's expressions,
`Geb.SizeBounded.Logspace.WTree.SigCheck.sigRecognizer`, is correct and
carries its machine bound, but evaluating it is slow enough that the tests
exercise it on one ten-bit word. This document recorded what the cost was,
where it came from, what the floor is, and how to rewrite the numeral
arithmetic to approach that floor; it now records what the rewrite
measured. It covers
`Geb/Prototypes/Computability/SizeBounded/Logspace/WTree/`, chiefly
`BitFold.lean`, `NumArith.lean` and `NumSum.lean`.

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

## Measurements before

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
bare recursion over the word already measures a slope near 1.9 there, since
the tail is a recursion over its argument, so an expression whose algorithm
is quadratic cannot measure better than about 3.

## Where the cost was, and the evaluator

Two causes were proposed, independent of each other.

The first was the numeral arithmetic. `BitFold.bitFold` folded over bit
indices and its step read one bit of each numeral by `NumExpr.numHit`, a
whole numeral scan from the numeral's position, so a comparison of two
numerals was a scan inside a fold.

The second was the evaluator, and it is measured and dismissed. A recursion
over the word whose step reads a register, with no tail, measures a log-log
slope of 1.00 over a sixteenfold range of lengths, 500 to 8000 bits and 21 to
335 ms; the same recursion with a tail as its step measures 1.7 to 1.8 over an
eightfold range. `Sharing.lean` costs a constant per level. The extra power
`dropBy` shows is `Geb.SizeBounded.tailOf` being itself a recursion over its
argument, which `Sharing.lean`'s docstring and `TODO.md` § The degree of
evaluation already record. No power is available there.

## The expression written

`BitFold.bitFold` gives each numeral two registers, a pointer at the bit it
has reached and a mask, an end segment as long as the run of bits to read.
Reading a bit is a dispatch on the pointer's head and the test of the run's
end a dispatch on the mask's emptiness; both registers advance by a tail at
every level. The bases are a parameter of the fold, so it serves two readings:
`codeScan` reads a numeral's code from its position, which the code's
injectivity makes sufficient for equality and which the scanner's end position
alone delimits, and `payScan` reads the payload, which the order, the sum and
the reading into a counter need aligned by index, from the gamma code's zero
run and the size field's value.

`natEq_natCode` and its siblings keep their statements, so `SigLabel.lean` and
`SigEdge.lean` are untouched.

Making the doubling in `natValue` conditional, which the plan below put first,
measured nothing, on its own (51, 139, 341 and 978 ms against a baseline of
55, 156, 328 and 1033) or on top of the rewrite (68, 142, 220 and 502 with the
conditional against 71, 128, 223 and 520 without). The evaluator forces the
power register only through the value register's chain, so the count of
doublings performed is already the numeral's rather than the word's. The
conditional is not in the branch.

## Measurements after

The numeral operations, at the lengths of the table above:

| expression | 6 bits | 9 bits | 12 bits | 18 bits | slope |
| --- | --- | --- | --- | --- | --- |
| `natEq` before | 102 | 295 | 680 | 2109 ms | 2.8 |
| `natEq` after | 31 | 51 | 92 | 181 ms | 1.7 |
| `natValue` before | 55 | 156 | 328 | 1033 ms | 3.0 |
| `natValue` after | 87 | 151 | 257 | 550 ms | 2.0 |

The recognizer on accepted spellings, the two expressions measured one after
the other on the same machine under the same load:

| bit length | before | after | ratio |
| --- | --- | --- | --- |
| 10 | 29.6 s | 55.0 s | 1.86 |
| 11 | 49.2 s | 87.1 s | 1.77 |

So the rewrite removes about a power from each numeral operation taken alone
and costs the recognizer a factor near two, with no crossover in the range
that can be measured. The recognizer's degree is unchanged by it, which
falsifies the expectation above that removing a nesting level from the numeral
operations would remove about one power from the recognizer: the recognizer's
degree is not set by that nesting.

The direction of the discrepancy is where the two cost models part. The old
expression paid one numeral scan per bit index actually reached, and the
evaluator reaches few: a comparison whose numerals differ at the first bit
short-circuits through `andOkAt` after one index. The new expression pays for
its bases — one scan per position for a code, three for a payload, since
`payPtr` names the zero run twice — as soon as any bit is read, and advances
six registers by a tail per level rather than one. The recognizer evaluates
its label and edge checks at every level of its own recursion over the word,
most of them on words that are not labels, so most of its numeral operations
reject at the first index, which is the case the old expression is fastest at
and the new one slowest.

`natValue` shows the same crossover directly: slower than before at 6 bits and
faster at 18. The recognizer's spellings are 10 to 16 bits, below it.

## What remains

- Whether to keep the rewrite is a judgement the measurements above do not
  settle by themselves: it is the faster expression for long words and the
  slower one for the words the tests use.
- The bases can be cheaper. `payPtr` evaluates `zSeg` twice, so a payload
  position costs three runs of the scanner where two would do; doubling the
  zero run by `Geb.SizeBounded.Logspace.dblApp` instead would name it once.
- `NumExpr.numHit`, the scanner's bit-at-an-index register and the index
  parameter it reads are now unused. Removing them, and the index parameter of
  `Numeral.nrun`, would take a comparison of counters out of every level of
  the scanner's step and shrink the compiled expression.
- The scanner is what every numeral operation now rests on, and its tests of
  the position, of the size field's end and of the bits' end are three
  `eqSeg`, each a `dropByApp` and so a recursion whose step is a tail. A
  counter register that the step exhausts, as this fold's mask is, would
  replace each by a dispatch and take a power off every run of the scanner.
