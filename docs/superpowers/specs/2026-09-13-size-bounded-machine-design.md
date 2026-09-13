# Machine bounds for the non-size-increasing algebra

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Target statement](#target-statement)
- [Relation to the paper](#relation-to-the-paper)
- [What the libraries provide](#what-the-libraries-provide)
- [Design](#design)
  - [Registers](#registers)
  - [The program contract](#the-program-contract)
  - [Primitives](#primitives)
  - [Combinators](#combinators)
  - [Compilation](#compilation)
  - [Bounds](#bounds)
  - [Wrapper](#wrapper)
  - [Modules](#modules)
  - [Tests](#tests)
- [Plan decomposition](#plan-decomposition)
- [Fallback](#fallback)
- [Out of scope](#out-of-scope)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

A compilation of every expression of `Geb.SizeBounded.S`, the bitstring
form of the algebra `S(sbs₀, sbs₁)` of [Mazzanti2016], into a multi-tape
Turing machine of `Cslib` (`Turing.MultiTapeTM`), with a proof that the
machine computes the expression's meaning within a polynomial number of
steps and a linear number of visited cells. The result is the soundness
half of the paper's Theorem 5.7, `S ⊆ FPTIMELINSPACE ∩ NSI`, the
non-size-increase half being `Geb.SizeBounded.nsi_eval` already.

This document is a transient process artifact in the sense of
`CONTRIBUTING.md` § Concern shape: remove it in the final commits of the
branch. What is permanent is in the module docstrings and in `docs/index.md`.

## Target statement

For every `e : SOf 1` there are `c` and `d` with

```lean
Turing.MultiTapeTM.ComputableInTimeAndSpace (fun w ↦ e.sem ![w])
  (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (n + 1))
```

The time bound is stated in the `IsPolyBounded` form of
`SizeBounded/Cost.lean`, `t m ≤ c * (m + 1) ^ d`. Mathlib's `Polynomial`
is not used: it lives in a `noncomputable section`, and a statement
mentioning `Polynomial.eval` depends on `Classical.choice`.

The statement is unary. Recognizers are unary, so it covers every use the
algebra is written for. Expressions of higher arity are compiled and
bounded internally, since substitution and recursion need them, but receive
no machine-level statement of their own; an n-ary statement would need an
encoding of tuples on the input tape that the paper never chooses.

## Relation to the paper

The paper proves Theorem 5.7 as the conjunction of three results: Theorem
5.3, `S ⊆ clos(C₀, s₀, s₁, max, quad; SUBST, BRN)`, by a block encoding of
simultaneous recursion into one bounded recursion; Theorem 5.6, the
converse for non-size-increasing functions; and Theorem 5.2, the identity
of that closure with `FPTIMELINSPACE`, cited from [Clote1999] Theorem 3.45
and not proved. The soundness half is Theorem 5.3 composed with the
machine-simulation half of Theorem 5.2.

This design proves the soundness half directly: the compiler is a
structural fold over `S` itself, and the simultaneous recursion is
implemented as a machine loop rather than encoded into a single bounded
recursion. That is one compile-an-algebra-to-machines proof for the
algebra at hand, instead of the block-encoding proof plus a compiler for
the larger Cobham-style algebra of Theorem 5.2. Every ingredient of the
paper's Section 2 accounting, Lemma 2.1 and Lemma 2.2, is already in
`SizeBounded/Basic.lean` and `SizeBounded/Cost.lean` and is reused as the
source of the length and time bounds.

The fallback, if the direct route is found not to scale, is the paper's
route: the Theorem 5.3 encoding into `Cobham.SmashFree` followed by a
compiler for that algebra. The trigger for the fallback is stated in
§ Fallback.

## What the libraries provide

- `Turing.MultiTapeTM k Symbol State`: a read-only input tape whose head
  is clamped to the input, `k` bi-infinite work tapes over `Option Symbol`
  with `none` the blank, an output stream to which a transition may
  append one symbol, and halting by a transition whose successor state is
  `none`. `step` applies the write at each head's current cell, then the
  move. `initCfg` places every work head at cell `0` on blank tapes.
- `ComputesInTimeAndSpace tm input output t s`: halted at step `t`, output
  string equal to `output`, `spaceUsed` at step `t` equal to `s`, where
  `spaceUsed` is the sum over tapes of the cardinality of the set of cells
  the head has visited. `ComputesFunInTimeAndSpace` asks, per input, for
  some `t' ≤ t n` and `s' ≤ s n` with that property.
  `ComputableInTimeAndSpace` existentially quantifies a machine over
  `Fin sym` symbols and `Fin state` states and an embedding of the
  input/output alphabet.
- No composition lemma exists for the multi-tape model. The single-tape
  model's `compComputer` and `TimeComputable.comp` show the proof pattern
  for sequencing, states as a `Sum` and a halting transition redirected
  into the second machine's initial state; they are single-tape and
  without a space measure, and the `PolyTimeComputable` layer above them
  is `noncomputable` through mathlib's `Polynomial`.
- `spaceUsed` depends on `Classical.choice` through `Finset.image`, and
  `Cfg.inputSymbol` through `grind`, so every module stating a bound on a
  machine is listed in `GebMeta.classicalAllowedModules`, as the existing
  `Bound` modules are.

## Design

### Registers

All values live on work tapes. A register `i` holds the word `w` when
cells `0` to `|w| - 1` hold `w` in reverse, cell `0` the list's last
element and cell `|w| - 1` its head, and every other cell is blank. In this
layout `cons` is one write at the first blank cell, `List.rec`'s order of
recursion is a walk from cell `0` rightwards, and a head returns to cell
`0` without a marker symbol: every phase that walks right ends on the
transition that reads the terminating blank, and that transition moves
left; thereafter the head moves left while the cell read is non-blank,
and the transition that reads a blank, at cell `-1`, moves right and ends
the return. For an empty register the terminating blank is cell `0`
itself and the return is the same two transitions. No head ever moves
right from a blank cell, so a register holding a word of length at most
`B` is visited only within `[-1, B]`. The symbol type is `Bool`
throughout; transport to `Fin 2` happens once, in the wrapper.

### The program contract

A program is a `MultiTapeTM k Bool State` with a specification of the
following form, a predicate on the machine, an environment `Fin n → Fin k`
of argument registers, an output register `out`, a set of scratch
registers, a function `f`, a step bound `T` and a length bound `B`. The
environment is injective, `out` is outside its range, and the scratch
registers are disjoint from both; these side conditions are hypotheses of
the predicate, since a lockstep walk of two heads on one tape is a
different machine.

- Start: state `q₀`, every head at cell `0`, every register holding some
  word of length at most `B`, the environment registers holding the
  arguments, the input head anywhere.
- Halt: within `T` steps the state is `none`, every head is at cell `0`,
  every register holds some word of length at most `B`, `out` holds `f` of
  the arguments, every register outside `out` and the scratch registers
  holds what it held at the start, the input head has not moved, and
  nothing has been output.
- Path: at every step up to the halting step, every head position lies in
  `[-1, B]`.

The requirement that every register hold a well-formed word at start and
at halt is what lets one program's scratch be the next program's output
register: `const` and `copy` blank the cells beyond the written word until
they read a blank, which terminates within `B` cells only because the
previous content was a word. The halt clause is stated at the
configuration after the halting transition, since a redirected halting
transition still applies its writes and moves; the transition that ends
each primitive's return is therefore its halting transition. The path
clause is what yields the space bound: the visited set of each tape is a
subset of `Finset.Icc (-1) B`, so `spaceUsedByTape ≤ B + 2` by
cardinality and `spaceUsed ≤ k * (B + 2)`. No composition lemma for
`spaceUsed` itself is needed. The input-head and no-output clauses hold
by construction, every inner transition having `inputMove = 0` and
`outS = none`.

### Primitives

Three hand-written machines, each proved against the contract by a
closed-form configuration family as the existing scanners are, each of a
few phases:

- `const w out`: write `w` into `out` from cell `0`, blank the cells beyond
  until a blank is read, return. Time linear in `|w|` plus the previous
  length of `out`.
- `copy i out`: walk `i` and `out` in lockstep copying until `i` reads
  blank, blank `out` beyond until it reads blank, return both. Time linear
  in `|i|` plus the previous length of `out`.
- `sbs b x y out`: walk `x` and `y` in lockstep until either reads blank,
  recording in the state whether `y` was still non-blank when `x` became
  blank, which is `|x| + 1 ≤ |y|`; return both; copy `x` into `out` as
  `copy` does; if the record allows, write `b` at `out`'s first blank cell
  before returning. Time linear in `|x| + |y|` plus the previous length of
  `out`.

The comparison and the copy may be separate machines joined by `seq` with
the record passed through a scratch register, or one machine; the choice
is made at implementation, whichever gives the shorter proof.

### Combinators

- `seq P Q`: states `SP ⊕ SQ`; in an `inl` state the transition is `P`'s,
  with a successor `none` replaced by `some (inr Q.q₀)`; in an `inr` state
  it is `Q`'s. Its two lifting lemmas are stated on configurations, not on
  the contract: a step of `seq P Q` from a lifted `P` configuration is the
  lift of `P`'s step, with the halting case lifted to `Q`'s start, and
  likewise for `Q`. The contract-level corollary, that `seq` of two
  programs meeting the contract meets it with the time bounds added, the
  path intervals joined and the frame clauses composed, is a separate
  lemma; the wrapper's reader and writer, which move the input head and
  emit output, use the configuration-level lemmas directly.
- `seqFin`: sequencing of a `Fin m`-indexed family of programs, a
  `Nat.rec` on `m` through `seq`, so that the state is an iterated binary
  sum. This is what `comp`'s children, the loop's step programs and the
  loop's copies are sequenced by; no `Sigma`-typed state arises.
- `loop`: the simultaneous recursion with `b` components over registers
  `X` (the recursion argument, read only), `V` (the processed suffix), `b`
  value registers and `b` scratch registers. It begins with `const [] V`,
  since an enclosing loop may run it more than once. One iteration walks
  `X` and `V` in lockstep until `V` reads blank, at which point `X`'s head
  is at cell `|V|`; if `X` reads blank, return and halt; otherwise return
  both heads, run the `b` step programs for the bit read into the scratch
  registers, copy each scratch register into its value register, and
  write the bit at `V`'s first blank cell. The state is the sum of the
  control states and the states of the step programs and copies, with
  each sub-program's halting transition redirected to the next phase.
  Proved by `List.rec` on the recursion word against the `evalSRN`
  equations: after `j` iterations `V` holds the last `j` bits and the
  value registers hold `evalSRN` at that suffix.

The reading order is that of `List.rec`: the list's last element is
processed first and its head last, and in the reversed layout that is a
left-to-right walk over `X`.

### Compilation

`compile` is a `SlicePFunctor.W.elim` fold over `S`, as `eval` and `evalC`
are, at a tape count `k` fixed for the whole fold. Its carrier at arity
`n` is a pair of a register count `regs` and a function of an environment
`Fin n → Fin k`, an output register, a first free register `free : ℕ` and
a proof `free + regs ≤ k`, returning a state type with a `FinEnum`
instance and a machine over `Fin k` tapes; the proof is what lets a fresh
register `free + i` be a `Fin k`, and the fold's step threads it to the
children. `regs` is zero for the base forms, `m` plus the maximum over the
children for `comp n m`, and `2 b + 1` plus the maximum over the children
for `srn a b j`; the maximum is taken because siblings run in sequence and
may share scratch. For a top-level `e : SOf 1`, `k = 2 + regs e`: the
input register, the top-level output register, and the scratch. No tape
reindexing is ever needed: every program of one top-level expression lives
over the same `Fin k`. `FinEnum` instances are the choice-free scoped ones
of `Geb/Mathlib/Data/FinEnum.lean`, `FinEnum.unit`, `FinEnum.finFin` and
`FinEnum.finSum`, under `open scoped FinEnum`; mathlib's `FinEnum.sum` is
derived through `FinEnum.ofList` and depends on `Classical.choice`.

- `const n w` compiles to `const w out`; `proj n i` to `copy (env i) out`;
  `sbs b` to `sbs b (env 0) (env 1) out`.
- `comp n m` allocates `m` fresh registers `r₀, .., r_{m-1}`, compiles each
  child `g_i` with the node's environment into `r_i`, and the head `h`
  with environment `r` into `out`, and sequences them.
- `srn a b j` allocates `V`, the value registers and the scratch registers,
  compiles the base children with the parameter environment `Fin.tail env`
  into the value registers, the step children with environment
  `Fin.cons V (Fin.append vals (Fin.tail env))` into the scratch
  registers, the arity `b + a + 1` form `evalSRN` takes, builds the loop
  over `X = env 0`, and copies value register `j` into `out`.

Correctness and the bounds are proved afterwards by
`SlicePFunctor.W.induction`, each subtree's contract instance obtained
from its children's. The induction motive carries the allocation
invariant: every register of the environment and `out` is below `free`,
the environment is injective, and `out` is outside its range, which is
what the primitives' side conditions and the frame clause need.
Intermediate lengths are bounded through `nsi_sem` on the subtrees with
the top-level constant, `nsiConst` being monotone from child to parent by
its definition as a maximum; the register contents at every point are
values of subexpressions on arguments of length at most `B = max m K`,
hence of length at most `B`.

### Bounds

The step bound is a second fold, `stepData`, distinct from `Cost.lean`'s
`costData` and `timeValue` but patterned on them: a pair of the
non-size-increase constant and a function `ℕ → ℕ` of the argument length
bound, the recursion's function reading its steps' functions at
`max m K`. It is proved `IsPolyBounded` by the closure lemmas of
`SizeBounded/Cost.lean`. The machine's step count is not made to match the
evaluator's account; it is bounded on its own, by the same induction that
proves correctness, since the loop's iteration count is the recursion
word's length and each phase's time is linear in lengths bounded by `B`.

The space bound is `k * (B + 2)` with `B = max m K`, which is at most
`c * (m + 1)` for `c = k * (K + 2)`.

### Wrapper

The top-level machine for `e : SOf 1` is the sequence of

1. an input reader: move the input head to the right end, then walk left
   writing each symbol read at register `0`'s first blank cell, which
   produces the reversed layout; return;
2. the compiled program with environment `![0]` and a fresh output
   register;
3. an output writer: walk the output register to its first blank cell,
   then walk left emitting each bit read through `outS`, halting on the
   blank at cell `-1`.

The reader and writer are the only machines that move the input head or
emit output; each has its own closed-form proof. The composite is
transported along `FinEnum.equiv` on states and `Bool ≃ Fin 2` on symbols
by one machine-transport lemma. Since `Cfg` is indexed by the input list,
the lemma relates `configs` from `initCfg input` over `Bool` to `configs`
from `initCfg (input.map e)` over `Fin 2`, the input position cast along
the equality of lengths, and `outputString` accordingly; the embedding
`Bool ↪ Fin 2` is the one supplied to `ComputableInTimeAndSpace`.
`Fintype.equivFin` is not used, being `noncomputable`.

The target statement is existential in `c` and `d`, as `time_le_poly` is;
`Bound.lean` also names the bound functions the fold produces, so that
the test module can run the machine for a computed number of steps.

### Modules

Under `Geb/Prototypes/Computability/SizeBounded/Machine/`, each a
literate module:

- `Register.lean`: the layout predicate and its lemmas, on tape contents
  alone.
- `Program.lean`: the contract predicate; monotonicity in `T` and `B`; the
  absorbing-halt lemmas; the bound `spaceUsedByTape ≤ B + 2` from a path
  clause, which mentions `spaceUsedByTape` and so lives here rather than
  in `Register.lean`.
- `Seq.lean`: sequencing, `seqFin`, and their lifting lemmas.
- `Const.lean`, `Copy.lean`, `Sbs.lean`: the primitives.
- `Loop.lean`: the recursion loop.
- `Compile.lean`: `regs`, the state-type and machine fold, correctness by
  induction.
- `Bound.lean`: the step-bound fold, `IsPolyBounded`, the space bound.
- `Wrapper.lean`: reader, writer, transport, and the target statement.

`GebMeta.classicalAllowedModules` lists those that state a fact about
`step`, `configs`, `outputString`, `spaceUsedByTape` or `spaceUsed`, and
the test module below; `Register.lean` and the folds of `Compile.lean` and
`Bound.lean` are expected to stay strict, the proofs about them being
split into allowlisted modules where a measurement shows the need. The
`SizeBounded.lean` index imports the `Machine` index. `docs/index.md` gains
the machine bound beside the algebra's entry, and `TODO.md`'s entry for the
machine bound is removed.

### Tests

`GebTests/Prototypes/Computability/SizeBounded/Machine.lean` `#guard`s the
compiled machine of `isBitTree`, run by `configs` for its bound's number of
steps on a few words, against `validBool`, so that the compiler is executed
and not only proved. It names a `def` value built from the module under
test, as the other test mirrors do for `lake shake`, and carries a
`public meta import` of the module under test beside the ordinary import,
as `docs/rules/lean-coding.md` § Lean 4 module system requires of a
cross-module `#guard`.

## Plan decomposition

Three implementation plans, in order:

1. `Register`, `Program`, `Seq` with `seqFin`, the three primitives, and
   `Loop`. Its exit criterion is the fallback trigger below: the loop's
   proof either goes through from the primitives' contracts and the
   lifting lemmas, or it does not.
2. `Compile`: `regs`, the fold, and correctness by induction with the
   allocation invariant.
3. `Bound`, `Wrapper`, the transport, the tests, and the documentation
   changes.

## Fallback

The route is abandoned for the paper's if the combinator proofs turn out
to require a closed-form configuration family per expression rather than
per primitive, which is the one outcome under which the direct compiler
does not scale. Difficulty in any single primitive's proof is not a
trigger; the existing scanner proofs show those close.

## Out of scope

- Completeness, `FPTIMELINSPACE ∩ NSI ⊆ S`: rests on the
  machine-to-recursion half of [Clote1999] Theorem 3.45 and on the paper's
  Lemma 5.5, which cites Mazzanti's earlier regressive-machine results. To
  be assessed after soundness.
- An n-ary statement with an input encoding.
- Matching the machine's step count to `Cost.lean`'s account.

## References

- [Mazzanti2016], Sections 2 and 5: Theorems 5.1 to 5.3, Lemma 5.5,
  Theorems 5.6 and 5.7 and Corollary 5.8 as numbered in the published
  text, Theorem 5.2 citing [Clote1999] Theorem 3.45.
- `Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`,
  `TapeLemmas.lean`; `SingleTape/Deterministic.lean` for the sequencing
  pattern.
- `Geb/Prototypes/Computability/BitTree/Bound.lean` and
  `TreeScanner/Bound.lean` for the existing machine-bound modules.
