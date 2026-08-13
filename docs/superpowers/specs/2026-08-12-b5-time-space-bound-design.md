# B5, the time and space bound — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [The statement](#the-statement)
- [Transcription or novel](#transcription-or-novel)
- [Facts established by building](#facts-established-by-building)
- [The machine](#the-machine)
- [Why the count is the head position](#why-the-count-is-the-head-position)
- [Why the work tape carries two markers](#why-the-work-tape-carries-two-markers)
- [Uniform per-symbol cost](#uniform-per-symbol-cost)
- [The proof architecture](#the-proof-architecture)
- [The invariant](#the-invariant)
- [The time bound](#the-time-bound)
- [The space bound](#the-space-bound)
- [Correctness](#correctness)
- [Constructive posture](#constructive-posture)
- [The rules file and its rationale](#the-rules-file-and-its-rationale)
- [Artifacts](#artifacts)
- [Verification](#verification)
- [Risks](#risks)
- [Size](#size)
- [References](#references)
- [Staged reduction of scope](#staged-reduction-of-scope)
- [Out of scope](#out-of-scope)
- [Deferred](#deferred)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This is the specification for B5, the last segment of the ranked-tree
recognizer workstream. The workstream's other segments are recorded in
[TODO.md](../../../TODO.md) § Extensions of the tree recognizers; the
session handoff is
[docs/superpowers/plans/2026-08-12-b5-time-space-bound-handoff.md](../plans/2026-08-12-b5-time-space-bound-handoff.md).
Both this document and that one are transient and are removed in the final
commits of the branch, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape, which also
fixes the branch's commit order: the spec and plan first, the
implementation and its documentation next, their removal last. The plan
sequences the tasks within that order.

## Scope

A concrete deterministic multi-tape Turing machine deciding
`RankedAlphabet.Binary.binRanked.validBool`, together with proofs that it
runs in time and space affine in the input length.

The time bound is sharper than the polynomial-time membership that
`Cobham.isTree_smashFree` gives through [Strahm2003] Theorem 1(2). The
space bound is not sharper: that result already gives linear space, and
the bound obtained here is also linear. Nothing formal connects the two
statements, the Cobham side being a `SmashFree` membership that is cited
rather than reproved, so the comparison is motivation and not a claim any
docstring may make.

The return against
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost is a
`ComputableInTimeAndSpace` theorem about a decision function the
repository already defines, and the idioms for constructing a
`MultiTapeTM` at all: no term of that type is constructed anywhere under
`.lake/packages/`, where the type occurs only in its own declaration, in
`def`s over it, and in lemma binders.

## The statement

`Geb/Mathlib/` may not import `Cslib.*` and `Geb/Cslib/` may not import
`Geb.Mathlib.*`, per
[docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md)
§ Subtree import rules. The statement needs both, so it is confined to
`Geb/Internal/`.

```lean
namespace Geb.TreeScanner

open Turing MultiTapeTM

theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace
      (fun w : List Bool ↦ [RankedAlphabet.Binary.binRanked.validBool w])
      (fun n ↦ 2 * n + 3) (fun n ↦ 2 * n + 4)
```

`ComputableInTimeAndSpace` is `Turing.MultiTapeTM.ComputableInTimeAndSpace`,
so the `open` is what lets the statement be written unqualified. The name
places the enclosing predicate first, per mathlib's naming guide
(`IsClosed (Icc a b)` gives `isClosed_Icc`, not `Icc_isClosed`), which
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Naming
conventions binds for every `.lean` file here.

The coefficients are those § The machine yields: a seek pass of `n + 1`
steps, one plant step, a sweep of one step per symbol, and one emitting
step, against which `spaceUsed_linear` at one work tape gives `1 * t + 1`.
They are written as literals so that nothing in the specification lacks a
declaration site. The plan re-derives them from the machine, and § Staged
reduction of scope states what happens if a measurement falsifies any
design assumption, coefficients included.

Three properties of the target fix the shape of the statement.

- The function is the computable decision function in one-symbol list
  form, not `DecidableInTimeAndSpace`. `DecidableInTimeAndSpace` is
  `ComputableInTimeAndSpace (indicator L)`, and `indicator` is
  `open Classical in noncomputable def`, whose value is `[default]` or
  `[]` rather than the decision bit. The reason to avoid it is that it
  states a weaker fact about a `Classical` function where the actual
  decision procedure is available, and that
  [docs/rules/lean-coding.md](../../rules/lean-coding.md)
  § Constructive-only directs us to minimise `Classical`. It is not that
  mentioning an upstream `noncomputable` constant is barred; the rule
  bars declaring one, and this statement already mentions the
  `Classical`-dependent `spaceUsed`.
- `ComputableInTimeAndSpace` existentially quantifies the tape count, the
  machine alphabet, the state set, the embedding and the machine. The
  embedding covers the input and output alphabet only; work-tape symbols
  come from the existential machine alphabet.
- The bounds are per input length, and the `≤` lives in
  `ComputesFunInTimeAndSpace`, not in `ComputesInTimeAndSpace`, whose
  space conjunct is an equality.

## Transcription or novel

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing requires each definition to be marked.

- Novel here, none transcribed from a published statement and no source
  followed: the machine, its four named states, the alphabet embedding
  `boolEmb : Bool ↪ Fin 2`, the three named configurations, the invariant
  and the bound.
- The recognition algorithm is standard context rather than a
  transcription: a one-counter pass deciding a prefix-code term language.
  A docstring may state that context, which per the same section is what
  comments cite when what is defined is not itself a transcription. No
  `[Key]` accompanies it, because no particular published machine is
  reproduced.
- The scan the machine mirrors is `RankedAlphabet.scanStep`, already in
  `Geb/Mathlib/` and already carrying whatever citation it warrants.

This branch therefore introduces no new key to `docs/references.bib`.

## Facts established by building

Each fact was measured by a compiled prototype at the toolchain pinned in
`lean-toolchain`, not inferred by reading. The prototype is
`Geb/Internal/TMSpike.lean`; § Artifacts states its treatment. An
adversarial reviewer should treat every item as falsifiable, and items 8,
12 and 13 mark which of their clauses a reader can reproduce from the
committed artifact.

1. **Two prototypes were built**: one halting on its first step with no
   work tapes, and one copying its input to a work tape and to the
   output. The second yields
   `ComputableInTimeAndSpace (fun w ↦ w) (fun n ↦ n + 1) (fun n ↦ n + 2)`
   in about a hundred and fifty lines. That measurement was taken with
   `linter.unusedSimpArgs` disabled in the prototype, so it excludes the
   cost of making every `simp` set precise, which committed code pays.
2. **`Cfg` is indexed by `input`, so no induction on the input is
   available**: the configuration type varies with the list. Proofs run
   by `Nat.rec` against a named closed-form configuration family, which
   is a function of the input and of the step count both.
3. **A step lemma must not let `simp` unfold the configuration family.**
   Doing so replaces the family by a structure literal and invalidates
   any hypothesis stated about its projections. The operative discipline
   is to state the projections as lemmas and cite them. Not every
   projection lemma needs `@[simp]`, and the base case of a
   configuration theorem may unfold the family outright; in the prototype
   the work-tape projection is deliberately not `@[simp]` and the base
   case is closed by unfolding.
4. **`Cfg.ext` needs `dsimp only` after `unfold step`**, since the
   projections of a structure literal do not reduce syntactically.
5. **`spaceUsed_linear : spaceUsed cfg t ≤ k * t + k`** derives an affine
   space bound from an affine time bound, with no computation of
   `visitedByTapeHead`. The copying prototype's space bound is
   `le_trans (spaceUsed_linear _ _) (by simp)`.
6. **The right end of the input is detectable.** `Cfg.inputSymbol` reads
   `none` at position `0` and at `input.length + 1`, and
   `moveInputPos_rightBoundary` makes a right move at the far end a
   no-op, so rightward movement terminates without reference to the
   length.
7. **`initCfg` places the input head at position `1`, the left end**,
   with work tapes blank and their heads at `0`.
8. **`Cfg.inputSymbol`'s two guards elaborate at different types.**
   `cfg.inputPos = 0` is an equality at `Fin (n + 2)`; `cfg.inputPos =
   input.length + 1` is an equality at `ℕ`, the coercion falling on the
   left. Measured, and reproducible: `apply Fin.ext` fails on
   the second with "could not unify the conclusion of `@Fin.ext`". Not
   reproducible, resting on item 12's discarded patch: that patch
   supplied the second guard to `omega` directly while converting the
   first by `Fin.ext`. The committed `inputSymbolCF` is not evidence for
   this fact, restating both guards at `.val` and using no `Fin.ext`.
   Only the second guard was exercised by the prototype; the machine's
   emitting step reads at position `0` and so takes the first.
9. **Under the pinned toolchain `if_pos`, `if_neg`, `dif_pos` and
   `dif_neg` are deprecated**, in favour of `ite_eq_left`,
   `ite_eq_right`, `dite_eq_left` and `dite_eq_right`, and
   `List.take_succ` in favour of `List.take_add_one`.
   `weak.warningAsError` makes each an error. `split_ifs` names no lemma
   and is unaffected.
10. **A concrete machine's output reduces in the kernel.**
    `example : copyIn.outputString (copyIn.initCfg [0, 1]) 3 = [0, 1] :=
    by decide` closes. The same assertion by `#guard` fails, and it fails
    at elaboration, with "Invalid `meta` definition, `initCfg` is not
    accessible here". That is a different failure from the one
    [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Lean 4
    module system records, which is a failure at evaluation; the repair
    that section prescribes, a `public meta import` of the module under
    test, applies to both. The test mirror takes `decide` instead,
    because the value reduces in the kernel and `decide` needs no `meta`
    import, as the Cobham mirrors do. The measurement is at three steps
    on a one-state machine; § Staged reduction of scope re-measures it at
    the mirror's intended size before the mirror's shape is fixed.
11. **A machine definition and a configuration family are choice-free.**
    Measured: the two prototype machines each report `[propext]`, the
    prototype's configuration family reports `[propext, Quot.sound]`, and
    `MultiTapeTM`, `Cfg`, `Cfg.workTapeSymbols` and `Function.update`
    report no axioms. Of the `MultiTapeTM` API, the declarations
    measured are tainted exactly when they mention `step`, `configs`,
    `outputString`, `Cfg.inputSymbol` or `spaceUsed`. The
    `moveInputPos` lemmas the seek's step lemmas will use were not
    measured individually; they live in the admitted `Steps.lean` either
    way, so nothing in the split depends on them. § Constructive posture turns this
    into the module split.
12. **The `MultiTapeTM` API depends on `Classical.choice` from three
    roots**, listed in § Constructive posture. Reproducible from the
    committed prototype: `inputSymbolCF` and `stepCF` both measure
    `[propext, Quot.sound]`. Each differs from the Cslib original in more
    than one respect — `inputSymbolCF` restates both guards at `.val` as
    well as replacing the `grind` index bound with `omega`, and `stepCF`
    restructures `step`'s `let`-destructuring — so together they show
    that a choice-free `step` is reachable, not that the index bound is
    the only variable. Not reproducible: patching only that bound in the
    dependency checkout, leaving both guards as written, and rebuilding
    showed `Cfg.inputSymbol`, `configs`, `outputString`,
    `configs_succ_eq_step'` and `outputString_succ` measuring
    `[propext, Quot.sound]` with all of Cslib still building; the
    checkout was then restored.
13. **`inputSymbolInner` is separately tainted.** It is the `@[simp]`
    lemma reading an input symbol out of a configuration, which the
    prototype uses and which any machine proof will use. Reproducible: it
    measures `[propext, Classical.choice, Quot.sound]`. Its proof is
    `grind [Cfg.inputSymbol]`, so it mentions the first root but carries
    a `grind` of its own. Not reproducible, and resting on the same
    discarded patch as item 12: that patching the first root leaves this
    one tainted.

## The machine

One work tape, and a machine alphabet of two symbols with the embedding
`boolEmb : Bool ↪ Fin 2`. The input bits are the two output symbols, and
both symbols are also available on the work tape, which is what § Why the
work tape carries two markers depends on.

The pending count is the work head's position. Cell `0` carries one
marker and cell `1` a different one; every other cell stays blank for the
whole run. A count of `d` is the head at cell `d`, so a single read
separates `d = 0`, `d = 1` and `d ≥ 2`.

Four states — seek, plant, live, dead — each named as a definition
carrying an assigned bound proof, following `leafSym` and `nodeSym` in
`Geb/Mathlib/Data/Tree/Ranked/Binary.lean`.

A design constraint on the transition function: `tr` is constant in
its work-symbol argument at every combination of state and input symbol
except two: the live state at input `some (boolEmb true)`, and the live
state at input `none`. The constraint is over pairs, not states, because the live
state is entered before the current bit is read and so serves the leaf
bit, the node bit and the left end alike. § The proof architecture
explains what the constraint is for.

**Seek**, `n + 1` steps. The input head moves right until it reads blank,
which by fact 6 is the cell past the right end; that reading step is the
exit, writing the first marker at work cell `0`, moving the work head
right to cell `1`, and moving the input head one cell left — onto the
word's last symbol when `1 ≤ n`, and onto the left blank when `n = 0`.
The non-exit steps write nothing and leave the work head at cell `0`, so
the tape is blank throughout the seek. Nothing reads the work tape during
the seek, so writing the marker earlier would achieve nothing and would
cost a `Function.update` obligation in every seek step lemma. The sweep
does read cell `0`, at a live node bit with count zero.

**Plant**, one step. It writes the second marker at work cell `1` and
moves the work head back to cell `0`. The input head does not move. The
sweep therefore begins with count `0` and both markers in place. The step
exists because a write applies at the head's current cell, so the two
markers cannot both be placed while the head is at one of them, and
because at `n = 0` the seek is a single step with no room to place the
second.

**Sweep**, one step per symbol, the input head moving left on each. The
live state at input `some false` moves the work head right and ignores the
work symbol. At input `some true` it reads:

- blank, so `d ≥ 2`: move the work head left, staying live;
- either marker, so `d ≤ 1`: fail to the dead state, with the work head
  unmoved.

The dead state moves the input head left, leaves the work head where it
is, and ignores the work symbol. Leaving the work head fixed is what
matches `scanStep`'s absorption, which returns its argument unchanged.

**Emission**, one step. When the input head reads blank at the left end,
the live state reads the work symbol and emits `true` for the second
marker and `false` otherwise, and the dead state emits `false` without
reading. Both halt in the same step, `TransitionOut` carrying `outS` and
`q' := none` together.

Underflow is the only failure mode. `scanStep`'s other failure, a block
spelling no symbol, is unreachable at `binRanked`: width is one, and both
one-bit blocks decode, by `arOf_decodeBits_false` and
`arOf_decodeBits_true`. The machine has no case for it.

## Why the count is the head position

The count could be a run of marks read off the tape. It is not, for two
reasons. Marks would make the work-tape field of every configuration
family a function of the count, and they would put a `Function.update`
reconciliation in every incrementing step with a `1 ≤ d` side condition
available only as the outcome of the tape read. With the count as the
head position no cell is written after the plant step, so the work tape
is constant for the rest of the run and `Function.update` does not appear
in the sweep at all.

## Why the work tape carries two markers

`scanStep` tests `decide (2 ≤ s.depth)` atomically and, on failure,
returns `⟨[], s.depth, false⟩` with the depth unchanged. A machine that
learns the count only by moving cannot match that: with a single marker
at cell `0`, a node bit at count `1` moves left, discovers the marker,
and has already changed the count that `scanStep` preserves. Recovering
the match then costs a second substep to restore the head, a second
failing state to distinguish how far it had moved, and an extra
configuration between the two.

Two markers remove all of that. Cells `0` and `1` are the only non-blank
cells and they carry different symbols, so one read separates `d = 0`,
`d = 1` and `d ≥ 2`. `scanStep`'s guard `decide (2 ≤ s.depth)` is a
two-way test; the machine needs the three-way split because a single
non-moving read must establish `d ≥ 2` for the node bit and `d = 1` for
the emission. The machine therefore detects failure before moving, and
on failure the head does not move at all, which is precisely the
depth-preservation `scanStep` performs.

The consequences are these: the sweep is one
step per symbol rather than two; no restoring move and no second failing
state exist; a sweep group is a single `step`, so no intermediate
configuration arises within the sweep; and the emitting step folds into
the live and dead states rather than needing a finish phase with its own
family and its own step lemmas. One intermediate configuration remains,
between the seek and the sweep, and § The proof architecture names it.

The cost is one extra step and one extra state to plant the second
marker, and a three-way rather than two-way case analysis at the two
`(state, input symbol)` pairs that read the work symbol.

## Uniform per-symbol cost

Every input symbol costs one step during the sweep, in the dead state as
in the live one.

The reason is not that the API demands a halting step uniform in the
length. It does not: `ComputesFunInTimeAndSpace` quantifies the step
count per input and requires only `t' ≤ t n`, and `configs_of_halts`
together with `outputString_eq_of_halt` let the predicate be evaluated at
any step at or after the machine halts.

The reason is that uniform cost keeps the number of symbols consumed at
step `t` recoverable from `t`, which is what makes a closed-form
configuration family possible at all. The dead state costing the same as
the live one serves the same end by a second means: it removes the need
to define the index of the first scan failure and to reason about it.
`configs_add` would accept such an index — it takes arbitrary `ℕ`
arguments, not literals — so the objection to defining one is its cost,
not its impossibility.

## The proof architecture

Three named configurations, and two of them families. Each family
carries the bound on its index as an explicit argument, as the
prototype's does, since the `inputPos` field is a `Fin (input.length + 2)`
and that bound is not derivable from the index alone.

- `seekCfg w t (h : t ≤ n)`, blank-taped with the work head at cell `0`
  throughout, since the marker is written only on the exit step. At
  `t = 0` it is `initCfg` definitionally, `initCfg` being
  `⟨some q₀, 1, fun _ _ ↦ none, fun _ ↦ 0⟩`, so the recursion is a plain
  `Nat.rec` from zero with `configs_zero` as its base and no shifted
  index, no `1 ≤ t` argument and no separate `n = 0` route.
- `plantCfg w`, not a family: the single configuration after the seek's
  exit step, in the plant state with the first marker written, the work
  head at cell `1` and the input head at position `n`. It must be named.
  `configs_add`'s right side is `configs (configs cfg a) b`, so at
  `a = n + 1` the inner term is this configuration, and writing it as a
  structure literal is the failure fact 3 records.
- `sweepCfg w k (h : k ≤ n)`, indexed by the drop count `k` from `n` down
  to `0`. Its state field is a conditional on
  `RankedAlphabet.Binary.ok (w.drop k)` — live when that holds, dead when
  it does not. This is the one conditional projection in the design,
  discharged once per step lemma by
  `cases h : RankedAlphabet.Binary.ok (w.drop k)`, with
  `RankedAlphabet.Binary.scanStep_of_not_live` closing the dead branch.
  Its `workTapePos` field is
  `((RankedAlphabet.Binary.depth (w.drop k) : ℕ) : ℤ)`.

The emitting step needs no configuration of its own. Nothing downstream
uses the halted configuration: `ComputesInTimeAndSpace` needs
`(configs … t).state = none` and the output needs
`outputSymbol (sweepCfg w 0 _)`, so the emitting step is stated as those
two projections rather than as a `Cfg.ext`.

The families are phrased over `RankedAlphabet.Binary.ok` and
`RankedAlphabet.Binary.depth`, not over the raw `Scan` projections
`.live` and `.depth`. The supporting lemmas are stated at that grain, and
a rewrite by an `ok`-headed rule does not fire against a goal carrying
`(scanFinal …).live`, ordinary syntactic matching being what governs
there. Two uses remain at `scanStep` grain and are named in
§ The invariant.

The phases are composed by `configs_add` and `outputString_add_eq_append`,
both in Cslib and neither used by the prototypes. The three boundaries
are step lemmas:

- `step (seekCfg w n _) = plantCfg w`, which covers `n = 0` uniformly,
  `seekCfg w 0` being `initCfg`;
- `step (plantCfg w) = sweepCfg w n _`, which needs `w.drop n = []` by
  `List.drop_length`, and then `ok [] = true` and `depth [] = 0`, both
  `rfl` through `RankedAlphabet.scanFinal_nil`, so that `sweepCfg w n`'s
  conditional state field resolves to the live branch and its
  `workTapePos` to `0`;
- the emitting step out of `sweepCfg w 0 _`, which needs `w.drop 0 = w`.
  It is stated as `(step (sweepCfg w 0 _)).state = none` together with
  the value of `outputSymbol (sweepCfg w 0 _)`, the latter a fact about
  the configuration before the step, so no `Cfg.ext` is needed.

Each boundary also owes a no-emission fact — `outputSymbol` is `none` at
`seekCfg w t` and at `plantCfg w` — which its `tr`-resolution lemma
supplies, and which the output conjunct needs in order to compose across
the seek and plant steps.

Two further composition obligations: `configs_add`'s inner term is not a
named configuration, so each composition step rewrites by the preceding
phase's theorem first; and every `Fin` bound is over
`(w.map boolEmb).length + 2`, so `List.length_map` is carried through
each bound proof and each `inputSymbolInner` application.

The sweep's recursion is over two indices, since the family descends in
`k` while the step count ascends. The motive carries the linking equation
and both conjuncts:

```lean
Nat.rec (motive := fun j ↦ ∀ k, ∀ h : k + j = n,
  configs (sweepCfg w n le_rfl) j = sweepCfg w k (by omega) ∧
  outputString (sweepCfg w n le_rfl) j = [])
```

so the step case obtains `(k + 1) + j = n` from `k + (j + 1) = n` by
`omega` and applies the sweep step lemma. The seek phase's theorem
bundles its output conjunct the same way. Handoff item 26 records that
`omega` treats an unreduced `Nat.zero` as an atom, so each base case
names its index at a literal first.

Because a sweep group is one `step`, no intermediate configuration arises
within the sweep and no sub-family per substep is needed. The sweep step
lemma is

```lean
step (sweepCfg w (k + 1) h) = sweepCfg w k (by omega)
```

for `h : k + 1 ≤ n`, so the configuration read is the one at index
`k + 1` and the configuration produced is the one at `k`. Everything the
step scrutinises therefore belongs to the source: the bit is `w[k]`, by
`w.drop k = w[k] :: w.drop (k + 1)`, and the work symbol is
`if pos = 0 then marker₀ else if pos = 1 then marker₁ else none` at the
opaque position `↑(depth (w.drop (k + 1)))`, whose `Int.decEq` does not
reduce. The three-way split at a live node bit is on
`depth (w.drop (k + 1))` against `0`, `1` and `2 ≤`, and the case
analysis on the source's liveness is on `ok (w.drop (k + 1))`.

The target's conditional state field is resolved separately, per case,
from the `cons` lemmas: `ok_cons_false` for a leaf, and `ok_cons_true`
together with `2 ≤ depth (w.drop (k + 1))` or its negation for a node.
Casing on the source's liveness does not discharge it.

The two constraints in § The machine confine the work-symbol split to the
two `(state, input symbol)` pairs that read it and keep the plant step
free of an input-symbol split; every other pair ignores the argument in
question and needs neither.

One `tr`-resolution lemma per case carries both obligations. `step`
and `outputSymbol` call `tm.tr q cfg.inputSymbol cfg.workTapeSymbols` on
identical arguments, so a lemma resolving that application at a given
configuration discharges the step lemma and the no-emission lemma
together, and the input-symbol resolution through `inputSymbolInner` and
`List.length_map` is performed once rather than twice. The no-emission
facts are not state-only: both the live and dead states emit at input
`none`, so each requires the input symbol resolved. Stating the
`tr`-resolution lemmas is the largest single economy available in the
proof and the plan schedules them first.

Within a phase the prototype's architecture applies: the family's
projections stated as lemmas, one step lemma per case, and the phase's
configuration theorem by an explicit recursor application.
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Recursion and
induction through recursors bars the `induction` tactic; Cslib's own
proofs use it freely and ours may not.

## The invariant

`sweepCfg`'s fields carry it rather than a theorem stating it: at the
boundary where the machine has consumed `w.drop k`, its work head is at
`((RankedAlphabet.Binary.depth (w.drop k) : ℕ) : ℤ)` and it is in the
live state exactly when `RankedAlphabet.Binary.ok (w.drop k)` holds. What
is proved is that the family so defined is what `configs` produces.

Indexing by the drop count makes the advance
`w.drop k = w[k] :: w.drop (k + 1)`, an instance of
`List.drop_eq_getElem_cons`, so the recursion introduces no truncated
subtraction. The step lemma's opening move is that rewrite on the right,
`List.getElem_map` on the left to turn `input[k]` into `boolEmb w[k]`,
and only then a case analysis on `w[k]`, which is a term rather than a
variable and so is rewritten in rather than substituted.

The count field crosses `ℕ` and `ℤ`: the successful node case relates
a head displacement of `-1` to
`depth (true :: v) = depth v - 1` at `ℕ`. `omega` handles `↑(a - b)` at
`ℕ → ℤ` natively, so this is expected to need no explicit cast lemma; the
plan confirms rather than assumes it.

The supporting lemmas, named so the plan does not discover them: for the
advance, `RankedAlphabet.scanFinal_cons` and
`List.drop_eq_getElem_cons`; at `ok`/`depth` grain,
`RankedAlphabet.Binary.ok_cons_false`, `ok_cons_true`,
`depth_cons_false_of_ok` and `depth_cons_true_of_ok_of_two_le_depth`; and
at `scanStep` grain, where no `ok`/`depth`-level lemma exists,
`RankedAlphabet.Binary.scanStep_of_not_live` for the dead branch and
`scanStep_true_of_live_of_buf_nil_of_depth_lt_two` for the failing node,
which is the source of the depth preservation the design depends on and
whose `s.buf = []` hypothesis is discharged by
`RankedAlphabet.Binary.buf_scanFinal_eq_nil`. Both of the latter route
through `scanFinal_cons` first, and both return a `Scan` constructor
application, whose projections need `dsimp only` — which is what handoff
item 12 records.
`RankedAlphabet.scanFrom_not_live` is not the lemma this induction wants:
it concludes only about `.live`, while the induction also needs `.depth`
preserved.

All of these exist. This branch adds no lemma to `Geb/Mathlib/`; see
§ Out of scope.

## The time bound

Uniform per-symbol cost makes each phase's length an affine function of
the input length, and `configs_add` composes them. The halting step is
`2 * n + 3`, proved as an equality, then weakened to the `≤` of
`ComputesFunInTimeAndSpace`. Given the phase theorems this reduces to
`(n + 1) + 1 + n + 1 = 2 * n + 3` and a `le_rfl`.

## The space bound

By fact 5, `le_trans (spaceUsed_linear _ _)` applied to the time bound,
at `k = 1`. The existential witness for the space is the machine's actual
`spaceUsed` value, so the exactness of `ComputesInTimeAndSpace`'s space
conjunct is discharged by `rfl` and the inequality is proved one layer
up.

`RankedAlphabet.Binary.depth_le_length` is not required. It would be
required only for a bound sharper than affine in the step count. The
count never exceeds the word length, so the sweep visits cells `0` to `n`
at most, and the plant step's excursion to cell `1` adds nothing above
that except at `n = 0`, where the visited set is `{0, 1}`; the sharper
bound is therefore `n + 2`, and proving it needs `visitedByTapeHead`
computed as a `Finset` image. See § Deferred.

## Correctness

`binRanked.validBool w` is
`(scanFinal w).live && (scanFinal w).buf.isEmpty && (scanFinal w).depth == 1`,
and at width one the middle conjunct is `true` by
`RankedAlphabet.Binary.buf_scanFinal_eq_nil`. `&&` is left-associative, so
rewriting by that lemma, then `List.isEmpty_nil`, then `Bool.and_true`
gives

```lean
binRanked.validBool w = (RankedAlphabet.Binary.ok w && depth w == 1)
```

which is what the emitting step computes: `ok w` selects the live or dead
state and `depth w == 1` is the second marker's read.
`RankedAlphabet.Binary.valid_iff_ok_and_depth_eq_one` is not needed —
`Valid` is defined as `validBool w = true`, so routing through a `Prop`
and back is a detour.

Two obligations remain: the families relate `(w.map boolEmb)[j]` to
`boolEmb w[j]` by `List.getElem_map` and case back to a `Bool`; and the
output conjunct relates `[boolEmb (validBool w)]` to the machine's
emission on each of the emitting step's three cases (dead; live with the
second marker; live otherwise).

## Constructive posture

By fact 11 a machine definition and a configuration family are
choice-free, so
[docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Constructive-only Lean code's instruction to split modules by what can
be stated choice-free applies and determines the split. It is followed,
and the allowlisted surface is the smallest the design admits.

- `TreeScanner/Machine.lean` — the machine, `boolEmb`, the four named
  states, the three named configurations, those projection lemmas that
  mention only structure fields, and § Correctness's bridge
  `binRanked.validBool w = (ok w && depth w == 1)`, which mentions only
  `RankedAlphabet` declarations and is choice-free.
  `Cfg.workTapeSymbols` measures no axioms, so its resolution lemmas
  live here too. The `Cfg.inputSymbol` projections do not; they go to
  `Steps.lean`. Not admitted.
- `TreeScanner/Steps.lean` — the `Cfg.inputSymbol` projections, the
  `tr`-resolution lemmas, the step lemmas, the phase configuration
  theorems, and the halting and output conjuncts. Admitted.
- `TreeScanner/Bound.lean` — the time and space bounds and
  `computableInTimeAndSpace_validBool`. Admitted.
- `GebTests/…/TreeScanner/Machine.lean` — the mirror. It is named for
  the module whose machine it exercises, but it asserts `outputString`
  values, so its statements name `Steps.lean`'s frontier and it is
  admitted while `Machine.lean` is not.

Handoff item 5 records that `omega` proving a non-`False` goal can pull
in `Classical.choice`, and that `lake lint` rather than inspection
settles it. `Machine.lean`'s `Fin` bound proofs and its `Cfg.workTapeSymbols`
resolution lemmas, which case on `↑(depth …)` against `0` and `1` at
`ℤ`, are where this can occur, though
the prototype's analogous bound is an `omega` and its family measures
`[propext, Quot.sound]`. If one measures tainted, the
resolution is one of the two the rule licenses — "over individually named
hypotheses, or by case analysis, rather than by the single lemma that
states it" — because the choice-dependent and choice-free lemmas of
`Nat`'s division and order API are not separated by name or namespace.
Which of the two applies depends on the bound: the `Fin` bounds here are
order facts, for which the named-hypotheses route is the one to take.
Admitting `Machine.lean` is not the resolution.

Three roots, each isolated by measurement.

- `Turing.MultiTapeTM.Cfg.inputSymbol` proves its array-index bound by
  `grind`. See fact 12 for what is reproducible and what is not.
- `Turing.MultiTapeTM.visitedByTapeHead` is a `Finset.image`, and
  mathlib's `Finset.image` depends on `Classical.choice`. The
  `DecidableEq ℤ` that instance search selects here does not, and
  `Finset.card` does not. This root taints `spaceUsed` and is not
  removable by this repository or by Cslib without redefining the space
  measure.
- `Turing.MultiTapeTM.inputSymbolInner` carries a `grind` of its own; see
  fact 13.

The second root is why admission is unavoidable rather than chosen. The
first and third are why `Steps.lean` needs admission too, and why
completing the deferred upstream patch first would not remove the need:
it would have to clean `inputSymbolInner` as well, and B5 must not depend
on two upstream changes.

The measurements were taken at the pinned toolchain and are re-taken when
the pin moves, per the same rule's final clause; `lake lint` enforces
them, as § Verification says.

## The rules file and its rationale

[docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Constructive-only Lean code contains, in the bullet that governs
admission:

> **Split modules by what can be stated choice-free.** Constructions and
> the content of their universal properties go in modules choice-free
> over the underlying data; mathlib structures and `Prop` instances go in
> a wrapper whose fields are those terms. Admit to
> `GebMeta.classicalAllowedModules` only such a wrapper, a module whose
> own subject is a `Classical`-dependent mathlib structure, their
> `GebTests` parallels, and the linter's own test fixture. A wrapper may
> carry content where that content cannot be stated choice-free.

and, earlier in the same section:

> The allowlist exists so thin wrappers over mathlib's
> `Classical.choice`-dependent category theory (e.g. `Over`) can reuse it
> while the constructive core stays strict.

Read on its own, that list is exhaustive, names mathlib twice and
category theory once, and is keyed to a module's subject. None of the
modules admitted above would qualify: their subjects are this branch's
own step lemmas and bound, and their dependence comes from Cslib
declarations they cannot avoid mentioning.

[docs/process.md](../../process.md) § Constructive-only discipline, the
rationale the rules file encodes, states the criterion and then states
that the list derives from it:

> The boundary is drawn at what can be stated, not at how much a module
> contains: a module reaches `GebMeta.classicalAllowedModules` when it
> has no choice-free content of its own left to state, either because
> its content is packaging or because its subject is a mathlib structure
> that is itself `Classical`-dependent. A module with choice-free
> content of its own is held to the strict set, so the constructive core
> cannot widen by accident. The remaining admissions follow from that
> reading rather than extending it: a test parallel inherits the
> dependence of the module it exercises, the linter's own fixture exists
> to establish that the allowlist has effect at all, and a wrapper may
> carry content that cannot be stated choice-free — a bridge through a
> `Classical`-dependent mathlib construct, say.

"The boundary is drawn at what can be stated" and "The remaining
admissions follow from that reading rather than extending it" settle
which of the two is the criterion: it is the absence of choice-free
content of a module's own, and the enumeration is derived from it rather
than bounding it. After the split of § Constructive posture, `Steps.lean`
and `Bound.lean` have no choice-free content of their own left to state,
every such piece having gone to `Machine.lean`, which is why that module
exists. They therefore qualify under the rationale as written.

The change this branch needs is accordingly a correction to match the
criterion rather than an amendment of policy. It touches both documents,
because the rationale's criterion sentence names mathlib in its two
`because` clauses just as the rules file's list does, and `Steps.lean`
satisfies the criterion's main clause while fitting neither clause: its
content is not packaging and its subject is a Cslib construct.

The correction states what the allowlist is *for*, and widens the library
rather than the test. An admitted module is one whose subject is the
correspondence between a concept developed here and a concept of an
external Lean library — Batteries, mathlib or CSLib — where that external
concept uses `Classical.choice`. `Steps.lean` and `Bound.lean` are
exactly that: their subject is how this branch's machine corresponds to
Cslib's `MultiTapeTM` and its `ComputableInTimeAndSpace`, and those use
choice. The rules file's purpose sentence, which names mathlib's category
theory as the motivating case, is generalised the same way rather than
being left to contradict the corrected list, and the rationale's two
`because` clauses follow.

Two alternatives are rejected. Naming Cslib alongside mathlib would need
a further correction the first time Batteries or core content needed one,
which is why the correction names the class — an external Lean library —
and gives the three current members as examples. And a criterion of
unavoidable mention, a module whose statements cannot be made without
naming a `Classical`-dependent upstream construction, is rejected because
mention is always avoidable at a price: any such concept can be dodged by
reimplementing it choice-free here, so that criterion rewards duplicating
an external library rather than corresponding to it, which is the
opposite of what
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost asks for.

The criterion's operative consequence is unchanged and is what
§ Constructive posture's split obeys: choice-free content has no business
in an admitted module. Anything statable choice-free, including
§ Correctness's `validBool` bridge, goes in a choice-free module that the
admitted one imports — which is what `Machine.lean` is.

The withdrawal condition is recorded in `TODO.md`: if the first and third
roots are cleaned upstream and the pin moves past them, `Steps.lean` and
the mirror recover choice-free content of their own and their entries are
removed, leaving only `Bound.lean` admitted.

The correction is made in this branch. It is three sentences across two
files, it is forced by this branch's own content, and no other branch
needs it; carrying it here is cheaper than a separate branch's review
round and merge, and leaves no interval in which the rules file and the
allowlist disagree. [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern
shape's default is a separate branch, and § Out of scope applies that
default to a `Geb/Mathlib/` lemma; the difference is that such a lemma
would be usable on its own, whereas this correction exists only to
describe what this branch does.

## Artifacts

Source and tests:

- `Geb/Internal/Computability/TreeScanner/Machine.lean`, `Steps.lean` and
  `Bound.lean` — as § Constructive posture divides them.
- `Geb/Internal/Computability/TreeScanner.lean` and
  `Geb/Internal/Computability.lean` — index files, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Repo structure.
- `Geb/Internal.lean` — `public import Geb.Internal.Computability`.
  Without it the new modules stay outside `lake lint`'s environment,
  which is what makes the allowlist entries meaningful.
- `GebTests/Internal/Computability/TreeScanner/Machine.lean` — the
  mirror. It asserts the machine's output against `binRanked.validBool`
  on valid and invalid words by `decide`, per fact 10, through a named
  `def` value built from the module under test rather than through
  anonymous `example`s: `scripts/pre-push.sh` runs `lake shake`, which
  infers required imports from the constants an olean references, and an
  anonymous `example … := by decide` leaves no such reference, so shake
  would report the import of the module under test as removable. Naming a
  `def` is the repair the repository's other test files use. The word
  length and any `set_option maxRecDepth` follow the measurement in
  § Staged reduction of scope.
- `GebTests/Internal/Computability/TreeScanner.lean`,
  `GebTests/Internal/Computability.lean` and `GebTests/Internal.lean` —
  the mirror's index files and its import.

Configuration and documentation:

- `GebMeta.lean` — `Steps.lean`, `Bound.lean` and the test mirror added
  to `classicalAllowedModules`, and the declaration docstring of
  `classicalAllowedModules` corrected: it describes the allowlist as
  covering the categorical wrappers over mathlib's `Classical`-dependent
  category theory, and says feature branches append their own wrapper
  module names; these entries falsify both. The module docstring
  needs no change.
- `docs/rules/lean-coding.md` and `docs/process.md` — the correction of
  § The rules file and its rationale: the rules file's purpose sentence
  and its admission clause, and the rationale's criterion sentence, whose
  second `because` clause names mathlib in the same way and takes the
  same generalisation. The `TODO.md` entry below is conditional on how
  far the branch gets, and § Staged reduction of scope adds one further
  conditional artifact; these two are not conditional.
- `styles/config/vocabularies/GebMathlib/accept.txt` — the terms this
  branch's prose introduces, appended without reordering the file.
- [docs/index.md](../../index.md) — entries for the new content, in
  topological order, beside the existing `Geb/Internal/` entries.
- [TODO.md](../../../TODO.md) — see below.

`lakefile.toml` needs no change, its globs being `Geb.*` and
`GebTests.*`, and CI needs none.

The `TODO.md` changes depend on how far the branch gets. On a complete
segment the workstream is finished, so § Extensions of the tree
recognizers is removed rather than gaining another "done" entry:
`TODO.md` records active workstreams and says complete ones are removed
with their content merged into the persistent documentation. Three
things that section carries must survive its removal.

- Its record that these segments subsume items under § Binary trees and
  their preorder encoding and under § The Bellantoni-Cook tree
  recognizer, including the tree recursor. Subsumption is not uniform and
  the items are treated one by one. § Extensions states that "labelled
  leaves and ranked alphabets are one construction and are B1" and
  records B1 as done, so § Binary trees item 1 is delivered and closes
  with the section. § Binary trees items 2, 3 and 4 — the
  `ConcreteSyntax.Ast` deduplication, the `Term.size` against
  `BinaryTree.numNodes` question, and the `DyckWord.equivTree` relation —
  are not subsumed by this workstream and stay active on their own terms.
  Item 2 names item 1 by number, so closing item 1 renumbers the section
  and item 2's reference is rewritten to name the construction rather
  than a position; its own "the condition on this item is met" is about
  `Geb/Internal/ConcreteSyntax.lean` carrying the initial algebra, the
  other side of the duplication, and is unaffected.
  § The Bellantoni-Cook tree recognizer item 6 is B5 and closes.
  Its item 1, the tree recursor, stays active: its own text says "Its
  soundness is a new theorem, not a corollary", and B3 delivered a
  catamorphism over a bit list rather than a recursor whose step receives
  two subtree spellings. Its item 3, the labelled variant, stays active
  and its cross-reference into § Binary trees item 1 is redirected to
  `docs/index.md`, item 1 having closed. The dependency the removed
  section recorded — that the surviving items build on B1's ranked
  alphabet and on this recognizer's scan — moves into their own sections.
- Its deferrals, which move to sections of their own: the
  Bellantoni-Cook port of the scan combinator, the paramorphism, the fold
  at an infinite carrier, the unary degree-sequence encoding, the
  `oneAtOf`/`falseAtOf`/`predPred` duplication, the `combSem`
  equation-lemma question, the redundancy of `Cobham/Tree.lean`'s
  recognizer beside `Cobham/RankedTree.lean`'s, the sweep-scale
  cross-check of `isTreeSem` against `validBool`, and the
  `BellantoniCook/Tree.lean` alignment.
- Its record that `BarringtonCorbett1989`,
  `BenoitDemaineMunroRamanRamanRao2005`, `Mehlhorn1980` and
  `BraunmuhlVerbeek1983` are absent from `docs/references.bib` and
  unverified against their primary sources. § References cites that
  record, so it survives with the same wording in whichever section
  receives it.

The items of § Deferred, the withdrawal condition of § The rules file and
its rationale, and — on a partial segment — the residue of the cost bound
are recorded in the same sections, so that nothing this branch defers is
left without a destination once § Extensions is gone.

On a partial segment § Extensions survives carrying the residue; § Staged
reduction of scope says which outcomes are merged.

The spikes — `Geb/Internal/TMSpike.lean`, the stage-0 spike
`Geb/Internal/TreeScannerSpike.lean`, and its companion
`Geb/Internal/TreeScannerSpikeMirror.lean` — are committed for the record
and removed later in the branch, as B6's and B3's were. The companion
exists because the mirror's `decide` runs across a module boundary while
a spike's own `example` does not, and the cross-module behaviour is the
one at issue; B3's spike carried `FoldSpikeMirror.lean` for exactly that
reason. None of the three is added to
`Geb/Internal.lean`: they are outside `lake lint`'s environment only
while unimported, and they are not allowlisted, so importing them would
fail the linter. All three are brought to the standard B6's and B3's spikes
were held to, which for `TMSpike.lean` as it stands means a module
docstring with the mandated sections in place of its present four lines;
a content namespace rather than its bare `namespace TMSpike`, following
`RankedTreeSpike.lean`'s `namespace RankedAlphabet` and `FoldSpike.lean`'s
`namespace Cobham`; docstrings on its five projection lemmas; a name for
its anonymous `example`; and removal of the process narration and the
barred words from its docstring, its section heading and its comments.
Its `#print axioms` commands are left, as B3's spike carried its own
(B6's carried none); § Verification's exclusion of `#print axioms` governs library
content, not a prototype committed for the record. Its
`linter.unusedSimpArgs` setting has no precedent in either spike and is
left only because fact 1 states what it excludes.

## Verification

The branch is checked by, and is not complete until:

- `lake build` and `lake test` clean;
- `lake lint` clean over `Geb`, which is what the `Steps.lean` and
  `Bound.lean` allowlist entries and the `Geb/Internal.lean` import exist
  to make meaningful, and `lake lint -- GebTests` clean, which exercises
  the mirror's entry; `lake lint` is also what enforces the axiom
  measurements § Constructive posture's split depends on, so no
  `#print axioms` is added to library content;
- `lake shake` clean, which constrains the mirror's shape above;
- `scripts/lint-imports.sh` clean, though nothing here touches an
  upstream-eligible subtree;
- `scripts/check-commit-msg.sh` clean over the branch's commits, per
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
  § Commit-message convention;
- `scripts/pre-push.sh` clean, which runs the above and additionally
  `lake exe cache get` (stamp-guarded, so usually skipped),
  `lake build GebTests` as `lake shake`'s prerequisite,
  `scripts/check-md-links.sh`, `markdownlint-cli2`, `doctoc`,
  `scripts/lake-update-warning.sh`, the docs-coverage reminder and the
  script self-tests, over the documents this branch adds and removes as
  well as the code. Its `lake shake` invocation is
  `--add-public --keep-implied --keep-prefix Geb GebTests`, and its
  commit-message check runs over `fork_point(main | @)..@ ~ merges()`.

## Risks

[TODO.md](../../../TODO.md) records that B5's difficulty is unbounded by
anything done so far, and the handoff calls the segment exploratory. The
concrete exposures, each with the measurement that retires it:

- The transition function may not resolve at `Fin` literals, in which case
  the machine is encoded differently. Stage 0 measured it on the first of
  three encodings: the `ite` chain on state equality resolves by `rfl`, and
  under `simp only` it does not resolve in either direction of the chain, so
  the encoding stands. The resolution has two levels: each arm of `tr`
  resolves by `rfl` at literal arguments, and the configuration-level
  resolution of § The proof architecture is that arm lemma preceded by
  rewrites of the input-symbol and work-symbol projections.
- The step lemma may not resolve `Cfg.workTapeSymbols` at an opaque head
  position, which would force a different representation of the count.
  Stage 0 measures it.
- The two-index motive with `by omega` inside a family application may
  not elaborate, which would change the shape of § The proof
  architecture. Stage 0 measures it.
- Kernel reduction may not reach the mirror's intended word length.
  Stage 0 measures it; if it fails, the mirror shrinks or asserts
  differently.
- `Machine.lean` may measure tainted through an `omega` bound proof, as
  § Constructive posture records.

## Size

The copying prototype is about a hundred and fifty lines for a machine
with one state, one substep per symbol, and an action independent of both
the symbol read and the work tape. Extrapolating from it alone would
understate this segment.

The calibration points are mathlib's
`Mathlib/Computability/TuringMachine/ToPartrec.lean` at about thirteen
hundred lines and `StackTuringMachine.lean` at about eight hundred, both
concrete machines with step-indexed correctness proofs and neither
carrying a cost bound. A comparable artifact in the exploratory tree that
preceded this repository is of the same order; it is not cited by path,
being outside this repository and so uncheckable by a reader here.

The planning figure is eight hundred to eleven hundred lines. Against the
calibration points, the two-marker design removes the finish phase, the
restoring machinery and every intermediate configuration within the
sweep, and the `tr`-resolution lemmas halve the input-symbol work; the
four named states with their mandated docstrings, the plant
configuration, the three-way split at two `(state, input symbol)` pairs,
and the bound argument carried through every family and lemma add to it.
No direction within the range is claimed.

Reading mathlib's `Mathlib/Computability/TuringMachine/ToPartrec.lean`
and `StackTuringMachine.lean` for idiom before writing the step lemmas is
a task of the plan, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost's instruction
to reuse existing abstractions: they are concrete-machine-with-step-lemma
precedent, at a different API but for the same proof shape.

## References

No `[Key]` citation is introduced by this branch and no entry is added to
`docs/references.bib`. No docstring cites the machine model: the model is
Cslib's and is cited there, against Cslib's own bibliography, and this
branch states nothing taken from those works. See § Transcription or
novel.

`BarringtonCorbett1989` is not cited. It would be cited only if the
branch came to state the DLOGTIME-uniform TC⁰ claim attributed to it,
which it does not, and then only after verifying that attribution against
the article, per
[AGENTS.md](../../../AGENTS.md) § Verify agent claims. The same holds for
the succinct tree-encoding references recorded as unverified in
[TODO.md](../../../TODO.md).

## Staged reduction of scope

Stage 1 is not a small stage. `tr` is one total function over the whole
state set, so the complete machine is settled before any configuration
theorem elaborates. The remaining stages are proof work against a fixed
object.

Stage 0's measurements test assumptions this document has already fixed.
If one is falsified, the plan records the measurement and this
specification is corrected with it before execution continues, so that
the reviewed artifact and the executed one do not diverge. That applies
to the coefficients of § The statement and to every design assumption
§ Risks lists.

0. A measurement spike in `Geb/Internal/TreeScannerSpike.lean` with a
   companion `Geb/Internal/TreeScannerSpikeMirror.lean`. Two states, one
   work tape with two markers, a head position that is an opaque function
   of the step, an emitted symbol chosen by a work-tape read, and two
   composed phases. It measures:
   - which of three transition encodings resolves, and by what tactic: a
     match on `Fin` literals, a match on `Fin.mk` patterns, or a
     vector-valued `tr` through `Matrix.vecCons`. The first resolves by
     `rfl` and not by `simp only`, so the other two were not measured; and
     in the first, whether a branch that ignores the work symbol reduces
     with that symbol left opaque, and whether a branch that ignores the
     input symbol reduces with that symbol left opaque, which is what the
     two constraints of
     § The machine assume;
   - whether a step lemma resolves `Cfg.workTapeSymbols` at an opaque
     head position across a three-way marker split, and what the working
     order of `cases` and `unfold step` is;
   - whether a leftward work-head move at a cast position closes: the
     prototype's rightward move closed by `rfl` because
     `Int.ofNat t + Int.ofNat 1` reduces, while
     `Int.ofNat d + Int.negSucc 0` is `Int.subNatNat d 1`, stuck for
     opaque `d`, and the sweep's node case is a decrement;
   - whether a conditional state field survives `step` and `Cfg.ext`;
   - whether `Cfg.inputSymbol` resolves at an input position of the form
     `⟨k, _⟩` through `inputSymbolInner` with `List.length_map` in the
     same step, and at position `0`, which takes the first guard of fact
     8 and which the prototype never exercised;
   - whether one `tr`-resolution lemma discharges both a step lemma and a
     no-emission lemma, as § The proof architecture assumes;
   - whether a configuration family defined in one module reduces against
     `initCfg` from a consuming module, which is what
     `seekCfg w 0 = initCfg` asserts across the `Machine.lean` and
     `Steps.lean` boundary. The claim is asserted and not measured; the
     prototype closes its analogous base case by `Cfg.ext` and `simp`
     rather than `rfl`, it is a single module, and
     `Geb/Mathlib/Data/Tree/Ranked/Binary.lean`'s implementation notes
     record that a consuming module's `rfl` reduces through a definition
     only if it unfolds across the boundary. The spike is written as two
     modules so that `@[expose]` is exercised where the real split needs
     it. Nothing structural depends on the answer — indexing `seekCfg`
     from `0` is what removes the shifted index and the `n = 0` route —
     so a negative result costs the two lines of the prototype's route;
   - whether `configs_add` and `outputString_add_eq_append` compose two
     toy phases, neither having been used by either prototype. The spike
     composes one phase theorem with itself, so what it measures is the
     two lemmas' application and rewrite direction; the handoff between
     two different configuration families, which is where § The proof
     architecture's obligation to rewrite by the preceding phase's theorem
     lives, is unmeasured;
   - whether the two-index motive with `by omega` inside a family
     application elaborates, with both conjuncts bundled;
   - whether a `decide` at the mirror's intended word length closes, and
     at what `maxRecDepth`. This one is measured in the companion module,
     across a module boundary, because that is the condition the mirror
     faces and an in-module `example` does not. Stage 0 measured it: the
     six-word list closes at the default `maxRecDepth`. The spike halts
     within four steps on every one of the six words, so the remainder of
     each `2 * |w| + 3` evaluation is halted steps on a tape with one
     written cell. What the measurement bounds is a short run padded that
     way; the kernel cost of the scanner's own run, active for all
     `2 * |w| + 3` steps over a tape that grows with the count, is not
     measured. § Artifacts states the fallback the mirror takes if it
     exceeds the budget.
1. The machine, its four named states, `boolEmb`, the three
   configurations, the `tr`-resolution lemmas, and the seek and plant
   phases' configuration theorem.
2. The sweep family's configuration theorem, composed by `configs_add`.
3. The emitting step and correctness of the emitted answer.
4. The time bound, which given stage 3 is the arithmetic
   `(n + 1) + 1 + n + 1 = 2 * n + 3`.
5. The space bound, and `computableInTimeAndSpace_validBool`.

Stage 3 is the minimum merge point. At stage 3 the branch has the first
concrete `MultiTapeTM` construction in that dependency set together with
a proof that it decides `binRanked.validBool`, which is a theorem worth a
`docs/index.md` entry and is part of the return § Scope names; the cost
bound is then recorded in `TODO.md` as the remainder. The ground for the
merge point is
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost: at stage 3
there is a theorem to document, and below it there is not. The handoff's
instruction to prefer completing an early stage over halting in a late
one points earlier still — its own stage A is this document's stage 1
or 2 — so it is consistent with a stage-3 minimum without establishing
it. Work reaching only stage 2 describes
a machine without relating it to `binRanked.validBool` and is committed
locally but not merged, since
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost does not admit
a machine that decides nothing.

Stages 4 and 5 are short given stage 3 — stage 4 is arithmetic and stage
5 a few lines by fact 5 — so the expected outcome is that all five
complete together. Stage 3's separate merge point exists for the case
where they do not.

If stage 3 is not reached, the segment's artifact is a record of what was
built, what did not succeed and why, with a `TODO.md` entry. The handoff
prescribes such a record as a note under `Geb/Internal/`; it is placed
under `docs/` instead, since that tree holds `.lean` modules and a stub
module whose only content is a docstring would still have to pass
`lake lint`. Declaring that outcome is preferred to leaving
the segment open.

## Out of scope

- **Additions to `Geb/Mathlib/`.** Every fact § The invariant needs
  exists, so none is anticipated. If one proves necessary it is a second
  concern: a lemma in `Geb/Mathlib/Data/Tree/Ranked/` carries its
  `GebTests/Mathlib/` mirror, the upstream authoring bar and the
  upstream-PR posture into a branch whose concern is a `Geb/Internal/`
  machine.
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape puts it on
  its own branch, and this branch is then rebased on it.
- **A lower bound.** Nothing here claims the machine is optimal.
- **Any change to `RankedAlphabet.scanStep` or the counter form.** B4 is
  merged and the machine mirrors it as it stands.

## Deferred

- **The sharper space bound**, `spaceUsed ≤ n + 2` rather than affine in
  the step count, via `RankedAlphabet.Binary.depth_le_length` and a
  computation of `visitedByTapeHead` as a `Finset` image.
- **The upstream patch to Cslib.** Cleaning the first root is one line in
  `Cfg.inputSymbol`'s index bound, verified to leave all of Cslib
  building; cleaning the third is a reproof of `inputSymbolInner`, not
  yet attempted. Both together would make the time-side API choice-free
  for downstream users; either alone would not. It is a Cslib pull
  request rather than content of this repository, so it belongs to
  neither upstream-eligible subtree and is recorded in
  [TODO.md](../../../TODO.md) as its own item. Its pull request
  description is user-authored, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Submission policy.
- **Whether the marks representation would ever be preferable**, for
  instance if a sharper space bound wanted the count readable from the
  tape rather than from the head position.
