# Fold over recognized terms — prototype findings

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Question 1: generalizing the recognizer to a fold](#question-1-generalizing-the-recognizer-to-a-fold)
  - [The recognizer is the fold's projection under the terminal algebra](#the-recognizer-is-the-folds-projection-under-the-terminal-algebra)
  - [The growth bound does not survive, and the repair](#the-growth-bound-does-not-survive-and-the-repair)
  - [The state layout: a presence marker per entry](#the-state-layout-a-presence-marker-per-entry)
  - [The sharper pending-count bound](#the-sharper-pending-count-bound)
  - [What coincides at `p = 0`, and what does not](#what-coincides-at-p--0-and-what-does-not)
- [Question 2: the linear-time proof](#question-2-the-linear-time-proof)
  - [What the existing proof is about](#what-the-existing-proof-is-about)
  - [Whether linear time generalizes](#whether-linear-time-generalizes)
  - [What a general machine would cost](#what-a-general-machine-would-cost)
- [Question 3: a carrier the class does not bound](#question-3-a-carrier-the-class-does-not-bound)
  - [The remaining word is what makes it possible](#the-remaining-word-is-what-makes-it-possible)
  - [The state-reading is polynomial, and space is what binds](#the-state-reading-is-polynomial-and-space-is-what-binds)
  - [The unbounded construction has the narrower step dispatch](#the-unbounded-construction-has-the-narrower-step-dispatch)
  - [The construction computes the fold](#the-construction-computes-the-fold)
- [Prototype](#prototype)
  - [Smash-freeness at a symbolic tree](#smash-freeness-at-a-symbolic-tree)
  - [What the growth condition establishes](#what-the-growth-condition-establishes)
- [Open obligations](#open-obligations)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

Findings on two questions: generalizing the ranked-tree recognizer of
`Geb/Mathlib/Computability/Cobham/RankedTree.lean` to a fold at an algebra of
the ranked alphabet, and the reach of the linear-time bound of
`Geb/Prototypes/Computability/TreeScanner/Bound.lean`. The prototype is
`Geb/Prototypes/Computability/CobhamFoldProto/`.

The prototype carries two expression-layer constructions over one semantic core.
The first is at a carrier with a fixed-width bit encoding
`enc : α → Fin p → Bool` and a retraction, so `|α| ≤ 2 ^ p`; its steps dispatch
on a constant window holding the stack they read. The second is at the carrier
`List Bool` with the algebra's operations supplied as expressions of the class,
so the carrier is unrestricted. § Question 3 covers the second and the trade
between them; `Geb.CobhamFold.foldOut_algOfFixed` relates the two at the shared
semantic layer: the folds their algebras denote agree, up to the encoding, at an
algebra whose carrier stays within a fixed width. Each construction is tied to
that layer separately.

The semantic layer `Fold.lean` is at an arbitrary carrier and is shared
unchanged by both.

This document is a transient artifact under `CONTRIBUTING.md` § Concern shape
and is removed in the branch's final commits. The prototype modules are not: they
are `Geb/Prototypes/` source, indexed in `docs/index.md`, and their follow-on work
is recorded in `TODO.md` § The fold over recognized terms.

## Question 1: generalizing the recognizer to a fold

### The recognizer is the fold's projection under the terminal algebra

`RankedAlphabet.Scan` carries an incomplete block, a pending count and a
liveness flag, and `RankedAlphabet.scanStep` at a completed block pops the
symbol's arity from the count and pushes one. That is a stack discipline whose
entries carry no data. Replacing the count by a stack of carrier values and the
pop-push by an application of an algebra gives `Geb.CobhamFold.FoldScan` and
`Geb.CobhamFold.foldScanStep`.

The identification is stronger than an instance at one carrier.
`Geb.CobhamFold.toScan` sends a fold state to the validity state by taking the
stack's length, and `Geb.CobhamFold.toScan_foldScanStep` proves it a step
homomorphism at every carrier and every algebra. The validity scan is therefore
the projection of the fold scan, not a parallel construction.
`Geb.CobhamFold.toScan_foldScanFinal` extends this to whole words, and the
negative half of the correctness statement — a word spelling no term folds to
nothing — follows from it with no separate argument.

The scan direction is what makes the stack discipline correct.
`RankedAlphabet.scanFrom` is a `List.foldr`, reading the word's last bit first,
so at a symbol's block the subterms to its right are already reduced. The stack
holds their values with child zero on top, which
`Geb.CobhamFold.foldScanFrom_ofFn` and `Geb.CobhamFold.foldScanFrom_spell`
establish.

The fold's codomain is `Option α`: `Geb.CobhamFold.foldOut_eq` states

```text
foldOut R alg w = (R.parse w).map (Term.fold R alg)
```

`Geb.CobhamFold.Term.fold_unique` gives the term algebra's initiality, so
`Term.fold` is the algebra morphism out of it rather than one of several. The
algebra itself is total; partiality comes only from the parse.

### The growth bound does not survive, and the repair

`Cobham.scan`'s bound child is `Cobham.boundRaw`, which prepends `growth` bits
to the recursion variable, so every scan built with it satisfies
`|state| ≤ |w| + growth` — an additive constant over the input. The recognizer
fits, its state being `1 + R.width + depth` bits with `depth ≤ |w|`.

A fold laid out this way does not. Its state carries one `(p + 1)`-bit entry per
pending subterm, so it is about `((p + 1) / R.width) · |w|` bits.
`binRanked.width = 1`, so for binary trees any carrier wider than nothing breaks
the additive bound.

Two things this leaves open. It has side conditions — `R.width < p + 1`, and an
alphabet whose symbols grow the stack — which `length_stateWordF_not_le_add`
meets by instantiating at `binRanked` and a positive carrier width; the algebra
is quantified over, the stack's height being independent of it under
`toScan_foldScanFinal`. And it rules out this stack-scan layout only: nothing
here excludes some other expression, bounded by `Cobham.scan` as it stands,
computing the same fold, and a constant algebra is computed by the recognizer's
own state, storing nothing per entry.

The repair stays inside the subalgebra. `Geb.CobhamFold.multRaw` is the
`mult`-fold self-concatenation of the recursion variable, built from
`Cobham.concatCompRaw`; `Geb.CobhamFold.boundMulRaw` prepends `growth` bits to
it; and `Geb.CobhamFold.scanMul` is the scan combinator at the resulting bound
`mult · |w| + growth`. `concat` is a generator of the subalgebra
`Cobham.SmashFree` names, which [Strahm2003] Theorem 1(2) contains in the
functions computable simultaneously in polynomial time and linear space, so the
multiplicative bound costs nothing in class membership, which
`smashFreeBool_boundMulRaw` states at every multiplicity and growth.
`Cobham.cond` already takes a concatenation bound in place of
[HeraudNowak2011]'s smash bound for the same reason, so the pattern is
established rather than new.

`Geb.CobhamFold.scanBRaw` takes its bound child as a parameter, and
`Geb.CobhamFold.scanBRaw_boundRaw` states that `Cobham.scanRaw` is the instance
at the additive child. The two bounds are instances of one node, and the
migration into `Cobham/Scan.lean` is definitionally transparent.

The multiplier is constrained by `p + 1 ≤ mult · R.width` rather than fixed;
`mult = p + 1` always meets it, and a wide alphabet admits a smaller one.

### The state layout: a presence marker per entry

`Cobham.stateWord` spells the pending count in unary, and the run of `true`
ending at the first `false` gives the count capped at the dispatch window,
because `Cobham.bits` pads past the word's end with `false`.

A carrier defeats that encoding: a value may encode to all `false` and would be
indistinguishable from padding. `Geb.CobhamFold.entryBits` therefore gives each
entry a `true` presence marker followed by the `p` encoding bits, and
`Geb.CobhamFold.dispatchWidthF` reads `R.maxArity + 1` such entries — the
`R.maxArity` an algebra can consume, plus one whose marker separates a stack of
exactly `R.maxArity` entries from a longer one.

### The sharper pending-count bound

`RankedAlphabet.depth_scanFinal_le_length` gives `depth ≤ |w|`.
`Geb.CobhamFold.width_mul_depth_add_length_buf_scanFinal_le` sharpens it to

```text
R.width * depth + |buf| ≤ |w|
```

The pending count rises only at a completed block, so it counts symbols rather
than bits. The invariant has to carry the incomplete block's length: a partial
block is progress toward the next increment, and without that summand the
induction does not close at the completing step. This is what fixes the
multiplier, and it is what places the fold's space at `p + 1` bits per symbol of
the tree rather than per bit of the input.

### What coincides at `p = 0`, and what does not

At the carrier `Unit`, whose encoding is empty, an entry is `[true]` and the
layout is `Cobham.stateWord`. The module
`Geb/Prototypes/Computability/CobhamFoldProto/Degenerate.lean` states the
coincidences: `dispatchWidthF_zero` and `readoutWidth_zero` for the two windows,
`stackBits_unit` and `stateWordF_unit` for the layout, `dropCountF_unit` and
`nextPrefixF_unit` for both halves of a step, and `foldOut_unit` with
`foldOutSem_unit_eq_ite` for the accepted language.

The two are not one expression. `Geb.CobhamFold.boundMulRaw_ne_boundRaw`
separates the two bound children at multiplicity one, at every growth, so the
raw trees differ;
and the rejecting words differ, `outWord` spelling both branches at the width
`p + 1` where `Cobham.isRankedSem_eq_ite` gives the empty bitstring. What holds
is that each component coincides and the languages agree.

## Question 2: the linear-time proof

### What the existing proof is about

`Geb.TreeScanner.computableInTimeAndSpace_validBool` is a statement about
`Geb.TreeScanner.treeScanner`, a hand-built deterministic multi-tape Turing
machine. It shares no code with `Cobham.isTree` — no `TreeScanner`
module imports a Cobham module or contains an occurrence of the name — and is a
separate object proved to compute `binRanked.validBool`, the same decision the
Cobham side makes under a different output encoding, in `2n + 3` steps and
`2n + 4` cells.

Generalizing the Cobham side therefore cannot break it, and no restriction of it
to the recognizer is needed: it was never a statement about the Cobham
expression. The two results are independent. Membership in
`Cobham.SmashFree` would give
polynomial time and linear space by [Strahm2003] Theorem 1(2)'s
left-to-right inclusion, and the machine gives linear time specifically. The
fold has that membership unconditionally for the fixed-width construction, at a
symbolic alphabet and carrier width, by `smashFree_foldOutExpr`, and for the
bitstring construction under the hypothesis that the algebra's own expressions
are smash-free, by `smashFree_foldOutExprV`;
`Cobham/RankedTree.lean` defers it for `isRanked`, whose symbolic route is
`instFinEnumSigB`, `smashFreeBool_mk_iff` and `smashFreeBool_casesRaw` together,
which the subtree import rules keep it from citing.

### Whether linear time generalizes

For a carrier that is finite and an alphabet that is fixed, the sketch below
gives a linear bound. It is a sketch: no such machine is formalized, and neither
is the general-alphabet recognizer machine it builds on.

`treeScanner` represents the pending count as the work head's *position*, with
markers at cells `0` and `1` so one read separates a count of `0`, of `1`, and
of `2` or more. It writes no work cell outside those two, so every other cell it
reads is blank — which is possible precisely because `Unit`-valued stack entries
carry no data. That is the degenerate case of the same observation as
§ The recognizer is the fold's projection under the terminal algebra, seen on the
machine rather than on the scan.

A machine for the general fold keeps the stack on the work tape with the head at
the top, over a work alphabet carrying the carrier. It first walks the input head
to the right end, as `treeScanner`'s `stSeek` phase does, the scan being
right-to-left. It then sweeps: per input bit it moves the input head one cell
left and accumulates the block in its finite state (`2 ^ R.width` states' worth).
On the `R.width`-th bit the block is complete and the state knows the symbol; the
machine reads the top `r ≤ R.maxArity` cells into its state
(`|α| ^ R.maxArity` states' worth), writes the algebra's value into the new top
cell, and repositions. Underflow is detected by a bottom marker, within those
same `r` moves.

Per completed block that is `O(R.maxArity)` steps, a constant; per input bit in
the sweep it is one step; and the seek pass is another `n`. Total

```text
(2 + R.maxArity / R.width) * n + O(1)
```

steps, and `n / R.width + O(1)` work cells over an alphabet of size
`|α| + O(1)`. Both linear. The carrier's size enters the state count and the work
alphabet, not the step count. The work-cell count is the one part of this
paragraph with formal backing: it is
`Geb.CobhamFold.width_mul_depth_scanFinal_le` applied to each suffix of the
input.

At `binRanked` — width one, maximum arity two — the formula gives `4n`, against
the existing machine's `2n + 3`. The general machine is slower on the case the
existing one covers, which is what paying for the stack's contents costs.

### What a general machine would cost

Four things separate it from the existing one, and none is a small edit:

1. The machine reads and writes stack cells. `treeScanner`'s work tape is blank
   but for two markers, and every invariant in
   `Geb/Prototypes/Computability/TreeScanner/Steps.lean` is stated on closed-form
   configurations that exploit that. A machine carrying data on the work tape
   needs configurations parameterized by the stack's contents.
2. The constants do not survive, and are worse at `binRanked`, as above.
3. Generalizing over the alphabet is already a separate step. `treeScanner` is
   binary-only: at `binRanked.width = 1` a block is a single bit, so the machine
   needs no block buffer in its state and no general `r ≤ depth` test. That
   generalization is a prerequisite for the fold machine and is orthogonal to
   it.
4. The output lengthens. The existing proof emits one symbol
   (`outputString_eq w` against a singleton list); a fold emits the carrier's
   value and a presence marker, so the emitting phase becomes several steps and
   Cslib's `Turing.MultiTapeTM.outputString` is exercised on a longer list.
   This is the machine's output alphabet, not the `p + 1` bits `outWord` spells
   on the Cobham side; the two encodings are different.

Recommendation: treat the general linear-time machine as its own workstream,
downstream of a general-alphabet recognizer machine, and do not couple it to the
fold's Cobham-side work.

## Question 3: a carrier the class does not bound

The fixed-width restriction above is a restriction of one technique, not of the
class. A scan's step is an arbitrary `Cobham.COf 1`, and `Cobham.casesOf` is a
convenience; a step may itself be a bounded recursion walking the whole state.
Taking the carrier to be bitstrings and the algebra's operations to be members
of the class turns the fold from a construction at a fixed carrier into a
closure property: the class is closed under folding over recognized terms
whenever the algebra's operations lie in it and the fold's values stay linearly
bounded.

`Geb/Prototypes/Computability/CobhamFoldProto/Variable.lean` builds it. The
subsections below record what building it settled.

### The remaining word is what makes it possible

Stack entries must delimit themselves, and a step must parse one. `firstBitOf`,
`unaryOf` and `takeUnaryOf` recurse without reading the remaining word;
`dropUnaryOf`,
`dropEntryOf` and `takeEntryOf` read the remaining word as well, and
`takeEntryOf` is the one whose use of it is least avoidable: the
recursion appends a bit at the payload's *end*, which is not a head operation.
It works because `Cobham.evalRec` hands a step the remaining word in slot zero
as well as the recursive value in slot one:

```text
takeEntrySem (true :: v) = takeEntrySem v ++ firstBitSem (dropEntrySem v)
takeEntrySem (false :: v) = []
```

the `concat` generator supplies the append and the appended bit is read off
slot zero.
A scan combinator exposing only the recursive value — which is all
`Cobham.scan`'s `liftRaw` gives — cannot express this, so the module adds
`Geb.CobhamFold.scan2`, a scan node taking arity-two steps. Had `evalRec` not
passed the remaining word, the construction would fail here.

### The state-reading is polynomial, and space is what binds

A step reads the stack through primitives that are themselves recursions with
non-constant steps: `dropEntryOf`'s step applies `Cobham.pred`, itself a
`boundedRec`, and `takeEntryOf`'s step runs a fresh `dropEntryOf` over the
remaining word. Counting a `boundedRec`'s cost as the sum over its levels of
its step's
cost, `dropEntryOf` is quadratic in its argument and `takeEntryOf` cubic, so the
fold's state-reading is polynomial of a degree above two.

Nothing in the repository measures reduction steps, as
`Geb/Mathlib/Computability/Cobham/Tree.lean` records of its own subject, so that
figure is an analysis under one cost model rather than a result. What the
analysis settles without a model is a lower bound on this layout: reading an
unbounded field of the state requires a recursion over the state, `boundedRec`
being the class's only recursion, so no step of this construction, whose steps
do read one, is constant-time. It does not exclude some other expression
computing the same fold without reading an unbounded field.

The algebra is an arbitrary member of the class and so carries whatever cost the
class admits. The state-reading is therefore not what limits a fold: any cost the
class admits at all is reached by spending it inside the algebra rather than in
the fold's machinery. How far that goes is a question about the class and is not
settled here. Only the left-to-right inclusion of [Strahm2003] Theorem 1(2) is
relied on anywhere in this repository, and `docs/references.bib` records that
the equality fails read literally, the smash being computable in polynomial time
and logarithmic work space while lying outside the algebra. No claim that the
subalgebra exhausts the polynomial-time-and-linear-space functions is made or
used.

Space binds. The state holds every pending value, so a linear-space reading
forces a constant `c` bounding the pending values' total length by `c * n`,
which is `Geb.CobhamFold.length_foldSemV_le`'s hypothesis. That hypothesis is
not an artifact of the construction: [Clote1999]'s arithmetic analogue reads its
class as one of functions of linear growth. It also bears on the deferral
`TODO.md` records of a fold at an infinite carrier:
`concat` gives only linear multiples of the input, so the
argument is that `smash` is needed when the values grow superlinearly and
the linear-growth hypothesis is the condition under which it is not. Neither
direction is formalized.

The bounded/unbounded dichotomy is unaffected, and it is the only split there
is. A carrier whose values are bounded by a constant is the fixed-width case —
pad to that constant, dispatch on a constant window, and no step reads an
unbounded field. A carrier whose values are unbounded needs self-delimiting
entries, and every step of this layout reads one. A bound of any constant `B` is
the fixed-width case at width `B`, so there is no intermediate regime. No
quadratic *lower* bound is established anywhere: the quadratic and cubic figures
are upper bounds under one cost model, and the model-free argument gives only
non-constancy.

### The unbounded construction has the narrower step dispatch

The fixed-width construction's dispatch reads the stack, so its branch family is
`2 ^ (1 + R.width + (p + 1) * (R.maxArity + 1))`, and `Cobham.casesRaw`, which
both constructions dispatch through, recurses with three children per level. The
bitstring construction's dispatch reads only the flag, the slot
and the pending count — the stack sits past a sentinel and is reached by
recursion, not by the window — so its family is `2 ^ Cobham.dispatchWidth R`,
the recognizer's own width, whatever the carrier.

This is a statement about the step's branch family alone, not about expression
size and not about the readout, whose two windows are
`1 + R.width + 2 * (p + 1)` and `1 + R.width + (R.maxArity + 2)` and so order
either way according as
`R.maxArity` exceeds `2 * p`. What the comparison carries is that the step
dispatch stops growing in the carrier's width.
The bitstring construction's completing branch carries a `rebuildOf` subtree no
fixed-width branch does, and at `p = 0` the two families are equal, `Geb.CobhamFold.dispatchWidthF_zero`
proving `dispatchWidthF R 0 = Cobham.dispatchWidth R`. The two expressions'
sizes are not compared.

### The construction computes the fold

`Geb.CobhamFold.foldOutExprV` is a member of `Cobham.C` and
`Geb.CobhamFold.foldOutSemV_eq` identifies its value with
`Geb.CobhamFold.foldOut`, spelled by `outWordV` — a `true` marker followed by
the value, and `[false]` at no value. With `foldOut_eq` that is
`RankedAlphabet.parse` followed by the algebra morphism, the same specification
the fixed-width construction meets through `foldOutSem_eq`.

The readout's window has a count region of `R.maxArity + 2` bits. Any two or
more separate a count of one from a longer one; the dispatch window will not do,
its count region being one bit at an alphabet whose symbols are all nullary.

## Prototype

`Geb/Prototypes/Computability/CobhamFoldProto/`, building `Classical.choice`-free
under `lake lint` and `lake lint -- GebTests`, with `lake test` passing:

| Module | Content |
| --- | --- |
| `Bound.lean` | `projOf`, `compOf`, `comp1Of`, `concatCompOf`, `scan2Raw`, `multRaw`, `boundMulRaw`, `scanBRaw` parameterized by its bound child, `scanBRaw_boundRaw`, `scanMul` |
| `Fold.lean` | `FoldScan`, `foldScanStep`, `toScan` and its homomorphism, `Term.fold_unique`, `foldOut`, `foldOut_eq`, the sharper depth bound |
| `Layout.lean` | `entryBits`, `stackBits`, `stateWordF`, `decodeStateAt`, `dropCountF`, `nextPrefixF`, the step lemma |
| `Expr.lean` | `foldStepF`, `foldSemF`, `foldExprF` in `Cobham.C`, the readout and its output lemmas, `foldOutSem_eq` |
| `Degenerate.lean` | the `p = 0` coincidences with the recognizer |
| `SelfDelim.lean` | `scan2` at arity-two steps, `entryWord`, and the parsing primitives |
| `Variable.lean` | the fold at the carrier `List Bool`, `foldExprV` and `foldOutExprV` in `Cobham.C`, `foldOut_algOfFixed`, and the growth bridge `length_fold_le_of_growth`, `potential_foldScanStep_le`, `potential_foldScanFinal_le`, `stackSize_le_of_growth` |
| `SmashFree.lean` | `instFinEnumSigB`, `smashFreeBool_mk_iff`, the combinator lemmas, `smashFree_foldOutExpr`, `smashFree_foldOutExprV` |

`GebTests/Prototypes/Computability/CobhamFoldProto/Fold.lean` evaluates the fold
at the two-symbol alphabet under an algebra counting nodes modulo four, checks
it against `Term.fold`, and checks absence at a word spelling no term. It also
bears on the order in which the scan presents a symbol's children to the
algebra: a symmetric algebra cannot witness that order, so `leftHeavy` and its
transpose
`rightHeavy` are checked against each other, `leftHeavy_ne_rightHeavy`
establishing that the two disagree on the sample term and
`leftHeavyFold_eq_termFold` with `leftHeavyFold_ne_rightHeavy` then pinning the
stack's head as child zero at a concrete alphabet. The order is already pinned
symbolically by `Geb.CobhamFold.foldScanFrom_code`, whose conclusion names
`alg i vals` against a stack beginning `List.ofFn vals`; a transposed step
falsifies it, and with it `foldScanFrom_spell`, `foldOut_eq` and both
expression-level correctness theorems. The samples cross-check the order rather
than fixing it.

It also states `Cobham.SmashFree` at named instances. `smashFree_unitExpr` is a
kernel evaluation at `p = 0`, retained as an independent check on the symbolic
`Geb.CobhamFold.smashFree_foldOutExpr`, which gives the same conclusion.
`smashFree_parityExpr` applies that theorem at `p = 1` over the two-element
carrier `Bool`, a carrier the recognizer does not cover and so the one that
bears on simultaneous polynomial time and linear space, and the width at which
a `decide` needs a raised recursion depth. `leafCountExpr` is the bitstring
construction's witness:
an algebra counting a term's leaves in unary, so not constant in its arguments,
whose growth condition holds at `c = 1` and whose whole hypothesis bundle is
discharged — the linearity hypothesis by
`Geb.CobhamFold.stackSize_le_of_growth` from that condition alone — with
`smashFree_leafCountExpr` from `smashFree_foldOutExprV`. Neither construction is
exercised on an input at the expression level; the samples evaluate the semantic
`foldOut`, and the `decide` on `unitExpr` checks tree shape rather than value.

### Smash-freeness at a symbolic tree

`Cobham.smashFreeBool` is a `WType.elim` whose node clause applies `decide` to a
quantification over `Cobham.sig.B`. Two obstructions stand between it and a
symbolic claim, and neither is about the subalgebra. Instance search does not
delta-reduce the semireducible `Cobham.sig`, so `Cobham.sig.B a` is never
matched against `Cobham.sigFinitary`'s branches, which are stated at the literal
`Cobham.Direction` each shape produces — this at a constructor shape as much as
at a variable one; and the `WType.elim` reduces only at a constructor, so at a
variable shape the two sides of the intended equivalence are not defeq.
`instFinEnumSigB` names the enumeration at the form the quantification reads,
and splitting the shape before stating the equivalence
(`smashFreeBool_mk_iff`) reduces the clause. Neither step alone suffices, each
addressing a different one of the two obstructions. The resulting implications
compose through the combinators to both constructions.

The two proofs are not alternatives. `smashFree_foldOutExpr` holds outright: the
fixed-width construction compiles the algebra into its dispatch tree, so nothing
foreign enters. `smashFree_foldOutExprV` holds when the algebra's own
expressions do, the bitstring construction splicing them in unconstrained; its
converse, that a `smash` in the algebra forces one in the fold, is not stated.
Each construction needs its own theorem, and together they say that the
machinery contributes no `smash` at any alphabet or carrier width.

### What the growth condition establishes

`length_fold_le_of_growth` turns a per-symbol condition on the algebra — each
operation lengthens its arguments' total by at most a constant `c` — into
`|fold t| ≤ c * t.size`. `stackSize_le_of_growth` turns the same condition into
the linearity hypothesis the expression-level construction consumes, by way of
the potential `R.width * stackSize + c * |buf|`: it starts at zero, and each
input bit raises it by at most `c`, whether the bit extends the buffer or
completes a symbol and collapses the top of the stack. This is the sense in
which linear space is a condition on the algebra and not on the layout: the
state holds every pending value at once, so a fold whose values grow faster than
its input cannot be run in linear space by any encoding.

## Open obligations

These are not resolved, and are recorded in `TODO.md` § The fold over recognized
terms so that they survive this document's removal:

- **The fixed-width construction does not scale in the carrier's width.** The
  dispatch tree
  has `2 ^ dispatchWidthF` branches and, `Cobham.casesRaw` recursing with three
  children per level, a normal form growing by about a factor of three per bit
  of dispatch width — 21318 nodes at `unitExpr` and 547695 at `parityExpr`. At
  `binRanked` the widths are five at `p = 0`, eight at `p = 1` and eleven at
  `p = 2`. The
  term elaborates at each, `Cobham.casesOf` taking its branch family as a
  function; what the width ends is normalization, a `decide` succeeding outright
  at five, needing a raised `maxRecDepth` at eight, and exceeding the heartbeat
  limit at eleven whatever the depth. The symbolic proof is therefore what makes
  any statement available beyond a few bits, while a practical carrier
  needs a construction whose normal form does not grow this way. The bitstring
  construction has no such growth.
- **Whether the linear-growth condition forces smash-freeness.**
  `smashFree_foldOutExprV` assumes the algebra's expressions smash-free, and
  `stackSize_le_of_growth` assumes the growth condition. Whether the two
  hypotheses are one is unestablished, as is the converse of
  `smashFree_foldOutExprV`. That superlinear growth of the fold's values forces
  `smash`, `concat` giving only linear multiples of the input, is argued
  informally in § Question 3 and formalized nowhere.
- **Neither construction is exercised on an input at the expression level.** The
  samples evaluate the semantic `foldOut`; no expression's output word has been
  computed from an input word.
- **Three parameterizations belonging upstream**, each in the merged module
  whose special case it generalizes: the bound child and the arity-two scan node
  `scan2Raw` into `Cobham/Scan.lean`, and the state decoder's window into
  `Cobham/RankedTree.lean`, whose `Cobham.decodeState` is
  `Geb.CobhamFold.decodeVAt` at the dispatch window and shares its body
  verbatim. Each touches a merged upstream-eligible module and its consumers
  (`Cobham/Tree.lean`, `Cobham/RankedTree.lean`, `Cobham/Fold.lean`, and
  `GebTests/Mathlib/Computability/Cobham/Scan.lean`, which names `scanRaw`).
  `scanBRaw_boundRaw` makes the bound child's substitution definitionally
  transparent, but the migration is still a branch of its own.
- **The general linear-time machine**, per § What a general machine would cost.

## References

- [Clote1999], [HeraudNowak2011], [Strahm2003] — see `docs/references.bib`.
  The prototype's Lean modules additionally cite [Cobham1965] for the function
  algebra and [GambinoHyland2004] for the initiality `Term.fold_unique`
  instantiates.
- `Geb/Mathlib/Computability/Cobham/RankedTree.lean` — the recognizer being
  generalized.
- `Geb/Prototypes/Computability/TreeScanner/Bound.lean` — the linear-time bound
  discussed in § Question 2.
