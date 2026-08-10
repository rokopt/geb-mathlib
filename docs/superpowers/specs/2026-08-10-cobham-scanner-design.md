# The scan combinator over Cobham's class

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [The combinator](#the-combinator)
- [Main statements](#main-statements)
- [Rebuilding the recognizer](#rebuilding-the-recognizer)
- [Verification](#verification)
- [Risks](#risks)
- [Out of scope](#out-of-scope)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

One branch over `Geb/Mathlib/Computability/Cobham/`, the item TODO.md
§ Extensions of the tree recognizers records as B2, reduced to two of its
three deliverables: the `Scanner` combinator and the present
`Cobham.isTree` rebuilt on it. The generic ranked recognizer that entry
also lists moves to an entry of its own, since nothing depends on it —
B3 needs the combinator, B4 needs B1's `RankedAlphabet.Binary.valid_iff`,
and B5 needs a recognizer of either width — and it carries an unsettled
design decision of its own, the layout of `RankedAlphabet.Scan` as a
bitstring.

Every definition below is novel. The recursion scheme they package,
bounded recursion on notation, is the transcription of [Cobham1965]
already carried by `Cobham.sig` and `Cobham.evalRec`; `List.foldr` is
mathlib's. No definition or theorem in this branch is taken from
published mathematics, so the branch adds no key to
[docs/references.bib](../../references.bib).

## The combinator

`Geb/Mathlib/Computability/Cobham/Scan.lean`, importing
`Geb.Mathlib.Computability.Cobham.Basic` alone.

A scanner is a right-to-left fold over a bitstring whose state is itself
a bitstring: a base value, one step per bit read, and a bound on how far
the state can exceed the input. `Cobham.evalRec` supplies the recursion,
peeling the word's last bit at each step and passing the remainder on;
the state is the recursive value it passes alongside.

`evalRec`'s step is applied to `Fin.cons v (Fin.cons (ih x) x)`: slot
zero is the remaining suffix, slot one the recursive value, slots two
upward the ambient environment. A fold's step is a function of the state
alone, so a scanner's steps are `COf 1` and the node's step children are
those lifted by `comp` with `proj 2 1`. A `COf 2` step field would
advertise the suffix, which no fold reads.

The definitions, in dependency order:

- `boundRaw (growth : ℕ)` — `succ true` iterated `growth` times over
  `proj 1 0`, by `Nat.rec`, of arity one. It is the node's bound child,
  returning `growth` bits more than the recursion variable. `growth = 0`
  is the `Nat.rec` base, the bare projection.
- `liftRaw (e : sig.toPFunctor.W)` — the `comp 2 1` node with head `e`
  and sole argument `proj 2 1`, carrying a step of arity one into the
  shape `evalRec` applies.
- `scanRaw (base step₀ step₁ : sig.toPFunctor.W) (growth : ℕ)` — the
  `boundedRec 0` node over
  `![base, liftRaw step₀, liftRaw step₁, boundRaw growth]`.
- `scanValid` — admissibility of `scanRaw` as a `sig`-tree, from the
  components' own admissibility.
- `scanStepSem (step₀ step₁ : COf 1) (b : Bool) (r : List Bool)` — the
  semantic step: the meaning of `step₁` at `![r]` when `b`, of `step₀`
  otherwise.
- `scanFold (base : COf 0) (step₀ step₁ : COf 1) (w : List Bool)` — the
  fold `w.foldr (scanStepSem step₀ step₁) (base.eval Fin.elim0)`, the
  function a scanner computes.
- `scanSem (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : Sem 1` —
  the meaning at the raw tree, as `Cobham.combSem` is.
- `scanner base step₀ step₁ growth (hbound)` — the expression of `C`,
  its `RecBounded` discharged from `scanSem_eq`, the hypothesis
  `hbound`, and the components' own `RecBounded`.
- `scannerOf base step₀ step₁ growth hbound : COf 1`.

`scanRaw` takes raw trees and `scanSem` takes expressions, which is the
layering `Cobham.combRaw`, `Cobham.combSem` and `Cobham.comb` already
have and which this branch preserves. `Cobham.eval` asks only for
admissibility as a `sig`-tree, not for the recursion bound, so a scanner
is characterized before the expression carrying its bound exists. The
characterization is what the bound's own proof consumes: `Cobham.comb`
establishes `hb` by rewriting through `combSem_eq`. A combinator
demanding the bound as a structure field would order the two the other
way, leaving no characterization to state the bound against.

The bound is an argument to `scanner` rather than a field of a
structure, for the same reason: a field stating
`∀ w, (scanFold base step₀ step₁ w).length ≤ w.length + growth` cannot
name `scanFold`, which is a function of the structure being declared.

`growth` is a natural number rather than an expression of arity one with
a semantic bound of its own. A constant covers every consumer in view:
`Cobham.comb` at one, a fold at a finite carrier at the width of that
carrier's encoding, and a ranked scan at a multiple of the alphabet's
width. An expression-valued bound would oblige each instance to supply a
bound term and characterize its meaning, for generality none of the
three asks for.

## Main statements

- `scanSem_nil` — the scanner's value on the empty bitstring is the
  base's, by `rfl`.
- `scanSem_cons` — one step: `scanSem … ![b :: w]` is the semantic step
  at `b` and `scanSem … ![w]`.
- `scanSem_eq` — `scanSem base step₀ step₁ growth ![w] =
  scanFold base step₀ step₁ w`, by `List.rec` from the two above. It
  holds for every `growth`, the bound child being a side condition on
  admissibility rather than part of a tree's value.
- `scannerSem_eq_eval` — the meaning read at the raw tree is the meaning
  the expression of `C` carries, as `Cobham.combSem_eq_eval` states for
  the scan.

## Rebuilding the recognizer

`Cobham/Tree.lean` is rewritten to build its scan from the combinator.

`Cobham.combFalseStep` and `Cobham.combTrueStep` drop from arity two to
arity one: `proj 2 1` becomes `proj 1 0`, `falseAt 2` becomes
`falseAt 1`, and each `comp 2 k` node becomes `comp 1 k`. Neither
references slot zero at present, so the rewrite removes an argument
neither reads. `Cobham.cond` and `Cobham.pred` keep their arities, being
applied rather than lifted.

`Cobham.combRaw` becomes
`scanRaw (oneAtRaw 0) combFalseStepRaw combTrueStepRaw 1`,
`Cobham.combSem` becomes the corresponding `scanSem`, and `Cobham.comb`
becomes `scanner` at the same `growth = 1` with the length bound
`Cobham.comb` already discharges, unchanged.

`Cobham.combSem_cons_false` and `Cobham.combSem_cons_true` become
corollaries of `scanSem_cons`: each keeps its present statement, and its
proof loses the `change` to the step's own application, retaining the
`generalize` of the recursive value and the match on it.

Every statement from `Cobham.combSem_eq` downward — the scan's
characterization against `BinTree.depth` and `BinTree.ok`, the one-test,
the recognizer, its correctness on both branches, and
`Cobham.isTree_smashFree` — keeps its present form and its present
proof.

## Verification

`GebTests/Mathlib/Computability/Cobham/Scan.lean` mirrors the new
module: a scanner over named steps, its meaning checked against
`scanFold` on the words of a fixed small length, and a scanner at
`growth = 0` exercising `boundRaw`'s base case. The existing
`GebTests/Mathlib/Computability/Cobham/Tree.lean` is unchanged, and its
passing is the evidence that the rewrite of `Tree.lean` preserves the
recognizer.

`docs/index.md` gains the entry for `Scan.lean` beside the entry for
`Tree.lean`.

Every declaration measures `[propext, Quot.sound]`, which `lake lint`
settles.

## Risks

Two are settled by building before the rest of the branch is written.

`Cobham.isTreeRaw`, `Cobham.eqOneRaw` and the two step expressions
discharge admissibility by `decide`, and after the rewrite the trees
they contain include `scanRaw` applied to named constants. `decide`
evaluates in the kernel, so an `@[expose] def` should unfold; that is a
prediction, and `Nat.land` failing to reduce during elaboration is the
same class of failure the ranked encoding branch hit. `Cobham.combRaw`'s
own `by decide` is replaced by `scanValid` regardless, the arguments
there being variables.

The arity-one rewrite of the two step expressions changes how a step's
meaning reduces on a symbolic word, which is what the present proofs of
`combSem_cons_false` and `combSem_cons_true` depend on.

## Out of scope

The generic ranked recognizer as a scanner instance, which becomes its
own TODO.md entry, depending on this branch and on B1. Recorded with
it: the state layout is undecided, and the step must dispatch on `2 ^
width` block values against `RankedAlphabet.arOf`, so the dispatch is
built by recursion on `width` rather than written out.

The Bellantoni-Cook port of the combinator remains deferred, as
TODO.md records, its signature being over arities in normal and safe
position.

Nothing in this branch measures a number of reduction steps or an
amount of space, which is B5.
