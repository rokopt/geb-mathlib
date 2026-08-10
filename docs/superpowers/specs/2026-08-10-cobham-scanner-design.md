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
three deliverables: the scan combinator and the present `Cobham.isTree`
rebuilt on it. The generic ranked recognizer that entry also lists moves
to an entry of its own, since nothing depends on it — B3 needs the
combinator, B4 needs B1's `RankedAlphabet.Binary.valid_iff`, and B5 needs
a recognizer of either width — and it carries an unsettled design
decision of its own, the layout of `RankedAlphabet.Scan` as a bitstring.

The branch touches no file B1 touches: the new module imports
`Geb.Mathlib.Computability.Cobham.Basic` alone, and the rebuilt
`Cobham/Tree.lean` keeps its present imports plus the new module. B1's
commits are confined to `Geb/Mathlib/Data/Tree/Ranked/` and its index
files. The branch is nonetheless stacked on B1, which sequences review
rather than recording a dependency.

Rewriting TODO.md § Extensions of the tree recognizers is a deliverable
of this branch, not a promise made by it: left unedited, that entry
states that B2 delivers the ranked recognizer, and names a `Scanner`
structure this branch deliberately does not build.

Every definition below is novel. The recursion scheme they package,
bounded recursion on notation, is the transcription of [Cobham1965]
already carried by `Cobham.sig` and `Cobham.evalRec`; `List.foldr` is
mathlib's. No definition or theorem in this branch is taken from
published mathematics, so the branch adds no key to
[docs/references.bib](../../references.bib).

The design below was settled by building it: every definition and every
statement in the two sections that follow compiles at variable base,
steps and growth, and `Cobham.scanner`, `Cobham.scanSem_cons` and
`Cobham.boundSem_eq` each measure `[propext, Quot.sound]`.

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

The raw layer takes bare trees and the expression layer takes `COf`
values, as `Cobham.combRaw` and `Cobham.comb` already do. The two meet at
index equations, which admissibility of a node requires alongside the
children's own (`SlicePFunctor.wValid_mk` constrains
`wIndexRoot ∘ children`, not only their validity):

- `boundRaw (growth : ℕ)` — `succ true` iterated `growth` times over
  `proj 1 0`, by `Nat.rec`, of arity one. It is the node's bound child,
  returning `growth` bits more than the recursion variable. `growth = 0`
  is the `Nat.rec` base, the bare projection.
- `wIndexRoot_boundRaw`, `wValid_boundRaw`, `arity_boundRaw` — its arity
  is one and it is admissible, at every growth. The arity is a case
  split, not a recursion: both `Nat.rec` branches are nodes whose shape
  `q` sends to one. Admissibility is a `Nat.rec`.
- `liftRaw (e : sig.toPFunctor.W)` — the `comp 2 1` node with head `e`
  and sole argument `proj 2 1`, carrying a step of arity one into the
  shape `evalRec` applies; `wIndexRoot_liftRaw` and `wValid_liftRaw`,
  the latter taking `wIndexRoot e = 1`.
- `scanRaw (base step₀ step₁ : sig.toPFunctor.W) (growth : ℕ)` — the
  `boundedRec 0` node over
  `![base, liftRaw step₀, liftRaw step₁, boundRaw growth]`;
  `wIndexRoot_scanRaw` and `wValid_scanRaw`, the latter taking six
  hypotheses: each of base, `step₀` and `step₁` admissible and at its
  prescribed arity, zero for the base and one for the steps.
- `scanRawOf (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : sig.W`
  — the node over expressions, its admissibility from `wValid_scanRaw`
  at the components' own; `arity_scanRawOf`, by `rfl`.

Each meaning is read at the raw tree and transported along the
composition of `fst_eval` with the arity equation, in one step rather
than two:

- `baseSem (base : COf 0)` —
  `transport ((fst_eval base.1.1).trans base.2) (eval base.1.1).2`
  at `Fin.elim0`.
- `stepSem (step : COf 1) (r : List Bool)` — the same at `![r]`.
- `scanStepSem (step₀ step₁ : COf 1) (b : Bool) (r : List Bool)` — the
  bit selects which step reads the state.
- `boundSem (growth : ℕ) : Sem 1` — the bound child's meaning.
- `scanSem (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : Sem 1`.

The single composed transport is forced, and is the branch's one
non-obvious design constraint. `Cobham.combSem` transports along
`fst_eval` alone because at a named constant every index reduces to a
literal, so `C.eval`'s own transport disappears by proof irrelevance. At
a variable expression nothing reduces, and a transport along a composite
equality is not definitionally the composition of two transports. Stating
the meanings in the composed form keeps `scanSem_nil` a `rfl` and lets
`scanSem_cons`'s `change` land; the bridge back to `C.eval` is then a
theorem rather than the definition, and `transport_trans` — proved by
`subst` — is what supplies it.

- `scan base step₀ step₁ growth (hbound) : C` — the expression, its
  `RecBounded` discharged from `hbound`, `boundSem_eq`, and the
  components' own, through `recBounded_boundRaw` and
  `recBounded_liftRaw`.
- `scanOf … : COf 1`.

`hbound` is stated over `scanSem` directly, as
`∀ w, (scanSem base step₀ step₁ growth ![w]).length ≤ w.length + growth`.
This is not circular: `Cobham.eval` asks only for admissibility as a
`sig`-tree, not for the recursion bound, so a scanner is characterized
before the expression carrying its bound exists — which is also why
`Cobham.comb` can establish its own bound by rewriting through
`combSem_eq`. No separate fold function appears in the interface;
`scanSem_eq` characterizes the value as a fold, rather than the fold
being what the caller must bound.

The bound is an argument to `scan` rather than a field of a structure: a
field stating it cannot name a function of the structure being declared.

`growth` is a natural number rather than an expression of arity one with
a semantic bound of its own. A constant covers `Cobham.comb` at one, a
fold at a finite carrier at the width of that carrier's encoding, and a
ranked scan at a multiple of the alphabet's width. It costs the four
`boundRaw` lemmas above; an expression-valued bound would instead oblige
every instance to supply a bound term and characterize its meaning.

## Main statements

- `scanSem_nil` — the scanner's value on the empty bitstring is the
  base's, by `rfl` in the composed-transport form.
- `scanSem_cons` — one step: `scanSem … ![b :: w]` is `scanStepSem` at
  `b` and `scanSem … ![w]`. Proved by `change` to the step's own
  application in the composed-transport form, then `congrArg` over
  `(fun _ : Fin 1 ↦ r) = ![r]`, which is a `funext` and not a `rfl`.
  This is where the difficulty of the module sits.
- `scanSem_eq` — `scanSem base step₀ step₁ growth ![w] =
  w.foldr (scanStepSem step₀ step₁) (baseSem base)`, by `List.rec` from
  the two above. It holds for every `growth`, `evalValue`'s `boundedRec`
  clause not consulting its bound child.
- `boundSem_eq` — the bound child prepends `growth` bits to the
  recursion variable, by `Nat.rec`. Stated at an arbitrary environment,
  which is the form the recursion bound reads it at; stated at `![u]` it
  does not match the goal `RecBoundedValue` presents.
- `baseSem_eq_eval`, `stepSem_eq_eval` — each meaning is the one the
  expression of `C` carries, by `transport_trans`. These are the
  analogue of `Cobham.combSem_eq_eval`, which is a `rfl` only because
  its subject is named.

## Rebuilding the recognizer

`Cobham/Tree.lean` is rewritten to build its scan from the combinator.

`Cobham.combFalseStep` and `Cobham.combTrueStep` drop from arity two to
arity one: `proj 2 1` becomes `proj 1 0`, `falseAt 2` becomes
`falseAt 1`, and each `comp 2 k` node becomes `comp 1 k`. Neither
references slot zero at present, so the rewrite removes an argument
neither reads. `Cobham.cond` and `Cobham.pred` keep their arities, being
applied rather than lifted. `combFalseStepOf` and `combTrueStepOf`
become `COf 1`, and the docstrings naming their arity — theirs and the
module docstring's entry for them — are corrected.

`Cobham.combRaw` becomes
`scanRaw (oneAtRaw 0) combFalseStepRaw combTrueStepRaw 1`,
`Cobham.combSem` becomes the corresponding `scanSem`, and `Cobham.comb`
becomes `scan` at the same `growth = 1` with the length bound
`Cobham.comb` already discharges.

`Cobham.combSem_cons_false` and `Cobham.combSem_cons_true` keep their
present statements and become corollaries of `scanSem_cons`; each
present proof opens with a `change` naming an arity-two application,
which the rewrite invalidates, so each is restated against the
combinator and retains only the `generalize` of the recursive value and
the match on it.

Every statement from `Cobham.combSem_eq` downward — the scan's
characterization against `BinTree.depth` and `BinTree.ok`, the one-test,
the recognizer, its correctness on both branches, and
`Cobham.isTree_smashFree` — keeps its present form.

## Verification

`lake build` is the evidence for every claim above that a proof is
preserved or a `change` still lands; `lake lint` settles that each
declaration measures `[propext, Quot.sound]`.

`GebTests/Mathlib/Computability/Cobham/Scan.lean` mirrors the new module.
It exercises what carries no universal theorem behind it: the bound
child, through `boundSem_eq` at a growth other than one and at zero, and
the `RecBounded` discharge, by forming a scanner whose bound is
discharged from `scanSem_eq`. Sampling `scanSem` against its own fold
adds nothing `scanSem_eq` does not already prove for every word, so the
sampling it does carries a different load: that the meaning reduces in
the kernel at named steps, and that the bit selects the intended step —
a transposition of the two step children is invisible to type checking
and to any test using one step twice.

The existing `GebTests/Mathlib/Computability/Cobham/Tree.lean` is
unchanged, and its passing is the evidence that the rewrite of
`Tree.lean` preserves the recognizer.

`docs/index.md` gains the entry for `Scan.lean`, and the entry for
`Tree.lean` gains the new import in its dependency line.

## Risks

The kernel-reduction risk is settled and was found absent. `decide`
discharges `sig.WValid` of the assembled node and `smashFreeBool` over
it, at a literal growth and at zero, so `Cobham.isTree_smashFree` and
the `by decide` admissibility proofs of `Cobham.isTreeRaw` and
`Cobham.eqOneRaw` survive the rebuild. `Cobham.combRaw`'s own `by
decide` is replaced by `wValid_scanRaw` regardless, its arguments there
being variables.

What remains unsettled is confined to the rebuilt `Tree.lean`: the
arity-one rewrite changes how a step's meaning reduces on a symbolic
word, and `combSem_cons_false` and `combSem_cons_true` are the two
proofs that depend on it.

## Out of scope

The generic ranked recognizer as a scanner instance, which becomes its
own TODO.md entry, depending on this branch and on B1. Recorded with it:
the state layout is undecided, and the step must dispatch on `2 ^ width`
block values against `RankedAlphabet.arOf`, so the dispatch is built by
recursion on `width` rather than written out.

The Bellantoni-Cook port of the combinator remains deferred, as TODO.md
records, its signature being over arities in normal and safe position.

Nothing in this branch measures a number of reduction steps or an amount
of space, which is B5.
