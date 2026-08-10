# The scan combinator over Cobham's class

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [The combinator](#the-combinator)
- [Main statements](#main-statements)
- [Rebuilding the recognizer](#rebuilding-the-recognizer)
- [The roadmap and the handoff](#the-roadmap-and-the-handoff)
- [Verification](#verification)
- [Risks](#risks)
- [Out of scope](#out-of-scope)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

One branch over `Geb/Mathlib/Computability/Cobham/`, the item TODO.md
§ Extensions of the tree recognizers records as B2, reduced to two of its
three deliverables: the scan combinator and the present `Cobham.isTree`
rebuilt on it. The generic ranked recognizer that entry also lists moves
to an entry of its own, since nothing depends on it — B3 consumes the
combinator, B4 rewrites the tree layer and reads B1's
`RankedAlphabet.Binary.valid_iff`, and B5 measures a recognizer that
already exists — and it carries an unsettled design decision of its own,
the layout of `RankedAlphabet.Scan` as a bitstring.

No Lean file this branch touches is a Lean file B1 touches: B1's source
commits are confined to `Geb/Mathlib/Data/Tree/Ranked/`,
`GebTests/Mathlib/Data/Tree/Ranked/` and the index modules above them in
both trees. The two branches do share `TODO.md`, `docs/index.md` and the
handoff plan, and the roadmap entry this branch rewrites is text B1
wrote, so they are ordered rather than interchangeable. The branch is
stacked on B1 accordingly.

Every definition below is novel. The recursion scheme they package,
bounded recursion on notation, is the transcription of [Cobham1965]
already carried by `Cobham.sig` and `Cobham.evalRec`; `List.foldr` is
mathlib's. No definition or theorem in this branch is taken from
published mathematics, so the branch adds no key to
[docs/references.bib](../../references.bib).

The design below was settled by building it. Every definition and every
statement named in § The combinator and § Main statements compiles at
variable base, steps and growth, and every declaration's axioms lie in
`{propext, Quot.sound}`.

## The combinator

`Geb/Mathlib/Computability/Cobham/Scan.lean`, importing
`Geb.Mathlib.Computability.Cobham.Basic` alone.

A scanner is a right-to-left fold over a bitstring whose state is itself
a bitstring: a base value, one step per bit read, and a bound on how far
the state can exceed the input. `Cobham.evalRec` supplies the recursion,
peeling the word's last bit at each step and passing the rest of the
word on; the state is the recursive value it passes alongside.

`evalRec`'s step is applied to `Fin.cons v (Fin.cons (ih x) x)`: slot
zero is the rest of the word, slot one the recursive value, slots two
upward the ambient environment. A fold's step is a function of the state
alone, so a scanner's steps are `COf 1` and the node's step children are
those lifted by `comp` with `proj 2 1`. A `COf 2` step would advertise
slot zero, which no fold reads.

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
- `scanW (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : sig.W` —
  the node over expressions, its admissibility from `wValid_scanRaw` at
  the components' own; `arity_scanW` states that its arity is one, by
  `rfl`. It is named rather than written inline at each of its four use
  sites, its term carrying ten arguments; and it is not named `…Of`,
  which in this development means the expression at its declared arity,
  a `COf n`, as `combOf` and `isTreeOf` do. The suffix `W` names the
  slice W-type it lands in, the step between `…Raw` and the member
  of `C`.

The values a base and a step contribute are bitstrings rather than
functions of an environment, and are named `…Word` accordingly. They are
not `…Sem`, which in this development means a `Sem n`, as
`Cobham.predSem`, `condSem`, `combSem`, `eqOneSem` and `isTreeSem` all
are; nor `…Value`, which in `Cobham` already means the one-node,
non-hereditary form of a like-named notion, as `evalValue` and
`RecBoundedValue` do — and `evalValue` returns a `Sem`, so that suffix
would carry the opposite of the distinction being drawn:

- `baseWord (base : COf 0) : List Bool` —
  `transport ((fst_eval base.1.1).trans base.2) (eval base.1.1).2`
  at `Fin.elim0`.
- `stepWord (step : COf 1) (r : List Bool) : List Bool` — the same at
  `![r]`.
- `scanStepWord (step₀ step₁ : COf 1) (b : Bool) (r : List Bool) :
  List Bool` — the bit selects which step reads the state.
- `boundSem (growth : ℕ) : Sem 1` — the bound child's meaning.
- `scanSem (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : Sem 1`.

The component meanings are transported along the composition of
`fst_eval` with the component's arity equation, in one step rather than
two. That composed form is a choice, and the reason for it is the
branch's one constraint that is not read off the signatures.
`Cobham.transport` along an equation whose two sides reduce to the same
literal disappears by proof irrelevance; along an opaque equation it
does not, and a transport along a composite equality is then not
definitionally the composition of two transports. The scan node's own
arity reduces to one whatever its children are, so its transport
disappears; a *component's* arity equation is `base.2` or `step.2` at a
variable, which reduces to nothing. Stating the component meanings in
the composed form is what keeps `scanSem_nil` a `rfl` and lets
`scanSem_cons`'s `change` land. The opposite choice is available —
`transport_transport` carries the equivalence both ways — at the price
of making those two proofs rewrites.

`transport_transport`, proved by `subst`, is a general fact about
`Cobham.transport` and is added to `Cobham/Basic.lean`, beside the
definition it concerns, with its entry in that module's
`## Main statements`. It is named for its left-hand side, as core's
`cast_cast` is.

- `scan base step₀ step₁ growth hbound : C` — the expression, its
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

The bound is an argument to `scan` rather than a field of a structure
because no consumer holds a scanner as a value: each call site supplies
the four components and consumes the resulting expression, so a
structure would add a type whose only use is to be taken apart again. A
field could state the bound — `scanSem` takes exactly the fields that
would precede it — so what rules the structure out is cost, not
whether it can be written.

`growth` is a natural number rather than an expression of arity one with
a semantic bound of its own. A constant covers `Cobham.comb` at one, a
fold at a finite carrier at the width of that carrier's encoding, and a
ranked scan at a multiple of the alphabet's width. It costs the four
`boundRaw` lemmas above together with `boundSem` and its `Nat.rec`
characterization, where a bound child fixed at one bit would discharge
the same obligation with the bare `change` `Cobham.comb` uses today; an
expression-valued bound would instead oblige every instance to supply a
bound term and characterize its meaning.

## Main statements

- `scanSem_nil` — the scanner's value on the empty bitstring is the
  base's, by `rfl` in the composed-transport form.
- `scanSem_cons` — one step: `scanSem … ![b :: w]` is `scanStepWord` at
  `b` and `scanSem … ![w]`. Proved by `change` to the step's own
  application in the composed-transport form, then `congrArg` over
  `(fun _ : Fin 1 ↦ r) = ![r]`, which is a `funext` and not a `rfl`.
- `scanSem_eq` — `scanSem base step₀ step₁ growth ![w] =
  w.foldr (scanStepWord step₀ step₁) (baseWord base)`, by `List.rec`
  from the two above. It holds for every `growth`, `evalValue`'s
  `boundedRec` clause not consulting its bound child.
- `scanSem_eq_eval` — the meaning read at the raw tree is the meaning
  `scanOf` carries, by `rfl`. This is the analogue of
  `Cobham.combSem_eq_eval`, and holds at variable base, steps and growth
  for the reason given above: the scan node's own arity reduces whatever
  its children are. It is the statement every downstream consumer needs,
  every other statement of the module being about `scanSem`.
- `boundSem_eq` — the bound child prepends `growth` bits to the
  recursion variable, by `Nat.rec` whose step opens with a `change`
  exposing the `comp` node's value. Stated at an arbitrary environment,
  which is the form the recursion bound reads it at; stated at `![u]` it
  does not match the goal `RecBoundedValue` presents.
- `baseWord_eq_eval`, `stepWord_eq_eval` — each component's value is
  the one its expression of `C` carries, by `transport_transport`.
  Unlike `scanSem_eq_eval` these are not `rfl`, the component arities
  being opaque.

`scan`'s bound obligation additionally rewrites `Fin.tail x` to
`Fin.tail ![x 0]`, as `Cobham.comb`'s does; `comb` reaches that rewrite
after a `change`, and `scan` before one, the bound child's meaning being
a `Nat.rec` rather than a single `succ` node.

## Rebuilding the recognizer

`Cobham/Tree.lean` is rewritten to build its scan from the combinator.

`Cobham.combFalseStep` and `Cobham.combTrueStep` drop from arity two to
arity one: `proj 2 1` becomes `proj 1 0`, `falseAtRaw 2` becomes
`falseAtRaw 1`, and each `comp 2 k` node becomes `comp 1 k`, with the
matching changes in the expressions built on them. Neither references
slot zero at present, so the rewrite removes an argument neither reads.
`Cobham.cond` and `Cobham.pred` keep their arities, being applied rather
than lifted. `combFalseStepOf` and `combTrueStepOf` become `COf 1`.

`Cobham.combRaw` becomes
`scanRaw (oneAtRaw 0) combFalseStepRaw combTrueStepRaw 1`,
`Cobham.combSem` becomes the corresponding `scanSem`, and `Cobham.comb`
becomes `scan` at the same `growth = 1` with the length bound
`Cobham.comb` already discharges. `comb` takes its admissibility from
`wValid_scanRaw` at the components' own proofs, that being what the
combinator supplies; `combRaw` remains a named constant, so `decide`
stays available and is what `isTreeRaw` continues to use.

`Cobham.combSem_nil` keeps its statement and becomes `scanSem_nil` at
the instance. `Cobham.combSem_cons_false` and
`Cobham.combSem_cons_true` keep their statements and are re-proved as
corollaries of `scanSem_cons`; each present proof opens with a `change`
naming an arity-two application, which the rewrite invalidates, so each
retains only the `generalize` of the recursive value and the match on
it.

Every statement from `Cobham.combSem_eq` downward — the scan's
characterization against `BinTree.depth` and `BinTree.ok`, the one-test,
the recognizer, its correctness on both branches, and
`Cobham.isTree_smashFree` — keeps its present form.

The rebuild falsifies documentation at these sites, each of which is
corrected:

- `Tree.lean:49-50`, `288`, `325` — the two steps described as of arity
  two, and `Tree.lean:274-275`, which describes the recursive value as
  the second of the step's two arguments.
- `Tree.lean:24-25`, `108-109`, `348-349`, `433-434` — the bound child
  described as the successor `S₁`. It becomes `boundRaw 1`, a `comp`
  node of the same meaning but not that tree.
- `Tree.lean:102-111` — `combSem` and `comb`'s meaning described as
  "the same transport along `fst_eval`", which stops holding once
  `combSem` is a `scanSem`.
- `Tree.lean:120-127` and `141-144` — the two `cons` lemmas described as
  proved by rewriting to the step's own application, stated once in the
  implementation notes and once more where `isTreeSem_apply` is said to
  be proved as they are. Only the latter remains true of
  `isTreeSem_apply` itself.

`Geb/Mathlib/Computability/Cobham.lean` and its `GebTests` counterpart
each gain an import of the new module; `lakefile.toml`'s `globs` build
every module regardless, so nothing fails if this is forgotten.

## The roadmap and the handoff

Two transient documents in the working tree describe B2 as pending and
describe it wrongly once this branch lands. Both are corrected here, per
CONTRIBUTING.md § Concern shape, under which no active branch presents
superseded decisions as current.

TODO.md § Extensions of the tree recognizers is rewritten. Left unedited
it states that B2 delivers the ranked recognizer, and names a `Scanner`
structure this branch deliberately does not build. The rewritten
section:

- records B2 as delivered, in the form B1 uses — "**B2 is done.**"
  naming what `Geb/Mathlib/Computability/Cobham/Scan.lean` gives and
  pointing at [docs/index.md](../../index.md) — rather than restating
  it as pending work the same branch commits;
- adds the ranked recognizer as B6, labelled so that it can be cited as
  the others are, depending on B2 and B1, carrying the two constraints
  § Out of scope records;
- removes the section's opening count of branches rather than correcting
  it, and the "part of none of the five" later in the section, per
  CONTRIBUTING.md § Document only the persistent: this branch is itself
  the instance that falsifies such a count, and the members are named
  already;
- removes from the B2 text the two sentences this branch resolves — the
  length bound stated over the fold with `growth = 0` needing its own
  clause, and the `COf 1`-not-`COf 2` reading of `evalRec`'s step —
  these being realized code rather than open questions, together with
  the claim that `combFalseStep` and `combTrueStep` "both reference slot
  1 only", which the arity-one rewrite falsifies;
- removes the name `Scanner` from the B2 text and from the deferred
  Bellantoni-Cook port, which names the structure that is not built;
- leaves the B3, B4 and B5 dependency lines against B2 in place. They
  are not all the same relation: B3 consumes the combinator, while B4
  and B5 are ordered after this branch because each rewrites or measures
  the module it rewrites. None of the three needs the ranked
  recognizer.

[The handoff plan](../plans/2026-08-10-ranked-tree-b2-b5-handoff.md) is corrected
in the same commits and for the same reason. It remains in the tree,
being still needed for B3 to B5, and it is not this branch's to remove.
Its § B2 states the object as a `Scanner` combinator carrying the ranked
recognizer as an instance, prescribes an interface whose bound cannot
name `stepSem`/`baseSem` as fields, and records `growth = 0` as needing
its own clause; that section is replaced by a pointer to the delivered
module. Its two "part of the five" counts go the way TODO.md's do, and
the name `Scanner` goes from its deferral list.

## Verification

`lake build` is the evidence for every claim above that a proof is
preserved or a `change` still lands. `lake lint` settles that every
declaration's axioms lie within the permitted set; it does not measure
them exactly, and several declarations of the module depend on `propext`
alone or on no axiom at all.

`GebTests/Mathlib/Computability/Cobham/Scan.lean` mirrors the new
module. Sampling `scanSem` against its own fold proves nothing
`scanSem_eq` does not already prove for every word, so what the samples
carry is different: that the meaning reduces in the kernel at named
steps, and that the bit selects the intended step — a transposition of
the two step children is invisible to type checking and to any test
using one step twice. The same holds of the `boundSem_eq` samples at a
growth other than one and at zero: `boundSem_eq` is universal, and what
the samples add is kernel reduction at the `Nat.rec` base and at a
successor. Beyond the samples, the module forms a scanner whose bound is
discharged from `scanSem_eq`, which exercises the `RecBounded` path.

The existing `GebTests/Mathlib/Computability/Cobham/Tree.lean` is
unchanged, and its passing is the evidence that the rewrite of
`Tree.lean` preserves the recognizer.

`docs/index.md` gains the entry for `Scan.lean`, placed between the
entries for `Cobham/Basic.lean` and `Cobham/Tree.lean` as its
topological order requires; the entry for `Tree.lean` gains the new
import in its dependency line; and the entry for `Basic.lean` gains
`transport_transport`, that module's interface growing by it.

## Risks

The kernel-reduction risk is settled and was found absent, at the size
the rebuild actually assembles rather than at a smaller probe. `decide`
discharges admissibility of both steps rewritten to arity one, of the
scan node assembled from them, and of the recognizer built over that
node; `smashFreeBool` reduces to `true` over both the assembled node and
the recognizer, which is `Cobham.isTree_smashFree`'s own obligation; and
every `rfl` the existing test mirror asserts reproduces over the
rebuild, both the six on the scan's meaning and the four on the
recognizer's, which reduce further, through `predRaw` and `eqOneRaw`'s
`cond` over the scan's value. That is what lets the mirror stay
unchanged. The steps carry `condRaw`, itself a `boundedRec` node over
nested `concatCompRaw`, so the probe is at the size the rebuild
assembles.

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
