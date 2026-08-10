# The scan combinator over Cobham's class

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [The combinator](#the-combinator)
- [Main statements](#main-statements)
- [Rebuilding the recognizer](#rebuilding-the-recognizer)
- [The roadmap entry](#the-roadmap-entry)
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

No Lean file this branch touches is a Lean file B1 touches: B1's source
commits are confined to `Geb/Mathlib/Data/Tree/Ranked/`,
`GebTests/Mathlib/Data/Tree/Ranked/` and the two `Tree.lean` index
modules above them. The two branches do share `TODO.md` and
`docs/index.md`, and the roadmap entry this branch rewrites is text B1
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
- `scanW (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : sig.W` —
  the node over expressions, its admissibility from `wValid_scanRaw` at
  the components' own; `arity_scanW`, by `rfl`. It is not named `…Of`:
  in this development that suffix means the expression at its declared
  arity, a `COf n`, as `combOf` and `isTreeOf` do.

Each meaning is read at the raw tree. Those of the components are
transported along the composition of `fst_eval` with the component's
arity equation, in one step rather than two:

- `baseSem (base : COf 0)` —
  `transport ((fst_eval base.1.1).trans base.2) (eval base.1.1).2`
  at `Fin.elim0`.
- `stepSem (step : COf 1) (r : List Bool)` — the same at `![r]`.
- `scanStepSem (step₀ step₁ : COf 1) (b : Bool) (r : List Bool)` — the
  bit selects which step reads the state.
- `boundSem (growth : ℕ) : Sem 1` — the bound child's meaning.
- `scanSem (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : Sem 1`.

The composed transport is a choice, and the reason for it is the
branch's one non-obvious constraint. `Cobham.transport` along an
equation whose two sides reduce to the same literal disappears by proof
irrelevance; along an opaque equation it does not, and a transport along
a composite equality is then not definitionally the composition of two
transports. The scan node's own arity reduces to one whatever its
children are, so its transport disappears; a *component's* arity
equation is `base.2` or `step.2` at a variable, which reduces to
nothing. Stating the component meanings in the composed form is what
keeps `scanSem_nil` a `rfl` and lets `scanSem_cons`'s `change` land. The
opposite choice is available — `transport_transport` carries the
equivalence both ways — at the price of making those two proofs
rewrites.

`transport_transport`, proved by `subst`, is a general fact about
`Cobham.transport` and is added to `Cobham/Basic.lean`, beside the
definition it concerns. It is named for its left-hand side, as mathlib's
`cast_cast` is.

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
- `baseSem_eq_eval`, `stepSem_eq_eval` — each component's meaning is the
  one its expression of `C` carries, by `transport_transport`. Unlike
  `scanSem_eq_eval` these are not `rfl`, the component arities being
  opaque.

`scan`'s bound obligation additionally opens by rewriting
`Fin.tail x` to `Fin.tail ![x 0]`, as `Cobham.comb`'s does.

## Rebuilding the recognizer

`Cobham/Tree.lean` is rewritten to build its scan from the combinator.

`Cobham.combFalseStep` and `Cobham.combTrueStep` drop from arity two to
arity one: `proj 2 1` becomes `proj 1 0`, `falseAt 2` becomes
`falseAt 1`, and each `comp 2 k` node becomes `comp 1 k`. Neither
references slot zero at present, so the rewrite removes an argument
neither reads. `Cobham.cond` and `Cobham.pred` keep their arities, being
applied rather than lifted. `combFalseStepOf` and `combTrueStepOf`
become `COf 1`.

`Cobham.combRaw` becomes
`scanRaw (oneAtRaw 0) combFalseStepRaw combTrueStepRaw 1`,
`Cobham.combSem` becomes the corresponding `scanSem`, and `Cobham.comb`
becomes `scan` at the same `growth = 1` with the length bound
`Cobham.comb` already discharges. `comb` takes its admissibility from
`wValid_scanRaw` at the components' own proofs, that being what the
combinator supplies; `combRaw` remains a named constant, so `decide`
stays available and is what `isTreeRaw` and `eqOneRaw` continue to use.

`Cobham.combSem_nil` keeps its statement and becomes `scanSem_nil` at
the instance. `Cobham.combSem_cons_false` and
`Cobham.combSem_cons_true` keep their statements and become corollaries
of `scanSem_cons`; each present proof opens with a `change` naming an
arity-two application, which the rewrite invalidates, so each is
restated against the combinator and retains only the `generalize` of the
recursive value and the match on it.

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
- `Tree.lean:120-127` — the two `cons` lemmas described as proved by
  rewriting to the step's own application, which is no longer how they
  are proved.

`Geb/Mathlib/Computability/Cobham.lean` and its `GebTests` counterpart
each gain an import of the new module; `lakefile.toml`'s `globs` build
every module regardless, so nothing fails if this is forgotten.

## The roadmap entry

TODO.md § Extensions of the tree recognizers is rewritten. Left
unedited it states that B2 delivers the ranked recognizer, and names a
`Scanner` structure this branch deliberately does not build. The
rewritten entry:

- describes B2 as the combinator and the rebuilt recognizer, and drops
  the ranked recognizer from it;
- adds the ranked recognizer as its own entry, depending on B2 and B1,
  carrying the two constraints § Out of scope records;
- corrects the count of branches the section opens with, which the split
  falsifies;
- replaces the design paragraph this branch resolves — the length bound
  stated over the fold, and `growth = 0` needing its own clause — with
  nothing, the questions being answered;
- removes the name `Scanner` from the B2 text and from the deferred
  Bellantoni-Cook port, which names the structure that is not built;
- leaves the B3, B4 and B5 dependency lines reading against B2, which
  remain correct: each needs the combinator, and none needs the ranked
  recognizer.

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
topological order requires, and the entry for `Tree.lean` gains the new
import in its dependency line.

## Risks

The kernel-reduction risk is settled and was found absent, at the size
the rebuild actually assembles rather than at a smaller probe. `decide`
discharges admissibility of both steps rewritten to arity one, of the
scan node assembled from them, and of the recognizer built over that
node; and `smashFreeBool` reduces to `true` over both the assembled node
and the recognizer, which is `Cobham.isTree_smashFree`'s own obligation.
The steps carry `condRaw`, itself a `boundedRec` node over nested
`concatCompRaw`, so this is not the two-node probe the first round of
this spec relied on.

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
