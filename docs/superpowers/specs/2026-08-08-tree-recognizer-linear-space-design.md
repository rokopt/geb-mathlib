# Linear space for the Bellantoni-Cook tree recognizer

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Status](#status)
- [Question](#question)
- [What the recognizer costs](#what-the-recognizer-costs)
- [The four function algebras](#the-four-function-algebras)
- [Why this is not a variant of the algebra we have](#why-this-is-not-a-variant-of-the-algebra-we-have)
- [Cost of Route A](#cost-of-route-a)
- [The class](#the-class)
  - [What is built](#what-is-built)
  - [Reuse](#reuse)
  - [`RecBounded`](#recbounded)
  - [Admissibility](#admissibility)
  - [Derived expressions](#derived-expressions)
  - [Conventions and obligations](#conventions-and-obligations)
- [The recognizer](#the-recognizer)
- [Scope and branches](#scope-and-branches)
- [Deferred](#deferred)
- [Reference status](#reference-status)
- [References](#references)

<!-- END doctoc -->

## Status

Transient per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## Question

`BellantoniCook.isTree` (`Geb/Mathlib/Computability/BellantoniCook/Tree.lean`)
decides `BinTree.Valid`, and its membership in `B` places that decision in
the polynomial-time functions. The licence for that is [HeraudNowak2011]
Theorems 1 and 2 composed with Cobham's theorem, not [BellantoniCook1992]:
`BellantoniCook/Basic.lean`'s docstring records that the class formalized
is that paper's § 3.2 reformulation and not [BellantoniCook1992]'s, the
conditional and the recursion's base case both differing.
`BellantoniCook/Tree.lean`'s docstring makes the same mis-citation and is
corrected on its own bookmark. Two further questions:

1. Is the decision also linear-space?
2. If so, how is a bound on it expressed and proved?

Two routes were considered for question 2.

- Route A. `Cslib.Computability.Machines.Turing.MultiTape.Deterministic`
  carries `ComputableInTimeAndSpace` and `DecidableInTimeAndSpace`.
  Exhibiting a machine for the recognizer and proving both bounds gives
  numbers rather than class membership.
- Route B. A function algebra is contained in the functions computable
  simultaneously in polynomial time and linear space. Defining the
  recognizer there places it in that class the way membership in `B`
  already places it in the polynomial-time functions.

Route B is taken. Route A is deferred to `TODO.md`.

## What the recognizer costs

The scan's value on `w` is `List.replicate (BinTree.depth w + 1) true`
while `BinTree.ok w` holds and `[false]` once it has failed, by
`combSem_eq`, and `BinTree.depth w ≤ w.length` by `List.rec` on the two
`depth` unfoldings, truncated subtraction only lowering the left side. So

    (combSem ![w] ![]).length ≤ w.length + 1

The scan's value is the largest the recognizer builds. It is not the case
that everything around it is bounded: `isTreeRaw` is
`eqOne (pred (comb w))`, and `pred (comb w)` is of length up to `w.length`,
so `eqOne`'s argument grows with the input while its output does not.

That bound is a statement about the value, not about the space of
evaluating the expression, and no claim of the latter is made without a
cost model. Three statements are distinct:

- the length bound displayed above, a corollary of `combSem_eq` and
  `depth_le_length`;
- containment of a function algebra in the functions computable
  simultaneously in polynomial time and linear space, which is what
  Route B delivers;
- a bound on some machine deciding `BinTree.Valid`, which is what Route A
  delivers, and which the language satisfies for reasons stronger than
  anything the expression exhibits: a binary counter decides it in
  logarithmic space.

The answer reaches `isTree` through the decided predicate, not through the
expression. Equal accepted sets would not make the two recognizers equal
as functions; `isTreeSem_eq_ite`, which § Scope and branches adds to both
modules, is what does, and it is what makes the containment Route B
establishes a property of the function `isTree` computes.

No claim of linear time is made. The scan has `w.length` layers and the
layer at depth `k` produces a value of length up to `k + 1`, so an
evaluation that materializes each layer is quadratic; and the class Route
B reaches bounds time polynomially, not linearly.

## The four function algebras

[Strahm2003] § 2 Theorem 1 states four characterizations over binary
words `W`, attributing them to [Cobham1965], [Thompson1972] and
[Ritchie1963]. Writing `[X; OP]` for the smallest set of functions
containing `X` and closed under the operators `OP`:

| Class | Algebra |
| --- | --- |
| `FPtime` | `[ε, I, s₀, s₁, ∗, ×; COMP, BRN]` |
| `FPtimeLinspace` | `[ε, I, s₀, s₁, ∗; COMP, BRN]` |
| `FPspace` | `[ε, I, s_ℓ, ∗, ×; COMP, BRL]` |
| `FLinspace` | `[ε, I, s_ℓ, ∗; COMP, BRL]` |

`∗` is concatenation, `s₀` and `s₁` the two successors on notation, `s_ℓ`
the lexicographic successor, `BRN` bounded recursion on notation and `BRL`
bounded lexicographic recursion. `×` is word multiplication, the
`|y|`-fold concatenation of `x` with itself, so `|x × y| = |x| · |y|`.

Only the left-to-right inclusion of the `FPtimeLinspace` row is used:
every expression of `[ε, I, s₀, s₁, ∗; COMP, BRN]` denotes a function
computable simultaneously in polynomial time and linear space. The licence
is [Strahm2003], whose § 2 defines `BRN` with a length proviso agreeing
with [HeraudNowak2011]'s; [Strahm2010] restates the theorem without
defining either operator, and [Clote1999] Theorem 3.20 is an arithmetic
analogue whose `∗`, `brn` and `×` all differ. Why each of those holds, and
why only the one inclusion is relied on, is recorded in the `note` fields
of the three `docs/references.bib` entries and is not restated here.

The difference between the `FPtime` and `FPtimeLinspace` rows is one
generator: word multiplication is dropped. Why every member of the smaller
algebra has affine growth is an adaptation of [HeraudNowak2011]
Proposition 1, novel in that the source has no `∗` clause: it assigns each
expression a length-bounding polynomial, with `PolC(#) = x₀ · x₁ + 1` and
`PolC(S_b) = x₀ + 1`; adding `PolC(∗) = x₀ + x₁` keeps every `PolC` affine
with non-negative coefficients, that family being closed under the
substitution `PolC(Comp)` performs and under `PolC(Rec …) = PolC(j)`.
Every smash-free expression therefore has an affine length bound. That
bounds output length, which is necessary and not sufficient for the space
claim; the space claim rests on [Strahm2003] Theorem 1(2).

## Why this is not a variant of the algebra we have

`B` is Bellantoni-Cook: two-sorted, unbounded safe recursion, no bounding
term. All four algebras above are Cobham-style: one-sorted, with a bounding
term whose satisfaction is a semantic side condition. [HeraudNowak2011]
§ 3.1 gives the bitstring syntax of the Cobham class `C` — `O`, `Π^i_n`,
`S_b`, `#`, `Comp^n h ḡ`, `Rec g h₀ h₁ j` with `|f(y, x)| ≤ |j(y, x)|` —
and `Rec`'s bound `j` is what `B` was designed to remove. Route B is
therefore built on Cobham's class, not on `B`.

A Bellantoni-Cook-shaped route exists but answers a weaker question.
[Clote1999] Theorem 3.101 ([Bellantoni1992]) gives
`E² = normal ∩ [0, I, S, Pr, K; scomp, sr]`, and `Flinspace = E²` is its
Theorem 3.36, with `S` a single unary successor; Leivant's tiering
formulation in the same section says the same. Against it: `E²` bounds
space with no time bound, so combining it with `B` yields membership in
`P ∩ LINSPACE`, and whether that equals `TISP(nᴼ⁽¹⁾, O(n))` is a standard
open question. The simultaneity the question asks for is lost.

The distance from `sig` is larger than one generator: `sr`
([Clote1999] Definition 3.100) is ordinary primitive recursion with one
step function rather than recursion on notation with two, and the ground
type is `ℕ` rather than bitstrings. An objection that a bitstring
recognizer has no input to read there would be wrong for
[Clote1999] Theorem 3.101, which is over `ℕ` with `|x| = ⌈log(x+1)⌉` and
whose `E²` contains `mod2`, `msp` and `bit` by the proof of its
Theorem 3.36; it holds only against Leivant's formulation over the unary
word algebra, where a numeral's length is its value.

That the equality is not known is standard and is not cited to a source
here; it is stated as the reason for a design choice and nothing
downstream depends on it. [Clote1999] Problem 3.102 and the absence of any
safe characterization of simultaneous polynomial time and linear space in
its § 3.6 are corroborating context.

## Cost of Route A

`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean` defines
`MultiTapeTM`, `Cfg`, `step`, `configs`, `spaceUsed`, `visitedByTapeHead`,
and the four predicates `ComputesInTimeAndSpace`,
`ComputesFunInTimeAndSpace`, `ComputableInTimeAndSpace` and
`DecidableInTimeAndSpace`. It carries no machine constructions, no worked
example machine and no composition combinators, so the recognizer's
machine, its halting proof, its output proof and the cardinality of
`visitedByTapeHead` at the halting step have no existing basis to build
on.

Three further constraints, restated in the `TODO.md` entry:

- Subtree placement. `docs/rules/upstream-eligible.md` bars `Geb/Cslib/`
  from importing `Geb.Mathlib.*` and `Geb/Mathlib/` from importing
  `Cslib.*`, so a statement relating `BinTree.Valid` to
  `ComputableInTimeAndSpace` lands in `Geb/Internal/` and is not
  upstream-eligible as a unit.
- Constructive discipline. `DecidableInTimeAndSpace` is stated over
  `Turing.MultiTapeTM.indicator`, an `open Classical in noncomputable def`.
  Using it imports `Classical.choice`. `ComputableInTimeAndSpace` applied
  to our own decidable indicator avoids that and is the form to use.
- The result is about one machine and one language. It says nothing about
  the expression `isTreeRaw`.

Against those: Route A alone yields an unconditional bound with an
explicit constant, resting on no cited characterization theorem.

## The class

`Geb/Mathlib/Computability/Cobham/Basic.lean`, under `namespace Cobham`,
a second module of the same shape as `BellantoniCook/Basic.lean`.

### What is built

Cobham's bitstring class of [HeraudNowak2011] § 3.1 — `O`, `Π^i_n`, `S_b`,
`#`, `Comp^n h ḡ`, `Rec g h₀ h₁ j` — a transcription, extended by one
generator `∗` for concatenation. `∗` is redundant under `#`, since
`|x ∗ y| = |x| + |y| ≤ |#(S₁x, S₁y)| = (|x|+1)(|y|+1) + 1` bounds the two
lines `f(ε, x) = x`, `f(y·b, x) = S_b(f(y, x))`. [Strahm2003] states the
corresponding fact for its own generators, that "word concatenation `∗` is
redundant in the presence of word multiplication `×`, and we have included
it in the formulation of this theorem for reasons of uniformity only",
which is the reason this signature carries both. It is not redundant
without `#`: every `PolC` built from `O`, `Π` and `S_b` alone is a single
variable plus a constant, or a constant, and `PolC(∗) = x₀ + x₁` is not.
Carrying it is what lets one signature present both rows of the table,
`#` standing in the `FPtime` row for [Strahm2003]'s `×`, the two being
interchangeable as generators of that class while denoting different
operations: [HeraudNowak2011]'s `C` carries `#` and no `×` and is the
polynomial-time functions by Cobham's theorem, which its § 3.1 states and
does not prove, while [Strahm2003] Theorem 1(1) is that class with `×` and
no `#`.

`Cobham.C := {e : sig.W // RecBounded e}` denotes Cobham's class of
functions, `∗` being redundant under `#`, over a syntax strictly larger
than [HeraudNowak2011]'s `C`, whose name it takes. `eval` and `arity`
reach it through `Subtype.val`, the raw tree sitting at `e.1.1`.
`Cobham.SmashFree`, a hereditary
decidable predicate, picks out the subalgebra
`[ε, I, s₀, s₁, ∗; COMP, BRN]` of [Strahm2003] Theorem 1(2). A top-node
test would not: only a hereditary one excludes `#` from subterms.

`smash` is carried so that `TODO.md` § Bellantoni-Cook item 3's
translations are served, both of them needing `#`: the `Poly → C` encoding
that builds `Rec` bounds, and [HeraudNowak2011] § 4's `B → C(cond)`, whose
bound uses `#` directly.
No appeal to `docs/rules/lean-coding.md` § Structure and typeclass
patterns' rule against weakening a standard interface is made:
`[ε, I, s₀, s₁, ∗; COMP, BRN]` is itself a named standard object, so a
module transcribing that alone would weaken nothing.

`Cobham.COf n`, the analogue of `BCOf n s`, is the type of an expression
at a reduced arity. Two devices sit beside it and are not the same thing:
the meanings `combSem`, `eqOneSem` and `isTreeSem` are ascribed at reduced
arity so that rewriting under the arity type-checks, and named `def`s with
values (`combOf`, `eqOneOf`, `isTreeOf`, and the test module's own) are
what `lake shake` sees, a type being no anchor for that.

### Reuse

`SlicePFunctor` with its `W` and `Decidable` modules is the shared layer,
and both modules instantiate it. Nothing in `BellantoniCook/Basic.lean`
above that layer is parameterized over the index type: `Shape`,
`Direction`, `rc`, `q`, `sig`, `sigFinitary`, `compChildren`, `BC`,
`BC.arity`, `BCOf`, `Sem`, `transport`, `evalRec`, `evalValue`,
`evalStep` and `BC.eval` are specific to `ℕ × ℕ` and to that shape set,
and their Cobham counterparts differ throughout: the index is `ℕ`, `Sem n`
is `(Fin n → List Bool) → List Bool` with one environment, `Direction` of
`comp` is `Unit ⊕ Fin m` with one argument vector, `Rec` has four
children, and the arity relation is `a_h = a_g + 2 = a_j + 1` over a
single `ℕ`.

### `RecBounded`

`RecBounded` is the side condition `|f(y, x)| ≤ |j(y, x)|` at every `Rec`
node, hereditarily. It is a fold over the term, expressed through
`SlicePFunctor.W.RecProp` (`Geb/Mathlib/Data/PFunctor/Slice/W.lean`),
whose step receives the children as `sig.W` elements so that `eval` is
available on them. `Geb/Mathlib/Data/PFunctor/Presheaf/W.lean`'s
`IsHereditarilyNatural` instantiates the same pattern, including the
`compatible_iff … .mp x.2` idiom and the `∀ b, ih b` conjunct, and is the
model. It is a `Prop` in a subtype, so it is erased, needs no
decidability, and does not obstruct reduction. [HeraudNowak2011] § 1
states only that the condition "does not allow for an automatic procedure
to check whether a program satisfies or not the conditions to be in
Cobham's class"; no stronger undecidability claim is made here.

Four costs, each budgeted:

- The step cannot match on the shape in place. `BellantoniCook/Basic.lean`
  records why `evalValue` is separate from `evalStep`: the match on
  `Shape` must generalize the compatibility hypothesis, which arrives
  bundled. `RecBoundedValue`, taking the shape, the children and the index
  equation, mirrors that split and is `Prop`-valued and so
  `UpperCamelCase`. The `Step` suffix is not the one to take:
  `BellantoniCook.evalStep`, `SlicePFunctor.wValidStep` and
  `wIndexStep` all name the bundled half, which is what `W.RecProp`
  receives, and this is the unbundled half `evalValue` names.
- The transport is not the one `evalValue` performs. There the index
  equation arrives from `compatible_iff`; here the children are trees, so
  `SlicePFunctor.W.comp_elim` is needed first to relate a child's
  evaluated index to its `wIndex`.
- Every committed term carries its own `RecBounded` proof. Beyond `pred`,
  `cond` and `comb`, that is `zeroAt`, `oneAt`, `falseAt`, `inc`, `dec`,
  `predPred`, the two `comb` steps, `eqOneInner`, `eqOne` and `isTree`:
  fourteen. `recBounded_mk` is written first so that each is one line. It
  is stated in raw form rather than at `W.mk`, since every committed term
  is `⟨WType.mk a f, _⟩`, which is already destructured, so `WType.rec`
  iota-reduces and the raw form closes by bare `rfl`.
  `SlicePFunctor.W.recProp_mk` needs its `obtain` only because its subject
  is `W.mk x` at a bundled `x`.
- Of those fourteen, only three carry a new inequality. `zeroAt`, `oneAt`,
  `falseAt` and `inc` contain no `Rec` node, so their obligation is the
  vacuous conjunction over children; `dec`, `predPred`, the two `comb`
  steps, `eqOneInner`, `eqOne` and `isTree` only re-discharge the `pred`,
  `cond` and `comb` nodes they contain. The three are semantic rather than
  arithmetic, each gated on its own `Sem` equation: `pred` on
  `predSem_eq` with `List.length_tail`, `cond` on `condSem_eq` with a
  three-way split and `List.length_append`, `comb` on `combSem_eq` with
  `depth_le_length` and `List.length_replicate`. Where `ℕ` arithmetic does
  appear it is discharged by `omega` or explicit cases, per
  `docs/rules/lean-coding.md` § Constructive-only Lean code, which records
  that mathlib's `Nat` order API interleaves choice-free and
  choice-dependent lemmas under no separating convention.

`SmashFree` is not a `RecProp`; a `Prop` fold carries no decision
procedure. It is one artifact, not two: `smashFreeBool` is the
`WType.elim` fold into `Bool` rejecting a `#` node and conjoining its
children's values, and `SmashFree e := smashFreeBool e.1.1 = true`, so no
`_eq_true_iff` bridge exists to state. Decidability is
`inferInstanceAs (Decidable (smashFreeBool _ = true))` rather than
`inferInstance`, which does not see through the definition.
`SlicePFunctor.wValidBool` is the shape it follows, not a
lemma it reuses, that one being about admissibility alone.

### Admissibility

Arity admissibility is `sig.W`, decided by `decide` through
`SlicePFunctor.wValidBool` and `wValidBool_eq_true_iff`, as
`⟨_, by decide⟩` decides it in `BellantoniCook/Tree.lean`. `RecBounded` is
never decided; it is always proved.

Cobham terms are larger. `pred` is `Rec O Π^0_2 Π^0_2 Π^0_1`, five nodes
where `B`'s `pred` is one; `cond` is eleven where `B`'s is one; `comb` is
seventy-five where `combRaw` is thirty-six; and `isTree` is about a
hundred and fifty against `isTreeRaw`'s seventy, which already decides.
`comb` grows by `2.08` and `isTree` by `2.14`. Measurement at
v4.33.0-rc2 under the instances of § Scope and branches decides synthetic
`sig`-trees of 262 nodes in under a second at default `maxHeartbeats`, and
Cobham's direction type (`Unit ⊕ Fin m`, `Fin 4`) is cheaper than `B`'s
(`Unit ⊕ Fin m ⊕ Fin k`, `Fin 3`), so no fallback is planned. Should one
be wanted, it is `maxRecDepth` or `maxHeartbeats` on the declaration:
`decide +kernel` does not help, the proof term being
`of_decide_eq_true rfl` either way and the kernel re-checking it.

### Derived expressions

- `pred`, [HeraudNowak2011] § 4's `Rec O Π^0_2 Π^0_2 Π^0_1`, bounded by
  its argument. A transcription.
- `cond`, the four-argument conditional with three branches, transcribed
  from [HeraudNowak2011] § 4's `Rec Π^0_3 Π^4_5 Π^3_5 j` and agreeing with
  `B`'s `cond` as `combSem_cons_false` and `combSem_cons_true` pin it:
  `Rec` peels the last bit, so `Π^4_5` fires on `s₀` and `Π^3_5` on `s₁`,
  and under the head-is-last-bit convention that is the Lean
  `false :: _ ↦ y 3`, `true :: _ ↦ y 2`. It is transposed against
  [HeraudNowak2011] § 3.2's prose for `B`, which is why the paper's own
  `B` clause cannot be used to check it;
  `BellantoniCook/Basic.lean`'s docstring already records that this
  repository follows the authors' Coq ordering, and § 4 is on that side.
  Only the bound is novel: [HeraudNowak2011] uses
  `#(S₁x, #(S₁y, S₁z))`, the `S₁` wrappers keeping it non-degenerate at
  `ε`, and the smash-free replacement is the concatenation of the three
  branch arguments, which dominates because the value is one of `x`, `y`,
  `z` and `|x ∗ y ∗ z| = |x| + |y| + |z|`.
- `condSem_eq` and `predSem_eq`, the meaning of each at its arity, the
  latter as `predSem u = u.tail` by cases on `u`. They are needed for the
  two bounds above and again in § The recognizer, where the unfolding
  lemmas close by `rw` rather than by `rfl`, `cond` and `pred` being `Rec`
  nodes here and generators in `B`.

### Conventions and obligations

The bit-order convention determines every unfolding lemma and is recorded
in the module docstring: [HeraudNowak2011]'s `S_b(x) = xb` appends and
`Rec` peels the last bit, while the Lean `succ b` is `b :: y` and `pred`
is `.tail`, so the list head is the word's last bit. The one clause where
that convention can silently invert is `∗`, whose meaning is therefore
written out beside it as `fun x ↦ x 1 ++ x 0`. It is also the convention
under which `BinTree.depth`'s reading matches the recursion.

`Cobham/Basic.lean` imports `Geb.Mathlib.Data.PFunctor.Slice.W`,
`Geb.Mathlib.Data.PFunctor.Univariate.Finitary`,
`Geb.Mathlib.Data.FinEnum` and `Mathlib.Logic.Equiv.Fin.Basic`, the last
because the `Rec` evaluator needs `Fin.cons`, as
`BellantoniCook/Basic.lean` imports it for the same reason.
`Geb.Mathlib.Data.PFunctor.Slice.Decidable` is imported too, unlike in
`BellantoniCook/Basic.lean`: that module commits no terms, while this one
commits `pred` and `cond` as `⟨_, by decide⟩`, and `decidableWValid` lives
there and nowhere else. `Cobham/Tree.lean` imports `Cobham.Basic` and
`Geb.Mathlib.Data.Tree.Preorder`. `Basic.lean` carries
`open scoped FinEnum`, without which mathlib's instances win resolution
and its `by decide` sites acquire `Classical.choice`; `Tree.lean` does not
need it, instance selection for `sig.B` being fixed where `sigFinitary`
elaborates.
Each import is `public import` where a caller of the module needs it and
plain `import` otherwise; all lie within
`docs/rules/upstream-eligible.md`'s allowed set for `Geb/Mathlib/`.

`@[expose]` sits on the counterparts of the declarations
`BellantoniCook/Basic.lean` exposes — its `Direction`, `rc`, `q`, `sig`,
`compChildren`, `BC`, `BC.arity`, `BCOf`, `Sem`, `transport`, `evalRec`,
`evalValue`, `evalStep` and `BC.eval` —
because the unfolding lemmas of § The recognizer close across the module
boundary. Removing one fails at `lake build` and not at the language
server.

Both modules are held to `{propext, Quot.sound}` and are not admitted to
`GebMeta.classicalAllowedModules`. Module docstrings carry every section
`docs/rules/lean-coding.md` § Documentation makes mandatory where
non-vacuous, tags included, and name declarations rather than repository
paths. Their reference sections cite, each with the `note` field
§ Reference status describes: `Strahm2003`, `Strahm2010`, `Clote1999`,
`HeraudNowak2011`, `Thompson1972`, `Ritchie1963`, `Cobham1965` and
`Bellantoni1992`.

## The recognizer

`Geb/Mathlib/Computability/Cobham/Tree.lean`. `comb`, `eqOne` and
`isTree` transcribe from `BellantoniCook/Tree.lean` onto `Rec`, `cond` and
`pred`. They are novel as expressions of this algebra; the function they
compute is the one `BellantoniCook/Tree.lean` already defines. `comb`'s
bound is `S₁` itself, of arity one and so needing no projection, giving
`|y| + 1`. It is novel.

The correctness argument does not transfer from the existing module. Its
`combSem` is `(BC.eval comb).2`, a different expression in a different
signature under a different evaluator, so no transfer lemma is planned —
that is the cross-algebra translation § Scope and branches puts out of
scope. This module re-proves its own analogue of `combSem_eq`: the scan
computes `BinTree.depth` in unary offset by one while `BinTree.ok` holds,
and `[false]` once it has failed. Its `0 / 1 / m+2` split for the
two-predecessor guard is the existing proof's, but the guard now reduces
through an `evalRec` fold and a `transport` cast rather than through a
primitive `.tail`, so each branch opens with `simp only [predSem_eq]` —
`rw` would rewrite only the outer occurrence and leave the inner one —
before the existing rewrites expose a `List.replicate` constructor for the
`cond` match. `predSem_eq` as `.tail` leaves `List.tail_replicate`
applicable in `isTreeSem_eq_singleton_iff_valid`, which additionally needs
this module's analogue of `eqOneSem_env`, the argument arriving as
`fun _ ↦ …` rather than `![…]`.

The `RecBounded` obligation for `comb` follows from this module's
`combSem_eq` together with `BinTree.depth_le_length`, the lemma
`feat/tree-depth-le-length` adds for this bound.

The concluding statement is that the recognizer accepts exactly
`BinTree.Valid`, together with `SmashFree` by `decide`. With
[Strahm2003] Theorem 1(2)'s left-to-right inclusion cited, that places the
decision in the functions computable simultaneously in polynomial time and
linear space. The recognizer's output is `[true]` or `[]`, so the
linear-growth qualifier [Clote1999] Theorem 3.20 carries is satisfied.

The module's implementation notes record the distinction § What the
recognizer costs draws, between a bound on a value and a bound on
evaluating an expression, over this module's own `combSem`. They do not
restate the `BellantoniCook` inequality, which this module's imports do
not reach and which no committed declaration would prove.

Proofs are driven by explicit recursor applications per
`docs/rules/lean-coding.md` § Recursion and induction through recursors:
`List.rec` for `depth_le_length`, and `sig.W`'s recursor for statements
over terms. The object-language `Rec` is not a Lean recursor and does not
discharge that rule.

## Scope and branches

`TODO.md` § Bellantoni-Cook item 3 is Cobham's class and the translations
of Theorems 1 and 2. Its class half is discharged by `feat/cobham-class`,
which therefore carries the rewrite of item 3 to the translations alone,
recording that they additionally need a `∗` case in the `C → B` direction
and whether item 3's stated dependence on items 1 and 2 still holds. The
section's opening line, which scopes its items to
`BellantoniCook/Basic.lean` and is already falsified by its own item 1, is
restated there as covering each item's own destination.

Six bookmarks. Independent ones branch from `main` directly; only
`refactor/finenum-sum-instance`, `feat/cobham-class` and
`feat/cobham-tree-recognizer` form a chain. CONTRIBUTING § Repo structure
puts topic branches per PR-candidate, so independent candidates are not
serialized behind each other.

| Bookmark | Depends on |
| --- | --- |
| `doc/todo-cobham-deferrals` | — |
| `fix/bc-tree-polytime-citation` | — |
| `feat/tree-depth-le-length` | — |
| `refactor/finenum-sum-instance` | — |
| `feat/cobham-class` | `refactor/finenum-sum-instance` |
| `feat/cobham-tree-recognizer` | the two above it |

`feat/cobham-tree-recognizer` has two parents. No repository document
covers that shape: `docs/process.md` § main and integration documents
fan-in for regenerating `integration` from `main` plus topic branches, not
for a topic branch with two topic-branch parents. It is workable —
`scripts/rebase-topics.sh` rebases roots and preserves parent structure —
under two constraints: both parents land on `main` before this bookmark's
PR means anything, and the merge goes stale if either is rewritten. The
policy question goes to § Deferred.

The spec is added in the first commit of `feat/cobham-class` and removed
in the final commits of `feat/cobham-tree-recognizer`, the root and tip of
the chain it describes; the four independent bookmarks carry no spec, none
of them being creative work that needs one. The removal requires
`feat/cobham-tree-recognizer` to be rebased onto a `main` that has
absorbed the adding commit. CONTRIBUTING § Concern shape states its
ordering for a workstream that is one branch and does not cover a
multi-branch series. No precedent supports a wider spread: `main` carried
several specs at once only before that ordering was introduced, and every
spec since has been removed before the next was added. Confining the spec
to the chain keeps the arrangement inside the rule rather than executing
an unadjudicated one, which § Deferred asks to have settled. The plan
follows the spec, on the same two bookmarks.

Independence holds for the Lean sources. Four bookmarks touch `TODO.md`
and three touch `docs/index.md`, so those files conflict textually
whichever lands second, and the order is stated at push time.

Per-bookmark contents:

- `doc/todo-cobham-deferrals`: all four § Deferred entries, no code; one
  concern, recording this series' deferrals. It also adds the
  `BeckmannBussFriedmanMuellerThapen2017` entry to `docs/references.bib`,
  its text being the only one that cites it. Route A goes under `TODO.md`
  § The Bellantoni-Cook tree recognizer, whose opening line "Five items
  over `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`" this branch
  replaces with the property its items share: Route A is a sixth and is
  not over that file.
- `fix/bc-tree-polytime-citation`: `BellantoniCook/Tree.lean`'s module
  docstring attributes the polynomial-time characterization of `B` to
  [BellantoniCook1992], while `BellantoniCook/Basic.lean`'s docstring
  records that the class formalized is [HeraudNowak2011] § 3.2's
  reformulation and not that paper's. The licence is [HeraudNowak2011]
  Theorems 1 and 2 composed with Cobham's theorem. This is a defect in
  committed content and is independent of the rest of the series. It also
  adds `[HeraudNowak2011]` to that docstring's reference section, and
  `isTreeSem_eq_ite` for `BellantoniCook.isTreeSem` with its main-statement
  and `docs/index.md` entries, that docstring being open on this branch
  already.
- `feat/tree-depth-le-length`: `BinTree.depth_le_length` in
  `Geb/Mathlib/Data/Tree/Preorder.lean`, its main-statement entry, its
  `GebTests` mirror, and its `docs/index.md` entry.
- `refactor/finenum-sum-instance`: in `Geb/Mathlib/Data/FinEnum.lean`,
  scoped choice-free `FinEnum.unit` (`card := 1`,
  `equiv := finOneEquiv.symm`), `FinEnum.finSum` from
  `[FinEnum α] [FinEnum β]` as `(Equiv.sumCongr _ _).trans finSumFinEquiv`,
  and `FinEnum.finFin` moved from `BellantoniCook.finEnumFin`;
  `finEnumCompDirection` replaced by them; `BellantoniCook/Basic.lean`'s
  docstring updated and given the `Geb.Mathlib.Data.FinEnum` import and
  `open scoped FinEnum` it does not currently carry; that file's own
  module docstring updated, its title, main-definitions list and tags all
  naming only `Decidable` instances today; `docs/index.md`'s axiom
  sentence for it, which names `finEnumCompDirection`; test mirror; the
  `TODO.md` trigger deleted. Both mathlib instances are unusable:
  `FinEnum.sum` and `FinEnum.punit` route through `ofList`, and
  measurement at v4.33.0-rc2 puts `FinEnum Unit` and
  `FinEnum (Unit ⊕ Fin 3)` at `{propext, Classical.choice, Quot.sound}`
  against the hand-built `{propext}` and `{propext, Quot.sound}`. Scoping
  alone does not settle it: without `open scoped FinEnum` at the consumer,
  mathlib's instances win, so `sigFinitary` and through it every
  `by decide` in both modules would acquire `Classical.choice`, surfacing
  only at `lake lint`. The `TODO.md` trigger names a second consumer of
  either `finEnumFin` or `finEnumCompDirection`; `feat/cobham-class` is a
  second consumer of `finEnumFin`, so it fires as written. `TODO.md`
  § Concrete-syntax prototype separately schedules `Geb.finEnumFin` and
  `Geb.finEnumEmpty` into the same file; the generalized instances subsume
  `Geb.finEnumFin` only, `FinEnum Empty` following from neither
  `FinEnum.unit` nor `FinEnum.finSum`.
- `feat/cobham-class`: § The class, its `GebTests` mirror,
  `Geb/Mathlib/Computability/Cobham.lean` and its `GebTests` counterpart,
  the added `public import` in `Geb/Mathlib/Computability.lean` and plain
  `import` in `GebTests/Mathlib/Computability.lean`, the `docs/index.md`
  entry, the `TODO.md` item-3 rewrite, the extension of `TODO.md`'s
  attested-locators trigger, and the `docs/references.bib` entries its
  module docstrings cite.
- `feat/cobham-tree-recognizer`: § The recognizer, its `GebTests` mirror,
  its `docs/index.md` entry, the added imports of `Cobham.Tree` in
  `Geb/Mathlib/Computability/Cobham.lean` and its `GebTests` counterpart,
  and `isTreeSem_eq_ite` for this module, pinning its value on both
  branches rather than only on the accepting one.

## Deferred

To `TODO.md`, each entry naming its own subjects since this file is
removed, and each to the section named with it: § Triggers for an entry
with a firing condition, § Next up otherwise.

- Route A: proving a time and space bound for a tree recognizer against
  `Cslib.Computability.Machines.Turing.MultiTape.Deterministic`'s
  `ComputableInTimeAndSpace`. That module supplies `MultiTapeTM`, `Cfg`,
  `step`, `configs`, `spaceUsed` and `visitedByTapeHead` among others, but
  no machine constructions, worked examples or composition combinators.
  Three constraints: the subtree rules place any statement relating
  `BinTree.Valid` to that predicate in `Geb/Internal/`, since `Geb/Cslib/`
  may not import `Geb.Mathlib.*` and `Geb/Mathlib/` may not import
  `Cslib.*`; `DecidableInTimeAndSpace` is stated over
  `Turing.MultiTapeTM.indicator`, an `open Classical in noncomputable def`,
  so `ComputableInTimeAndSpace` over a decidable indicator is the form to
  use; and the result speaks of one machine and one language, not of any
  function-algebra expression. To § Next up.
- Allowing `Geb/Cslib/` to import `Geb.Mathlib.*`. Trigger: a `Geb/Cslib/`
  module needing content from `Geb/Mathlib/`. The case for it: the reason
  `docs/rules/upstream-eligible.md` gives, that unupstreamed
  mathlib-targeted content is unavailable to a CSLib PR, holds equally of
  one `Geb/Mathlib/` module importing another. The case against it, which
  the entry must answer: extraction of a `Geb/Mathlib/` module orders PRs
  within one review queue, whereas a `Geb/Cslib/` module importing
  `Geb.Mathlib.*` waits on mathlib merge, mathlib release and CSLib's own
  mathlib bump, three cadences the project does not set, against
  CONTRIBUTING § Floodgate test's "on short notice". The converse
  direction stays barred on its own reason: mathlib does not depend on
  CSLib, so no ordering makes a `Geb/Mathlib/` module's `Cslib.*` import
  extractable. The change set discovered so far:
  - `scripts/lint-imports.sh` — the two Cslib `check_subtree` calls, with
    `Geb.Mathlib.` added to both the allowed-prefix and the leakage-prefix
    list, since extraction rewrites that prefix too; and the header
    comment block restating the allowed-import table.
  - `scripts/extract-pr.sh` — the `Geb/Cslib/*` and `GebTests/Cslib/*`
    arms set one `rewrite_prefix` each, so a `Geb.Mathlib.` import is
    emitted verbatim and the extracted file does not compile. A second
    rewrite pair is needed.
  - `scripts/tests/test-lint-imports.sh` — the case asserting exit 1 on
    `import Geb.Mathlib.Foo` in `Geb/Cslib/` must be inverted; a
    `GebTests/Cslib/` parallel case does not exist and should be added.
  - `scripts/tests/test-extract-pr.sh` — a case for the new rewrite.
  - `docs/rules/upstream-eligible.md` — the `Geb/Cslib/` and
    `GebTests/Cslib/` table rows, the § Floodgate test sentence asserting
    that each subtree's extractability is independent of the other, which
    the change falsifies, and the closing cross-subtree paragraph.
  - `docs/process.md` § Floodgate test, which carries the rationale.
  - Adjacent and not bundled: `Batteries.` is arguably missing from the
    `Geb/Cslib/` allowed list by the same argument, CSLib depending on
    mathlib which depends on Batteries.
- A recursion combinator for `Geb/Mathlib/Computability/Cobham/`
  discharging the `Rec` bound of [HeraudNowak2011] § 3.1 once for all
  users rather than at each use, by truncating each layer against the
  bound. Deferred: at the Cobham tree recognizer's three recursions it is
  net cost, the agreement law's hypothesis needing the naive recursion's
  unfolding lemmas anyway. Trigger: a Cobham module reaching a fourth
  recursion. The construction, its law, its arities and the naming
  question are written out in that entry and are not restated here.
- CONTRIBUTING § Concern shape orders spec and plan commits for a
  workstream that is one topic branch, and says nothing about a series of
  branches merging separately into an append-only `main`, nor about a
  topic branch with two topic-branch parents. Since that ordering was
  introduced, `main` has never carried two specs at once, so no practice
  settles either question. The entry is to settle both. To § Next up.

## Reference status

The adjudication of the sources — which defines `BRN`, which states the
theorem, how [Clote1999]'s arithmetic analogue differs, why the reverse
inclusion is not relied on, why the truncating scheme must not be called
limited recursion, and what [Strahm2010] Lemma 4 does and does not
license — lives in the `note` fields of `docs/references.bib`, added by
`feat/cobham-class`. It is written there rather than here because this
file is removed and those entries are not.

[Thompson1972], [Ritchie1963], [Cobham1965] and [Bellantoni1992] are
recorded from [Strahm2003]'s and [Clote1999]'s bibliographies and were not
read; the first two carry a DOI and the last two have none. A
`theoremsearch` query for Thompson's statement returned no hit, that index
covering arXiv. `TODO.md`'s trigger to verify attested locators is
extended by `feat/cobham-class` to name all four.

## References

Every work cited here has a `docs/references.bib` entry carrying its
locators and its caveats: [Strahm2003] (the licence), [Strahm2010],
[Clote1999], [HeraudNowak2011], [BellantoniCook1992], [Thompson1972],
[Ritchie1963], [Cobham1965], [Bellantoni1992] and
[BeckmannBussFriedmanMuellerThapen2017].

Section locators used by this file: [Strahm2003] § 2 (Theorem 1, `BRN`),
§ 4 (`msp`, the cut-off operator); [Clote1999] Definitions 2.13, 3.18,
3.100, 4.5, Theorems 3.20, 3.36, 3.101, Problem 3.102, footnote 10;
[HeraudNowak2011] § 3.1 (syntax, arity relation, semantics, Proposition
1), § 3.2 (`B`), § 4 (`pred`, `cond`, the `B → C` translation). § 3.1
records that its bitstring reformulation of Cobham's class is taken from
Tourlakis, Computability (1984), which was not consulted.
