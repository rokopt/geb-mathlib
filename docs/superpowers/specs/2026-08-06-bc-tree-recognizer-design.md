# The Bellantoni-Cook tree recognizer — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Sources](#sources)
  - [Per-definition classification](#per-definition-classification)
- [Design](#design)
  - [Alternatives considered](#alternatives-considered)
  - [The recognizer must be a counter automaton](#the-recognizer-must-be-a-counter-automaton)
  - [The expressions](#the-expressions)
  - [The quadratic recomputation](#the-quadratic-recomputation)
  - [Unfolding is constructor-shaped and environment-canonical](#unfolding-is-constructor-shaped-and-environment-canonical)
  - [The theorems](#the-theorems)
  - [Exposure](#exposure)
  - [Placement and file manifest](#placement-and-file-manifest)
- [Verification evidence](#verification-evidence)
- [Tests](#tests)
- [Documentation](#documentation)
- [Non-goals](#non-goals)
- [Deferred](#deferred)
- [Constraints](#constraints)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Purpose

Define, as expressions of the Bellantoni-Cook class `B`, a recognizer
deciding whether a bitstring is the preorder spelling of a binary tree,
and prove it correct against the `Valid` predicate of
`Geb/Mathlib/Data/Tree/Preorder.lean`.

Composed with that module's `valid_iff_exists_print`, the result is that
a Bellantoni-Cook expression accepts exactly the spellings of trees. `B`
is a characterization of the polynomial-time functions
([BellantoniCook1992]; not proved here, see § Non-goals), so exhibiting
the membership test as an expression of `B` places it in that class
without a separate complexity argument.

The consumer is the tree recursor, § Deferred item 1: locating the split
point between a node's two subtrees is the same scan this recognizer
performs, so the recognizer is the recursor's first factor rather than
separate work.

This segment sits above `feat/binary-tree-preorder`'s bookmark in the
branch stack and imports its module. Its spec, plan, bibliography
entries, and code are all created here, so that merging the preceding
branch puts none of them on `main`'s working tree.

## Sources

The soundness of `B` for polynomial time is [BellantoniCook1992], in the
reformulation of [HeraudNowak2011] § 3.2 that
`Geb/Mathlib/Computability/BellantoniCook.lean` transcribes. Nothing here
re-proves it; the class is used as given.

Three items from the literature bear on the design. The first rules out
an approach a reader would otherwise expect; the second records the two
published recoveries from it; the third is what this development relies
on.

Trees cannot be built freely from recursive results under an explicit
string representation. [DalLagoMartiniZorzi2010] § 1 exhibits

    f(0) = f(1) = nil        f(w·0) = f(w·1) = tree(f(w), f(w))

which "outputs the full binary tree, which has exponential size in the
length of the input", and notes that some of Leivant's proofs — in
particular that of his Lemma 3.8 — "only go through when the involved
algebras have constructors of at most unary arities". They recover
soundness by representing terms as DAGs with sharing, where "the time
needed to print the string representation of the output is not (and
should not be) counted in the computing time". Under an explicit
bitstring representation, which is what this development uses, that
recovery is unavailable.

The example is stated for Leivant's tiers rather than for `B`'s safe
arguments, and § 1 also records that in that setting "linearity does
not play a major role — a function can duplicate its inputs as many
times as it likes". The paper's own diagnosis is representational.

Two recoveries exist. [Hofmann2000]'s abstract states soundness for
"recursion over trees and other data structures", in a system it
describes as having "modal and linear types". By what restriction that
soundness is obtained is not stated here: the paper's own account of the
mechanism was not consulted, and nothing below depends on it.
[DalLagoMartiniZorzi2010] § 1 further reports
that Marion extends polynomiality to constructors `s₁ × ⋯ × sₙ → s`
under the constraint that `s` occurs at most once among the `sᵢ`. That
attribution is secondhand and is used here only as context; no design
decision below rests on it, and § Deferred item 5 schedules the
primary-source check.

`B` needs neither, because it has no joining base function. Its growth
lemma — [HeraudNowak2011] Proposition 2, Polymax Bounding — gives a
monotone polynomial with `|f(x̄; ā)| ≤ p(|x̄|) + maxᵢ |aᵢ|`, a maximum
rather than a sum. Duplication of safe arguments is permitted and does
not affect the bound, because no base function concatenates two of them.

Two consequences, with distinct grounds. Negatively, the growth lemma is
a necessary condition on every definable function, and a `node` on two
safe arguments would have size `|a| + |b| + 1`, exceeding
`p(0) + max(|a|, |b|)` for large arguments; so that `node` is not
definable. Positively, `node` at arity `(2, 0)` is definable —
not by the growth lemma, which establishes no definability, but by the
completeness half of [BellantoniCook1992], which delivers every
polynomial-time function at all-normal arity. `node` at `(1, 1)` does
not follow from completeness, which says nothing about mixed arities;
it requires exhibiting concatenation with a normal prefix and a safe
suffix as an expression of `B`, which this spec does not do and no
claim below depends on.

What follows for the recursor is a statement about the normal slot, not
about `node` in general. `evalRec` delivers the recursive value in safe
position, and no expression moves safe to normal; at both `(2, 0)` and
`(1, 1)` at least one child sits in a normal slot; so no definable `node`
can receive two recursive results. A single recursive result reaching a safe
slot is permitted, and is how strings are ordinarily built in `B` — by
`succ`, whose arity is `(0, 1)`, applied to the recursive value. This
resembles the "at most once" constraint reported of Marion, reached by a
different mechanism; § Deferred item 5 records the check.

### Per-definition classification

| Definition | Classification |
| --- | --- |
| the class `B` and its interpretation | already transcribed, [HeraudNowak2011] § 3.2 |
| `compChildren`, `zeroAt`, `oneAt` | novel; the shared constructors of § The expressions |
| `incRaw`, `decRaw`, `countRaw`, `count`, `countOf` | novel |
| `guardRaw`, `nuTrueStepRaw`, `noUnderflowRaw`, `noUnderflow`, `noUnderflowOf` | novel |
| `eqOneInnerRaw`, `eqOneRaw`, `eqOne`, `eqOneOf` | novel |
| `isTreeRaw`, `isTree`, `isTreeOf` | novel |
| `countSem`, `noUnderflowSem`, `eqOneSem`, `isTreeSem` | novel; the meanings at their arities, per § Unfolding |
| every theorem in § The theorems | novel |
| the unfolding, environment and auxiliary lemmas § Unfolding calls for | novel |

The `*Raw` entries are the raw `sig`-trees, the unsuffixed entries the
admissible expressions built from them, and the `*Of` entries their
arity witnesses. Every definition this segment ships into `Geb/Mathlib/`
appears above; the one it ships into `GebTests/Mathlib/` is the named
`def` § Tests calls for, classified there. § The theorems lists the
characterizations; the last row above covers the lemmas their proofs run
through, which the plan enumerates.

## Design

### Alternatives considered

Recursive descent mirroring the Lean parser. Rejected:
see § The recognizer must be a counter automaton, where the obstruction
is shown to be the class's own restriction.

Defining the recognizer in Cobham's class `C` and translating. The
`C → B` translation is [HeraudNowak2011] § 5, Theorem 2, and `C`'s
bounded recursion on notation would carry the counter and the underflow
flag together without the recomputation of § The quadratic recomputation.
Rejected for this segment under CONTRIBUTING.md § Code is cost:
formalizing a second function algebra and a translation theorem is
justified by a library of `B` expressions we do not yet have. § Deferred
item 2 records it, and the test of whether it earns its cost is whether
the second and third expressions in `B` cost as much as the first.

One file rather than two. The unfolding and environment lemmas of
§ Unfolding are few and are consumed only here. § Deferred item 3 records
extraction once a second Bellantoni-Cook function needs them.

### The recognizer must be a counter automaton

A recursive-descent recognizer for a node would parse the left subtree
off the suffix, take the remainder, and parse the right subtree from that
remainder. In `B` the remainder would be the recursive value, which sits
in safe position, and recursion on a safe argument is what the class
forbids. No encoding avoids this: it is the growth lemma again, seen from
the parsing side.

What remains is a single scan whose state never needs joining. The
`Valid` predicate of the preceding segment is such a scan.

### The expressions

`evalRec` is `List.rec`, so its step receives the leading bit, the
remaining bitstring in normal position, and the recursive value in safe
position. `print leaf = [false]`, so the `false` bit increments and the
`true` bit decrements.

| Expression | Arity | Shape |
| --- | --- | --- |
| `count` | `(1, 0)` | `safeRec 0 0` over `zero`; `false`-step `comp` of `succ true` with the recursive value; `true`-step `comp` of `pred` with it |
| `noUnderflow` | `(1, 0)` | `safeRec 0 0` over `[true]`; `false`-step returns the recursive value; `true`-step is `cond` on `pred (count v)`, yielding `[]` when that is empty and the recursive value otherwise |
| `eqOne` | `(0, 1)` | `cond` on the argument, then `cond` on its `pred` |
| `isTree` | `(1, 0)` | `and (noUnderflow x) (eqOne (count x))`, with `and (; a, b) = cond (; a, [], b, b)` |

`count` returns the stack depth in unary as
`List.replicate (depth w) true`. `noUnderflow` returns `[]` or `[true]`;
failure propagates outward, because `[]` is only ever passed up.
`isTree` returns `[]` or `[true]`, so the output is canonical and
correctness is an equation rather than a disequation.

The guard in `noUnderflow`'s step reaches `count` as the head of an
inner `comp`, not as a safe child. A `safeRec 0 0` step has arity
`(1, 1)`. A `comp n s m k` requires its head at arity `(m, k)`, its
normal children at `(n, 0)`, and its safe children at `(n, s)`. Placing
`count` as a safe child of the step would require it at `(1, 1)`, which
it does not meet at `(1, 0)`; that route is measured inadmissible.
Writing the inner node as `comp 1 1 1 0` instead requires its head at
`(1, 0)`, which `count` does meet, and its one normal child at `(1, 0)`,
which the projection onto the recursion variable meets. `count` is
therefore applied to the normal tail, and the guard is `comp 1 1 0 1`
with head `pred` over that inner node as its single safe child.

### The quadratic recomputation

`noUnderflow` must track the counter and whether it underflowed, and
`safeRec` yields one recursive value which cannot be a pair, since two
safe bitstrings do not concatenate. The step therefore recomputes
`count v` from the normal tail at each level, making the recognizer
quadratic in the input length.

This is admissible and does not affect the theorem — `B` is closed under
it — but it is a deliberate cost, and the source carries a comment
naming the bound and the replacement.

That replacement is [HeraudNowak2011] § 7's own proposal. The authors
report that "dealing with the carry bit does not fit immediately in
Bellantoni-Cook's recursion scheme" and suggest defining such functions
in Cobham's class `C` and applying the `C → B` translation. The
counter-plus-flag here is the same difficulty.

### Unfolding is constructor-shaped and environment-canonical

This constraint governs every proof in the segment, and all three parts
were measured.

`Sem (n, s)` is a function type, so `evalRec` recurses at a function
motive and every eliminator in the chain — `W.elim`, `List.rec`, `ite` —
sits at that motive. Eliminators at function motives reduce only when
their scrutinee is a constructor, and never commute with application
definitionally. So a lemma with a symbolic bit
(`countSem ![b :: v] ![] = if b then … else …`) and a lemma in fold
shape (`countSem ![w] ![] = List.rec [] (fun b _ ih ↦ …) w`) are both
non-definitional; only a per-constructor lemma with the recursive value
exposed on the right is.

That is necessary and not sufficient. `count`'s per-constructor lemmas
hold by `rfl` only because its steps discard the normal environment.
`noUnderflow`'s step applies `count` to a symbolic bitstring, so the
resulting `evalRec` is stuck and carries environments of the form
`(fun i : Fin 1 ↦ …)` which are not definitionally `![v]`. `Sem` being a
function type, closing that gap needs `funext`, which no `rfl` lemma
reaches.

A third requirement binds the expressions rather than the lemmas. It is a
correspondence between what the lemma names and what the expression
builds, and its scope is narrower than it first appears.

`evalValue`'s `comp` clause constructs the environments it passes to the
head:

    fun i ↦ transport … (c (.inr (.inl i))).2 x Fin.elim0     -- normal
    fun j ↦ transport … (c (.inr (.inr j))).2 x y             -- safe

A step lemma for `noUnderflow` must name the environment at which the
inner `count` is applied — it appears on the right as
`countSem (fun _ ↦ v) (fun _ ↦ [])`. For the two sides to be
definitionally equal, the environments the expression builds must reduce
to those constant functions, and that happens exactly when the inner
`comp`'s own child families are written `fun _ ↦ e`. A family written
`![e]` is `Matrix.cons e ![]`, which does not reduce at symbolic `i` or
`j`, and `Fin.elim0` is not the constant function either.

The requirement is local to the node whose environment the lemma names.
Measured over six variants differing only in the spelling of three
families — the enclosing guard's safe family, and the inner node's
normal and safe families — the lemma holds by `rfl` exactly when both of
the inner node's families are constant functions, and is unaffected by
the enclosing family's spelling:

| enclosing safe | inner normal | inner safe | `rfl` |
| --- | --- | --- | --- |
| `![…]` | `![…]` | `Fin.elim0` | fails |
| `![…]` | `fun _ ↦` | `Fin.elim0` | fails |
| `![…]` | `fun _ ↦` | `fun _ ↦` | holds |
| `fun _ ↦` | `fun _ ↦` | `fun _ ↦` | holds |
| `fun _ ↦` | `![…]` | `Fin.elim0` | fails |
| `![…]` | `![…]` | `fun _ ↦` | fails |

Rows three and two isolate the inner safe family; rows three and six
isolate the inner normal family; rows three and four show the enclosing
family does not matter.

Vector notation is therefore admissible in general — the existing
`BellantoniCook` test module and `count` use it throughout — and no rule
requiring it everywhere would be satisfiable: a `cond` node has four
distinct safe children, which `fun _ ↦ e` cannot express. The rule this
segment adopts is the one the table measures: a family consumed at a
bound index is written as a constant function. That is the inner
node of `noUnderflow`'s guard, which `evalRec`'s stuck recursion reaches;
every other family in the segment is consumed at a literal index, where
`Matrix.cons` reduces and either spelling works.

Three devices are therefore required, all three measured to work:

1. State each step lemma at abstract `Fin.cons`-shaped environments,
   which is definitional:

        theorem noUnderflowSem_cons (v : List Bool) (x y : Fin 0 → List Bool) :
            noUnderflowSem (Fin.cons (true :: v) x) y = … := rfl

2. Supply one environment-normalization lemma for each expression whose
   meaning is named at an environment other than the canonical one,
   proved by `funext` and `Subsingleton.elim`, rewriting an arbitrary
   environment to the canonical `![…]` form.
3. Write as a constant function every child family a lemma reaches at a
   bound index, so that the environment the lemma names is the one the
   expression builds.

A failed `rfl` therefore signals one of three things — a rejected
statement shape, a non-canonical environment, or a child family whose
spelling does not reduce to the environment the lemma names — and the
third is a defect in the expression, not in the lemma. That ordering
matters for the plan: device 3 is settled when the expression is
written, and retrofitting it means rebuilding the expression and every
lemma above it.

The three devices govern the lemmas' shape. What the lemmas are stated
over is a separate matter: `countSem`, `noUnderflowSem`, `eqOneSem` and
`isTreeSem` name each expression's meaning at its arity — `(BC.eval count).2`
and its siblings, ascribed to the reduced function type. A
meaning taken through the `Sigma` projection instead has a type headed by
that projection rather than by an arrow, and `rw` under it fails as not
type-correct at `implicit` transparency. Every statement in § The
theorems is over these.

### The theorems

| Theorem | Statement |
| --- | --- |
| `countSem_nil` | `countSem ![[]] ![] = []` |
| `countSem_cons_false` | `countSem ![false :: v] ![] = true :: countSem ![v] ![]` |
| `countSem_cons_true` | `countSem ![true :: v] ![] = (countSem ![v] ![]).tail` |
| `countSem_env` | `countSem f g = countSem ![f 0] ![]` |
| `countSem_eq` | `countSem ![w] ![] = List.replicate (depth w) true` |
| `noUnderflowSem_cons` | the `Fin.cons`-shaped step lemma of § Unfolding |
| `noUnderflowSem_env` | the environment-normalization lemma for `noUnderflow` |
| `noUnderflowSem_eq` | `noUnderflowSem ![w] ![] = if ok w then [true] else []` |
| `eqOneSem_eq` | `eqOneSem ![] ![u] = if u.length = 1 then [true] else []` |
| `isTreeSem_eq_singleton_iff_valid` | `isTreeSem ![w] ![] = [true] ↔ Valid w` |
| `isTreeSem_eq_singleton_iff_exists_print` | `isTreeSem ![w] ![] = [true] ↔ ∃ t, print t = w` |

The last follows from the one above it and the preceding segment's
`valid_iff_exists_print`, and is the segment's stated goal.

Each name is that of the function its statement mentions. The `Sem`
ascriptions of § Unfolding are what the statements are stated over, so
`countSem_nil` rather than `eval_count_nil`; mathlib names a lemma after
the head symbol of its statement, and `eval` occurs in none of these.
`isTreeSem_eq_singleton_iff_valid` says `= [true]`, a one-element list,
not `= true`.

### Exposure

Every step lemma in `Tree.lean` closes by `rfl` across a module boundary
into `Basic.lean`, so the module system decides whether the design works
at all: it does not unfold a non-exposed definition, and an unexposed
`sig`, `Direction`, `rc`, `q`, `BC`, `BC.eval`, `evalRec` or `evalValue`
would leave every such lemma stuck. All of them are already `@[expose]`
inside a `public section` in the module as merged, and the restructure of
§ Placement carries them across untouched, so the property is preserved
rather than newly established. The plan re-measures it after the move
rather than assuming it, since the failure is silent at the LSP and
surfaces only at `lake build`.

`Tree.lean`'s own expressions are `@[expose]` in a `public section` for
the same reason: the test module's assertions close by `rfl` across
another boundary.

### Placement and file manifest

| File | Contents |
| --- | --- |
| `Geb/Mathlib/Computability/BellantoniCook.lean` | becomes the directory index |
| `Geb/Mathlib/Computability/BellantoniCook/Basic.lean` | the class, moved from the file above, gaining `compChildren` |
| `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` | the expressions, unfolding and environment lemmas, characterizations |
| `GebTests/Mathlib/Computability/BellantoniCook.lean` | becomes the test directory index |
| `GebTests/Mathlib/Computability/BellantoniCook/Basic.lean` | the existing worked expressions, moved from the file above, losing their private `compChildren` |
| `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean` | the assertions of § Tests |
| `docs/references.bib` | gains `Hofmann2000`, `Marion2003` |
| `docs/index.md`, `TODO.md` | § Documentation |
| `docs/superpowers/specs/2026-08-06-bc-tree-recognizer-design.md` | this spec; added, then removed |
| `docs/superpowers/plans/2026-08-06-bc-tree-recognizer-plan.md` | the plan; added, then removed |
| `docs/superpowers/plans/2026-08-06-bc-tree-recognizer-handoff.md` | the measured Lean § Verification evidence rests on; added, then removed |

`compChildren` orders a `comp` node's children as `Direction` gives
them, so it belongs with `Direction` rather than with the expressions
built over it. The existing test module declares its own copy at the
root namespace; that copy is deleted in the same commit, which is what
keeps the name unambiguous once `Basic.lean` declares it in the
`BellantoniCook` namespace.

Commit order: this spec, then the plan, then the restructure, then the
implementation commits, then the documentation commit, then a final
commit removing this spec, the plan and the measured-Lean companion
(CONTRIBUTING.md § Concern shape).

The restructure is what CONTRIBUTING.md § Repo structure requires — "one
indexing file per directory". The repository is not uniform here:
`Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` carries content
beside its own directory. The restructure follows the rule rather than
that precedent. Leaving the class in
`BellantoniCook.lean` would make `Computability.lean` index two levels
and leave `BellantoniCook/` without an index; moving the content into
`BellantoniCook/BellantoniCook.lean` instead would name the module
`Geb.Mathlib.Computability.BellantoniCook.BellantoniCook`.
Importers of `Geb.Mathlib.Computability.BellantoniCook` are unaffected,
since the index re-exports `Basic` with `public import`.

The namespace is `BellantoniCook`; no index title or docstring carries
the `Geb.Mathlib.` self-prefix.

## Verification evidence

Measured by `lake build` against v4.33.0-rc2 on probe modules. Zero
diagnostics.

Those probes are not in the repository: they were scratch modules in
`GebTests/Mathlib/`, which is upstream-eligible, and were removed. Their
sources are preserved outside the working tree, and the plan's first
Bellantoni-Cook task rebuilds the expressions and lemmas below as the
real module rather than treating these measurements as standing
evidence.
Declaration names appearing only in this section are those probes' names
and are not shipped. They are `cnt`, which survives in a quoted
diagnostic below, the `nu*` variants of the spelling experiment, and
`guardSafeRaw`, which exists only to record an inadmissible route for
the guard. What this
segment ships is
listed in § Per-definition classification for definitions and in § The
theorems for theorems.

- `count` is admissible: `⟨countRaw, by decide⟩` elaborates, and
  `countOf : BCOf 1 0 := ⟨count, rfl⟩` elaborates, so the arity is
  `(1, 0)`.
- `countSem ![[true, false, true, false, false]] ![] = [true]` by
  `rfl` — three leaves and two nodes leave depth one.
- `countSem_nil`, `countSem_cons_false` and `countSem_cons_true`
  all hold by `rfl`, the latter two at symbolic `v`.
- `countSem_eq` follows by `List.rec` over those two, at symbolic `w`.

The proof obligation the design turns on was carried to completion
rather than deferred to the plan: `noUnderflowSem_eq`, stating
`noUnderflowSem ![w] ![] = if ok w then [true] else []`, elaborates.
Its route is a `List.rec` over the three step lemmas — nil, `false`-step
and `true`-step — with the guard discharged by the `count`
characterization and a `tail`-of-`replicate` lemma, splitting on whether
`depth v - 1` is zero. § The theorems names one `noUnderflowSem_cons`; the
proof needs all three, and the plan states them separately. `isTree`'s
own two correctness theorems are stated in § The theorems; they compose
`noUnderflowSem_eq` with `countSem_eq` and `eqOneSem_eq`. They were not
measured when this spec was first written; the plan carries them with
proofs measured at v4.33.0-rc2.

Negative measurements, which are why § Unfolding is stated as a
constraint rather than as guidance:

- The fold-shaped statement of `countSem` fails with *Not a
  definitional equality*.
- The symbolic-bit statement fails the same way.
- Device 3 was isolated by a six-variant experiment over the three child
  families involved, tabulated in § Unfolding. Two variants hold by
  `rfl` and four fail with *Not a definitional equality* between
  `nu*.eval.snd (Fin.cons (true :: v) x) y` and the match on
  `(cnt.eval.snd (fun x ↦ v) fun x ↦ []).tail`. The two that hold are
  exactly those whose inner node has both families constant; the
  enclosing family's spelling is immaterial.

All four expressions were constructed and checked at their arities, by
`⟨_, by decide⟩` admissibility on a separately bound raw tree and `rfl`
arity: `countOf : BCOf 1 0`, `noUnderflowOf : BCOf 1 0`,
`eqOneOf : BCOf 0 1`, `isTreeOf : BCOf 1 0`. The expressions themselves
are `count`, `noUnderflow`, `eqOne`, `isTree`, each of type `BC`. The
`⟨WType.mk …, by decide⟩` form does not elaborate — instance search fails
against an inline `WType.mk` application — so each raw tree is bound as
its own `def` first, as the Bellantoni-Cook spec records for the same
reason.

Two inadmissible routes for the guard were measured, and the admissible
one. Putting `count` in a safe-child slot, which is the route
§ The expressions rules out by arity, gives `false`; so does the probes'
`guardSafeRaw`, which instead makes `count` the head of an inner
`comp 1 1 0 1` whose head requirement is `(0, 1)` — a second obstruction,
not the one § The expressions argues. The normal-slot route of
§ The expressions is admissible.

Behavioural agreement was checked exhaustively rather than on examples:
`isTree` agrees with `Valid` on all 2047 words of length at most ten,
`noUnderflow` agrees with `ok` on the same set, both outputs are
canonical there, and no counterexample to failure propagation exists in that
range.

## Tests

`GebTests/Mathlib/Computability/BellantoniCook/Tree.lean`. Each assertion
is a `theorem` closing by `rfl`, following the existing Bellantoni-Cook
test module.

- `isTree` accepting `print leaf`, `print (node leaf leaf)`, and an
  asymmetric tree of two nodes and three leaves.
- `isTree` rejecting: the empty word; a word failing only `ok`; a word
  failing only `depth`; a word with the right bit counts in the wrong
  order.
- `count` on a word whose depth exceeds one, separating `count` from
  `isTree`.

The two separated rejections are the non-vacuity control for the
conjunction in `isTree`.

`lake shake` reports an import as removable when nothing in the olean
references it, so the test module names a `def` built from the module
under test rather than relying on anonymous assertions alone. That `def`
is novel, and is the only definition this segment ships outside
`Geb/Mathlib/`.

## Documentation

`docs/index.md` gains the module, and its entry for the module the
restructure moves is corrected. `TODO.md` gains § Deferred, and cites
`[Hofmann2000]` and `[Marion2003]` there, so that neither bibliography
entry is left citing nothing once this spec is removed; its two other
references to the moved module's path are corrected too. `TODO.md`
§ Triggers gains one entry, for the two `FreeCoprodCompDisc.lean` files
this restructure leaves as the remaining departures from
CONTRIBUTING.md § Repo structure.

## Non-goals

- Proving the growth lemma, or that `B` is sound or complete for
  polynomial time. § Sources uses those results; it does not establish
  them, and no declaration here asserts them.
- A tree recursor. § Deferred item 1.
- Any `node` or `leaf` expression. The recognizer decides membership; it
  does not construct.

## Deferred

1. The tree recursor — the analogue of `safeRec` on the encoded tree,
   whose step receives the two subtree spellings in normal position and
   the two recursive values in safe position. Its soundness is a new
   theorem, not a corollary:
   [HeraudNowak2011] Proposition 2 is proved by induction over the
   constructors of `B`, and a tree recursor is a further constructor. The
   expected argument is that the step inherits the maximum bound, giving
   `|f(node l r)| ≤ p(|l| + |r|) + max(|f l|, |f r|, |ā|)`, and induction
   on height gives a polynomial. Depends on this recognizer's scan for
   the split point.
2. Cobham's class `C` and the `C → B` translation of [HeraudNowak2011]
   § 5, Theorem 2, which would remove the quadratic recomputation.
3. Extract the unfolding and environment lemmas into their own module
   once a second Bellantoni-Cook function needs them.
4. The labelled variant, tracking the corresponding item in the preceding
   segment's spec.
5. Verify the Marion attribution against [Marion2003] directly rather
   than through [DalLagoMartiniZorzi2010]'s report of it, or drop the
   attribution. The paper was not reachable when this spec was written,
   so the check may not be actionable; nothing in the design depends on
   it, and dropping both the mention in § Sources and the
   `Marion2003` bibliography entry is an acceptable outcome.
6. A linear-logic strand. [Hofmann2000]'s abstract states soundness for
   recursion over trees in a system it describes as modally and linearly
   typed, by a mechanism § Sources deliberately does not characterise,
   and the light and
   soft linear logics tune one family of systems to several complexity
   classes. The motivation to record is that tunability. Against it:
   those systems are reported to need more elaborate syntax or encodings
   than the function algebras, and a well-typed term there does not carry
   its own bound — the type derivation is needed to extract it, which
   tells against the representation strategy used here, in which the
   program is the term. Any pursuit of this item begins by verifying
   both claims against primary sources, which this spec does not.

## Constraints

1. No `noncomputable`. `#print axioms` on every declaration lies within
   `{propext, Quot.sound}`, measured monomorphically in the consuming
   closure. No `Computability` module is in
   `GebMeta.classicalAllowedModules`, so any `Classical.choice`
   dependence fails `lake lint`.
2. No self-referential `inductive` and no self-calling `def`.
3. No `induction` tactic; general characterizations are driven by
   explicit `List.rec` applications.
4. `Geb/Mathlib/` import rules, as in the preceding segment's spec.
5. Every unfolding lemma is per-constructor with the recursive value
   exposed, and is stated at canonical or `Fin.cons`-shaped environments,
   per § Unfolding.
6. Docstring and module-docstring requirements, as in the preceding
   segment's spec.
7. Names follow mathlib's conventions: `lowerCamelCase` for the
   expressions, `snake_case` for every theorem.
