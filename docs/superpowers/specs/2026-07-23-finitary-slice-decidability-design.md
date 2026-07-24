# Decidable slice validity for finitary slice polynomial functors

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Concern shape and the PR split](#concern-shape-and-the-pr-split)
- [Prior state](#prior-state)
  - [This repository](#this-repository)
  - [mathlib](#mathlib)
- [The finitary condition](#the-finitary-condition)
- [Module layout](#module-layout)
- [Module contents](#module-contents)
  - [The choice-free `FinEnum (Fin n)`](#the-choice-free-finenum-fin-n)
  - [`Slice/Finitary.lean`](#slicefinitarylean)
- [Tests](#tests)
- [Transcription or novel](#transcription-or-novel)
- [Universe constraints](#universe-constraints)
- [Choice boundary](#choice-boundary)
- [Verification performed](#verification-performed)
- [Documentation and roadmap](#documentation-and-roadmap)
- [Out of scope](#out-of-scope)
- [References](#references)

<!-- END doctoc -->

## Scope

The decidable-validity layer
(`Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean`, merged in PR #91 as
change `svqnnupluorm`) decides the slice fiber-membership, compatibility,
and W-type-admissibility predicates from two hypotheses supplied by the
caller: `F.Finitary` (each direction type carries a `FinEnum`) and
`DecidableEq` on the index type. Nothing in that layer supplies the
hypotheses; it only consumes them.

This work supplies the `Finitary` hypothesis in the case the functor is
finitary with `Fin` directions. A bundled structure records a slice
polynomial functor whose direction types are `Fin` (so `Finitary` is a
derived field, not a hypothesis), with an arbitrary shape type and
arbitrary domain and codomain. The existing decidability instances are
reused unchanged; no new decision procedure is written.

The `DecidableEq` hypotheses on the index types remain caller-given.
Nothing in the decidability mechanism requires the domain, the codomain,
or the shapes to be finite — only the directions. Forcing finiteness
elsewhere is a stronger specialization than decidability needs, and is
deferred (§ Out of scope).

Two tiers, matching where decidability holds:

- **dom/cod-general.** The fiber and compatibility predicates, decidable
  for differing domain and codomain.
- **diagonal.** W-type admissibility (`SlicePFunctor.WValid`), decidable
  only when the domain and codomain are the same type, since the
  admissibility step compares a child's codomain-index against its parent's
  domain-index.

The presheaf case is a separate concern; see § Out of scope.

## Concern shape and the PR split

One concern — supplying the `Finitary` hypothesis in the finitary-with-`Fin`
-directions case — on one branch, delivered as one dependency-ordered PR.

| PR | Modules | Depends on |
| --- | --- | --- |
| 1 | `Slice/Finitary.lean` and its test; a choice-free `FinEnum (Fin n)` helper | `Slice/Decidable.lean`, `Slice/Basic.lean`, `Slice/W.lean`, `Univariate/Finitary.lean`, `Data/FinEnum.lean` |

PR 1 depends on content not yet upstreamed: the decidable-validity layer
and the slice modules. The dependency is recorded so the delivery order is
derivable; it is not a deliverable of this branch.

## Prior state

### This repository

| Module | Content consumed by this work |
| --- | --- |
| `Slice/Basic.lean` | `SliceDomPFunctor`, `SlicePFunctor`, `Compatible`, `ofCurried`, `rCurried`, the fiber formers |
| `Slice/W.lean` | `WValid`, the `wIndexStep`/`wIndexValid` fold it is the `valid` component of |
| `Slice/Decidable.lean` | the five `Decidable` instances this work specializes |
| `Univariate/Finitary.lean` | `PFunctor.Finitary`, the abbreviation `∀ a, FinEnum (P.B a)` |
| `Data/FinEnum.lean` | the three choice-free decidability instances (`decidableForallFinEnum`, `decidableForallSubtype`, `decidablePiFinEnum`) |

The five existing instances and the hypotheses they consume:

| Instance | Hypotheses |
| --- | --- |
| `SliceDomPFunctor.decidableDirectionOver` | `DecidableEq dom` |
| `SliceDomPFunctor.decidableForallDirection` | `Finitary`, `DecidableEq dom` |
| `SliceDomPFunctor.decidableCompatible` | `Finitary`, `DecidableEq dom` |
| `SlicePFunctor.decidableShapeOver` | `DecidableEq cod` |
| `SlicePFunctor.decidableWValid` | `Finitary`, `DecidableEq I` (stated at `SlicePFunctor.{uA,uB,uI,uI} I I`) |

`Finitary` enters three of the five: the two domain-side quantifier
predicates and the W-type predicate. The remaining two —
`decidableDirectionOver` and `decidableShapeOver` — are single-element
equality checks taking only `DecidableEq`. None of the five receives an
instance that supplies `Finitary` for a finitary functor; that is the
omission this work addresses.

### mathlib

- `Mathlib.Data.FinEnum` provides `FinEnum.fin : FinEnum (Fin n)`, but it is
  `Classical.choice`-dependent — verified against the pinned tree,
  `#print axioms FinEnum.fin` reports `[propext, Classical.choice,
  Quot.sound]` (§ Verification performed).
- A choice-free `FinEnum (Fin n)` is constructible independently,
  `card := n`, `equiv := Equiv.refl (Fin n)`, `decEq := inferInstance`;
  verified axiom-free (§ Verification performed).
- No bundled finitary polynomial functor exists; the reuse target is this
  repository's `SlicePFunctor`.

## The finitary condition

`Finitary` reduces to `∀ a, FinEnum (B a)`. When each direction type is
`Fin (arity a)`, the `FinEnum` is the choice-free construction of § Prior
state, and `Finitary` is a derived field of the bundled structure rather
than a hypothesis. The remaining hypotheses are `DecidableEq` on the index
type(s), supplied by the caller; no finiteness is imposed on the shapes,
the domain, or the codomain.

| Predicate | Required of the structure | Supplied by the caller |
| --- | --- | --- |
| `decidableDirectionOver` | — | `DecidableEq dom` |
| `decidableForallDirection`, `decidableCompatible` | `Finitary` (derived) | `DecidableEq dom` |
| `decidableShapeOver` | — | `DecidableEq cod` |
| `decidableWValid` (diagonal) | `Finitary` (derived) | `DecidableEq I` |

The shape type is arbitrary: no instance enumerates shapes, and `Finitary`
depends only on the directions. A later specialization may restrict the
shapes (or the index types) to `Fin`; that is not this work (§ Out of
scope).

## Module layout

One new source module and one new test module.

| Path | Role |
| --- | --- |
| `Geb/Mathlib/Data/PFunctor/Slice/Finitary.lean` | the bundled structure, the coercion, the derived `Finitary`, the two-tier decidability wrappers |
| `GebTests/Mathlib/Data/PFunctor/Slice/Finitary.lean` | reduction tests for both tiers |

The choice-free `FinEnum (Fin n)` helper lives in `Slice/Finitary.lean`
for this branch, declared in `namespace FinEnum` as `FinEnum.finEnumFin`
so the eventual hoist to `Data/FinEnum.lean` (once a second consumer
arrives) is a move, not a rename. Hoisting is deferred to avoid adding to
an existing module before a second caller exists (§ Out of scope). It is a
named definition marked `@[instance_reducible]`, not a global `instance`;
see § Choice boundary.

Both modules are registered in their respective import-index files, and
`docs/index.md` is updated.

## Module contents

### The choice-free `FinEnum (Fin n)`

```lean
namespace FinEnum

/-- The choice-free `FinEnum (Fin n)`: the identity enumeration, axiom-free.
Permanent home `Data/FinEnum.lean`; declared here until a second consumer
arrives. -/
@[expose] @[instance_reducible]
def finEnumFin (n : ℕ) : FinEnum (Fin n) where
  card := n
  equiv := Equiv.refl (Fin n)
  decEq := inferInstance

end FinEnum
```

`Equiv.refl (Fin n)` discharges the equivalence laws definitionally;
`DecidableEq (Fin n)` is mathlib's constructive instance. The term is
axiom-free (§ Verification performed). It is marked `@[instance_reducible]`,
the transparency attribute the `warn.classDefReducibility` linter suggests
for a class-typed definition: it marks the definition reducible at instance
transparency (so instance synthesis can unfold it when matching) and
silences the linter. The `decide` tactic unfolds the definition by virtue
of its being a `def` (kernel WHNF computation unfolds plain definitions at
default transparency), independent of the attribute. The attribute is a
transparency annotation, not an instance registration — only the `instance`
keyword or an `@[instance]` attribute registers a global instance, and
`@[instance_reducible]` does neither (verified in § Verification performed).

It is deliberately not an `instance`. A global
`instance : FinEnum (Fin n)` coexists with mathlib's `FinEnum.fin`, and
which of the two instance search selects is decided by priority and
declaration order, not by axiom content: in the current toolchain a local
default-priority instance displaces `FinEnum.fin` by reverse declaration
order (verified in § Verification performed), but that outcome is a
property of declaration order, not of the axioms involved, and a mathlib
bump that changes `FinEnum.fin`'s priority would reverse it without indication.
Bundling the evidence and passing it explicitly removes the dependence on
resolution order (§ Choice boundary).

### `Slice/Finitary.lean`

The file carries a single `universe uA uD uC uI uX` declaration; the two
code blocks below share it (the structure block shows only the subset it
uses).

```lean
universe uA uD uC

structure FinitarySlicePFunctor (dom : Type uD) (cod : Type uC)
    : Type (max (uA + 1) uD uC) where
  A     : Type uA
  arity : A → ℕ
  r     : (a : A) → Fin (arity a) → dom
  q     : A → cod
```

The four fields present a finitary slice polynomial functor by its
direction arities: an arbitrary shape type `A`, the per-shape direction
count `arity`, the curried direction-input map into `dom`, and the
shape-output map into `cod`. The direction type of shape `a` is
`Fin (arity a)`. `@[ext]` is added, and `Inhabited` is provided by the
empty functor (`A := PEmpty`, whose direction and shape maps are unique;
see the instance in the namespace block below). `PEmpty.{uA+1} : Type uA`
keeps the instance universe-polymorphic in the shape parameter.
`Repr` and `DecidableEq` on the bundled structure are not derived.
`deriving Repr` fails: the function-typed fields (`arity`, `r`, `q`) carry
no `Repr` instances and the `A` field admits none. `DecidableEq` is not
required by the decidability deliverable, and no choice-free instance
exists over the dependent direction-input field `r` in general (the
non-dependent `FinEnum.decidablePiFinEnum` does not apply directly, and
`A` is arbitrary, not finite), so deriving it is omitted.

The carrier is recovered as the existing abstractions, not redefined. The
projections and wrappers live in `namespace FinitarySlicePFunctor`, which
is what makes `F.toSlicePFunctor` and `F.finitary` resolve as dot-notation
(Lean dot-notation `F.foo` for `F : FinitarySlicePFunctor …` reaches
`FinitarySlicePFunctor.foo F`); the index-type binders are implicit, the
codebase convention under `autoImplicit = false`:

```lean
universe uA uD uC uI uX

namespace FinitarySlicePFunctor

variable {dom : Type uD} {cod : Type uC}

@[expose]
def toSlicePFunctor (F : FinitarySlicePFunctor dom cod) :
    SlicePFunctor.{uA, 0, uD, uC} dom cod :=
  ⟨SliceDomPFunctor.ofCurried
      ⟨F.A, fun a ↦ Fin (F.arity a)⟩ dom (fun a b ↦ F.r a b), F.q⟩

@[expose] @[instance_reducible]
def finitary (F : FinitarySlicePFunctor dom cod) :
    F.toSlicePFunctor.toPFunctor.Finitary :=
  fun a ↦ FinEnum.finEnumFin (F.arity a)

instance : Inhabited (FinitarySlicePFunctor dom cod) where
  default := ⟨PEmpty, PEmpty.elim, fun a ↦ a.elim, PEmpty.elim⟩

/-- dom/cod-general: a domain-side quantifier predicate, forwarded through
`toSliceDomPFunctor` with the bundled `Finitary` and `DecidableEq dom`. -/
instance decidableForallDirection [DecidableEq dom] (F : FinitarySlicePFunctor dom cod)
    (a : F.toSlicePFunctor.A) (i : dom)
    {q : F.toSlicePFunctor.toSliceDomPFunctor.Direction a i → Prop}
    [DecidablePred q] : Decidable (∀ b, q b) :=
  @SliceDomPFunctor.decidableForallDirection dom F.toSlicePFunctor.toSliceDomPFunctor
    F.finitary inferInstance a i _ _

/-- dom/cod-general: compatibility of a direction assignment with a
projection, forwarded through `toSliceDomPFunctor` with the bundled
`Finitary` and `DecidableEq dom`. -/
instance decidableCompatible [DecidableEq dom] (F : FinitarySlicePFunctor dom cod)
    {X : Type uX} (p : X → dom) (a : F.toSlicePFunctor.A)
    (v : F.toSlicePFunctor.B a → X) :
    Decidable (F.toSlicePFunctor.toSliceDomPFunctor.Compatible p a v) :=
  @SliceDomPFunctor.decidableCompatible dom F.toSlicePFunctor.toSliceDomPFunctor
    F.finitary inferInstance _ p a v

/-- dom/cod-general: direction-fiber membership, forwarded with
`DecidableEq dom`. -/
instance decidableDirectionOver [DecidableEq dom] (F : FinitarySlicePFunctor dom cod)
    (a : F.toSlicePFunctor.A) (i : dom) :
    DecidablePred (F.toSlicePFunctor.toSliceDomPFunctor.DirectionOver a i) :=
  @SliceDomPFunctor.decidableDirectionOver dom F.toSlicePFunctor.toSliceDomPFunctor
    inferInstance a i

/-- dom/cod-general: codomain-side shape-fiber membership, forwarded with
`DecidableEq cod`. -/
instance decidableShapeOver [DecidableEq cod] (F : FinitarySlicePFunctor dom cod)
    (j : cod) :
    DecidablePred (F.toSlicePFunctor.ShapeOver j) :=
  @SlicePFunctor.decidableShapeOver dom cod F.toSlicePFunctor
    inferInstance j

/-- diagonal: W-type admissibility, forwarded with `Finitary` and `DecidableEq I`. -/
instance decidableWValid {I : Type uI} (F : FinitarySlicePFunctor I I)
    [DecidableEq I] (w : F.toSlicePFunctor.toPFunctor.W) :
    Decidable (F.toSlicePFunctor.WValid w) :=
  @SlicePFunctor.decidableWValid I F.toSlicePFunctor F.finitary inferInstance w

end FinitarySlicePFunctor
```

`toSlicePFunctor` and `finitary` carry `@[expose]` so the test module can
reduce through them across the module boundary (the existing slice modules
use the same attribute for the same reason). `finitary` additionally carries
`@[instance_reducible]`: `Finitary` is a Pi type (`∀ a, FinEnum (P.B a)`),
not a class, so the `warn.classDefReducibility` linter does not fire on it;
the attribute is for its transparency benefit, allowing instance resolution
to unfold `finitary` when it appears in an instance-argument position. It is
not an instance registration.

The two `DecidableEq`-only wrappers (`decidableDirectionOver` and
`decidableShapeOver`) are convenience forwarding rather than part of the
`Finitary`-supplying concern; they use the same explicit-supply form as the
`Finitary`-consuming wrappers.

The wrapper form follows from a property of instance resolution. The
existing instances are stated on `SlicePFunctor`; a goal on a
`FinitarySlicePFunctor` reaches them through the `toSlicePFunctor`
projection, a `def` that instance resolution does not unfold. The wrappers
therefore supply the coerced functor and the bundled evidence by explicit
argument. The explicit-supply `instance` form above is the chosen form: it
elaborates and `decide`-reduces to a verdict through the wrapper, the `def`
projection, and an `abbrev` carrier (§ Verification performed). The test
fixture's carrier form (`abbrev`/`@[reducible]`, as in
`Slice/Decidable.lean`) is an implementation detail of the test, not of
the module.

## Tests

A reduction test on a small endofunctor exercises both tiers by `decide`,
with one positive and one negative verdict per predicate:

- a branching shape and a leaf shape, directions `Fin`,
- an admissible and an inadmissible W-tree for `WValid` on the diagonal,
- a compatible and an incompatible assignment and a fiber verdict for the
  dom/cod-general tier, including a `dom ≠ cod` example
  (`FinitarySlicePFunctor (Fin 2) (Fin 3)`, say) to confirm the general
  tier carries no diagonal assumption.

The `DecidablePred`-returning wrappers (`decidableDirectionOver`,
`decidableShapeOver`) are tested by applying them to a concrete direction
or shape element, yielding a `Decidable` on a `Prop` that `decide` can
reduce.

The shape type in the fixture is chosen to be non-`Fin` (a small inductive
or `Bool`), to confirm the structure imposes no finiteness on shapes. Each
verdict is a named `def`, not a bare `example`: the axiom linter traverses
only named declarations, and a reduction assertion as a bare `example`
would escape it (§ Choice boundary). The `decide` reductions rely on two
distinct mechanisms. Instance resolution (which selects the wrapper)
operates at reduced transparency and cannot invert the `toSlicePFunctor`
`def` projection to match the wrapper's type against the goal; the test
fixture is therefore declared with an `abbrev`/`@[reducible]` carrier (or
explicit `@`-supply) so the types are already in reduced form for instance
matching — the same approach the `Slice/Decidable.lean` test fixture uses.
Once the instance is resolved, `decide`'s kernel reduction unfolds all
`def`s (including `toSlicePFunctor` and `finitary`, both `@[expose]`)
unconditionally. The dom/cod-general wrappers match only when their index
arguments are presented at the projected type (`a : F.toSlicePFunctor.A`;
`v : F.toSlicePFunctor.B a`): presenting an index at an unfolded type (a
`Bool` literal where `F.A` reduces to `Bool`) leaves the projection folded
and instance synthesis fails. The diagonal `decidableWValid` wrapper is
unaffected, its conclusion matching the goal shape directly.

## Transcription or novel

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing requires each definition to be marked.

| Declaration | Status | Source |
| --- | --- | --- |
| `FinitarySlicePFunctor`, `toSlicePFunctor`, `finitary`, the tier wrappers, `finEnumFin` | neither | packaging of the polynomial-functor and slice-functor notions already cited in `Slice/Basic.lean` and `Slice/W.lean`, and instance plumbing over the existing decidability layer |

The rows marked *neither* state nothing found in published mathematics:
they bundle a finiteness hypothesis and forward it to a predicate defined
and cited elsewhere. The underlying notions — polynomial functor, slice
functor, dependent polynomial functor, W-type — are covered by the
citations the slice modules already carry (`[GambinoHyland2004]`,
`[GambinoKock2013]`, `[AltenkirchGhaniHancockMcBrideMorris2015]`). The
standard notion "finitary polynomial functor" is already represented by
`PFunctor.Finitary`, marked *neither* in its own spec. No new bib entry is
added.

## Universe constraints

The two index types are universe-polymorphic: `dom : Type uD`,
`cod : Type uC`. The shape type is an arbitrary field `A : Type uA`. The
direction types are `Fin` and therefore `Type 0`. The coercion instantiates
`SlicePFunctor.{uA, 0, uD, uC}`, whose four universe parameters are
independent, so the `Type 0` of the directions imposes no constraint on
`uA`, `uD`, or `uC`: the functor acts on slices over a `dom` and a `cod`
at any two universes, with shapes at any universe. This is the reason a
lift of the index types (or the shapes) is never needed.

The structure's result sort is `Type (max (uA + 1) uD uC)`: the `+ 1` over
`uA` is because the shape type is a field (`A : Type uA`), as in
`PFunctor`/`SlicePFunctor`; the direction arities are `Type 0`-valued and
contribute no universe parameter.

The diagonal tier instantiates both index parameters to the same type
`I : Type uI`, matching `SlicePFunctor.{uA, uB, uI, uI} I I`, the form
`decidableWValid` is stated at. No equality proof between distinct types is
involved; the diagonal is the caller passing one type for both arguments.

No new universe constraint is imposed on the existing slice declarations;
the finitary module instantiates them at the universes they already carry.

## Choice boundary

Every declaration in this branch is within the axiom linter's default
permitted set `{propext, Quot.sound}`; none reaches `Classical.choice`.
The bundled `finitary` field is axiom-free, and the instances inherit the
`{propext, Quot.sound}` profile of the bounded-quantifier routing they
specialize. The reasoning has two parts.

**Routing.** The existing instances this work specializes already route
bounded quantifiers through `FinEnum.toList` and `List.decidableBAll`,
never through `Fintype` (their § Choice boundary). The wrappers add no
quantifier; they forward the bundled evidence, so they inherit that
routing and its axiom profile.

**The `FinEnum` source.** The bundled `Finitary` is built from
`finEnumFin`, which is axiom-free (§ Verification performed). Two sources
of `Classical.choice` dependence are avoided.

- *A global `instance : FinEnum (Fin n)` is not declared.* mathlib's
  `FinEnum.fin` is `Classical.choice`-dependent; a second global instance
  on `Fin n` is resolved against it by priority and order, and the outcome
  is not axiom-guaranteed. The choice-free term is instead a named
  definition marked `@[instance_reducible]` (a transparency attribute, not
  an instance registration), supplied to the instances by explicit
  argument.
- *No `FinEnum` is formed on a derived type through a choice-dependent
  combinator.* `finEnumFin` uses `Equiv.refl`, not `FinEnum.ofList` or
  `FinEnum.fin`; the prior layer's finding that `ofList` and `fin` carry
  `Classical.choice` therefore does not reach this branch.

No module in this branch is added to `GebMeta.classicalAllowedModules`.
The reduction assertions in § Tests are named `def`s so the axiom linter
sees them.

## Verification performed

Compiled against the pinned toolchain during design, with axioms as
reported by `#print axioms`.

| Fragment | Result |
| --- | --- |
| `finEnumFin` (`card := n`, `equiv := Equiv.refl (Fin n)`, `decEq := inferInstance`) | compiles; `#print axioms` reports no axioms |
| mathlib `FinEnum.fin : FinEnum (Fin n)` | `#print axioms` reports `[propext, Classical.choice, Quot.sound]` |
| `@[instance_reducible]` on a class-typed `def` (e.g. `@[instance_reducible] def finEnumIR : FinEnum (Fin n)`) | does not register a global instance: `inferInstance : FinEnum (Fin n)` still resolves to `FinEnum.fin` (choice-dependent), not to `finEnumIR`. Only the `instance` keyword / `@[instance]` registers. So `@[instance_reducible] def finEnumFin` does not compete with `FinEnum.fin` |
| `inferInstance : FinEnum (Fin n)` with a local default-priority choice-free `FinEnum (Fin n)` `instance` registered | resolves to the local instance (axiom-free) by reverse declaration order in the current toolchain; the outcome is declaration-order-dependent, not axiom-guaranteed — the reason `finEnumFin` is a `def` marked `@[instance_reducible]`, not an `instance` |
| `FinitarySlicePFunctor` result sort `Type (max (uA + 1) uD uC)` (shape type `A` a field) | compiles |
| `SlicePFunctor.{uA, 0, uD, uC} dom cod` as the coercion result type | consistent: `SlicePFunctor (dom : Type uD) (cod : Type uC) : Type (max (uA+1) (uB+1) uC uD)` extends `SliceDomPFunctor.{uA, uB, uD} dom`, so `uB = 0` leaves `uA`, `uD`, `uC` free |
| the five existing instances' hypotheses | read from `Slice/Decidable.lean` |
| the dom/cod-general wrappers (`decidableForallDirection`, `decidableCompatible`) and the diagonal `decidableWValid` wrapper, plus the two `DecidableEq`-only wrappers (`decidableDirectionOver`, `decidableShapeOver`) | elaborate within `namespace FinitarySlicePFunctor` with `{dom}{cod}` implicit binders (dot-notation `F.toSlicePFunctor`/`F.finitary` resolves); `finitary` is axiom-free, the `Finitary`-consuming wrappers resolve at `{propext, Quot.sound}` |
| the explicit-supply `instance` form (the chosen form) | elaborates and `decide`-reduces to a verdict through the wrapper + `def` projection + `abbrev` carrier; the form is chosen, not deferred |
| `@[expose]` on `toSlicePFunctor`, `finitary`, and `finEnumFin` | cross-module `decide`-reduction in the test module proceeds through all three definitions; matches the existing slice modules' use of `@[expose]` for cross-module unfolding |

## Documentation and roadmap

- `docs/index.md` gains an entry for the finitary slice functor, placed
  after the slice W-type and decidability entries, noting it supplies the
  `Finitary` hypothesis of the decidability layer in the finitary-with-`Fin`
  -directions case.
- The new module carries the mandatory `/-! … -/` module docstring (with
  `## Main definitions`, `## Tags`, and the other non-vacuous sections of
  `docs/rules/lean-coding.md` § Documentation) and a `/-- … -/` docstring
  on every `def`, `structure`, `instance`, and field.
- `TODO.md` gains a note on the follow-on workstreams: the stronger
  specializations that restrict shapes or index types to `Fin`, and the
  presheaf finitary case (with the finite-category construction it
  depends on).

## Out of scope

- Stronger finite specializations: restricting the shape type to `Fin`, or
  the index types to `Fin`. The decidability mechanism needs neither; those
  are separate specializations, recorded in `TODO.md`.
- The presheaf case: a bundled finitary presheaf polynomial functor over a
  finite category, whose category input is built from object counts and a
  composition function whose associativity is checked exhaustively,
  identities implicit. It is a separate spec and branch.
- Hoisting `finEnumFin` to `Data/FinEnum.lean`. Deferred until the
  presheaf layer gives a second consumer.

## References

The notions this work packages are cited in the slice modules it builds
on; no new bib entry is added.

- `[GambinoHyland2004]` — well-founded trees and dependent polynomial
  functors.
- `[GambinoKock2013]` — polynomial functors and polynomial monads.
- `[AltenkirchGhaniHancockMcBrideMorris2015]` — indexed containers.
