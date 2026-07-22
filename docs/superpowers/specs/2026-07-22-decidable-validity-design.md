# Decidable specializations of the slice and presheaf validity predicates

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Concern shape and the PR split](#concern-shape-and-the-pr-split)
- [Prior state](#prior-state)
  - [This repository](#this-repository)
  - [mathlib](#mathlib)
- [The decidability conditions](#the-decidability-conditions)
- [Module layout](#module-layout)
- [Module contents](#module-contents)
  - [`Data/FinEnum.lean`](#datafinenumlean)
  - [`Data/W/Basic.lean`](#datawbasiclean)
  - [`Univariate/Finitary.lean`](#univariatefinitarylean)
  - [`Slice/Decidable.lean`](#slicedecidablelean)
  - [`Presheaf/Decidable.lean`](#presheafdecidablelean)
- [Tests](#tests)
- [Transcription or novel](#transcription-or-novel)
- [Universe constraints](#universe-constraints)
- [Choice boundary](#choice-boundary)
- [Verification performed](#verification-performed)
- [Complexity of the checkers](#complexity-of-the-checkers)
- [Documentation and roadmap](#documentation-and-roadmap)
- [Out of scope](#out-of-scope)
- [References](#references)

<!-- END doctoc -->

## Scope

Roadmap item 1 of the polynomial-functor sequence in
[TODO.md](../../../TODO.md): supply decision procedures for the
term-validity predicates of the slice and presheaf polynomial functors
in the case where those predicates are decidable, together with proofs
that the procedures decide them.

The predicates are the ones restricting a functor's value to a
sub-collection of an unrestricted one: the domain-restriction predicate
of a single step, and the hereditary predicate defining the
corresponding W-type. Six predicates across four existing modules, all
currently stated as `Prop` with no computational content.

Deciding the *functor-law* predicates of `Presheaf/Basic.lean`
(`DirectionRestrId`, `DirectionRestrComp`, `ShapeRestrId`,
`ShapeRestrComp`, `ReindexNaturality`, `ReindexId`, `ReindexComp`, and
the two `IsFunctorial` bundles) is excluded. Those are properties of a
functor, not of a term, and nothing in the present tree consumes them as
decisions. Whether item 4's decidable universal morphisms will want them
is a forecast about a spec not yet written, and is recorded as an
assumption rather than a finding (§ Verification performed).

## Concern shape and the PR split

The branch spans three upstream destinations. Under
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape it is one
concern — deciding the validity predicates — but the floodgate test
requires dependency-ordered PRs, so the intended split is recorded here.

| PR | Modules | Depends on |
| --- | --- | --- |
| 1 | `Data/FinEnum.lean` | — |
| 2 | `Data/W/Basic.lean` (`para`, `beq`) | 1 |
| 3 | `Univariate/Finitary.lean` | — |
| 4 | `Slice/Decidable.lean` | 1, 3 |
| 5 | `Presheaf/Decidable.lean` | 1, 2, 3, 4 |

PRs 4 and 5 are additionally gated on content not yet upstreamed:
`Slice/Basic.lean`, `Slice/W.lean`, and the existing `WType.elim_mk` /
`elim_unique` additions to `Data/W/Basic.lean` for PR 4; those plus
`Presheaf/Basic.lean` and `Presheaf/W.lean` for PR 5. The gating is
recorded so the shipping order is derivable; it is not a deliverable of
this branch.

PRs 1 to 3 are independently reviewable and independent of the slice and
presheaf layers; PR 3 is polynomial-functor content, PRs 1 and 2 are not.
They are not split onto separate branches because each exists only to
serve PRs 4 and 5: a `Data/FinEnum.lean` carrying three instances with no
consumer would not meet
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost on its own.

## Prior state

### This repository

| Module | Predicate | Shape |
| --- | --- | --- |
| `Slice/Basic.lean` | `SliceDomPFunctor.Compatible p a v` | `p ∘ v = r ∘ Sigma.mk a`, an equation between functions out of `F.B a` |
| `Slice/Basic.lean` | `SliceDomPFunctor.DirectionOver a i` | pointwise, `rCurried a b = i` |
| `Slice/Basic.lean` | `SlicePFunctor.ShapeOver j` | pointwise, `q a = j` |
| `Slice/W.lean` | `SlicePFunctor.WValid` | the `valid` component of the `WType.elim` fold `wIndexValid`, whose step is `NodeValid = AllValid ∧ OverInput` |
| `Presheaf/Basic.lean` | `PresheafDomPFunctorData.IsNatural x` | `∀ i i' (f : i' ⟶ i) (b : Direction a i), value x (directionRestr a f b) = Z.map f.op (value x b)` |
| `Presheaf/W.lean` | `PresheafPFunctor.IsHereditarilyNatural` | `SlicePFunctor.W.RecProp` of a local naturality equation between sibling subtrees |

`Slice/W.lean` additionally defines the node-level `ForAll`, `AllValid`,
`OverInput`, and `NodeValid`, through which `WValid` is defined. Only
`AllValid` and `NodeValid` reach the arbitrary `Prop` field
`WIndex.valid`, so no hypothesis on the functor makes them decidable.
`ForAll` and `OverInput` are decidable given `F.Finitary` together with
decidability of their own arguments — `DecidablePred P` for the first,
`DecidableEq I` for the second, whose equation is between functions out
of `F.B a` and so needs the domain enumerated as well. None receives an
instance, for want of a consumer (§ `Slice/Decidable.lean`).

None carries a `Decidable` instance. `SliceDomPFunctor.Direction a i` and
`SlicePFunctor.Shape j` are subtypes of `DirectionOver` and `ShapeOver`;
`SliceDomPFunctor.Obj`, `PresheafDomPFunctorData.obj`, and
`SlicePFunctor.W` are subtypes cut out by the remaining predicates, and
the fibers of the presheaf `PresheafPFunctor.W` are a `ULift` of such a
subtype.

### mathlib

- No finitary-`PFunctor` predicate exists, and no finitary-container
  predicate under any name. Where mathlib needs the property it writes
  the instance binder directly, as `Mathlib/Data/W/Basic.lean` does with
  `[∀ a : α, Fintype (β a)]`.
- `CategoryTheory.FinCategory` bundles `Fintype J` and
  `Fintype (j ⟶ j')`, but requires `SmallCategory J`. The presheaf
  functors here are stated at `[Category.{vI} I]` with `I : Type uI`
  unconstrained.
- `Mathlib/Data/W/Basic.lean` has no `DecidableEq (WType β)`. Its only
  route to one is `Encodable (WType β)`, which requires `Encodable α`,
  `∀ a, Encodable (β a)`, and `∀ a, Fintype (β a)` — a countability
  hypothesis neither needed nor wanted, reached through an auxiliary
  depth-stratified encoding.
- `WType.elim` has no paramorphic companion: a fold whose step sees the
  node's children as subtrees, not only their folded values.
- `Mathlib/Data/FinEnum.lean` defines `FinEnum`, a constructive
  enumeration (`card`, `equiv : α ≃ Fin card`, `decEq`), with instances
  for `ULift`, `Prod`, `Sum`, `Fin`, `Finset`, `Subtype`, `Sigma`,
  `PSigma` in four variants, `Quotient`, `Pi`, `Empty`, `PEmpty`,
  `PUnit`, list-membership subtypes, and the machine-integer types,
  among others. It supplies no `Decidable` instance for a bounded `∀`,
  and its
  `(priority := 100) [FinEnum α] : Fintype α` instance is the only
  bridge between the two notions. Those of its instances that are
  derived through `FinEnum.ofList` are `Classical.choice`-dependent
  (§ Choice boundary).
- `List.Pi.finEnum : FinEnum (∀ a, β a)` — declared inside
  `namespace List` — together with the `decEq` field already yields
  `DecidableEq (α → Y)` when `Y` is finitely enumerable. The
  `decidablePiFinEnum` instance below is still needed because it drops the
  finiteness hypothesis on `Y`, keeping only `DecidableEq Y`.
- There is no `FinEnum (PLift p)`, so the hom-sets of a preorder
  category are not enumerable out of the box (§ Tests).

## The decidability conditions

The mathematical content of this item is the delimitation below. Each
row lists hypotheses sufficient for the decision procedure built here.
No claim of necessity is made: decidability is a property of a
proposition, and a proposition may be decidable for reasons unrelated to
the procedure deciding it here.

| Predicate | Hypotheses |
| --- | --- |
| `DirectionOver a i` | `DecidableEq dom` |
| `ShapeOver j` | `DecidableEq cod` |
| `Compatible p a v` | `F.Finitary`, `DecidableEq dom` |
| `WValid w` | `F.Finitary`, `DecidableEq I` |
| `IsNatural x` | `F.Finitary`, `FinEnum I`, `∀ i i' : I, FinEnum (i' ⟶ i)`, `∀ i : I, DecidableEq (Z.obj ⟨i⟩)` |
| `IsHereditarilyNatural z` | `F.Finitary`, `FinEnum I`, `∀ i i' : I, FinEnum (i' ⟶ i)`, `DecidableEq F.A` |

`DecidableEq I` is not listed in the last two rows: `FinEnum I` carries
`decEq` as a field, registered upstream at priority 100. Supplying
`DecidableEq I` as well would work — being below default priority, the
explicit binder would win uniformly rather than mixing — but it is
redundant, and
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost tells against
carrying a binder that resolution already supplies. The same reasoning
removes `DecidableEq (F.B a)` everywhere: `Finitary` unfolds to a
`FinEnum` binder, which carries it.

Four observations fix the shape of the layer.

**Finitarity is the branching condition, and nothing more.** The shape
type `F.A` is never quantified over by the slice predicates — only
compared against — so it may be infinite. `WValid` needs no hypothesis on
`F.A` at all. `F.A` becomes relevant only at `IsHereditarilyNatural`,
whose local condition is an equality of subtrees and therefore needs
`DecidableEq F.A` through `DecidableEq (WType β)`.

**Decidable equality of the base index types is a separate hypothesis.**
`dom` and `cod` are not required finite, so their decidable equality does
not follow from finitarity. The two fiber predicates need it and nothing
else: no finiteness whatever.

**The presheaf side assumes finitely many objects, not only finite
hom-sets.** `IsNatural` quantifies over four variables: `i`, `i'`, `f`,
and `b`. The `i` quantifier alone is eliminable — `Direction a i` is the
fiber of `rCurried a` over `i`, hence empty off the finite image of
`rCurried a`, so `∀ i, ∀ b : Direction a i` reindexes as `∀ b : F.B a` at
`i := rCurried a b` — but `i'` ranges over every object admitting a
morphism into `i`. A `FinEnum (Σ i', (i' ⟶ i))` on each slice would also
suffice; `FinEnum I` with finite hom-sets is assumed instead, being the
form the presheaf modules' other consumers will want. The reindexing is
not performed; the predicate is decided as stated.

**The input presheaf must have decidable equality of values.**
`IsNatural`'s body is an equation in `Z.obj ⟨i'⟩`. This is a hypothesis
on `Z`, not on `F`, and it does not arise for `IsHereditarilyNatural`,
where the presheaf is `F.W` and value equality reduces to equality of the
underlying trees.

## Module layout

Four new content modules and one modified, plus index modules and the
`GebTests/` mirrors.

Imports of each new or modified module, both from mathlib and from this
repository. `public import` marks a re-exported dependency; plain
`import` marks one used only internally.

| Module | Imports |
| --- | --- |
| `Data/FinEnum.lean` | `public import Mathlib.Data.FinEnum` |
| `Data/W/Basic.lean` | existing `public import Mathlib.Data.W.Basic`; adds `public import Geb.Mathlib.Data.FinEnum` |
| `Univariate/Finitary.lean` | `public import Mathlib.Data.PFunctor.Univariate.Basic`, `public import Mathlib.Data.FinEnum` |
| `Slice/Decidable.lean` | `public import Geb.Mathlib.Data.PFunctor.Slice.W`, `public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary`, `public import Geb.Mathlib.Data.FinEnum`, plain `import Geb.Mathlib.Data.W.Basic` |
| `Presheaf/Decidable.lean` | `public import Geb.Mathlib.Data.PFunctor.Presheaf.W`, `public import Geb.Mathlib.Data.PFunctor.Slice.Decidable`, `public import Geb.Mathlib.Data.W.Basic` |

`Slice/Decidable.lean` reaches `Slice/Basic.lean` through
`Slice/W.lean`, and `Presheaf/Decidable.lean` reaches
`Presheaf/Basic.lean` and `Slice/W.lean` through `Presheaf/W.lean`. Both
name `Data/W/Basic.lean` explicitly: `Slice/Decidable.lean` needs
`WType.elim_mk`, `Presheaf/Decidable.lean` needs `WType.para` / `WType.beq`,
and neither reaches it transitively — `Slice/W.lean` imports
`Slice/Basic.lean` and, through it, mathlib's `Mathlib.Data.W.Basic`, not
this repository's extension of it.

`Slice/Decidable.lean`'s import is plain: it uses `elim_mk` only in a
proof term, where a plainly-imported constant may appear.
`Presheaf/Decidable.lean`'s is `public`: it names `WType.para` and
`WType.beq` in the `@[expose]`d body of `isHereditarilyNaturalBoolCore`,
and an exposed body may name only constants from `public import`s.

`lake shake`, run in the pre-push checklist and CI, rejects an import
whose constants are all reachable another way; it does not adjudicate
`public` against plain, which is a visibility choice. The split above is
therefore a prediction on two independent axes: shake governs which
imports survive, and whether a downstream module needs the constants
re-exported governs which are `public`.

| Module | Upstream destination | Choice |
| --- | --- | --- |
| `Geb/Mathlib/Data/FinEnum.lean` | `Mathlib/Data/FinEnum.lean` | choice-free |
| `Geb/Mathlib/Data/W/Basic.lean` | `Mathlib/Data/W/Basic.lean` | choice-free |
| `Geb/Mathlib/Data/PFunctor/Univariate/Finitary.lean` | `Mathlib/Data/PFunctor/Univariate/Finitary.lean` (new) | choice-free |
| `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean` | `Mathlib/Data/PFunctor/Slice/` | choice-free |
| `Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean` | `Mathlib/Data/PFunctor/Presheaf/` | choice-free |

The decidable layers are separate modules rather than additions to
`Slice/Basic.lean`, `Slice/W.lean`, `Presheaf/Basic.lean`, and
`Presheaf/W.lean` so that the constructive cores keep their present
import sets. Those four modules import only
`Mathlib.Data.PFunctor.Univariate.Basic` and category-theory basics;
folding the decidable content into them would add the `FinEnum` closure
to every downstream consumer of the cores.

`Data/W/Basic.lean` is modified rather than duplicated: it is already
this repository's extension point for `WType` (`elim_mk`, `elim_unique`).
Its module docstring, currently titled *The W-type fold: computation rule
and uniqueness*, is rewritten to cover the paramorphism and decidable
equality.

`Presheaf/Decidable.lean` reaches `Mathlib.CategoryTheory.*` only
transitively, through `Presheaf/W.lean`. [TODO.md](../../../TODO.md)
§ Upstream placement of categorical wrappers enumerates the files that
import those modules *directly*, and records that transitive importers
"follow whatever placement is settled for them". `Presheaf/Decidable.lean`
is therefore a transitive importer and is not added to that enumeration;
its placement follows `Presheaf/W.lean`'s, and the upstream destination
recorded above is provisional on that decision, which the user takes.

## Module contents

The sketches below give signatures. Declaration docstrings are mandatory
per [docs/rules/lean-coding.md](../../rules/lean-coding.md) and are
omitted here only for brevity; instance binders fixed by
§ The decidability conditions may be repeated or elided as legibility
suggests. (That rule mandates a result-sort ascription for a structure,
of which this branch defines none; `Finitary`'s ascription is the
separate matter of § Universe constraints.)

Every `def` a `GebTests/` mirror must reduce through carries `@[expose]`,
as `Slice/Basic.lean` and `Slice/W.lean` already document for their own
definitions: under this repository's module system a `public section`
definition's body is not visible downstream without it, so `decide`
cannot unfold it across the module boundary. The `@[expose]` set is
`para`, `paraStep`, `beq`, `wValidData`, `wValidStep`, `wValidBool`,
`wRestrTreeRaw`, and `isHereditarilyNaturalBoolCore`.

`abbrev`s and `instance`s are exposed by default, and `@[expose]` on
either is an error rather than a redundancy, so `Finitary` and the
`Decidable` instances are absent from that set.

The algebra steps `paraStep` and `wValidStep` are public `@[expose]`
`def`s, not private, and carry docstrings accordingly. An exposed body
may not name a private declaration, and `@[expose]` on a private
declaration is itself an error, so a private step is unavailable to an
exposed fold. `Slice/W.lean` already follows this pattern with
`elimStep` / `elimData`. Only `paraStep_fst`, a theorem whose proof is
not interface, stays private.

An exposed body may likewise name only constants from `public import`s,
which is what forces `Presheaf/Decidable.lean`'s import of
`Data/W/Basic.lean` to be `public` (§ Module layout).

### `Data/FinEnum.lean`

Three instances, in `namespace FinEnum`, consumed by `Data/W/Basic.lean`,
`Slice/Decidable.lean`, and `Presheaf/Decidable.lean`.

```text
FinEnum.decidableForallFinEnum : {p : α → Prop} → [DecidablePred p] → [FinEnum α] →
    Decidable (∀ x, p x)
FinEnum.decidableForallSubtype : {p : α → Prop} → [DecidablePred p] →
    {q : Subtype p → Prop} → [DecidablePred q] → [FinEnum α] →
    Decidable (∀ x : Subtype p, q x)
FinEnum.decidablePiFinEnum : [DecidableEq Y] → [FinEnum α] → DecidableEq (α → Y)
```

The predicate arguments are implicit and the finiteness binder last,
matching `Fintype.decidableForallFintype`'s shape; `decidablePiFinEnum`
is named after `Fintype.decidablePiFintype`, its analogue.

The namespace follows mathlib's practice of placing a decidability
instance in the namespace of the finiteness notion it consumes, and
`decidableForallFinEnum` is named after its direct analogue
`Fintype.decidableForallFintype`. The name `decidableBAll` is avoided:
in `List.decidableBAll` the `B` marks a quantifier *bounded* by
membership in a list, whereas these quantify over the type.

The first two are `decidable_of_iff` transporting `List.decidableBAll`
along a membership fact — `FinEnum.mem_toList`, composed for the second
with the subtype projection. The third reduces `f = g` to `∀ a, f a = g a`
by `funext_iff` and then appeals to the first.

`decidableForallSubtype` decides a quantifier over a decidable subtype
without forming a `FinEnum` on the subtype, by ranging over the ambient
type's enumeration and discharging the subtype's predicate inside the
body. This is required, not merely convenient: mathlib's
`FinEnum.Subtype.finEnum` is `Classical.choice`-dependent (§ Choice
boundary).

All three pin their `Decidable` argument explicitly with `@`. Left to
inference, resolution takes mathlib's `[FinEnum α] : Fintype α` bridge
and lands on `Fintype.decidableForallFintype`, which depends on
`Classical.choice`; the resulting instance typechecks and carries the
dependency.

All three are declared at default priority, and win resolution by
declaration order: `Geb/Mathlib/Data/FinEnum.lean` imports
`Mathlib.Data.FinEnum`, so it is later than
`Fintype.decidableForallFintype` in every linearization, and Lean tries
equal-priority instances in reverse declaration order. That is the same
mechanism by which a test module's local `FinEnum` displaces mathlib's
(§ Tests), and it needs no annotation.

A priority annotation is deliberately not used. Two of the three have
maximally general heads, so raising them in `Mathlib/Data/FinEnum.lean`
would change which instance every downstream mathlib goal of those shapes
resolves to, with consequences for `decide` performance this branch does
not measure. The ordering therefore rests on import order alone, and the
axiom linter is what detects a site where it fails to hold.

### `Data/W/Basic.lean`

The paramorphism, and decidable equality.

```text
para    : (γ : Type uC) → ((Σ a : α, β a → WType β × γ) → γ) → WType β → γ
para_mk : para γ fγ (mk a f) = fγ ⟨a, fun b ↦ (f b, para γ fγ (f b))⟩

beq             : [DecidableEq α] → [∀ a, FinEnum (β a)] → WType β → WType β → Bool
beq_mk          : beq (mk a f) (mk a' f') =
                    if h : a = a' then decide (∀ b, beq (f b) (f' (h ▸ b)) = true) else false
beq_eq_true_iff : beq s t = true ↔ s = t
WType.instDecidableEq : DecidableEq (WType β)
```

`para` is `elim` at the carrier `WType β × γ`, with an exposed step
`paraStep` and a private lemma `paraStep_fst` — proved by one
`WType.rec` — that the fold's first component reconstructs its input.
`para_mk` is then a `congrArg` over that lemma; unlike `elim_mk` it does
not hold by `rfl`.

`beq` is `elim` at the carrier `WType β → Bool`, comparing shapes and
then quantifying over the finite direction type. `beq_eq_true_iff` is one
`WType.rec`, inside which the shape equality is split by explicit case
analysis on the `DecidableEq α` instance. `by_cases` would also stay
choice-free here, since it uses `Decidable.byCases` when an instance is in
scope; the explicit split is chosen because it puts the same `dite`
scrutinee in the proof as in `beq_mk`, so the two sides reduce alike. The
instance is `decidable_of_iff` of `beq_eq_true_iff`.

`beq` names a `Bool`-valued equality without a `BEq` class instance.
`BEq` and `LawfulBEq` instances are out of scope: nothing in this branch
consumes `==` on a `WType`, and `DecidableEq` is what the checkers need.

Comparing two trees consults the children's folded results only, so
`beq` uses `elim`, not `para`. Its algebra is inlined rather than named:
unlike `paraStep` and `wValidStep` it is a single `dite`, it is used
once, and nothing downstream reduces through it separately.

### `Univariate/Finitary.lean`

```text
abbrev PFunctor.Finitary (P : PFunctor.{uA, uB}) : Type (max uA uB) :=
  ∀ a : P.A, FinEnum (P.B a)
```

An `abbrev`, not a `class`. Being reducible, it is transparent to
instance resolution, so `[P.Finitary]` supplies `FinEnum (P.B a)` and
hence `DecidableEq (P.B a)` with no `instance` attribute registration —
where a `class`'s fields would be inert until registered
`instance_reducible, instance`. It introduces no new head symbol and so
no new instance-resolution behaviour: `[P.Finitary]` is the binder
`[∀ a, FinEnum (P.B a)]` under a name.

The name is worth a module, narrowly. Expanded, the binder is short, and
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost tells against
an abbreviation that only saves characters. What it buys instead is a
term for a notion the roadmap, `docs/index.md`, and this branch's own
`TODO.md` item all name in prose — a finitary polynomial functor — which
mathlib lacks under any spelling (§ Prior state), and which the
decidability results are stated relative to. The module is the smallest
unit that can carry it to `Mathlib/Data/PFunctor/Univariate/`, since its
destination differs from every other module here. Were the notion to stay
unnamed, four rows of § The decidability conditions would repeat the
expansion and the roadmap would have no referent.

It is declared on `PFunctor` rather than on `SliceDomPFunctor` so that
one binder serves all three layers. Generalized field notation resolves
through the parent projections, so the binder is written `[F.Finitary]`
whether `F` is a `SliceDomPFunctor`, a `SlicePFunctor`, or a
`PresheafPFunctor` — the same mechanism by which the existing sources
already write `F.A` and `F.B a` at those layers.

The category-side finiteness is carried as the plain binders
`[FinEnum I] [∀ i i' : I, FinEnum (i' ⟶ i)]`. No alias is introduced:
the object half is `FinEnum I`, already mathlib's own, and the hom half
is a single binder that a name would not shorten. In particular no
analogue of `CategoryTheory.FinCategory` is defined, so this branch
raises no question about mathlib's removal of `DecidableEq` from that
class.

### `Slice/Decidable.lean`

In order: the two fiber-predicate instances; the direction-quantifier
instance; the `Compatible` instance; and the W-type checker.

```text
SliceDomPFunctor.decidableDirectionOver : [DecidableEq dom] →
    DecidablePred (F.DirectionOver a i)
SlicePFunctor.decidableShapeOver : [DecidableEq cod] →
    DecidablePred (F.ShapeOver j)
SliceDomPFunctor.decidableForallDirection : {q : F.Direction a i → Prop} →
    [DecidablePred q] → [F.Finitary] → [DecidableEq dom] →
    Decidable (∀ b, q b)
SliceDomPFunctor.decidableCompatible : [F.Finitary] → [DecidableEq dom] →
    Decidable (F.Compatible p a v)
```

`decidableForallDirection` is required rather than redundant.
`SliceDomPFunctor.Direction` is a `def`, and instance resolution runs at
`instances` transparency, which does not unfold a semireducible `def`; so
a goal `Decidable (∀ b : F.Direction a i, q b)` does not match
`FinEnum.decidableForallSubtype`'s head, whose subject is a literal
`Subtype`. The `@[implicit_reducible]` attribute `Direction` already
carries does not change this. The instance is stated at `Direction` and
delegates to `FinEnum.decidableForallSubtype`.

No analogue is stated at `SlicePFunctor.Shape`, and no instance is stated
for any of the four node-level predicates. `WValid` is decided through
`wValidBool`, whose correctness lemma is a `Prop`-level equivalence
needing no instance, so none of `ForAll`, `AllValid`, `OverInput`,
`NodeValid` has a consumer; `wValidStep` decides `OverInput` inline and
pointwise, through `decidableForallFinEnum`. `AllValid` and `NodeValid`
have a second reason: no hypothesis makes them decidable, their arbitrary
`Prop` field being out of reach (§ Prior state).

`decidableCompatible` is the content consumer of `FinEnum.decidablePiFinEnum`:
`Compatible p a v` is by definition the function equality
`p ∘ v = F.r ∘ Sigma.mk a` out of the finite direction type, so the
instance decides it directly (rather than routing through
`compatible_iff` to a pointwise form).

```text
wValidStep : [F.Finitary] → [DecidableEq I] →
    F.toPFunctor.Obj (I × Bool) → I × Bool
wValidData : F.toPFunctor.W → I × Bool
wValidBool    : F.toPFunctor.W → Bool
wValidBool_eq_true_iff : F.wValidBool w = true ↔ F.WValid w
SlicePFunctor.decidableWValid : Decidable (F.WValid w)
```

`wValidData` is `WType.elim` at the carrier `I × Bool` with algebra
`wValidStep`, named rather than inlined so that it can be `@[expose]`d
and so that the fold matches the shape of `wIndexStep` beside it. It
mirrors the
existing `WIndex` / `wIndexStep` / `wIndexValid` fold with `Bool` in
place of `Prop`. A product rather than a named record: the carrier has no
recursive occurrence and the product makes that evident. The index
component must be carried even though `wIndexValid_index_eq_wIndexRoot`
shows it is non-recursive, because `WType.elim`'s step receives the
children's fold results and never the children, so `OverInput` cannot
otherwise be evaluated. `wValidBool_eq_true_iff` is one `WType.rec` against
`wValid_mk`, using `WType.elim_mk` to unfold each side one level.

### `Presheaf/Decidable.lean`

```text
PresheafDomPFunctorData.decidableIsNatural :
    {Z : Iᵒᵖ ⥤ Type uZ} → [F.Finitary] → [FinEnum I] →
    [∀ i i' : I, FinEnum (i' ⟶ i)] → [∀ i : I, DecidableEq (Z.obj ⟨i⟩)] →
    (x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z)) →
    Decidable (F.IsNatural x)

wRestrTreeRaw : (g : j' ⟶ j) → (w : F.toPFunctor.W) →
    F.q (PFunctor.W.head w) = j → WType F.toPFunctor.B
wRestrTree_val : (F.wRestrTree g z hq).1 = F.wRestrTreeRaw g z.1 hq
isHereditarilyNaturalBoolCore : (decI : DecidableEq I) → (feI : FinEnum I) →
    (feHom : ∀ i i' : I, FinEnum (i' ⟶ i)) → (feB : ∀ a, FinEnum (F.toPFunctor.B a)) →
    (decEqW : DecidableEq (WType F.toPFunctor.B)) → F.toPFunctor.W → Bool
isHereditarilyNaturalBoolCore_eq_true_iff : … = true ↔ F.IsHereditarilyNatural z
PresheafPFunctor.decidableIsHereditarilyNatural :
    Decidable (F.IsHereditarilyNatural z)
```

`IsNatural` is decided directly: four bounded quantifiers — over objects
twice, over a hom-set, and over `Direction a i` via
`decidableForallDirection` — and an equation in `Z.obj ⟨i'⟩`.

Its subject is a slice object over `elemProj Z`, not a
`PresheafDomPFunctorData.obj Z`: the latter is the `IsNatural` subtype
itself, on which the predicate holds by projection and there is nothing
to decide. The instance is stated in the `PresheafDomPFunctorData`
namespace, where `IsNatural` lives; generalized field notation carries it
to `PresheafPFunctor` (§ `Univariate/Finitary.lean`). This is
unaffected by the diamond below, `PresheafDomPFunctorData` extending
`SliceDomPFunctor` directly.

`IsHereditarilyNatural` is decided by `WType.para` over the raw tree, in
a classless core with a thin instance wrapper (the repository's
typeclass-instance pattern). The core is forced by a diamond:
`PresheafPFunctor` extends `PresheafDomPFunctorData` and `SlicePFunctor`
through a shared `SliceDomPFunctor`, and instance synthesis cannot resolve
`decidableForallDirection` / `decidableDirectionOver` through the merged
projection `F.toSliceDomPFunctor`. So `decide (∀ b : Direction …)` does
not elaborate over a `PresheafPFunctor` — verified, and verified to fire
on a bare `SliceDomPFunctor` and on `PresheafDomPFunctorData`, which is
why `IsNatural` is untouched. The core sidesteps the synthesis entirely:
it enumerates the raw directions of a node with `FinEnum.toList` /
`List.all`, admits a raw direction `b'` as one over `i` when the explicit
test `decI (rCurried x.1 b') i` succeeds, and takes every finiteness and
decidability datum — `decI`, `feI`, `feHom`, `feB`, `decEqW` — as an
explicit argument. The whole construction is verified to elaborate at
`{Quot.sound}`.

Three points of the encoding.

*The head-index witness.* `wRestrTree` takes not only a subtree but a
witness `hq : F.q (PFunctor.W.head z.1) = j`; on a compatible node it is
`compatible_iff` composed with the direction constraint `b.2`. A raw fold
has neither, so `wRestrTreeRaw` retains `hq` as an explicit argument, and
the core decides `F.q (PFunctor.W.head (x.2 b').1) = i` with `decI`,
using the resulting proof on the positive `isTrue` branch and returning
`true` on the negative one. On a node from a valid tree the negative
branch is unreachable, by `compatible_iff` at `x.2`; where it is reached,
the value is irrelevant, since such a node cannot arise under the `iff`'s
valid `z`.

*Same-headed tree equality.* `wRestrTreeRaw` returns `WType F.toPFunctor.B`,
matching the `para` carrier's child type, so the core's tree equation is
between two `WType β` values and `decEqW` (i.e. `WType.instDecidableEq`,
resolved at the wrapper) decides it. A `PFunctor.W`-typed result would
make the equation mixed-headed, on which no `DecidableEq` fires. The core
tests the equation with the explicit `(decEqW A B).decide`, so its
correctness relates to the subtype equality of `IsHereditarilyNatural` by
`decide_eq_true_iff`, `wRestrTree_val`, and `Subtype.ext_iff` — not by
`beq` (which `WType.instDecidableEq` uses internally, but the core proof
does not name).

*Reassociation at the constructor.* The correctness induction runs by
`SlicePFunctor.W.induction` against `isHereditarilyNatural_mk`, whose
constructor `SlicePFunctor.W.mk x` has underlying tree
`WType.mk x.1.1 (Subtype.val ∘ x.1.2)`. `para_mk` applies at that
reassociated form, presenting the children as `fun b ↦ ((x.1.2 b).1, _)`.

`DecidableEq F.A` enters here and only here, through `decEqW`.

The wrapper resolves `decI`, `feI`, `feHom`, `feB`, and `decEqW` at the
boundary — each a single, direct resolution from `[F.Finitary]`,
`[FinEnum I]`, `[∀ i i', FinEnum (i' ⟶ i)]`, `[DecidableEq F.A]`, none
of them the diamond-fragile `decide (∀ Direction)` synthesis — and passes
them as explicit values to the core.

The implementation plan takes this module first. `wRestrTreeRaw`,
`wRestrTree_val`, `isHereditarilyNaturalBoolCore`, and the wrapper are
verified to elaborate at `{Quot.sound}`, and
`isHereditarilyNaturalBoolCore_eq_true_iff` — the correctness `iff` — is
verified to compile sorry-free at `{propext, Quot.sound}`
(§ Verification performed). The branch has no remaining unverified
proof obligation.

## Tests

`GebTests/` mirrors for each new module. Beyond typechecking, every
decidable predicate is exercised by evaluating it on a concrete fixture
in both directions — one instance that holds and one that fails — with
the verdict asserted by `decide`.

A `Decidable` instance can typecheck and still fail to reduce, in which
case it decides nothing, and no test that only elaborates a type detects
this. Reduction is the acceptance criterion, not elaboration.

Two reduction obstacles are specific to the presheaf checkers and are
resolved during implementation rather than assumed away.
`PresheafDomPFunctorData.value` is a `cast` along
`congrArg (fun k : I ↦ Z.obj ⟨k⟩)`, and `IsNatural`'s body equates one
such cast with `Z.map f.op` applied to another; `objRestrElt` and
`wRestrTree` carry further casts and subtype transports. Whether `decide`
reduces depends on the kernel collapsing them at the fixture's concrete
indices. For `IsNatural` it does: both verdicts reduce by kernel `rfl`
on a `presheafWitness`-shaped fixture (§ Verification performed). For
`IsHereditarilyNatural`, which adds `objRestrElt` and `wRestrTree`'s
transports on top, it is untested. Should it fail, the fixture is chosen
so that the transported types are definitionally equal; restating the
checker to avoid the transport is a design change of the same kind as the
§ `Presheaf/Decidable.lean` fallback, and is likewise a decision the user
takes.

Each verdict is a named `def … : Bool := decide …` with an `example`
asserting its value, not a bare `example`. An `example` adds no constant
to the environment, so the axiom linter cannot see it; a bare assertion
would leave the instance resolution *at the assertion site* — the very
place an unpinned `Fintype`-derived instance enters — outside the
linter's reach. Naming the verdict also gives `lake shake` a constant to
attribute the module's imports to, which is the house pattern for
example-only imports.

| Predicate | Fixture | Hypotheses beyond § The decidability conditions |
| --- | --- | --- |
| `DirectionOver`, `ShapeOver` | the existing slice fixture | — |
| `Compatible`, `WValid` | the existing slice fixture | — |
| `IsNatural` | the existing `presheafWitness`, and a new input presheaf | — |
| `IsHereditarilyNatural` | a new presheaf fixture | — |

"Existing" above means the fixture's *data*, not the declaration. None of
the four test modules this branch draws from carries a `public section`:
`GebTests/.../Slice/Basic.lean`, `.../Slice/W.lean`,
`.../Presheaf/Basic.lean`, and `.../Presheaf/W.lean` all set
`linter.privateModule false` and leave their declarations module-private,
so `wSlice`, `presheafWitness`, and the rest cannot be imported. (Twelve
`GebTests/` modules do carry `@[expose] public section`, but all of them
sit under `IndRec/`, `CategoryTheory/`, `Logic/`, or
`Univariate/Fixtures.lean` — none is a module this branch reads.)

Each new test module therefore re-declares the fixture data it needs,
following the precedent `GebTests/.../Presheaf/W.lean` already sets when
it redefines `presheafWitness` for exactly this reason. Re-declaring is
the conservative route: the alternative, converting the four source test
modules to `@[expose] public section`, is the deferred *Reconcile
test-module import visibility* and *Decide a test-declaration privacy
discipline* decision, which is a repo-wide convention rather than content
of this concern.

*The slice rows re-declare `wSlice`'s data.* It already carries a leaf
shape (`B := fun a ↦ cond a Unit Empty`), so its W-type is inhabited and
all four slice predicates are falsifiable on it. Nothing about it changes.

*The `IsNatural` row re-declares `presheafWitness`'s data and adds a new
input presheaf.* Falsifying `IsNatural` needs a non-identity morphism in
the index category and an input presheaf with a fiber of size at least
two. `presheafWitness` supplies the first — its index category is
`Fin 2`, with the non-identity `0 ⟶ 1` and directions over two distinct
base indices — so only the input presheaf is new. `presheafWitness2`
cannot serve: its index category is `Fin 1`, whose only morphism is `𝟙`,
so both sides of the equation coincide for every element.

*The `IsHereditarilyNatural` row needs new functor data.* Neither
existing witness can serve: `presheafWitness2` is a
`PresheafPFunctor (Fin 1) (Fin 3)`, and `IsHereditarilyNatural` is
defined only for an endofunctor `PresheafPFunctor I I`, so it has no
W-type at all; `presheafWitness` is an endofunctor but sets
`B := fun _ ↦ Fin 2`, so no shape is a leaf and its W-type is empty, as
`elimConstPUnit`'s docstring records. Beyond a leaf shape, falsifiability
needs a shape carrying at least two directions over distinct base indices
and two distinct admissible subtrees over a common index, so that a child
and the root-restriction of its sibling can differ. The new fixture's
functor laws do not discharge by the `Subsingleton.elim` route the
existing one uses, that route depending on the present `r` and `q`; they
are proved directly. Whether data meeting all of these conditions exists
is not established here (§ Verification performed).

*The shared-fixtures trigger fires, and is not taken here.* `TODO.md`
§ Triggers records introducing a public-exported
`GebTests/.../Presheaf/Fixtures.lean` when a third consumer of
`presheafWitness` appears; `GebTests/.../Presheaf/Decidable.lean` is that
third consumer. The extraction is not performed on this branch: it means
making the currently-private `presheafWitnessData` and its supporting
lemmas public and editing two existing test modules to import them, which
is the same deferred visibility-and-privacy decision as above. This
branch records in `TODO.md` that the condition has been met, so the
follow-on branch takes the extraction and the two conventions together.

Introducing that module revises test-module interfaces, which is the
stated trigger for two further items — reconciling test-module import
visibility, and deciding a test-declaration privacy discipline. Both are
repo-wide conventions rather than content of this concern, so under
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape they go to
their own branch; this branch records in `TODO.md` that their trigger has
fired and follows the surrounding modules' existing practice in the
meantime.

Fixtures supply their own choice-free `FinEnum` instances, built from the
`card`, `equiv`, and `decEq` fields, with the `Equiv` laws proved by case
analysis. Proving those laws by `decide` routes through the type's
`Fintype` instance and reintroduces `Classical.choice`.

Where an instance is reached by search and mathlib already supplies a
choice-dependent one — `FinEnum (Fin 2)` for the index type — a plain
`instance` declared in the test module displaces it: Lean tries instances
of equal priority in reverse declaration order, so the local declaration
wins over the imported one, and no priority annotation is needed. Where
the value is written into a term instead, no displacement arises: a slice
fixture whose direction family is a `cond` rather than a class-indexed
family discharges `Finitary` by a `Bool`-cases term naming the local
choice-free values directly, mathlib's `FinEnum.punit` and `FinEnum.empty`
never being consulted.

The hom-sets need one instance, local to the presheaf test module. The
presheaf fixtures are preorder categories, whose hom-sets are
`ULift (PLift (i' ≤ i))`, and mathlib has no `FinEnum` for either layer.
The instance is stated directly at the `⟶` head, as a `dite` of two
structure literals. Stating it instead at `PLift` and lifting through
`ULift.instFinEnum` does not discharge `[∀ i i' : I, FinEnum (i' ⟶ i)]`:
`Quiver.Hom` for a preorder is a `def`, and instance resolution runs at
`instances` transparency, so a goal headed by `⟶` does not match a
`ULift`-headed instance even though the two types are definitionally
equal — the same obstruction as `decidableForallDirection` at
`Direction`. Since the `⟶`-headed instance is needed regardless, a
separate `PLift` one would have no consumer.

It lives in the test module rather than in `Data/FinEnum.lean`. Its only
consumer is a fixture, and an upstream-eligible addition whose sole
consumer is a test would not meet
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost — the same
ground on which the node-level predicates receive no instances. It is
category-theoretic in any case, and so out of place in a `FinEnum`
module.

## Transcription or novel

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing requires each definition to be marked.

| Declaration | Status | Source |
| --- | --- | --- |
| `WType.para`, `para_mk` | transcription | the paramorphism recursion scheme, [Meertens1992] |
| `PFunctor.Finitary` | neither | a hypothesis, not a statement: it records that each direction type is finite |
| `WType.beq`, `beq_eq_true_iff`, `DecidableEq (WType β)` | neither | decidability of equality for a Lean datatype |
| `FinEnum.decidableForallFinEnum`, `decidableForallSubtype`, `decidablePiFinEnum`, `decidableDirectionOver`, `decidableShapeOver`, `decidableForallDirection`, `decidableCompatible`, `WType.instDecidableEq`, `SlicePFunctor.decidableWValid`, `PresheafDomPFunctorData.decidableIsNatural`, `PresheafPFunctor.decidableIsHereditarilyNatural`, and the test module's hom-set `FinEnum` | neither | Lean instance plumbing |
| `paraStep`, `paraStep_fst`, `beq_mk`, `wValidStep`, `wValidData`, `wValidBool`, `wRestrTreeRaw`, `isHereditarilyNaturalBoolCore` and their correctness lemmas | neither | algebra steps and computational forms of predicates already stated and cited in the modules they specialize |

The rows marked *neither* state nothing found in published mathematics:
they record a finiteness hypothesis, or that a predicate defined
elsewhere is computable, or that two Lean expressions agree. Attaching a
citation would credit a source for a claim it does not make, so their
docstrings carry no `[Key]`.

`Finitary` is marked *neither* rather than a transcription of "finitary
polynomial functor". The notion is standard, but the declaration is an
abbreviation for a finiteness hypothesis, and the underlying notion is
already covered by the citations `Slice/Basic.lean` carries.

Four keys are added to `docs/references.bib`: `Meertens1992` for the
paramorphism, and the three supporting § Complexity.

```bibtex
@article{Meertens1992,
  author        = {Meertens, Lambert},
  title         = {Paramorphisms},
  journal       = {Formal Aspects of Computing},
  volume        = {4},
  number        = {5},
  pages         = {413--424},
  year          = {1992},
  doi           = {10.1007/BF01211391},
}

@article{Leivant1999,
  author        = {Leivant, Daniel},
  title         = {Ramified Recurrence and Computational Complexity III:
                   Higher Type Recurrence and Elementary Complexity},
  journal       = {Annals of Pure and Applied Logic},
  volume        = {96},
  number        = {1--3},
  pages         = {209--229},
  year          = {1999},
  doi           = {10.1016/S0168-0072(98)00040-2},
}

@inproceedings{DalLagoMartiniZorzi2010,
  author        = {Dal Lago, Ugo and Martini, Simone and Zorzi, Margherita},
  title         = {General Ramified Recurrence is Sound for Polynomial Time},
  booktitle     = {Developments in Implicit Computational Complexity (DICE 2010)},
  series        = {Electronic Proceedings in Theoretical Computer Science},
  volume        = {23},
  pages         = {47--62},
  year          = {2010},
  doi           = {10.4204/EPTCS.23.4},
}

@article{AvanziniDalLago2018,
  author        = {Avanzini, Martin and Dal Lago, Ugo},
  title         = {On Sharing, Memoization, and Polynomial Time},
  journal       = {Information and Computation},
  volume        = {261},
  pages         = {3--22},
  year          = {2018},
  eprint        = {1501.00894},
  archivePrefix = {arXiv},
  primaryClass  = {cs.LO},
  doi           = {10.1016/j.ic.2018.05.003},
}
```

## Universe constraints

`para` is fully polymorphic in its carrier: `γ : Type uC` is
unconstrained, since `elim` is, and the auxiliary carrier
`WType β × γ : Type (max uA uB uC)` imposes nothing on `γ`.

`Finitary P` for `P : PFunctor.{uA, uB}` is ascribed
`Type (max uA uB)`: `FinEnum (P.B a)` lives in `Type uB` and the
dependent function over `P.A` raises it by `uA`.

The category-side binders leave `uI` and `vI` independent, `FinEnum I`
and `∀ i i', FinEnum (i' ⟶ i)` constraining neither. This is the
generality `FinCategory` gives up by requiring `SmallCategory`.

No new universe constraint is imposed on the existing slice or presheaf
declarations; the decidable modules instantiate them at the universes
they already carry.

## Choice boundary

Every declaration in this branch lands in the axiom linter's default
permitted set `{propext, Quot.sound}`. Achieving that is not automatic,
and the reasons govern how the layer is written.

| Upstream declaration | Axioms |
| --- | --- |
| `List.decidableBAll` | none |
| `decidable_of_iff` | none |
| `WType.rec`, `WType.elim` | none |
| `decide_eq_true_iff` | propext |
| `FinEnum.toList` | Quot.sound |
| `FinEnum.mem_toList` | propext, Quot.sound |
| `FinEnum.ofEquiv`, `ULift.instFinEnum` | Quot.sound |
| `Multiset.decidableDforallMultiset` | propext, Quot.sound |
| `Multiset.toList` | Classical.choice |
| `Finset.toList` | propext, Classical.choice, Quot.sound |
| `Fintype.decidableForallFintype` | propext, Classical.choice, Quot.sound |
| `Fintype.decidablePiFintype` | propext, Classical.choice, Quot.sound |
| `Finset.decidableDforallFinset` | propext, Classical.choice, Quot.sound |
| `Fintype`, `Finset.univ` | propext, Classical.choice, Quot.sound |
| `FinEnum.ofList`, `FinEnum.ofNodupList`, `FinEnum.fin`, `FinEnum.Subtype.finEnum`, `FinEnum.prod`, `FinEnum.sum` | propext, Classical.choice, Quot.sound |

Three routes by which `Classical.choice` enters, each with its own
countermeasure.

**Through the decision procedure.** Deciding a bounded `∀` through
`Fintype` is `Classical.choice`-dependent; through `List` it is not.
Since every predicate here decides a bounded `∀`, the layer routes
through `FinEnum.toList` and `List.decidableBAll`, never through
`Fintype`.

**Through the `FinEnum` instance argument.** A choice-free decision
procedure applied to a choice-dependent `FinEnum` is choice-dependent.
The property is one of closed terms: a `FinEnum` term is choice-free
exactly when every constant it mentions is, including the proofs inside
its `equiv` field. No syntactic shape decides it — `FinEnum.ofNodupList`
is a structure literal and is choice-dependent, while the
`FinEnum (PLift p)` of § Tests is a `dite` of two literals and is not.
`FinEnum.ofEquiv` and `ULift.instFinEnum` propagate their argument's
dependencies, so `ULift.instFinEnum` applied to `FinEnum.fin` is
choice-dependent though the declaration itself is not.

The named exception is that everything reached through `FinEnum.ofList`
or `ofNodupList` is choice-dependent, by way of
`List.idxOf_lt_length_iff` and, for `ofList`, `List.mem_dedup` as well.
That covers most of mathlib's `FinEnum` instances, `fin`,
`Subtype.finEnum`, `prod`, `sum`, `empty`, `punit`, `Finset.finEnum`,
the `Sigma` instance, and `List.Pi.finEnum` among them.

The layer therefore forms no `FinEnum` at all on a derived type: in
particular `FinEnum (F.Direction a i)` is never formed, the quantifier
over `Direction a i` being decided by `decidableForallDirection` over the
ambient enumeration instead. `Finitary` and the category-side binders
take `FinEnum` as data supplied by the caller, and fixtures supply
structure literals (§ Tests).

**Through the signature.** `Lean.collectAxioms` traverses a
declaration's type as well as its value, so a signature mentioning
`Fintype` or `FinCategory` carries the dependency however the
declaration is proved. `Finset` alone does not: `Finset` is
`{propext, Quot.sound}`, and it is `Finset.univ` and `Fintype` that
carry `Classical.choice`. No declaration in this branch mentions any of
them.

The instance-ordering argument described under `Data/FinEnum.lean`
addresses only the first source, and only for the goal shapes it matches.
It is not the principal countermeasure, and it does not survive a mathlib
bump that introduces a higher-priority `Fintype`-derived instance; were
that to happen, downstream sites would need explicit `@`-pinning.

The axiom linter, which runs in CI and in the pre-push checklist, is what
detects any of the three sources recurring — but only across named
declarations. It does not see an `example`, which adds no constant to the
environment, so a reduction assertion written as a bare `example` escapes
it. That is why § Tests requires each verdict to be a named `def`.

No module in this branch is added to `GebMeta.classicalAllowedModules`.

## Verification performed

Compiled against the pinned toolchain during design, with axioms as
reported by `#print axioms`.

| Fragment | Result |
| --- | --- |
| `para`, `paraStep`, `paraStep_fst`, `para_mk` | compile; `para` axiom-free, `para_mk` depends on `Quot.sound` |
| `beq`, `beq_mk` | compile; `beq_mk` holds by `rfl`, and `decide` evaluates `beq` correctly on concrete unary-numeral trees in both directions |
| the `para_mk` reassociation at `(SlicePFunctor.W.mk x).1` | closes definitionally, as `WType.para_mk fγ x.1.1 (Subtype.val ∘ x.1.2)` |
| the three `Decidable` instances of `Data/FinEnum.lean`, `@`-pinned | compile at `{propext, Quot.sound}`; `decide` reduces for a bounded `∀`, a `∀` over a decidable subtype, and a function equality, positive and negative |
| the same instances, unpinned | compile at `{propext, Classical.choice, Quot.sound}` |
| the hom-set enumeration of § Tests | an instance stated at `PLift` does not discharge a goal headed by `⟶`; one stated at the `⟶` head does, and resolves at `{propext, Quot.sound}` |
| `PresheafDomPFunctorData.decidableIsNatural` | elaborates at the corrected subject type, is non-vacuous, resolves its four quantifiers from the four listed binders, and reaches `PresheafPFunctor` through the diamond; `{propext, Quot.sound}` pinned, `Classical.choice` unpinned |
| `decide` on `IsNatural`, both directions | reduces by kernel `rfl` on a rebuilt `presheafWitness` with a two-element-fiber input presheaf, at `{propext, Quot.sound}`; the `value` transports collapse at concrete indices |
| `Finitary` as an `abbrev` | `[F.Finitary]` resolves `FinEnum (F.B a)` and `DecidableEq (F.B a)` with no attribute registration, for `F` a `SliceDomPFunctor`, a `SlicePFunctor`, and a `PresheafPFunctor`, including through the `PresheafPFunctorData` diamond; a bounded `∀` through it decides at `{propext, Quot.sound}` |
| the category-side binders | `[FinEnum I] [∀ i i' : I, FinEnum (i' ⟶ i)]` resolves objects, homs, and `DecidableEq I`; a nested `∀ i i' (f : i' ⟶ i)` decides at `{propext, Quot.sound}` |
| `decidableForallDirection` | required — `Decidable (∀ b : F.Direction a i, q b)` fails to synthesize from `FinEnum.decidableForallSubtype` alone, and `@[implicit_reducible]` does not change it — and the instance stated at `Direction` fires at `{propext, Quot.sound}` |
| `wRestrTreeRaw` (returning `WType β`), `wRestrTree_val` | typecheck as sketched; `wRestrTreeRaw` needs no validity witness |
| `isHereditarilyNaturalBoolCore` and its wrapper | elaborate at `{Quot.sound}`, verified in a module file. The `decide (∀ b : Direction …)` form does *not* elaborate over a `PresheafPFunctor` — the diamond blocks `decidableForallDirection` synthesis, verified — which is why the classless core is used. Earlier drafts (and an earlier verification fragment) claimed the direct form typechecked; it does not |
| a `FinEnum` built from `card` / `equiv` / `decEq` with `Equiv` laws by case analysis | `{propext}`, or axiom-free with `Equiv.refl`; the same fixture with the laws by `decide` acquires `Classical.choice` |
| a locally declared fixture `FinEnum (Fin 2)` | displaces mathlib's `FinEnum.fin` with no priority annotation, by reverse declaration order. A fixture functor must be an `abbrev` and its `FinEnum`'s `decEq` field ascribed explicitly (`(inferInstance : DecidableEq Unit)`); a plain `def` leaves `decide` stuck at the unreduced `F.B` projection |
| every axiom figure in § Choice boundary | read from `#print axioms` |
| mathlib survey: no finitary-container predicate; no `DecidableEq (WType β)`; `FinCategory` requires `SmallCategory`; `FinEnum` provides no bounded-`∀` instance; `Mathlib.Data.PFunctor.Univariate.Basic` imports only `Mathlib.Data.W.Basic` | confirmed by search of the pinned tree |
| [Meertens1992] | publisher record: Formal Aspects of Computing 4(5):413–424, 1992, doi 10.1007/BF01211391 |
| [Leivant1999] | primary source read: Lemma 12 and the redex-rank definition preceding it, pp. 225–226; Table 1, p. 211; publisher record Annals of Pure and Applied Logic 96(1–3):209–229, 1999 |
| [DalLagoMartiniZorzi2010] | primary source read: the exponential-output tree-algebra definition, p. 48; Theorem 1, p. 56 |
| [AvanziniDalLago2018] | abstract read from the arXiv record (1501.00894), which is what the § Complexity sentence is scoped to; publisher record Information and Computation 261:3–22, 2018 |

Verified after the spec's adversarial review, during plan execution
(Task 1):

- `isHereditarilyNaturalBoolCore_eq_true_iff` compiles sorry-free at
  `{propext, Quot.sound}`. The proof drives its recursion through
  `SlicePFunctor.W.induction`, relates the `List.all` enumerations to the
  `IsHereditarilyNatural` quantifiers by `List.all_eq_true` /
  `FinEnum.mem_toList`, and bridges the tree equation by
  `decide_eq_true_iff`, `wRestrTree_val`, and `Subtype.ext`. The branch
  has no remaining unverified proof obligation.

Not verified:

- That `decide` reduces for `IsHereditarilyNatural` on a concrete
  fixture (§ Tests). The `IsNatural` half is verified (below); this half
  is not, and no fixture yet exists to test it on.
- That functor data meeting the `IsHereditarilyNatural` fixture's
  conditions exists — an endofunctor `PresheafPFunctor I I` over an index
  category with a non-identity morphism, carrying a leaf shape, a shape
  with directions over two distinct base indices, and two distinct
  admissible subtrees over a common index, with the seven functor laws
  proved directly. Constructing it is the branch's largest test
  deliverable and nothing of that shape exists to adapt.
- `beq_eq_true_iff` and the `DecidableEq (WType β)` instance built from
  it, `wValidStep` / `wValidData` / `wValidBool` and
  `wValidBool_eq_true_iff`, and the `Compatible` and `IsNatural`
  instances were not compiled, though each is routine beside the above.
- The complexity bounds below. Only the attributions supporting them are
  verified, not the bounds.
- That item 4 will want term-validity decisions only, not decisions of
  the functor laws (§ Scope). That item's spec is written only after this
  one is implemented, so the exclusion rests on an assumption about it,
  not on a reading of it.

## Complexity of the checkers

Not proved here. Recorded in [TODO.md](../../../TODO.md) as a claim to be
proved later, in the following form.

With `n` the number of nodes of the input term, `h` its height, `k` the
branching bound, `κ` the number of objects of `I`, and `H` the maximal
hom-set size, and taking equality in `I`, in `dom`, and in the presheaf's
value types to cost `O(1)`: the four single-step checks are constant-time
in `n`, with node-level factors `1` for the two fiber predicates, `k` for
`Compatible`, and `κ²Hk` for `IsNatural`; `WValid` runs in `O(k · n)`, a
single fold with an `O(1)` accumulator; and `IsHereditarilyNatural` runs
in `O(κ²Hk · n · h)`, worst case `O(n²)`, because each node's local
condition is an equation between a subtree and the root-restriction of a
sibling, whose decision cost is linear in subtree size. All six are
polynomial time, and the functor's
data enters as multiplicative constants rather than as a change of
complexity class. Upper bounds only: a `Bool` fold short-circuits, so no
matching lower bound is claimed on rejecting inputs.

No tower of exponentials arises, and nothing above polynomial. In
[Leivant1999] the reduction bound is `O(2_{q+1}(h)²)` where `q` is the
*redex rank* — defined there as the maximal order of the type of a
redex's operator — so the tower's height is the maximal type order
occurring in the program (Lemma 12 and the definition preceding it,
pp. 225–226). That paper's Table 1 (p. 211) places elementary complexity
in the higher-order ramified cell and polynomial time in the first-order
ramified polyadic cell. Every recursion here is a non-dependent fold at a
first-order carrier, so `q` is bounded and no tower is generated.

The word-algebra against tree-algebra distinction in the
implicit-complexity literature concerns producers whose output can grow
exponentially without term sharing: [DalLagoMartiniZorzi2010] exhibit a
tierable definition over a tree algebra whose output is exponential in
its input, and establish soundness for polynomial time under a
term-graph representation; [AvanziniDalLago2018] settle the general case
under a cost model in which lookup of an already-computed value is free.
These checkers consume a term and return a `Bool`, so the distinction
bears on them only through the height `h`: word algebras force `h = n`,
whereas branching algebras admit balanced inputs with `h = O(log n)`.

A sharing or hash-consing representation would reduce the fourth checker
to linear time, each subtree comparison becoming a pointer comparison.

The keys [Leivant1999], [DalLagoMartiniZorzi2010], and
[AvanziniDalLago2018] are added to `docs/references.bib` in this branch,
not deferred to the TODO item: the attributions above are made here, so
under [AGENTS.md](../../../AGENTS.md) § Verify agent claims the
verification belongs here too. Each attribution above is read from the
primary source, and § Verification performed records which reading
supports which claim.

## Documentation and roadmap

- Every concept added to the sources is added to
  [docs/index.md](../../index.md) in the same branch, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Each phase produces an
  artifact.
- Roadmap item 1 is removed from [TODO.md](../../../TODO.md) on
  completion and its content merged into `docs/index.md`.
- The complexity conjecture is added to `TODO.md` § Next up as a new
  item, it being a workstream rather than a condition to watch for. Its
  three literature keys are added to `docs/references.bib` in this
  branch, alongside [Meertens1992].
- `TODO.md` § Triggers records that the shared-presheaf-test-fixtures
  condition has been met (§ Tests). The item stays, since this branch
  does not take the extraction; it gains a note that the extraction and
  the test-module import-visibility and test-declaration-privacy items
  are to be taken together, the first entailing the other two.
- This spec and its plan are removed in the branch's final commits, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## Out of scope

- Decidability of the functor-law predicates and the `IsFunctorial`
  bundles (§ Scope). A separate concern under
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.
- `para_unique`, the companion to `elim_unique`.
- `BEq` and `LawfulBEq` instances for `WType`.
- A choice-free replacement for `FinEnum.ofNodupList`, which would let
  mathlib's `ofList`-derived `FinEnum` instances be used.
- Upstreaming the hom-set `FinEnum` instance of § Tests, or a
  `FinEnum (PLift p)` beneath it. Both fill genuine mathlib gaps, but the
  only consumer here is a fixture, so proposing either belongs to a
  branch that has a use for it.
- Extracting the shared presheaf test-fixtures module, whose trigger this
  branch fires but does not take (§ Tests).
- The sharing representation that would make the fourth checker linear.
- Proofs of the complexity claims; only the conjecture is recorded.
- Reformulating `IsNatural` to eliminate its `i` quantifier. It removes
  one of four quantifiers and leaves `i'` needing an enumeration of the
  objects mapping into `i`, so the hypotheses are unchanged in substance.

## References

- [TODO.md](../../../TODO.md) — roadmap item 1.
- [CONTRIBUTING.md](../../../CONTRIBUTING.md) — concern shape, citation
  policy, constructive discipline, code is cost.
- [AGENTS.md](../../../AGENTS.md) — verification of claims before they
  enter an artifact.
- [docs/rules/lean-coding.md](../../rules/lean-coding.md) — recursion
  through recursors; constructive-only Lean; structure and typeclass
  patterns.
- [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md) —
  subtree import rules.
- [docs/rules/markdown-writing.md](../../rules/markdown-writing.md) —
  conventions binding this document.
