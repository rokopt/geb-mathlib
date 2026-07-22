# Categorical wrappers for mathlib's `PFunctor` and `WType`

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Prior state](#prior-state)
- [Module layout](#module-layout)
- [Module contents](#module-contents)
  - [`Data/W/Basic.lean`](#datawbasiclean)
  - [`Univariate/Functor.lean`](#univariatefunctorlean)
  - [`Univariate/W.lean`](#univariatewlean)
  - [`Univariate/Initial.lean`](#univariateinitiallean)
  - [`Slice/Functor.lean`](#slicefunctorlean)
- [Transcription or novel](#transcription-or-novel)
- [Universe constraints](#universe-constraints)
- [Choice boundary](#choice-boundary)
- [Verification performed](#verification-performed)
- [Out of scope](#out-of-scope)
- [Supporting work](#supporting-work)
- [References](#references)

<!-- END doctoc -->

## Scope

Roadmap item 2 of the polynomial-functor sequence in
[TODO.md](../../../TODO.md): connect mathlib's generic endofunctor
algebras to mathlib's univariate `PFunctor`, characterise mathlib's
`WType` as the initial algebra of the resulting endofunctor, and
refactor the existing slice wrapper to reuse the result. This is
the base layer on which roadmap items 3 (slice and presheaf
W-types as initial algebras), 4 (M-types as terminal coalgebras),
and 5 (universal morphisms) build.

Compatibility of mathlib's `PFunctor.comp` with composition of the
corresponding functors, and the identity polynomial functor, are
excluded. That content is independently submittable and belongs to
no roadmap item — it is the 1-cell composition of `Cat`, a
2-categorical operation — so under
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape it is a
separate concern and goes on its own topic branch with its own spec
(§ Out of scope).

Roadmap item 1 remains open; the two items are independent, so
item 2 may precede it (§ Supporting work).

Roadmap references throughout this document use the numbering as it
stands before the renumbering this branch performs.

## Prior state

mathlib carries the two halves separately and does not connect
them.

- `Mathlib/Data/PFunctor/Univariate/Basic.lean` defines
  `PFunctor`, its interpretation `P.Obj α = Σ x : P.A, P.B x → α`,
  the action `P.map`, the functor laws `P.id_map` / `P.map_map`,
  and `P.W := WType P.B` with `W.mk` / `W.dest` and their mutual
  inverse laws `W.mk_dest` / `W.dest_mk`. It also carries the
  `Functor` and `LawfulFunctor` instances on `P.Obj`.
- `Mathlib/Data/W/Basic.lean` defines `WType`, the non-dependent
  fold `WType.elim`, and the fixed-point equivalence
  `WType.equivSigma : WType β ≃ Σ a, β a → WType β`. Its only lemma
  about `elim` is `elim_injective`: the computation rule exists
  only as the equation compiler's generated equation, unnamed and
  not `@[simp]`, and uniqueness of the fold is absent outright.
- `Mathlib/CategoryTheory/Endofunctor/Algebra.lean` defines
  `Endofunctor.Algebra F` and its category for an endofunctor `F`
  of an arbitrary category, with `Algebra.Initial.str_isIso`.

Nothing links the third to the first two: `Endofunctor/Algebra.lean`
imports only from `Mathlib/CategoryTheory/`, and `Data/PFunctor`
does not import it. `WType.elim` is the existence half of
initiality stated concretely; the uniqueness half is absent.

## Module layout

Four new content modules, plus two index modules and the
`GebTests/` mirrors; the existing `Slice/Functor.lean` is modified
but not new, so § Module contents has five subsections. Their
dependencies:

```text
Univariate/Functor.lean          Data/W/Basic.lean
   (no in-branch parent)                │
        │         │                     │
        │         └──────┐       ┌──────┘
        │                ▼       ▼
        │           Univariate/W.lean
        │                    │
        ▼                    ▼
Slice/Functor.lean   Univariate/Initial.lean
 (existing, leaf)            (leaf)
```

Each edge is a use, not an association. `Univariate/Functor.lean`
contains only `functor` and its two `rfl` theorems, so it imports
nothing from this branch; `Univariate/W.lean` is the sole consumer
of `WType.elim_unique`. Drawing the graph any wider would ship
unused imports, which `lake shake` rejects in the pre-push
checklist and CI.

| Module | Upstream destination | Choice |
| --- | --- | --- |
| `Geb/Mathlib/Data/W/Basic.lean` | `Mathlib/Data/W/Basic.lean` | choice-free |
| `Geb/Mathlib/Data/PFunctor/Univariate/Functor.lean` | `Mathlib/Data/PFunctor/Univariate/` | choice-free |
| `Geb/Mathlib/Data/PFunctor/Univariate/W.lean` | `Mathlib/Data/PFunctor/Univariate/` | choice-free |
| `Geb/Mathlib/Data/PFunctor/Univariate/Initial.lean` | `Mathlib/Data/PFunctor/Univariate/` | adds `Classical.choice` |

`Geb/Mathlib/Data/W/Basic.lean` extends a file that already exists
upstream and mentions no `PFunctor` and no category theory; it is
placed under `Data/W/` because that is the module it would be
submitted against.

The three categorical modules are assigned to
`Mathlib/Data/PFunctor/Univariate/`, and each imports
`Mathlib.CategoryTheory.*`. No file under `Mathlib/Data/` in the
pinned tree does so; mathlib's convention for categorical
packaging of concrete structures is `Mathlib/Algebra/Category/` and
`Mathlib/CategoryTheory/`. The assignment is nevertheless retained,
because this repository has already made it five times — the
shipped `Slice/Functor.lean`, `Presheaf/Functor.lean`, and
`Presheaf/Basic.lean` sit under `Data/PFunctor/` and import
`Mathlib.CategoryTheory.*` directly, while `IndRec/Basic.lean` and
`IndRec/Naturality.lean` import `Geb.Mathlib.CategoryTheory.*`,
which extracts to the same thing — and splitting the convention
within one directory would be worse than either consistent choice. The
consequence is recorded rather than resolved: an upstream
reviewer may require relocation to
`Mathlib/CategoryTheory/`, which would be a source-code change
(module names, namespaces, imports, index files) and so a
departure from CONTRIBUTING § Floodgate test. Settling the question
for all three wrapper families at once is carried as a `TODO.md`
item (§ Supporting work); it predates this workstream.

The existing `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean` gains
`domSubfunctor` and has `domFunctor` rebuilt on it. The
redefinition is definitionally equal to the current one, so no
downstream module changes.

Index modules `Geb/Mathlib/Data/W.lean` and
`Geb/Mathlib/Data/PFunctor/Univariate.lean` are added, and the
existing `Geb/Mathlib/Data.lean` and
`Geb/Mathlib/Data/PFunctor.lean` extended, following the
one-index-file-per-directory convention. `GebTests/` mirrors the
source tree.

## Module contents

Names below are decided, not indicative; the arguments for the
contested ones are recorded with them.

### `Data/W/Basic.lean`

The fold's two missing laws, stated without category theory.

- `WType.elim_mk` — the computation rule
  `elim γ fγ (WType.mk a f) = fγ ⟨a, fun b ↦ elim γ fγ (f b)⟩`,
  which holds by `rfl`, marked `@[simp]`. mathlib's equation
  compiler already generates this equation; what is missing
  upstream is the `@[simp]`-marked named form, which is what makes
  the hypothesis shape of `elim_unique` usable by `simp` at call
  sites. It has no consumer inside this branch — `wElim`'s
  commuting condition holds by `rfl` — so its return is upstream
  and in roadmap item 3, where those call sites arrive.
- `WType.elim_unique` — a function agreeing with `fγ` at every
  node equals `elim γ fγ`:

  ```lean
  theorem elim_unique {α : Type uA} {β : α → Type uB} {γ : Type uC}
      (fγ : (Σ a : α, β a → γ) → γ) (g : WType β → γ)
      (hg : ∀ a f, g (WType.mk a f) = fγ ⟨a, fun b ↦ g (f b)⟩) :
      g = WType.elim γ fγ
  ```

  The recursion is driven by an explicit `WType.rec` application
  into a `Prop`-valued motive, per
  [docs/rules/lean-coding.md](../../rules/lean-coding.md)
  § Recursion and induction through recursors.

### `Univariate/Functor.lean`

The functor and the definitional-equality theorems fixing its maps.

- `PFunctor.functor` — the functor `Type v ⥤ Type (max v uA uB)`,
  defined as `CategoryTheory.ofTypeFunctor P.Obj` from the upstream
  `Functor` and `LawfulFunctor` instances on `P.Obj`.
- `PFunctor.functor_obj` / `PFunctor.functor_map` — the categorical
  maps are definitionally the upstream `P.Obj` / `P.map`, so the
  wrapper carries no data beyond mathlib's. The morphism case rests
  on the upstream `PFunctor.map_eq_map`, itself `rfl`.

  `functor_map` is stated in the promoted form
  `(P.functor).map (↾f) = ↾(P.map f)`, as `SlicePFunctor.functor_map`
  is. The unpromoted form
  `ConcreteCategory.hom ((P.functor).map f) = P.map (ConcreteCategory.hom f)`
  does not elaborate: `ConcreteCategory.hom f` lands in
  `TypeCat.Fun X Y`, a one-field structure, not in `X → Y`.

`P.Obj : Type v → Type (max v uA uB)` maps `Type v` to itself
whenever `uA ≤ v` and `uB ≤ v`, so the functor is stated at an
unconstrained `v` and instantiated where an endofunctor is required
(§ Universe constraints). No separate endofunctor definition is
introduced: universe instantiation suffices, since
`max (max uA uB) uA uB` normalises to `max uA uB`.

Building the functor from `ofTypeFunctor` rather than writing the
object map, morphism map, and functor laws by hand is required by
[docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Higher-order constructions.

Morphisms of `Type v` are bundled, so the underlying function of a
morphism is read through `ConcreteCategory.hom` and a function is
promoted to a morphism with `↾`, as `Slice/Functor.lean` already
does. Equality of morphisms is proved by `ext`, not `funext`.
`functor` carries `@[expose]` so `functor_obj` / `functor_map` can
state the definitional equalities as exported `rfl` theorems, as
the analogous `SlicePFunctor.functor` does. Inside
`namespace PFunctor` under `open CategoryTheory`, the bare
identifier `Functor` is ambiguous between core `Functor` (used by
the upstream instances) and `CategoryTheory.Functor`;
`Slice/Functor.lean` resolves this by writing
`CategoryTheory.Functor` in full, and this module follows it.

### `Univariate/W.lean`

The W-type as an algebra, and initiality stated without reference
to mathlib's colimit API.

Declarations take `P : PFunctor` and so sit in the `PFunctor`
namespace with a `w` prefix, not in the `PFunctor.W` namespace:
`P.W.algebra` does not elaborate, because `P.W` is a `Type` and has
no constant head to project on, whereas `P.wAlgebra` does.

- `PFunctor.wAlgebra` — the algebra `⟨P.W, ↾PFunctor.W.mk⟩` of
  `P.functor` instantiated at `v := max uA uB`, the universe `P.W`
  inhabits. The structure map is bundled (`Algebra.str` is a hom
  `F.obj a ⟶ a`), so `W.mk` is promoted with `↾`.
- `PFunctor.wElim` — the algebra morphism `P.wAlgebra ⟶ B` for an
  algebra `B`, its underlying function the fold of `B`'s structure
  map and its commuting condition the computation rule.
- `PFunctor.wUniqueHom` — `Unique (P.wAlgebra ⟶ B)` for every
  algebra `B`, uniqueness supplied by `WType.elim_unique`. This is
  initiality, stated choice-free.

  It is an `@[instance_reducible] def`, not an `instance`. As an
  instance it makes `default` depend on how the hom type is
  spelled: `(default : Endofunctor.Algebra.Hom A A) = 𝟙 A` holds by
  `rfl`, because the upstream
  `instance : Inhabited (Hom A A) := ⟨{ f := 𝟙 _ }⟩` is stated at
  the `Hom` spelling, while at the definitionally equal `A ⟶ A`
  spelling `default` becomes `wElim`. Two defeq spellings would
  then have different `default`s. Consumers introduce it locally
  with `haveI` where a `Unique` instance is wanted. The
  `@[instance_reducible]` attribute silences the
  `warn.classDefReducibility` warning that a `def` of class type
  otherwise emits; mathlib uses the attribute for the same purpose.
- `PFunctor.wStrIso` — the structure map as an isomorphism
  `(P.functor).obj P.W ≅ P.W` in `Type (max uA uB)`, defined as
  `(WType.equivSigma P.B).symm.toIso` from mathlib's existing
  fixed-point equivalence and `Equiv.toIso`, both already available
  in modules this branch imports.

  The `Iso` form is chosen over `IsIso P.wAlgebra.str` because an
  `Iso` carries its inverse as data, so consumers never reach for
  `CategoryTheory.inv`, which does depend on `Classical.choice`.
  Constructing `IsIso` is itself choice-free, so that is not the
  distinguishing reason. mathlib's `Algebra.Initial.str_isIso` is
  not invoked: it would obtain this through `Limits.IsInitial` and
  so carry `Classical.choice`, which the direct construction does
  not.
- `PFunctor.wStrIso_hom` — `P.wStrIso.hom = P.wAlgebra.str`, by
  `rfl`. Without it nothing connects `wStrIso` to the algebra,
  since it is built from `WType.equivSigma` rather than from
  `W.mk`, and the stated purpose (consumers rewriting through the
  isomorphism instead of reaching for `inv`) needs the
  identification. The dual statement is deliberately absent:
  `wStrIso.inv` is `equivSigma`'s forward map, which is not
  definitionally `↾PFunctor.W.dest`, so no `rfl` theorem is
  available on that side.

Exposure follows the per-declaration convention of
`Slice/Basic.lean` rather than a whole-file `@[expose] public
section`. `wAlgebra`, `wElim`, and `wStrIso` are `@[expose]`, so
`wStrIso_hom` states its definitional equality as an exported
`rfl` theorem and the `GebTests/` mirror and roadmap item 3 can
unfold them across the module boundary. `wUniqueHom` carries
`@[expose, instance_reducible]` — both attributes, matching the
`@[expose, implicit_reducible]` pairing already used in
`Slice/Basic.lean`. The two are orthogonal: `@[expose]` decides
whether the body crosses the module boundary at all, and for a
`def` is the only thing that does so, while a reducibility
attribute only governs unfolding of a body already visible.
`@[expose]` alone would re-trigger `warn.classDefReducibility` on
a class-typed `def`, which `weak.warningAsError = true` in
`lakefile.toml` turns into a build failure. The two
`Data/W/Basic.lean` declarations are theorems and need no exposure
decision.

### `Univariate/Initial.lean`

One declaration.

- `PFunctor.wIsInitial : Limits.IsInitial P.wAlgebra`, obtained
  from `PFunctor.wUniqueHom` by `Limits.IsInitial.ofUnique`, with
  the `Unique` introduced by `haveI` since `wUniqueHom` is a `def`.
  `ofUniqueHom` is not used: it takes the hom family and its
  uniqueness as separate explicit arguments, which would restate
  what `wUniqueHom` already packages, and it is in any case defined
  upstream as `haveI := …; IsInitial.ofUnique X`. Both depend on
  `Classical.choice`.

The module is added to `GebMeta.classicalAllowedModules`. Its
`GebTests/` mirror is added likewise.

### `Slice/Functor.lean`

The refactor `TODO.md` item 2 asks for: `domFunctor` is rebuilt
from the new wrapper instead of being hand-written.

- `SliceDomPFunctor.domSubfunctor` — the `r`-compatible assignments
  as a `CategoryTheory.Subfunctor` of
  `Over.forget dom ⋙ F.toPFunctor.functor`. Its `obj` field is the
  compatibility predicate as a `Set`; its `map` field is
  `Prop`-valued, asserting that the predicate is closed under the
  ambient functor's action. The underlying function of
  `domFunctor.map` is then supplied by the ambient composite rather
  than written out, and only the closure proof remains.
- `SliceDomPFunctor.domFunctor` — redefined as
  `F.domSubfunctor.toFunctor`. The hand-written object map,
  morphism map, `map_id`, and `map_comp` are removed.

The refactor is behaviour-preserving and unconstrained in universe:
`F.domSubfunctor.toFunctor = F.domFunctor` holds by `rfl` at fully
general `{dom : Type uD}`, and `domFunctor` keeps its `uD`
polymorphism. `SliceDomPFunctor.domFunctor` is referenced only in
this module and its `GebTests/` mirror, so nothing else in the tree
is affected.

`domSubfunctor` is `@[expose]`, as every other definition in the
file is: after the redefinition the definitional chain from
`domFunctor` runs through it, so cross-module `rfl` depends on it
being exposed.

The trade is explicit. `Subfunctor` supplies `map_id` and
`map_comp`, four of the current definition's eight lines, and
supplies `Subfunctor.ι` for free. Against that it adds
`Mathlib.CategoryTheory.Subfunctor.Basic`, which directly imports
`Elementwise`, `Types.Basic`, and `Data.Set.Lattice.Image` and
carries a `CompleteLattice (Subfunctor F)` development, and it
introduces `Set` into a module that currently uses none. The
refactor is taken because `TODO.md` item 2 asks for it and because
[docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Higher-order constructions prefers assembling a functor from
existing constructions over hand-written laws, not because the line
count alone justifies it. There is no choice regression: the
current `domFunctor` already depends on `Classical.choice` and the
module is already in `GebMeta.classicalAllowedModules`.

No separate inclusion declaration is introduced. The natural
transformation into the underlying polynomial functor is the
upstream `Subfunctor.ι`, available from `domSubfunctor`; adding a
named wrapper for it would be cost without return.

Documentation changes are required at both the module and the
declaration level.

In the module docstring: `domSubfunctor` joins
`## Main definitions`; the `## Implementation notes` sentence
describing `domFunctor`'s proof machinery — that it reuses the core
`obj`/`map` with "the identity law discharged by `ext` and the core
`map_id`, and the composition law by `ext` and `rfl`" — becomes
false once those proofs come from `Subfunctor.toFunctor`, and is
rewritten; and a note is added, in the timeless form the
documentation rules require, that `domFunctor` is the subfunctor of
`Over.forget dom ⋙ F.toPFunctor.functor` cut out by the
compatibility predicate, with `Subfunctor.ι` the inclusion.

At the declaration level: `domFunctor`'s own docstring describes it
as "the core maps packaged over `Over dom`", which the refactor
falsifies in the same way — the morphism map now comes from the
ambient composite, not from `SliceDomPFunctor.map` — so it is
rewritten too. `domSubfunctor` gets its own docstring, mandatory
for every `def` under
[docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Comment and docstring rules.

The module docstring's `## References` section gains
`[AltenkirchGhaniHancockMcBrideMorris2015]`, which
§ Transcription or novel attributes to `domSubfunctor` and which
the section does not currently list.

The `## Implementation notes` sentence about the `cod` universe
describes `SlicePFunctor.functor` and is unaffected.

## Transcription or novel

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing requires each definition to be marked. The
citations are `GambinoHyland2004` and
`AltenkirchGhaniHancockMcBrideMorris2015`, both already in
`docs/references.bib`.

| Declaration | Status | Source |
| --- | --- | --- |
| `WType.elim_mk`, `WType.elim_unique` | transcription | the universal property of the W-type as initial algebra, [GambinoHyland2004] |
| `PFunctor.functor` | transcription | the interpretation of a container as a functor, [AltenkirchGhaniHancockMcBrideMorris2015] |
| `PFunctor.wAlgebra`, `wElim`, `wUniqueHom`, `wIsInitial`, `wStrIso` | transcription | W-type as initial algebra of the polynomial endofunctor, and its fixed-point property, [GambinoHyland2004] |
| `SliceDomPFunctor.domSubfunctor` | transcription | the dependent polynomial functor as the compatible part of its underlying one, [GambinoHyland2004], [AltenkirchGhaniHancockMcBrideMorris2015] |
| `PFunctor.functor_obj`, `functor_map`, `wStrIso_hom` | neither | identifications between two Lean spellings; no `[Key]` in their docstrings |

Every declaration stating mathematical content is a transcription;
none is novel. The criterion is CONTRIBUTING's — whether the
definition or theorem is taken from published mathematics — not
whether the Lean proof reuses an existing mathlib declaration.
`wStrIso` states `P (W) ≅ W`, the fixed-point property that is part
of the initial-algebra result cited in the same row; that it is
obtained by repackaging mathlib's `WType.equivSigma` bears on the
proof, not on the provenance of the statement. mathlib's own
docstring for `equivSigma` describes it in exactly those terms.

The last row is neither transcription nor novel, because its
members state nothing found in published mathematics: they record
that two Lean expressions are definitionally equal. Attaching a
citation to them would credit a source for a claim it does not
make, so their docstrings carry no `[Key]`.

`domSubfunctor` carries both keys, as `Slice/Basic.lean` already
does: Gambino–Hyland present the dependent polynomial functor as a
composite of adjoints, while the compatible-restriction-of-a-
container framing that `domSubfunctor` encodes is the
indexed-container presentation.

No `docs/references.bib` key is added. Both keys used are already
present, and each is already cited by at least one of
`Slice/Basic.lean` and `Slice/Functor.lean`.

## Universe constraints

`P.Obj : Type v → Type (max v uA uB)` maps `Type v` to itself
whenever `max v uA uB = v`, that is whenever `uA ≤ v` and
`uB ≤ v`. `v := max uA uB` is the least such `v`, not the only one:
`v := max uA uB w` works for every `w`. `PFunctor.functor` is
therefore defined at an unconstrained `v` as
`Type v ⥤ Type (max v uA uB)`, the most polymorphic form that
compiles, as
[docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Structure and typeclass patterns requires.

Where an endofunctor is needed, `functor` is instantiated rather
than redefined. `Univariate/W.lean` instantiates at
`v := max uA uB`, which is forced there and only there, because
`P.W : Type (max uA uB)` must be the algebra's carrier.

No universe is pinned elsewhere. In particular `Slice/Functor.lean`
needs no pin: `domFunctor` maps into `Type (max uA uB uD)`, and
`Over.forget dom ⋙ P.functor` instantiated at `v := uD` maps into
`Type (max uD uA uB)`, the same universe, so the composite exists
at fully general `{dom : Type uD}`. That instantiation is written
explicitly as `functor.{uA, uB, uD}`: the composite does not unify
if `v` is left to inference, which matches the repository's
recorded practice of writing full `.{…}` universe lists.

The codomain-side restriction already recorded in
`Slice/Functor.lean` § Implementation notes — that
`SlicePFunctor.functor` pins `cod` because `Functor.toOver`
requires its over-base object in the lifted functor's codomain
category — is unrelated to the above and stands as written. It has
no domain-side counterpart.

## Choice boundary

The upstream declarations this branch's choice profile turns on:

| Upstream declaration | Choice | Used by |
| --- | --- | --- |
| `Endofunctor.Algebra.instCategoryStruct` | free | `wElim`, `wUniqueHom` |
| `Endofunctor.Algebra.instCategory` | free | `wIsInitial` |
| `Equiv.toIso` | free | `wStrIso` |
| `Functor.comp` | requires `Classical.choice` | `domSubfunctor`, via `Over.forget dom ⋙ …` |
| `Over`, `Over.forget` | require `Classical.choice` | `domSubfunctor`; pre-existing in that module |
| `CategoryTheory.inv` (on an `IsIso`) | requires `Classical.choice` | nothing — avoided by using `Iso` |
| `Limits.IsInitial.ofUnique` | requires `Classical.choice` | `wIsInitial` |

`wAlgebra` names neither algebra-category instance: it is the pair
of a carrier and a bundled structure map, and needs no `Category`.

The functor, the algebra, the algebra morphism, the structure-map
isomorphism, and initiality-as-`Unique` name none of the tainted
declarations, so the constructive core — `Data/W/Basic.lean`,
`Univariate/Functor.lean`, and `Univariate/W.lean` — is certified by
the axiom linter under the default permitted set.
`Univariate/Initial.lean` is not, and is not claimed to be: it is a
single declaration whose only choice-dependent ingredient is
`IsInitial.ofUnique`.

Consumers in roadmap items 3 to 6 may use either form of
initiality: `wUniqueHom` where a choice-free development is
required, or the `IsInitial` packaging where mathlib's colimit API
is wanted.

## Verification performed

The following were compiled against the pinned toolchain during
design, with axioms as reported by `#print axioms`.

| Construction | Axioms |
| --- | --- |
| `WType.elim_unique` | `{Quot.sound}` |
| `PFunctor.functor` as `ofTypeFunctor P.Obj`, at unconstrained `v` | `{propext, Quot.sound}` |
| `wAlgebra`, the algebra `⟨P.W, ↾W.mk⟩` | `{propext, Quot.sound}` |
| `wElim`, the algebra morphism from `WType.elim` | `{propext, Quot.sound}` |
| `wUniqueHom : Unique (P.wAlgebra ⟶ B)` | `{propext, Quot.sound}` |
| `wStrIso` as `(WType.equivSigma P.B).symm.toIso` | `{propext, Quot.sound}` |
| `IsIso P.wAlgebra.str` constructed directly | `{propext, Quot.sound}` |
| `SliceDomPFunctor.domSubfunctor` | adds `Classical.choice` |
| `Limits.IsInitial.ofUnique` / `ofUniqueHom` (upstream) | add `Classical.choice` |
| `Functor.comp` (upstream) | adds `Classical.choice` |
| `Endofunctor.Algebra.instCategory` (upstream) | `{propext, Quot.sound}` |
| `Equiv.toIso` (upstream) | `{propext, Quot.sound}` |
| `wStrIso_hom : wStrIso.hom = wAlgebra.str` | `{propext, Quot.sound}`, by `rfl` |

`elim_mk` holds by plain `rfl`. `ofTypeFunctor P.Obj` was checked
to agree definitionally with the core: `(P.functor).obj α = P.Obj α`
by `rfl`. The endofunctor form was compiled at
`Type (max uA uB w)` for an arbitrary third universe `w`,
establishing that `v = max uA uB` is not the only solution.

The instance-versus-`def` question for `wUniqueHom` was settled by
compilation: with a `Unique (A ⟶ B)` instance in scope,
`(default : Endofunctor.Algebra.Hom A A) = 𝟙 A` holds by `rfl`
while `(default : A ⟶ A) = 𝟙 A` does not, so the two spellings
disagree. Without such an instance, `Inhabited (A ⟶ A)` does not
synthesize at all.

The `Slice/Functor.lean` refactor was compiled in full at fully
general `{dom : Type uD}`, with no universe constraint:
`domSubfunctor` elaborates, and
`F.domSubfunctor.toFunctor = F.domFunctor` holds by `rfl`, as does
the object-level agreement with the core
`F.Obj (ConcreteCategory.hom Y.hom)`. `Subfunctor.ι` supplies the
inclusion into `Over.forget dom ⋙ P.functor`.

An isomorphism in `Type v` is choice-free, which is what allows the
structure-map isomorphism to stay in `Univariate/W.lean`.

## Out of scope

- Compatibility of `PFunctor.comp` with functor composition, the
  identity polynomial functor, and the lemmas `comp.get_mk` /
  `comp.mk_get` that mathlib lacks. A separate concern on its own
  topic branch (§ Scope), carried as a `TODO.md` item. Two design
  points established here transfer to that branch's spec: the
  identity polynomial functor is `protected def PFunctor.id`,
  since an unprotected `id` shadows `_root_.id` throughout
  `namespace PFunctor` and breaks idiomatic uses such as
  `P.map id`; and both isomorphisms admit an ambient universe `w`
  beyond the parameters of the functors involved.
- Coalgebras and M-types, including the terminal-coalgebra
  characterisation of `PFunctor.M` — roadmap item 4.
- Initiality of the slice and presheaf W-types — roadmap item 3.
- Morphisms of polynomial functors as natural transformations of
  their interpretations. This is the hom-structure of the category
  of polynomial functors, and so a prerequisite of the base layer
  roadmap item 5 anticipates needing, rather than a universal
  morphism itself. It is left to item 5.
- A named abbreviation for the algebra category:
  `Endofunctor.Algebra P.functor` is used directly. Introducing a
  wrapper for a single notion is deferred until a consumer
  requires it.
- The multivariate `MvPFunctor` and the `QPF` layer.

## Supporting work

- A `GebTests/` module mirroring each new source module, each
  naming a `def` — or, where the module under test exports only
  theorems, as `Data/W/Basic.lean` does, a named `theorem` — built
  from the module under test, so that the olean records a constant
  and `lake shake` observes the import. An `example` does not
  suffice. Plus the mirrored index
  modules `GebTests/Mathlib/Data/W.lean` and
  `GebTests/Mathlib/Data/PFunctor/Univariate.lean`, and extension
  of the existing `GebTests/Mathlib/Data.lean` and
  `GebTests/Mathlib/Data/PFunctor.lean`.
- No new `docs/references.bib` key (§ Transcription or novel).
- An entry in [docs/index.md](../../index.md) for the new modules,
  and amendment of the existing `Geb/Mathlib/Data/PFunctor/Slice/`
  entry, which describes `domFunctor` as "reusing the core
  `obj`/`map`" and does not mention `domSubfunctor`. CONTRIBUTING
  requires a new concept to be documented in the branch that
  introduces it.
- Amendment of [TODO.md](../../../TODO.md)'s description of the
  polynomial-functor roadmap. Two sentences are affected: that the
  roadmap is "a linear sequence of separate planning–implementation
  cycles", and that "each item's full spec and plan are written
  only after the prior item's implementation is complete". Items 1
  and 2 touch disjoint files and neither depends on the other, so
  the roadmap is a partial order; both sentences are corrected in
  this branch rather than left asserting a discipline the branch
  departs from.
- Removal of roadmap item 2 from `TODO.md`, renumbering of the
  items below it (3→2, 4→3, 5→4, 6→5), and correction of the
  numeric cross-references embedded in the remaining items' prose.
  There are exactly six such sites, and they do not all need the
  same treatment:

  | Line | In item | Text | Action |
  | --- | --- | --- | --- |
  | 64 | 1 | "universal morphisms (item 5)" | → item 4 |
  | 82 | 3 | "wrappers of item 2" | referent removed — repoint |
  | 84 | 3 | "`WType` initiality of item 2" | referent removed — repoint |
  | 92 | 4 | "pattern of items 2 and 3" | referent removed; 3 → 2 |
  | 126 | 5 | "specializations (item 1)" | no change — item 1 keeps its number |
  | 156 | 6 | "W-type (item 3) or M-type (item 4)" | → items 2 and 3 |

  The three references to item 2 (lines 82, 84, 92) are not a
  renumbering: their referent leaves `TODO.md` entirely when item 2
  is removed, so they are repointed at the `docs/index.md` entry
  for the completed work. The TOC is regenerated with `doctoc`.
- A new `TODO.md` item for the composition workstream excluded
  above, so the content is not lost when item 2 is removed.
- A new `TODO.md` item: settle the upstream placement of every file
  under `Geb/Mathlib/Data/` that imports `Mathlib.CategoryTheory.*`
  — currently `Slice/Functor.lean`, `Presheaf/Functor.lean`,
  `Presheaf/Basic.lean`, `IndRec/Basic.lean`, and
  `IndRec/Naturality.lean`, plus the three added here — against
  mathlib's convention that no file under `Mathlib/Data/` does so.
  The criterion covers `Geb.Mathlib.CategoryTheory.*` imports too,
  since those extract to `Mathlib.CategoryTheory.*`
  (§ Module layout). The item is scoped by that criterion rather
  than by a module list, so it cannot be settled incompletely. The
  question predates this workstream.
- Removal of this spec and the implementation plan in the branch's
  final commits, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

## References

- [TODO.md](../../../TODO.md) — roadmap item 2.
- [CONTRIBUTING.md](../../../CONTRIBUTING.md) — concern shape,
  code is cost, the floodgate test, and the citation requirement.
- [docs/rules/lean-coding.md](../../rules/lean-coding.md)
  — recursor discipline, constructive discipline, higher-order
  constructions, universe polymorphism, documentation
  requirements.
- [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md)
  — subtree import rules and the floodgate test.
- `docs/references.bib` — `GambinoHyland2004` and
  `AltenkirchGhaniHancockMcBrideMorris2015`, the two keys cited.
