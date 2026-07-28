# Spec: W1 — `FinSetSkel` and its comparison with mathlib's skeleton

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Decisions fixed here](#decisions-fixed-here)
- [Transcription and novelty](#transcription-and-novelty)
- [Findings](#findings)
  - [Confirmed from the umbrella spec](#confirmed-from-the-umbrella-spec)
  - [Root `Vector`'s `ofFn` lemmas depend on `Classical.choice`](#root-vectors-offn-lemmas-depend-on-classicalchoice)
  - [The representation decision, re-derived](#the-representation-decision-re-derived)
  - [Two of the three index equivalences are choice-tainted](#two-of-the-three-index-equivalences-are-choice-tainted)
  - [An isomorphism in `Cat` cannot be choice-free](#an-isomorphism-in-cat-cannot-be-choice-free)
  - [The comparison is closed by `Functor.hext`](#the-comparison-is-closed-by-functorhext)
  - [The object carrier and reducibility](#the-object-carrier-and-reducibility)
  - [The index equivalences need no `ULift` transport](#the-index-equivalences-need-no-ulift-transport)
- [Module layout](#module-layout)
- [Deliverables](#deliverables)
- [Amendments to `TODO.md` and the documents stating subtree rules](#amendments-to-todomd-and-the-documents-stating-subtree-rules)
- [Out of scope](#out-of-scope)
- [Verification obligations](#verification-obligations)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope of this document

W1 of the workstream group whose roadmap is `TODO.md` § FinSetSkel as
an elementary topos. That entry is authoritative for the group: the
dependency order, the operation table, the class fields, the eight
cross-workstream interface constraints and the standing obligations
are read from it and are not restated here except where this document
amends them.

This document is transient, per `CONTRIBUTING.md` § Concern shape. It
records the decisions W1 fixes for W3 and W4, the findings supporting
them, and the amendments W1 makes to `TODO.md` and to the documents
stating subtree rules. What persists after the branch is the Lean
content, its `docs/index.md` entry, its `docs/references.bib` entry,
its module docstrings, and those amendments. Anything a later
workstream must act on is therefore in § Amendments to `TODO.md` and
the documents stating subtree rules, and not only here.

The group's umbrella spec pinned its findings to the mathlib revision
current on 2026-07-27; `TODO.md` requires each workstream to
re-verify the findings it consumes. § Findings records that
re-verification, against `leanprover/lean4:v4.33.0-rc1` and the
mathlib and Batteries pins in `.lake/packages/`. Four of the findings
W1 consumes did not survive it, and one assumption of the operation
table did not either.

## Decisions fixed here

Four decisions bind W3, W4 and W5, all downstream of W1, which would
otherwise each settle them; the fifth is W1's own.

1. **Objects.** `structure FinSetSkel : Type u where len : ℕ`.
   § The object carrier and reducibility gives the reason and the
   alternative.
2. **`ULift` placement.** The morphism type is
   `ULift.{u} (Vector (Fin Y.len) X.len)`, with the lift outside the
   vector rather than on its entries. Interface constraint 4 requires
   W1 to settle this.
3. **Morphism API.** A named `protected def FinSetSkel.Hom`, an
   `ofVec`/`toVec` pair with both round trips `toVec_ofVec` and
   `ofVec_toVec`, `@[ext]` extensionality, `@[simp]` identity and
   composition lemmas, and `attribute [irreducible]` sealing the
   representation once the API is in place. Both round trips are `rfl`
   before the seal, and neither is after it: `toVec_ofVec` then needs
   a proof unfolding `toVec` and `ofVec` by name, and `ofVec_toVec` is
   not provable at all, needing structure eta on the sealed type.
   Omitting them would therefore put `ofVec_toVec` beyond recovery and
   both on the branch off `main` that constraint 7 exists to avoid.
   They are what lets W3 and W4 reason about a morphism built by
   `ofVec` at all. This is the API shape
   `SimplexCategory` uses
   (`Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean`, lines
   71-140). The shape is what is borrowed and not the
   representation: `SimplexCategory.Hom` is a bundled monotone
   function, and its hom-`DecidableEq` depends on `Classical.choice`,
   which is the property this group exists to avoid.
4. **Application-normal form.** `f.toVec.get i`, with `i : Fin X.len`,
   together with a bridge to the `getElem` API that W1 states itself.
   Batteries has the bridge (`Vector.get_eq_getElem`,
   `Batteries/Data/Vector/Lemmas.lean:68`), and W0 admitted
   `Batteries.` to the subtree allow-list, so importing it is
   permitted. W1 declines to. No `Mathlib.*` module reaches
   `Batteries.Data.Vector.Lemmas`; the only route is the bare umbrella
   `import Mathlib`, which `scripts/lint-imports.sh` forbids in
   upstream-eligible files, so the import would have to be direct —
   and a direct import brings the tainted `@[simp]` lemmas of the last
   paragraph below with it. Core defines the `get` accessor but states
   almost no lemmas about it: its only two `Vector.get_*` theorems are
   `get_find?_mem` and `get_find?_replicate`. W1 therefore restates
   the bridge, which is `rfl`, and leaves it unmarked.

   The evidence for and against is recorded in full, so that a
   later reader has both. For `get`: the vector's index type is
   exactly `Fin X.len`, so the statement of every application lemma is
   coercion-free. Against it: the core API is `getElem`-shaped —
   core states 74 `Vector.getElem_*` theorems against 2
   `Vector.get_*`, and `Mathlib/Data/Vector/Defs.lean` names the
   absence of `getElem` as the preferred accessor a deficiency of
   `List.Vector`. `simp` proves neither orientation of
   `v.get i = v[i]`, so a choice is forced.

   The bridge bounds the cost of choosing `get`: it is `rfl`, so any
   `getElem`-shaped core lemma is available in `get` form after one
   rewrite, and W1 does not owe `get`-form restatements of the core
   `Vector` API. It is left unmarked, `simp` in either orientation
   being what would rewrite away the normal form.

   Declining the Batteries import is what leaves the `get` form
   usable. Batteries tags `Vector.get_ofFn` and `Vector.get_range`
   `@[simp]` and both depend on `Classical.choice`; they would fire on
   the normal form W1 fixes. Absent that import they are not in scope,
   and the only ambient family of this kind is core's, stated in
   `getElem` form.
5. **Module layout.** § Module layout.

## Transcription and novelty

`CONTRIBUTING.md` § Cite the literature when transcribing requires a
brainstorming-phase spec to mark each definition as transcription or
novel.

| Definition | Status | Source |
| --- | --- | --- |
| `FinSetSkel` | transcription | a skeleton of the category of finite sets, [nLabSkeletalCategory]; mathlib's `FintypeCat.Skeleton` is the same category |
| the morphism representation | neither | a representation choice for an existing category, not a definition of new mathematics |
| `Vector.ofFnC` and its round trips | neither | an alternative definition of an existing core construction, and choice-free reproofs of its lemmas |
| the `List.Nodup.getEquiv` rebuild, the compression, and the vector-level inversion | neither | choice-free reproof of an existing mathlib lemma, and equivalences assembled from existing mathlib lemmas |

W1 defines no novel mathematics: the category is standard and
everything else is a representation or a reproof.

The citation was verified against the primary source, per `AGENTS.md`
§ Verify agent claims: the nLab entry defines a skeletal category as
one in which "any two objects that are isomorphic are actually
already equal", which is mathlib's `Skeletal`, and a skeleton of `C`
as "a skeletal subcategory of `C` whose inclusion functor exhibits it
as equivalent to `C`". Both quotations were retrieved twice and agree.

No textbook locator is recorded, and the reason is recorded with it.
The page's reference list names Mac Lane, *Categories for the Working
Mathematician* (1971), p. 91; Riehl, *Category Theory in Context*
(2017), p. 34; Richter, *From categories to homotopy theory* (2020),
§2.6; and Isbell and Wright, *Another equivalent form of the axiom of
choice* (1966), besides a Wikipedia pointer and one arXiv paper that
are not textbook locators. Those four are locators nLab attests, not locators this
document checked against the books, and nLab is secondary to each of
them. W1 therefore carries a standing obligation of the kind
`TODO.md` already records for [Pare1974]: verify a textbook locator
against the primary source before any Lean docstring cites one. Until
then the docstring cites the nLab entry, whose definitions were
verified against the page itself.

nLab entries are already a citation form in `docs/references.bib`
(`nLabParametricRightAdjoint`); W1's branch adds
`nLabSkeletalCategory` in the same shape — keyed, titled and linked on
`skeletal category` at `https://ncatlab.org/nlab/show/skeletal+category`,
which is the page actually served: `.../show/skeleton+of+a+category`
redirects there with a 301, and `.../show/skeleton` is a separate
disambiguation page — cited from the
`FinSetSkel/Basic.lean` module docstring's `## References` section.
mathlib's own `CategoryTheory/Skeletal.lean` carries no citation, so
nothing is inherited from it.

The same page records that "in the absence of the axiom of choice, it
is more appropriate to define a skeleton of `C` to be a weak
skeleton". The docstring carries that alongside the citation, since it
states the group's own situation: W1's category is choice-free, and
`IsSkeletonOf` is obtainable only in the allowlisted wrapper.

## Findings

Verified by `#print axioms` and by elaborating each construction
through the `lean-lsp` MCP. The durable content is the pointers and
the axiom conclusions, not the line numbers.

### Confirmed from the umbrella spec

- `FintypeCat.Skeleton` is `ULift ℕ`;
  `FintypeCat.Skeleton.instSmallCategory` depends on no axioms.
- `List.Nodup.getEquiv` depends on `Classical.choice`, through
  `List.idxOf_lt_length_iff`; `List.idxOf_lt_length_of_mem` depends on
  `propext` alone, and the substitution yields a rebuild at
  `propext, Quot.sound`.
- `Cat.equivOfIso` and `Cat.ext` are present; `equivOfIso` is a plain
  `def` and so computable, as is `FintypeCat.Skeleton.incl`.
- `CategoryTheory.Equivalence` depends on `Classical.choice`.

The skeletal facts are `FintypeCat.Skeleton.is_skeletal` and
`FintypeCat.isSkeleton`; the umbrella spec writes both unqualified and
records the second's namespace correctly, so the fully qualified forms
are noted here only because the namespaces differ and a reader
qualifying them by symmetry would guess wrong.
`FintypeCat.Skeleton.equivalence` is `noncomputable`, so no W1
declaration may route through it; `CONTRIBUTING.md`
§ Constructive-only forbids `noncomputable`.

### Root `Vector`'s `ofFn` lemmas depend on `Classical.choice`

The lemmas relating a vector to its indexing function — which define
the identity morphism and discharge the category laws — are
choice-dependent for root `Vector` and choice-free for `List.Vector`:

| Declaration | Axioms |
| --- | --- |
| root `Vector`'s derived `DecidableEq`, as `inferInstance` selects it | `propext, Quot.sound` |
| the same via `instDecidableEqOfLawfulBEq` | `propext, Classical.choice, Quot.sound` |
| `List.Vector.instDecidableEq` | none |
| `Vector.getElem_ofFn` (core) | `propext, Classical.choice, Quot.sound` |
| `Vector.ofFn_getElem` (core) | `propext, Classical.choice, Quot.sound` |
| `Vector.get_ofFn` (Batteries) | `propext, Classical.choice, Quot.sound` |
| `Vector.getElem_range`, `Vector.getElem_finRange` (core) | `propext, Classical.choice, Quot.sound` |
| `List.Vector.get_ofFn`, `List.Vector.ofFn_get` | `propext, Quot.sound` |

There is no root-namespace `Vector.ofFn_get`; the core declaration in
that direction is `Vector.ofFn_getElem`. Root `Vector`'s `DecidableEq`
is `deriving`d in `Init/Data/Vector/Basic.lean` and has no stable
instance name, which is why the two rows above name resolution routes
rather than declarations: both inhabit the same class, and only one is
choice-free. `Vector.instLawfulBEq`, which the second goes through, is
itself choice-tainted.

The dependence runs `Vector.get_ofFn` → `Vector.getElem_ofFn` →
`Array.getElem_ofFn` → the private `Array.getElem_ofFn_go`
(`Init/Data/Array/Lemmas.lean:4257`), which is its root: every
other ingredient of `Array.getElem_ofFn` is choice-free.
`Array.toList_ofFn` (`Init/Data/Array/OfFn.lean:53`) is a
*consequence*, proved by `apply List.ext_getElem <;> simp`, not a
cause. It
reaches `Vector.getElem_range` and `Vector.getElem_finRange` too, so
no enumerating primitive in the root `Vector` or `Array` API supplies
a choice-free identity morphism — `Vector.finRange` being the natural
spelling of one. Taken as the umbrella spec describes it, the
`SmallCategory` instance would therefore depend on `Classical.choice`,
which interface constraint 8 forbids outside a wrapper.

The dependence is confined to the `ofFn` family. `Vector.ext`,
`Vector.getElem_mk`, `Vector.getElem_map`, `Vector.getElem_toList`,
`Array.getElem_toList`, `List.getElem_ofFn`, `List.getElem_toArray`,
`List.size_toArray` and `List.length_ofFn` are all choice-free and all
in Lean core, so constructing the vector through `List.ofFn` rather
than `Array.ofFn` gives a choice-free `ofFn` whose result is still
array-backed, leaving indexing constant-time:

```lean
universe u

namespace Vector

def ofFnC {α : Type u} {n : Nat} (f : Fin n → α) : Vector α n :=
  ⟨(List.ofFn f).toArray, by rw [List.size_toArray, List.length_ofFn]⟩

theorem getElem_ofFnC {α : Type u} {n : Nat} (f : Fin n → α)
    (i : Nat) (h : i < n) : (ofFnC f)[i] = f ⟨i, h⟩ := by
  rw [ofFnC, getElem_mk, List.getElem_toArray, List.getElem_ofFn]

end Vector
```

`ofFnC` elaborates at `propext`, and `getElem_ofFnC` and the two round
trips derived from it at `propext, Quot.sound`. With them the
`SmallCategory` instance, the `DecidableEq` instance and morphism
extensionality are all `propext, Quot.sound`. The repository sets
`autoImplicit false`, which is what makes the `universe u` line
necessary; the
`namespace Vector` is necessary because the proof writes `getElem_mk`
unqualified.

No choice-free equation in the existing core API relates `ofFnC` to
`Vector.ofFn`: the bridge is `List.toArray_ofFn`
(`Init/Data/Array/OfFn.lean:50`), itself choice-dependent. Nothing
prevents a choice-free reproof of `Array.getElem_ofFn_go`, from which
the bridge and the whole standard API would follow; § Out of scope
declines to attempt it and § Amendments records it as a trigger.
Until then the rebuilt `ofFn` and core's coexist unrelated, and W1's
constructions use the rebuilt one throughout.

W0's stated reason for preceding W1 lapses: that reason was Batteries'
`Vector.get_ofFn`, which W1 cannot use. Every ingredient above is in
Lean core, so W1 needs no `Batteries.` import. W0 is complete and W4
still requires it, so only the justification changes.

### The representation decision, re-derived

`TODO.md` fixes root `Vector` over `List.Vector` on the ground that
"the `propext`/`Quot.sound` that root `Vector`'s `DecidableEq` costs
is accepted, neither being `Classical.choice`". The finding above
shows that ground to be the wrong comparison, so the decision is
re-derived here rather than assumed.

Write `f : X ⟶ Y` with `X.len = m` and `Y.len = n`, so `f`'s vector
has length `m`. Composition is
`Vector.ofFnC fun i => g.toVec.get (f.toVec.get i)`: `m` steps, each
one index into `f` and one into `g`. On `List.Vector` an index at
position `i` costs `O(i)`, so the `m` reads of `f` cost `O(m²)` before
the `m` reads of `g` cost `O(m · n)`. `Vector.map` would serve equally and is
choice-free through `Vector.getElem_map`, but it would need a
`get`-form map lemma that core does not state, where `ofFnC` reuses
`get_ofFnC`, which W1 has already.

| | root `Vector` | `List.Vector` |
| --- | --- | --- |
| indexing | constant-time | linear |
| composing `f : X ⟶ Y` with `g : Y ⟶ Z` | `O(m)` | `O(m² + m · n)` |
| new declarations | five, in a new module with a `GebTests` parallel: `ofFnC`, `getElem_ofFnC`, the two round trips over it, and the `get`/`getElem` bridge | none — `List.Vector.get_ofFn`, `List.Vector.ofFn_get` and `Equiv.vectorEquivFin` are choice-free and already exist, and the `get` form is `List.Vector`'s own, so no bridge is needed |
| lemmas that must not be reached | a choice-tainted `@[simp]` family over `ofFn`, `range` and `finRange` | none |

`Mathlib/Data/Vector/Defs.lean` states considerations for each, and is
quoted in full rather than selectively: "Any combination of reducing the use of
`List.Vector` in Mathlib, or modernising its API, would be welcome",
and "Typically, if you are doing programming or verification, you will
primarily use `Vector α n`, and if you are doing mathematics, you may
want to use `List.Vector α n` instead."

The decision stands, on the ground that composition is the operation
the category exists to run: `TODO.md`'s statement of purpose is that
Geb requires morphisms that are data to be computed with, and an
asymptotic cost on composition falls on that property directly,
where five declarations are not. The evidence against is recorded in
full:
`List.Vector` would cost zero new declarations, would remove the
tainted-`@[simp]` hazard entirely, and is what the second half of the
mathlib quotation points to for mathematical use.

`ofFnC` is public and shared rather than private to
`FinSetSkel/Basic.lean` because W3 and W4 need it for every
construction that builds a vector from an index function.

### Two of the three index equivalences are choice-tainted

| Declaration | Axioms |
| --- | --- |
| `finSumFinEquiv` | `propext, Quot.sound` |
| `finProdFinEquiv` | `propext, Classical.choice, Quot.sound` |
| `finFunctionFinEquiv` | `propext, Classical.choice, Quot.sound` |
| `Fin.divNat` | `propext, Classical.choice, Quot.sound` |
| `Fin.modNat` | `propext` |

`Fin.divNat` is the tainted ingredient of `finProdFinEquiv`.

This is a finding about W3, not about W1, and it is recorded because
it invalidates an assumption of the operation table rather than of
W1's deliverables. Row c may use `finSumFinEquiv` as it stands. Rows d
and g cannot use `finProdFinEquiv` and `finFunctionFinEquiv` in a
module interface constraint 8 requires to be choice-free; W3 owes
choice-free replacements. The umbrella spec's plan was already
unusable in the same way — a `ULift` transport of a choice-tainted
equivalence is still choice-tainted — so this is not a consequence of
W1's amendment.

The replacements are not W1's, and the reasoning is recorded because
interface constraint 7 would otherwise appear to claim them.
Constraint 7 places in W1 what W3 and W4 *share*. Reading the
operation table: `finProdFinEquiv` feeds row d alone and
`finFunctionFinEquiv` row g alone; rows f and j derive from b, d, f
and h; all are W3. W4's row i and W5's row k touch neither. Constraint
7's purpose — keeping W3 and W4 independent of each other — is
therefore not engaged, and the replacements are W3-local. W1 records
the obligation in `TODO.md` so that W3 meets it by design rather than
discovering it at `lake lint`.

### An isomorphism in `Cat` cannot be choice-free

`CategoryTheory.Cat.category` depends on `Classical.choice`. An
isomorphism in `Cat` is an `Iso` with respect to that instance, so its
type mentions it and it inherits the dependence, by whatever route it
is constructed. The umbrella spec's contrary finding checked
`CategoryTheory.Iso` and `CategoryTheory.Functor`, both of which are
axiom-free, but not the category instance on `Cat`.

The isomorphism therefore belongs in the wrapper module with the
equivalence, and not in the choice-free core. This removes the reason
for a module separating the two.

### The comparison is closed by `Functor.hext`

The umbrella spec's route — `Cat.ext`, normalisation off `Cat.of`,
then `Functor.ext (fun X => rfl)` — does not close. Under
`Functor.ext` the `h_map` obligation retains `eqToHom` applied to
`(F ⋙ G).obj X = (𝟭 _).obj X`, and `eqToHom_refl` cannot fire on it,
the two sides being syntactically distinct.
`CategoryTheory.Functor.hext` takes the object equality together with
`HEq` of the morphism components and raises no `eqToHom` obligation.
`Functor.ext` must be written qualified: under `open CategoryTheory` a
bare `Functor.ext` resolves to the `LawfulFunctor` lemma and produces
an error mentioning `f <$> x`, which does not point at the cause.
`Functor.hext` is unambiguous, there being no `_root_.Functor.hext`.

Three further points, established by elaborating the construction:

- The two directions are factored as `toIdxFun` and `ofIdxFun`, whose
  round trips `ofIdxFun_toIdxFun` and `toIdxFun_ofIdxFun` are stated
  away from any functor and live in the choice-free core. Each
  composite identity then reduces to one of them through `heq_of_eq`,
  and the wrapper contains no argument. The two are not symmetric: the
  `FinSetSkel` direction is a single application, while the
  `FintypeCat.Skeleton` direction needs `funext` and a `ULift.up`
  congruence first, that category's hom type being a function type,
  with the object arguments given explicitly — under the seal,
  leaving them to unification fails with "invalid projection".
- The sealing of § Decisions fixed here item 3 constrains the order of
  declaration. `Hom.toVec` is a plain definition and survives the
  seal, as `SimplexCategory.Hom.toOrderHom` does; what does not
  survive is elaborating its body, the `ULift` projection `.down`,
  against a sealed `Hom`. A declaration whose body writes `.down`
  against the sealed type, and any `rfl` that must reduce through it —
  both round trips among them — fails with "invalid projection".
  Unfolding the pre-seal definitions by name recovers some of these
  and not others: it proves `toVec_ofVec` post-seal, axiom-free, as it
  proves mathlib's post-seal `SimplexCategory.id_toOrderHom`, but
  leaves `ofVec_toVec` at `⟨f.down⟩ = f`, which needs eta on the
  sealed type and is unreachable. The
  pointwise lemmas are stated before the seal regardless, over the
  pre-instance operations `Hom.id`, `Hom.comp` and `Hom.ofIdxFun'`;
  the seal follows; and the categorical forms
  `id_get`, `comp_get` and `ofIdxFun_get` are derived after the
  instance, each by application of its primed counterpart. The pinned
  morphism `DecidableEq` and `Repr` are likewise declared after the
  seal, both routing through `hom_ext` and `toVec` rather than through
  the representation. `ofIdxFun` is the post-seal name for
  `Hom.ofIdxFun'` at the categorical hom type.
- The `Cat.of` normalisation is `Cat.Hom.comp_toFunctor`,
  `Cat.Hom.id_toFunctor` and `Functor.toCatHom_toFunctor`. `Cat.of_α`
  exists but is not needed. The functor laws are discharged in term
  style, `funext fun i => congrArg ULift.up (id_get X i.down)` and its
  composition counterpart; a `simp`-based proof of the same goals
  additionally requires unfolding mathlib's `Skeleton.mk` and
  `Skeleton.len`, which are plain definitions W1 cannot make
  reducible.

The full chain — category instance, morphism API, `DecidableEq`, both
comparison functors, both composite identities, and the isomorphism —
elaborates, with the core at `propext, Quot.sound` and the wrapper at
`propext, Classical.choice, Quot.sound`. The comparison functors
themselves are `propext, Quot.sound`; the taint enters the composite
identities through their statements, `CategoryTheory.Functor.comp`
being choice-dependent. It is not `hext`, which is
`propext, Quot.sound`, nor `Functor.ext`, which is `Quot.sound` — the
choice between them is about which obligations they raise, not about
axioms.

### The object carrier and reducibility

Whatever names the object's length, it appears in the index type of
every morphism, so it must reduce at reducible transparency or no
`simp` lemma stated at `Fin X.len` fires against an index arising from
a construction. Three carriers were considered.

| Carrier | Length accessor | Reduces at reducible transparency |
| --- | --- | --- |
| `ULift ℕ` with `mk`, `len` as definitions | `len` | no |
| `ULift ℕ` with no accessors, using `ULift.up`/`ULift.down` | `down` | yes |
| one-field structure | `len` | yes |

The first fails because a definition is opaque at reducible
transparency. The repair is to mark `mk` and `len` `@[reducible]`, and
it cannot be confined to W1. Lean rejects `attribute [local reducible]`
by default, on the ground that reducibility affects the term-indexing
structures used by `simp` and instance resolution, and admits it only
under `set_option allowUnsafeReducibility true`; but the scoping is
the point rather than the syntax, since W3, W4 and W5 state their
constructions over `Fin X.len` and need the same reduction. A repair
that reached only W1's modules would not be a repair. The attribute is
therefore global whichever way it is written.

The second and third both work, `ULift` being itself a one-field
structure whose projection reduces by iota exactly as a bespoke one
does. The trade between them is: the second keeps carrier parity with
`FintypeCat.Skeleton`, leaving `TODO.md`'s "the same objects" true
unamended; the third supplies a named `len`, and an ext lemma once the
declaration carries `@[ext]` — a bare `structure` generates none —
where the second forces `X.down`, the representation's own name, into
the index type of every morphism and every downstream statement.

The third is chosen, for the readability of every downstream
statement, and the amendment below corrects "the same objects"
accordingly. The whole choice-free core — category instance,
`DecidableEq`, and both `toIdxFun`/`ofIdxFun` round trips — was
elaborated on it at `propext, Quot.sound` with no reducibility
attribute anywhere. Nothing requires the two carriers to agree: the
comparison functors map objects explicitly, and their composites are
identities by structure eta on each side.

### The index equivalences need no `ULift` transport

Interface constraint 4 has W1 supply `ULift`-transported forms of the
three index equivalences, on the grounds that every object carrier is
universe-zero data that must cross W1's `ULift` choice. That reasoning
holds for a morphism type lifting the entries. Under the placement
fixed in § Decisions fixed here the lift is outside the vector, so
index types are `Fin X.len` at `Type 0` and mathlib's equivalences
apply unlifted.

The route, recorded so that W3 can re-run it rather than re-derive it:
with `X Y : FinSetSkel.{u}` the hom type is
`ULift.{u} (Vector (Fin Y.len) X.len)`, `X.len : ℕ`, and
`Fin X.len : Type 0`; a row-d projection is then
`Hom.ofVec (Vector.ofFnC fun i => (finProdFinEquiv.symm i).1)` with
`i : Fin (m * n)`, and rows c and g are the same shape over
`finSumFinEquiv` and `finFunctionFinEquiv`. All three elaborate with
no transport. A `ULift` on indices survives only in the comparison
functors, whose target hom type is
`ULift (Fin X.len) → ULift (Fin Y.len)`; that needs `ULift.up` and
`ULift.down` directly.

The transported forms are therefore not written, and constraints 4 and
7 are amended. What remains owed to W3 is choice-freeness, not
lifting, per § Two of the three index equivalences are choice-tainted.

## Module layout

Interface constraint 8 divides each workstream into choice-free
modules carrying the constructions and the content of their universal
properties, and a wrapper carrying the mathlib structures. Only
wrappers are listed in `GebMeta.classicalAllowedModules`.

| Module | Content | Split |
| --- | --- | --- |
| `Geb/Mathlib/Data/Vector/OfFn.lean` | `Vector.ofFnC`, its round trips, and the `get`/`getElem` bridge | choice-free |
| `Geb/Mathlib/Data/Vector/NodupEquivFin.lean` | the vector-level inversion of an injective vector, named after the `List` module whose construction it transports | choice-free |
| `Geb/Mathlib/Data/List/NodupEquivFin.lean` | the choice-free `List.Nodup.getEquiv` rebuild and the predicate compression | choice-free |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` | the object structure with its `DecidableEq`, `Inhabited` and `Repr`; the morphism API with both `ofVec`/`toVec` round trips; the `SmallCategory` instance; extensionality and application lemmas; the pinned morphism `DecidableEq` and `Repr`; `toIdxFun`, `ofIdxFun` and their two round trips | choice-free |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` | the comparison functors, the two composite identities, the isomorphism in `Cat`, the equivalence, `incl`, and the transported `Skeletal` and `IsSkeletonOf` | wrapper |

Two criteria place a declaration in the wrapper, and both are needed.
Constraint 8's: a mathlib structure or `Prop` instance is packaging
and goes there whatever its axioms, which is why the comparison
functors are in `Skeleton.lean` although they are themselves
`propext, Quot.sound`. And, for a declaration constraint 8 does not
already assign, whether any proof of it within W1's budget avoids
`Classical.choice` — not whether its statement mentions tainted
vocabulary. The distinction matters for
`Skeletal FinSetSkel`: `CategoryTheory.Skeletal`,
`CategoryTheory.IsSkeletonOf`, `CategoryTheory.Iso` and
`CategoryTheory.Functor.IsEquivalence` all depend on no axioms, so
`Skeletal FinSetSkel` is a statement in wholly choice-free vocabulary
sitting in the wrapper. Its obvious proof route is not choice-free:
`Fin.equiv_iff_eq`, `Fintype.card_congr` and `Fintype.card_fin` all
depend on `Classical.choice`, so a choice-free proof needs a
choice-free pigeonhole. W1 transports it from
`FintypeCat.Skeleton.is_skeletal` and does not attempt the direct
proof. A choice-free proof would change no check the repository runs —
`GebMeta.permittedAxioms` grants `Classical.choice` to every
declaration in an allowlisted module — so the work would have no
consequence W1 can state, which `CONTRIBUTING.md` § Code is cost
rules out. The
choice-free pigeonhole is recorded as a § Triggers entry instead.

Index files, per `CONTRIBUTING.md` § Repo structure's
one-indexing-file-per-directory rule: `Geb/Mathlib/Data/Vector.lean`,
`Geb/Mathlib/Data/List.lean` and
`Geb/Mathlib/CategoryTheory/FinSetSkel.lean` are new, and
`Geb/Mathlib/Data.lean` and `Geb/Mathlib/CategoryTheory.lean` gain
entries. `GebTests/` carries a parallel for every module and index
file above.

Neither module under `Geb/Mathlib/Data/Vector/` mirrors a mathlib
original, and no claim is made that either does: mathlib's
`Mathlib/Data/Vector/Basic.lean` is `List.Vector` throughout. Their
targets differ. `OfFn.lean` restates part of the root-`Vector` `ofFn`
and `get` APIs, which are Lean core's (`Init/Data/Vector/`) and
Batteries', so its target is core or Batteries rather than mathlib.
It sits under `Geb/Mathlib/` because
`docs/rules/upstream-eligible.md` § Subtree import rules restricts
`Geb/Mathlib/` modules to `Mathlib.*`, `Batteries.*` and
`Geb.Mathlib.*` imports, so a dependency of `FinSetSkel/Basic.lean`
cannot live in `Geb/Internal/`. That conflicts with `docs/index.md`
§ Directory structure, which states `Geb/Mathlib/` content is intended
for extraction to mathlib4; the amendment below corrects it, and a new
`TODO.md` item owns the destination question. The existing
§ Upstream placement of categorical wrappers item does not: it is
scoped by an explicit criterion — files under `Geb/Mathlib/Data/` that
directly import `Mathlib.CategoryTheory.*` or
`Geb.Mathlib.CategoryTheory.*` — which this module does not meet, and
its own text says the criterion was chosen so the item would not be
settled incompletely.

`Geb/Mathlib/Data/Vector/NodupEquivFin.lean` targets mathlib, not core
or Batteries: its statement is an `Equiv`, which exists in neither —
`Equiv` is `Mathlib/Logic/Equiv/Defs.lean`'s. It mirrors no existing
mathlib module, `Mathlib/Data/Vector/` having no `NodupEquivFin`, and
it sits beside `OfFn.lean` rather than beside the `List` rebuild
because it is root-`Vector` content and would not extract to
`Mathlib/Data/List/NodupEquivFin.lean`. The § Next up item's criterion
therefore does not reach it, and neither does the "Choice-free
`Array.ofFn` lemmas" trigger recorded in § Amendments.
`Geb/Mathlib/Data/List/NodupEquivFin.lean`, holding only the `List`
rebuild and the compression, does mirror its original.

`GebMeta.classicalAllowedModules` gains
`Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton` and its `GebTests`
parallel, and nothing else.

## Deliverables

- The object structure, carrying `@[ext]` — a bare `structure`
  generates no ext lemma — together with `DecidableEq`, `Inhabited`
  and `Repr`, per `docs/rules/lean-coding.md` § Structure and
  typeclass patterns. `FintypeCat.Skeleton` carries `Inhabited`.
- The `SmallCategory` instance at an arbitrary universe, with
  morphisms length-indexed vectors of codomain indices.
- The morphism API of § Decisions fixed here item 3: `Hom`, `ofVec`,
  `toVec` with both round trips `toVec_ofVec` and `ofVec_toVec`,
  `@[ext]` extensionality, the `@[simp]` identity and composition
  application lemmas fixing the normal form, and the `irreducible`
  attribute, in the declaration order § The comparison
  is closed by `Functor.hext` fixes.
- The three properties `TODO.md` requires of morphisms — that they be
  "pattern-matched, serialised, and compared" — each discharged
  through `toVec`, since the seal makes `Hom` itself opaque. Compared:
  `DecidableEq`, below. Serialised: `Repr`, which does not come free
  for the same reason `DecidableEq` does not, instance search not
  unfolding the `Hom` definition, and so is likewise a pinned term
  through `toVec`. Pattern-matched: on `f.toVec`, which is an ordinary
  `Vector`; the seal hides the `ULift`, not the vector. The amended
  W1 bullet records that reading, so that the roadmap's purpose
  sentence and the seal are not read as contradicting each other.
- `DecidableEq` on morphisms, as an explicit term through `hom_ext`
  and root `Vector`'s derived `DecidableEq`, not as `inferInstance`.
  It does not follow from the category instance: instance search does
  not unfold the `Hom` definition. Pinning it is not stylistic — the
  `instDecidableEqOfLawfulBEq` route inhabits the same class and is
  choice-tainted, so an unpinned instance could flip on a bump, and
  this is the declaration interface constraint 7 makes W1 responsible
  for on W3's and W4's behalf.
- `Vector.ofFnC`, `getElem_ofFnC`, `get_ofFnC` and `ofFnC_get`. The
  `C` suffix marks the choice-free rebuild and distinguishes it from
  core's `Vector.ofFn`, which it cannot be related to; `mathlib`'s
  naming guide has no form for "same statement, different axioms",
  the situation being unusual, so the suffix is stipulated here rather
  than derived. It is written into `TODO.md` by constraint 9, so a
  later rename would be a cross-workstream change; the destination
  item below is where a name a core reviewer prefers would be settled.
  The `get`-form lemmas are tagged `@[simp]`; `getElem_ofFnC` is not,
  the `getElem` form not being the normal one. `ofFnC_get` is a
  higher-order
  pattern (`ofFnC (fun i => v.get i) = v`), so its `simp` behaviour is
  confirmed by test rather than assumed; if it does not fire reliably
  it is left unmarked and applied by name.
- The `get`/`getElem` bridge of § Decisions fixed here item 4, stated
  by W1 because Batteries' is unreachable, `rfl`, and unmarked.
- The choice-free rebuild of `List.Nodup.getEquiv`; the predicate
  compression

  ```lean
  def compress {n : ℕ} (p : Fin n → Bool) :
      Fin ((List.finRange n).filter p).length ≃ {i : Fin n // p i}
  ```

  — `p` is `Bool`-valued, that being the only reading under which
  both `List.filter p` and the subtype elaborate — built with
  `List.nodup_finRange`, `List.mem_filter` and
  `Equiv.subtypeEquivRight`, together with `List.Nodup.filter`,
  `List.get_mem`, `List.get_idxOf` and `List.mem_finRange`, which the
  umbrella spec's three-lemma sketch omits; and a vector-level form
  `Fin k ≃ {j : Fin n // j ∈ ι.toList}` inverting an injective
  `ι : Vector (Fin n) k`, which is the shape the umbrella spec fixed
  and the shape W3's equalizer and W4's coequalizer consume. Its
  hypothesis is `Function.Injective ι.get`, stated over the `get` view
  fixed as normal form rather than over `ι.toList.Nodup`, together
  with the bridge between the two — `List.nodup_iff_injective_get`
  relates them, and W3's row m ("`Mono` is an injective vector") is a
  third consumer that will want the injectivity form. The
  vector-level form is included rather than left to its consumers
  because interface constraint 7 exists to keep shared material off a
  later branch that W3 and W4 would both rebase onto.
- `toIdxFun`, `ofIdxFun` and their two round trips.
- The comparison functors, the two composite identities, the
  isomorphism in `Cat` to `FintypeCat.Skeleton`, the equivalence
  defined as `Cat.equivOfIso` of it, the inclusion
  `FinSetSkel ⥤ FintypeCat` as the comparison composed with
  `FintypeCat.Skeleton.incl` — `IsSkeletonOf` is indexed by such a
  functor — and the transported `Skeletal` and `IsSkeletonOf`. Both
  are `Prop`, so neither raises a computability obligation. The
  transports go along the isomorphism, not the equivalence: an
  equivalence need not be injective on objects, so skeletality does
  not transport along one.
- `hom_ext_iff`, obtained rather than written: `@[ext]` generates the
  bidirectional companion for a hand-written theorem as well as for a
  structure, so W1 writes `@[ext]` plain and not the
  `@[ext (iff := false)]` form `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
  uses at lines 207 and 444. Suppressing it is why `TODO.md`
  § Triggers "Add `ext_iff` companions" lists `GrothendieckOp.hom_ext`,
  `CoGrothendieck.hom_ext` and `IR.ext` as lacking one; W1 adds no
  further entry to that list.
- A `docs/index.md` entry, and the `nLabSkeletalCategory` entry in
  `docs/references.bib`.
- A module docstring recording the morphism-representation choice
  together with the evidence against it — both halves of the
  `Mathlib/Data/Vector/Defs.lean` quotation and the comparison of
  § The representation decision, re-derived — so that a later reader
  has the evidence against the choice and not only the evidence for.

## Amendments to `TODO.md` and the documents stating subtree rules

Made on W1's branch, since each corrects or adds a statement binding a
later workstream, and `TODO.md` is what later workstreams read from
`main` once this document is deleted.

- **W0's precedence.** The W0 bullet's clause "W1 is shortened by it,
  root `Vector.get_ofFn` being Batteries' and unreachable from any
  `Mathlib.*` module. It therefore precedes W1" is removed: W1 cannot
  use that lemma. § Workstreams' opening "W0 precedes the rest" is
  narrowed to W4, § Standing obligations' "W0 precedes W1 (above)"
  bullet is removed, and the status table's W1 row loses its
  dependence on W0. The W0 bullet's remaining sentence is repunctuated,
  the removal otherwise leaving "W4 requires it, needing
  `Batteries.Data.UnionFind`;" ending in a dangling semicolon. W4's
  dependence is unaffected. W2 never had one.
- **The objects.** The preamble's "the same objects" is corrected: the
  objects correspond to ℕ as `FintypeCat.Skeleton`'s do, but the
  carriers differ, `FinSetSkel` being a one-field structure and
  `FintypeCat.Skeleton` being `ULift ℕ`. The reason is recorded, since
  W3, W4 and W5 all state constructions over `Fin X.len`.
- **Constraint 9, appended** — appended rather than inserted, so that
  the existing eight keep their numbers, which this document, the
  umbrella spec and the unwritten W2 to W5 specs all cite. It binds
  W3, W4 and W5, and § Cross-workstream interface constraints is where
  they read what binds them. Its content: constructions in choice-free
  modules use `Vector.ofFnC` and never `Vector.ofFn`, `Vector.range`
  or `Vector.finRange`, nor the `Array.toList_ofFn` /
  `List.toArray_ofFn` bridges. The definitions themselves depend on
  `propext` alone; what is banned with them is their lemmas. Those
  that fire automatically — `Vector.getElem_ofFn`,
  `Vector.getElem_range`, `Vector.getElem_finRange`,
  `Vector.ofFn_getElem`, `Array.getElem_ofFn` and the two `Array`
  bridges — are `@[simp]`, most also `@[grind =]`, and all depend on
  `Classical.choice`; so do the `ofFn` lemmas carrying no attribute at
  all. So a bare
  `simp` or `grind` meeting such a term introduces `Classical.choice`
  into a module required to be choice-free. It is not an elaboration
  error: it surfaces at `lake lint`, on the branch's own CI run and
  pre-push check. Batteries' `get`-form
  counterparts are equally tainted and are not in scope: no
  `Mathlib.*` module reaches `Batteries.Data.Vector.Lemmas`, and the
  bare umbrella `import Mathlib` that would is forbidden in
  upstream-eligible files by `scripts/lint-imports.sh`. W0 permits a
  direct `Batteries.` import, so this is a standing choice rather than
  an impossibility: a workstream that adds one admits the same family
  into the `get` normal form.

  The constraint states the general shape as well as the instances,
  since the instances are not a closed list: where two routes inhabit
  one class and only one is choice-free, a choice-free module names
  the term rather than leaving instance search to pick. Morphism
  `DecidableEq` is one such (W1 pins it). Deciding a proposition
  quantified over `Fin n` is another, and W3 and W4 both need it:
  `inferInstance` gives an axiom-free term, while
  `Fintype.decidableForallFintype`, which inhabits the same class,
  depends on `Classical.choice`.
- **The remaining decisions of § Decisions fixed here**, which bind
  W3, W4 and W5 and are currently recorded only in this transient
  document. The W1 bullet gains: the `ULift` placement settled
  (outside the vector), since constraint 4 says only that W1 settles
  it; the application-normal form `f.toVec.get i`, since the W1 bullet
  says only that W1 fixes the `simp` orientation; the seal
  `attribute [irreducible] FinSetSkel.Hom` together with its
  consequence, that no downstream construction may project the
  representation and all must route through `ofVec`, `toVec` and
  `ofIdxFun`; the vector-level injective-vector inversion with its
  hypothesis, which amended constraint 7 assigns to W1 but the
  deliverable list does not currently name; the exports of both
  modules under `Geb/Mathlib/Data/Vector/` by name, together with
  which of them
  carry `@[simp]`, since W3 and W4 build against that `simp` set; and
  that morphism `DecidableEq` and `Repr` are the pinned terms W1
  exports, not `inferInstance`.
- **The index equivalences.** The W1 bullet loses the
  `ULift`-transported forms. Constraint 4 becomes "W1 settles the
  `ULift` placement in the morphism type", its trailing ground —
  "every object carrier being `Fin`-shaped universe-zero data" — going
  with the clause it supported, since it was the reason for the
  transports and not for the placement. Constraint 7's *first*
  sentence becomes "`DecidableEq` on morphisms and the
  injective-vector inversion live in W1."; its second sentence, which
  sends a shared lemma discovered after W1 merges to its own branch
  off `main`, is retained verbatim — W1's own reasoning depends on
  that rule, and it binds W3 and W4 after this document is deleted.
  Constraint 7 gains a sentence recording that the
  choice-free replacements for `finProdFinEquiv` and
  `finFunctionFinEquiv` are deliberately W3-local, each having a
  single consumer in W3, so that the question is not re-opened. The
  operation table's rows d and g record the taint and W3's obligation;
  row c records that `finSumFinEquiv` is choice-free and usable as it
  stands.
- **The isomorphism's placement.** The W1 bullet's "the isomorphism in
  `Cat` to `FintypeCat.Skeleton` in the choice-free core" is
  corrected: `Cat.category` is choice-tainted, so the isomorphism is
  in the wrapper with the equivalence.
- **The representation paragraph** gains the corrected axiom
  comparison and the re-derived reasoning, not only the axiom finding,
  so that a later reader does not re-derive either.
- **The evidence pointer.** The paragraph directing a reader to
  recover the umbrella spec from `docs/finsetskel-topos-roadmap` gains
  W1's spec change-id alongside it, and a note that W1 corrects four
  of the umbrella's findings — the `Functor.ext` route, the
  choice-free `Cat` isomorphism, W0's shortening of W1, and the
  `ULift`-transport plan — and adds the index-equivalence taint that
  the operation table assumed away. Without it the roadmap directs
  re-verification at the superseded document.
- **Two § Triggers entries**, in the form that section uses, a bold
  name and a "when" condition:
  - **Choice-free `Array.ofFn` lemmas** — when an upstream submission
    touching root `Vector`'s `ofFn` API is prepared: give
    `Array.getElem_ofFn_go` (`Init/Data/Array/Lemmas.lean`) a
    choice-free proof in Lean core, from which `Array.getElem_ofFn`,
    `Array.toList_ofFn`, `List.toArray_ofFn`, `Vector.getElem_ofFn`,
    `Vector.ofFn_getElem`, `Vector.getElem_range` and
    `Vector.getElem_finRange` all follow, retiring `Vector.ofFnC` and
    its round trips. It does not retire the `get`/`getElem` bridge in
    the same module: core states no `Vector.get_eq_getElem`, and a
    repaired core lemma is still in `getElem` form. The bridge goes
    only if the direct `Batteries.Data.Vector.Lemmas` import is taken
    at the same time, which the repair would make safe by
    de-tainting Batteries' `get_ofFn` and `get_range`; that is a
    second decision, not a consequence of this one. This is a Lean
    core submission, not a mathlib one, and it does not reach
    `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`, whose statement is
    an `Equiv` and so has no core or Batteries home.
  - **Choice-free `Skeletal FinSetSkel`** — when a use for it arises
    outside an allowlisted module: prove it directly rather than
    transporting it, which needs a choice-free pigeonhole, mathlib's
    `Fin.equiv_iff_eq`, `Fintype.card_congr` and `Fintype.card_fin`
    all depending on `Classical.choice`. There is no such use while
    `Skeletal` is consumed only by the wrapper.
- **A § Next up item**: settle the upstream destination of
  `Geb/Mathlib/` content targeting Lean core or Batteries rather than
  mathlib, scoped by that criterion rather than by a module list.
- **Every place stating `Geb/Mathlib/`'s upstream target** is
  corrected, on W0's precedent of amending every place that states a
  rule together with the place that enforces it. Enumerated by grep
  over `*.md`, `*.lean` and `*.sh`, they are: `docs/index.md`
  § Directory structure; `Geb.lean`'s root docstring;
  `Geb/Mathlib.lean`'s docstring, both its heading and its body
  sentence; `README.md` § Upstream targets, which is in rule form;
  `docs/rules/upstream-eligible.md` § Two-track development step 1 and
  its rationale mirror `docs/process.md` § Two-track development, both
  of which present the target as a mathlib-or-CSLib binary;
  `docs/rules/upstream-eligible.md` § Subtree import rules and the
  matching comment header of `scripts/lint-imports.sh`, which justify
  admitting `Batteries.*` on the ground that a Batteries import
  "survives extraction to mathlib4" — true of a mathlib-targeted
  module and false of one targeted at Lean core, which
  `Geb/Mathlib/Data/Vector/OfFn.lean` may be, so each gains the
  scoping clause; and
  `scripts/extract-pr.sh`, which is the enforcer — its `Geb/Mathlib/*`
  arm maps unconditionally to `Mathlib/`, so a core-targeted module
  would extract to the wrong upstream silently. (`README.md`'s opening
  "shaped to be plausibly upstreamable to mathlib4" is left,
  describing the project's register rather than a subtree rule.
  `docs/rules/lean-coding.md` § Authoritative upstream guides is left
  too: it states which style guides bind `Geb/Mathlib/` content, not
  where that content goes, and holding a core-targeted module to
  mathlib's style conventions is a choice this group does not
  disturb.) The
  prose statements record that the subtree targets mathlib4 and that
  where the subtree import rules leave no alternative a module may
  instead target Lean core or Batteries, cross-referencing the § Next
  up item rather than presenting the destination as settled. The
  script gains a comment at its `Geb/Mathlib/*` arm and at its
  `GebTests/Mathlib/*` arm, which maps to `MathlibTest/` with the same
  silent-misextraction consequence for the test parallel W1 adds
  beside `OfFn.lean`; changing either mapping waits on the item's
  outcome.
- **`Geb/Mathlib.lean`'s import clause.** Its docstring says modules
  "import only from `Mathlib.*` or `Geb.Mathlib.*`", which W0 left
  stale when it admitted `Batteries.*` — W0's own bullet requires
  every place stating that rule to be amended, and this one was
  missed. The clause is not adjacent to the upstream-target claim but
  conjoined with it in one sentence, which W1 must rewrite anyway, so
  a separate branch would collide with W1's own edit. That, rather
  than the size of the change, is why `CONTRIBUTING.md` § Concern
  shape admits it here.
- **A § Standing obligations entry**, on the [Pare1974] precedent:
  verify a textbook locator for the skeleton of a category against the
  primary source before any Lean docstring cites one. The nLab page's
  reference list attests Mac Lane (1971) p. 91 and Riehl (2017) p. 34,
  but attestation by a secondary source is not verification. Without
  the entry the obligation would die with this document.
- The status table's W1 row is set to complete when the branch
  merges, its `Code` column gaining the module paths — the two under
  `Geb/Mathlib/Data/Vector/`, `Geb/Mathlib/Data/List/NodupEquivFin.lean`,
  and the two under `Geb/Mathlib/CategoryTheory/FinSetSkel/` — which
  is what that column is for.

## Out of scope

- A choice-free proof of `Array.getElem_ofFn_go`, and any repair of
  root `Vector`'s `ofFn` API beyond the declarations W1 requires.
- Choice-free replacements for `finProdFinEquiv` and
  `finFunctionFinEquiv`. These have one consumer each, both in W3, so
  interface constraint 7 does not place them in W1.
- The route to W3's row m. The umbrella spec proposes
  `SimplexCategory.mono_iff_injective`'s, through
  `Functor.mono_map_iff_mono` and a faithful functor to a concrete
  category. Taken through W1's `incl`, which is in the wrapper, that
  route would put row m in W3's wrapper rather than its choice-free
  core. W1 records the alternative for W3 — characterising `Mono`
  directly over vectors, using the injective-vector inversion W1
  supplies — and leaves the choice to W3, whose spec weighs it.
- `Geb/Mathlib/Data/FinEnum.lean`. The umbrella spec anticipated W1
  adding to it; on the design above W1 has no occasion to, the
  predicate compression being built from `List.finRange` and
  `List.filter`. Should a need appear, W1 adds without changing
  existing signatures: that module has four importers in `Geb/` plus a
  test module, and restructuring it is a separate concern on a branch
  both W3 and W4 would depend on.
- A `FunLike` instance or a `ConcreteCategory` structure on
  `FinSetSkel`. Neither is required by any row of the operation table.
- Every row of the operation table: those are W3, W4 and W5.

## Verification obligations

- `#print axioms` on each declaration of the four choice-free
  modules, confirming `propext` and `Quot.sound` only, and on the
  exported morphism `DecidableEq` specifically, whose alternative
  resolution route is tainted. `lake lint` enforces the general rule
  through `GebMeta.detectNonstandardAxiom`, and the two allowlist
  entries confine the exception to the wrapper.
- That no W1 declaration carries the `noncomputable` modifier, which
  is what `CONTRIBUTING.md` § Constructive-only forbids.
  Reachability is not the criterion and could not be: the transported
  `IsSkeletonOf` takes an `IsEquivalence` field that mathlib fills
  from a `noncomputable instance`. Both are `Prop`, so nothing is
  extracted. `FintypeCat.Skeleton.incl` and `Cat.equivOfIso`, which W1
  uses in data positions, are computable;
  `FintypeCat.Skeleton.equivalence` is not, and W1 does not use it.
- `scripts/lint-imports.sh`, which W1 exercises more than most
  branches: it creates the first `Geb/Mathlib/Data/Vector/` and
  `Geb/Mathlib/Data/List/` directories, and because the lint forbids
  the `Geb.Mathlib.` self-prefix outside import lines, which module
  docstrings naming this workstream's own modules could otherwise
  introduce.
- Re-verification of the axiom findings of § Findings if the weekly
  mathlib or toolchain bump lands during the branch, and of the
  `get` API's continued existence. `Vector.get` is a plausible
  deprecation target on its thinness alone — two stated theorems
  against 74 in `getElem` form — rather than on any core statement of
  intent. The remark this document paraphrases as a deficiency —
  that `List.Vector` "does not use `x[i]` … as the preferred
  accessor" — is mathlib's, in `Mathlib/Data/Vector/Defs.lean`, and
  concerns `List.Vector`. The
  normal form of § Decisions fixed here item 4 rests on `Vector.get`,
  and neither it nor `List.get` is deprecated at the pins. A core
  repair of `Array.getElem_ofFn_go`, or a rename in the `ofFn` family,
  would leave `Vector.ofFnC` and its round trips duplicating core; the
  `get`/`getElem` bridge in the same module would survive either, for
  the reason the corresponding § Triggers entry gives.
- `scripts/pre-push.sh`, per `CONTRIBUTING.md` § Working.

Axiom and computability checks run through the `lean-lsp` MCP, per
`docs/rules/lean-coding.md`; `lake env lean` is not used.

## References

- `TODO.md` § FinSetSkel as an elementary topos — the group's
  authoritative roadmap.
- The group's umbrella spec, added and removed on branch
  `docs/finsetskel-topos-roadmap` (`jj` change
  `nkwoqxwytsvrlpnsklzzlzkxtovyxkzm`), for the evidence behind the
  findings this document confirms or amends.
- `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean` — the
  morphism-API template of § Decisions fixed here item 3.
- `Mathlib/CategoryTheory/FintypeCat.lean` — `FintypeCat.Skeleton`,
  `Skeleton.incl`, `Skeleton.is_skeletal`, `FintypeCat.isSkeleton`.
- [nLabSkeletalCategory] — skeletal categories and the skeleton of a
  category.
