# Finite-category specifications

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Scope](#scope)
- [Transcription status of the definitions](#transcription-status-of-the-definitions)
- [Encoding of the morphisms](#encoding-of-the-morphisms)
- [Encoding of the identities](#encoding-of-the-identities)
- [The specification type](#the-specification-type)
- [The checkers and their reflection lemmas](#the-checkers-and-their-reflection-lemmas)
- [The generated mathlib category](#the-generated-mathlib-category)
- [Functor and 2-cell specifications](#functor-and-2-cell-specifications)
- [The strict 2-category of specifications](#the-strict-2-category-of-specifications)
  - [In `Hom.lean`](#in-homlean)
  - [In `Hom2.lean`](#in-hom2lean)
  - [In `Bicategory.lean`](#in-bicategorylean)
  - [Why ten axioms are proved rather than defaulted](#why-ten-axioms-are-proved-rather-than-defaulted)
  - [Why not `CatEnriched`](#why-not-catenriched)
- [Decidable equality and `Repr`](#decidable-equality-and-repr)
- [Axiom hygiene](#axiom-hygiene)
- [File layout](#file-layout)
- [Verification obligations](#verification-obligations)
- [Testing](#testing)
- [Persistent documentation](#persistent-documentation)
- [Deferred work](#deferred-work)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Purpose

A constructive interface by which a client fully specifies a finite
category — finitely many objects, finitely many morphisms in each
hom-set — supplies a `rfl`-dischargeable proof that the category laws
hold, and obtains a mathlib `Category` whose objects and morphisms sit
at arbitrary and independent universe levels. The same interface
extends to functors and natural transformations between such
categories, and the specifications themselves carry the structure of a
strict 2-category.

The design criterion, in order of precedence: what a client writes is
minimal and unambiguous; the category laws are discharged by
computation rather than by hand; `Classical.choice` is confined to
modules that package results rather than prove them.

## Scope

In scope:

1. The specification type, its decidable associativity checker, and the
   generated `Category` instance, together with a `FinCategory`
   instance in the case where the object and morphism levels coincide.
2. Functor and natural-transformation specifications, their decidable
   law checkers, the generated `Functor` and `NatTrans`, and the
   `Bicategory` and `Bicategory.Strict` instances on specifications
   from which a `Category` instance on them follows.
3. `DecidableEq` and `Repr` on specifications, functor specifications
   and 2-cell specifications.

Items 2 and 3 are in scope on the strength of a near-term consumer
outside this workstream, recorded as a `TODO.md` entry on this branch.
Absent that entry, CONTRIBUTING § Code is cost
would put both with the deferred work below, the comparison with `Cat`
being the only consumer visible from the source tree, and that
comparison being itself deferred.

Out of scope, recorded under [Deferred work](#deferred-work): the
finiteness object property on `Cat` and the comparison between the
specifications and the corresponding full subcategory.

Also out of scope: notation for writing a specification's fields as
table literals. A client writes `nonIdCount` and `comp` as functions.
Notation is deferred until a client reports friction with that.

## Transcription status of the definitions

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing. Section numbers below were checked against the
arXiv LaTeX source of [JohnsonYau2021] (2002.06055,
`2categories_book.tex`).

- Category, functor, natural transformation: transcription, from
  [JohnsonYau2021] § 1.1, "Basic Category Theory".
- Bicategory, 2-category, and the 2-category `Cat`:
  transcription, from [JohnsonYau2021] § 2.1, "Bicategories", and
  § 2.3, "2-Categories", whose Definition 2.3.1 is the notion
  mathlib calls strict. The book does not use the phrase "strict
  bicategory"; mathlib's rendering is
  `CategoryTheory.Bicategory`, `CategoryTheory.Bicategory.Strict` and
  `CategoryTheory.Cat.bicategory`.
- The encoding below — the hom-count matrix, the reserved identity
  index, the checkers and their reflection lemmas — is novel. It is a
  presentation of the transcribed notions, not a new mathematical
  concept.

CONTRIBUTING's marking applies to definitions, and the two
transcription bullets
and the encoding bullet account for every declaration this
workstream introduces. No
declaration defines "finite category" as a named notion: the phrase
occurs only in prose describing what the encoding presents, and
finiteness enters the Lean text as `Fin`-indexing plus, at the diagonal
level, mathlib's own `CategoryTheory.FinCategory`. So there is no
third, unmarked definition. Worth recording because it is checkable:
[JohnsonYau2021] has no notion of a finite category — the source
contains no occurrence of the phrase, its size predicates being small,
essentially small and locally small — so citing it for one would be
wrong.

## Encoding of the morphisms

The objects are indexed by `Fin objCount` for `objCount : Nat`. Write
`c` for the client-supplied count of non-identity morphisms and `c'`
for the total count defined from it in the next section. Two encodings
of the morphisms were considered.

1. A hom-count matrix `c : Fin objCount → Fin objCount → Nat`.
2. A total morphism count `Nat` together with domain and codomain
   projections into `Fin objCount`, which presents a finite category as
   a category internal to finite sets.

Encoding 1 is adopted. Under it, composition has type

```lean
(i j k : Fin objCount) → Fin (c i j) → Fin (c j k) → Fin (c' i k)
```

and is total: the indexing makes well-typedness a typing obligation
rather than a proof obligation. Under encoding 2 composition is partial
— defined only where the codomain of one argument equals the domain of
the other — and the client and the checker additionally carry
`dom (g ∘ f) = dom f` and `cod (g ∘ f) = cod g`. Encoding 1 removes both
families of side condition. The internal-category presentation remains
derivable afterwards by summing the matrix over its indices, so nothing
is lost by not adopting it as the primitive.

## Encoding of the identities

The client supplies the count of **non-identity** morphisms. The
identity is inserted by this development, at the index one past the
client's range in each endo-hom:

```lean
def FinCat.homCountOf (objCount : Nat) (nonIdCount) (i j : Fin objCount) : Nat :=
  nonIdCount i j + if i = j then 1 else 0
```

with `FinCat.homCount S` the wrapper applying it to `S`'s own fields,
per [The specification type](#the-specification-type). The embedding of
a client morphism into the full hom type is therefore index-preserving
on and off the diagonal, and `𝟙 i` has index `S.nonIdCount i i`.

The alternative of reserving index `0` for the identity was rejected.
Under it the embedding is `Fin.succ` on the diagonal and the identity
map off it, so the client's numbering and this development's numbering
agree at some index pairs and disagree at others; a client's
composition function takes arguments in one numbering and returns a
result in the other. The alternative of requiring the client to include
the identities in their own counts was also rejected: it requires the
client to write the identity rows and columns of the composition table,
whose entries are determined by the identity laws.

The total composition dispatches on whether each argument is an
identity, which involves the equation `i = j` between objects. That
equation is used **only inside a `Prop`**: each branch in which it
arises returns `⟨x.val, proof⟩`, so the value component is a `Nat`
carried across with no `Eq.rec` and only the bound is transported. This
is core's own idiom for `Fin.castLE`. Consequently there is no
transport in the computational content, no named transport API is
required, and no `attribute [irreducible]` seal is applied — a seal
would in any case defeat the `rfl` discharge that the design rests on,
`irreducible` blocking the elaborator's definitional unfolding.

## The specification type

```lean
structure FinCat where
  objCount : Nat
  nonIdCount : Fin objCount → Fin objCount → Nat
  comp : (i j k : Fin objCount) →
    Fin (nonIdCount i j) → Fin (nonIdCount j k) →
      Fin (FinCat.homCountOf objCount nonIdCount i k)
  assoc : FinCat.assocCheckOf objCount nonIdCount comp = true
```

with the derived notions

```lean
abbrev FinCat.Mor (S : FinCat) (i j : Fin S.objCount) : Type :=
  Fin (S.homCount i j)

def FinCat.emb {S : FinCat} {i j : Fin S.objCount} :
    Fin (S.nonIdCount i j) → S.Mor i j :=
  Fin.castLE (Nat.le_add_right _ _)

protected def FinCat.id (S : FinCat) (i : Fin S.objCount) : S.Mor i i :=
  ⟨S.nonIdCount i i, by simp [FinCat.homCount]⟩
```

`FinCat.id` is `protected`: inside `namespace FinCat` an unqualified
`id` would otherwise shadow core's, as
`Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` records for its own
`protected def id`, whose body has to write `_root_.id`.

`FinCat` is marked `@[ext]`, per `docs/rules/lean-coding.md` §
Structure and typeclass patterns; its derived lemma is heterogeneous for
the same reason `FinCat.Hom`'s is, `nonIdCount`'s type mentioning
`objCount`. `FinCat.Obj` is a one-field structure and takes the derived
homogeneous lemma. `Inhabited FinCat` is derived, witnessed by the
specification with no objects; `Inhabited (FinCat.Hom S T)` is not
derivable at variable `S` and `T` and is not provided.

`Mor` is an `abbrev`, not a `def`. Instance search does not unfold a
plain `def`, so `DecidableEq (S.Mor i j)` would not be found and the
checkers below — whose `decide` bodies are equalities at `Mor` — would
not elaborate. An `abbrev` inherits `Fin`'s `DecidableEq` and
`Repr`, both axiom-free. It also inherits `Fin.fintype`, which is not.
A `Fintype` on a hom type has exactly one consumer in scope,
`FinCat.Obj.finCategory`, whose `fintypeHom` field routes to it through
`ULift.fintype`; that is why the module holding that instance is
allowlisted, and § Axiom hygiene records that no choice of witness
avoids it. The checkers do not use it, resolving through
`Nat.decidableForallFin`.

and the total composition
`FinCat.compTotal : S.Mor i j → S.Mor j k → S.Mor i k`, defined by

```lean
if hf : f.val < S.nonIdCount i j then
  if hg : g.val < S.nonIdCount j k then S.comp i j k ⟨f.val, hf⟩ ⟨g.val, hg⟩
  else ⟨f.val, _⟩          -- g is the reserved identity, so j = k
else ⟨g.val, _⟩            -- f is the reserved identity, so i = j
```

The two elided proofs both reduce to one arithmetic fact, which is the
single reusable ingredient of the module and is stated once:

```lean
theorem FinCat.eq_of_nonIdCount_le (S : FinCat) {i j : Fin S.objCount}
    (x : S.Mor i j) (h : S.nonIdCount i j ≤ x.val) : i = j
theorem FinCat.val_eq_of_nonIdCount_le (S : FinCat) {i j : Fin S.objCount}
    (x : S.Mor i j) (h : S.nonIdCount i j ≤ x.val) :
    x.val = S.nonIdCount j j
```

Hypotheses are stated as `≤` rather than `¬ <`, mathlib preferring the
former, and the names relate the terms they mention rather than
interpreting them. An index outside the client's range can only exist
on the diagonal, because off it the `if` in `homCount` contributes `0`.
`eq_of_nonIdCount_le` discharges both elided bounds;
`val_eq_of_nonIdCount_le` is what `comp_id` and the associativity
reduction need, and its `j j` indexing is the usable one — in
`comp_id (f : S.Mor i j)` the outer `else` returns `⟨(S.id j).val, _⟩`,
so closing it against `f` requires exactly `f.val = S.nonIdCount j j`.
When both arguments are identities the outermost `else` fires and
returns the identity, which is correct.

Field types cannot mention the structure being defined, so everything
the `comp` and `assoc` field types mention precedes `FinCat` and takes
`objCount`, `nonIdCount` and `comp` as explicit arguments:
`homCountOf`, `embOf`, `compTotalOf`, `assocCheckOf`, and unbundled
forms of the two arithmetic lemmas below, which discharge
`compTotalOf`'s elided bounds where no `S : FinCat` exists.
`FinCat.emb`, `FinCat.compTotal`, `FinCat.assocCheck`,
`FinCat.eq_of_nonIdCount_le` and `FinCat.val_eq_of_nonIdCount_le` are
one-line bundled wrappers over them. These references are written
qualified inside the structure's own field types, where
`docs/rules/lean-coding.md` § Naming conventions' "rely on `namespace`
to scope" is unavailable: no `namespace FinCat` can be open while
`FinCat` is being defined. The same applies one
level up, to `FinCat.Hom`: its `compValid` field type needs unbundled
`mapTotalOf` and `compCheckOf` over `objMap` and `map`. The bundled
`FinCat.homCount`, `FinCat.emb`, `FinCat.compTotal` and
`FinCat.Hom.mapTotal` shown in this document are the wrappers applying
them to a given `S` or `F`, and are what every later module uses.
`FinCat.Mor` and `FinCat.id` are defined directly on `S` and have no
unbundled form: the `comp` field type writes `Fin (FinCat.homCountOf …)`
inline rather than through a `Mor`, and no unbundled definition needs an
identity. Bundled `FinCat.assocCheck`,
`FinCat.Hom.compCheck` and `FinCat.Hom₂.natCheck` are among them, so
that the reflection lemmas below and all prose outside this section
name declarations that exist.

The client writes `objCount`, `nonIdCount` and `comp`, and discharges
`assoc`. The client designates no identities, states no identity laws,
and supplies no domain or codomain data. The composition a client
writes returns a value in the **full** hom type, because a composite of
two non-identity morphisms may be an identity.

The specification type carries no universe parameters. Its content
lives at `Type 0`; universe levels enter only at the boundary described
under [The generated mathlib category](#the-generated-mathlib-category).

## The checkers and their reflection lemmas

The identity laws are not checked. They are proved here, once, at
variable indices:

```lean
theorem FinCat.id_comp (S) (i k) (g : S.Mor i k) :
    S.compTotal (S.id i) g = g
theorem FinCat.comp_id (S) (i j) (f : S.Mor i j) :
    S.compTotal f (S.id j) = f
```

Neither is `rfl`. The dispatch in `compTotal` is a `dite` on
`f.val < S.nonIdCount i j`, a `Nat.decLt` at two variable naturals,
which does not reduce; `comp_id` additionally needs
`val_eq_of_nonIdCount_le`. Both are ordinary proofs, and the implementation
budgets for them rather than describing the laws as definitional.

Associativity is checked, and only on triples of client morphisms:

```lean
def FinCat.assocCheckOf … : Bool :=
  decide <| ∀ (i j k l : Fin objCount)
    (f : Fin (nonIdCount i j)) (g : Fin (nonIdCount j k))
    (h : Fin (nonIdCount k l)),
      cTot (cTot (embOf f) (embOf g)) (embOf h)
        = cTot (embOf f) (cTot (embOf g) (embOf h))
```

where `cTot` abbreviates `FinCat.compTotalOf` and `embOf` is
`FinCat.embOf`; both live in the `FinCat` namespace and are written
qualified in the source, the elision here being for width only. The
composition appearing in the statement is the total one, so a composite
landing on the reserved identity index is covered.
Associativity of the total composition on all triples is

```lean
theorem FinCat.compTotal_assoc (S : FinCat) {i j k l : Fin S.objCount}
    (f : S.Mor i j) (g : S.Mor j k) (h : S.Mor k l) :
    S.compTotal (S.compTotal f g) h = S.compTotal f (S.compTotal g h)
```

proved from `assocCheck_eq_true_iff` by cases on which arguments are
identities, using `eq_of_nonIdCount_le` to substitute the index equation
before an identity can be named, then `val_eq_of_nonIdCount_le`,
`id_comp` and `comp_id`. It
is named because three later constructions consume it and none can
reach the checker directly, every one of them quantifying over full hom
types: the `assoc` fields of `FinCat.Obj.category` and of
`FinCat.Hom.instCategory`, and the `natValid` field of the vertical
composite of 2-cells, which interleaves two naturality squares and so
uses it three times.

The `Decidable` instance is to be left to Lean's default resolution,
which reaches core's `Nat.decidableForallFin`. Neither
`Fintype.decidableForallFintype` nor the repository's
`FinEnum.decidableForallFinEnum` is to be used: the former depends on
`Classical.choice` directly, and the latter requires `FinEnum (Fin n)`,
whose only instance `FinEnum.fin` is choice-dependent. See
[Axiom hygiene](#axiom-hygiene).

The validity field is a `Bool` equation, so a client with a concrete
category discharges it with `rfl`.

The functor and naturality checkers are stated in the same form, over
the *total* composition and the *total* morphism map, for the same
reason — a client composite may land on the reserved index, on which
the partial map is undefined:

```lean
def FinCat.Hom.compCheckOf (S T : FinCat) (objMap) (map) : Bool :=
  decide <| ∀ (i j k : Fin S.objCount)
    (f : Fin (S.nonIdCount i j)) (g : Fin (S.nonIdCount j k)),
      mapTotalOf (S.compTotal (S.emb f) (S.emb g))
        = T.compTotal (mapTotalOf (S.emb f)) (mapTotalOf (S.emb g))

def FinCat.Hom₂.natCheckOf (S T : FinCat) (F G) (app) : Bool :=
  decide <| ∀ (i j : Fin S.objCount) (f : Fin (S.nonIdCount i j)),
    T.compTotal (F.mapTotal (S.emb f)) (app j)
      = T.compTotal (app i) (G.mapTotal (S.emb f))
```

Each checker is accompanied by a reflection lemma
(`assocCheck_eq_true_iff`, `compCheck_eq_true_iff`,
`natCheck_eq_true_iff`) relating it to the corresponding `Prop`. They
are stated over the **unbundled** arguments, not the bundled wrappers:
their consumers discharge validity fields of structures under
construction, where no bundled `F.compCheck` yet exists. These
are required by the constructions of
[the strict 2-category](#the-strict-2-category-of-specifications), not
merely convenient. Vertical composition of 2-cells must produce a valid
2-cell, and its validity field cannot be discharged by the `decide`
tactic, because the source and target specifications are variables.
Each such construction proves the law at the `Prop` level from its
hypotheses and converts back through the reflection lemma.

## The generated mathlib category

```lean
structure FinCat.Obj.{u} (S : FinCat) : Type u where
  idx : ULift.{u} (Fin S.objCount)

instance FinCat.Obj.category.{v, u} (S : FinCat) :
    Category.{v} (FinCat.Obj.{u} S) where
  Hom X Y := ULift.{v} (S.Mor X.idx.down Y.idx.down)
  …
```

The objects are a one-field structure rather than `ULift (Fin _)`
directly, for the reason
`Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` records for its own
objects — a structure projection reduces by iota, which is available at
reducible transparency — and because a `Category` instance on
`ULift (Fin _)` would be a global instance on a type this development
does not own.

The instance is written out rather than obtained by stacking
`CategoryTheory.ULiftHom` on `CategoryTheory.uliftCategory`. mathlib's
`ULiftHom.category` yields `Category.{max v₂ v₁}`; it reaches
independent levels here only because the underlying category sits at
`Category.{0}` on `Type 0`. Going through it requires
`attribute [local instance] uliftCategory` and two layers of `ULift`
unwrapping in every proof, for a result the direct instance states
in one.

`FinCat.Obj` and the generated hom types carry `DecidableEq` instances,
derived from `Fin` and `ULift`. A category whose purpose is that its
laws are decidable is of limited use if its objects and morphisms are
not comparable, and mathlib's `FinCategory` dropped its own
`DecidableEq` requirements, so the instances have to originate here.

Where the object and morphism levels coincide the category is small,
and

```lean
instance FinCat.Obj.finCategory.{u} (S : FinCat) :
    FinCategory (FinCat.Obj.{u} S)
```

applies. `CategoryTheory.FinCategory` requires `SmallCategory`, so no
such instance exists at independent levels; this is the reason the
finiteness carried by a specification is not expressible through that
class in general. mathlib's universe-polymorphic analogue,
`CategoryTheory.CountableCategory`, is a `Prop` class over
`Category*` with `countableObj` and `countableHom` fields; no
corresponding finite class exists upstream.

This instance is unavoidably choice-dependent and gets a module of its
own. See [Axiom hygiene](#axiom-hygiene).

## Functor and 2-cell specifications

```lean
structure FinCat.Hom (S T : FinCat) where
  objMap : Fin S.objCount → Fin T.objCount
  map : (i j : Fin S.objCount) →
    Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j)
  compValid : FinCat.Hom.compCheckOf S T objMap map = true

structure FinCat.Hom₂ {S T : FinCat} (F G : FinCat.Hom S T) where
  app : (i : Fin S.objCount) → T.Mor (F.objMap i) (G.objMap i)
  natValid : FinCat.Hom₂.natCheckOf S T F G app = true
```

The 2-cell structure is `FinCat.Hom₂` rather than `FinCat.Hom.Hom`,
following `CategoryTheory.Cat.Hom₂`
(`Mathlib/CategoryTheory/Category/Cat.lean:111`) and avoiding a
name that collides visually with dot notation on a `FinCat.Hom` value.
`FinCat.Hom` is named for its position — the 1-cells of a 2-category —
not for its shape: unlike `Cat.Hom` it is not a one-field bundling.

`map` is given on client morphisms and lands in the target's full hom
type, since a functor may send a non-identity morphism to an identity;
every functor into the terminal category does. It extends to `mapTotal`
by sending `S.id i` to `T.id (F.objMap i)`, so preservation of
identities holds by construction and only the composition law is
checked. Defined by dispatch at variable `i` and `j`, the extension
carries the object equation only inside a `Prop`, exactly as
[Encoding of the identities](#encoding-of-the-identities) describes for
`compTotal`: the identity branch must inhabit
`T.Mor (F.objMap i) (F.objMap j)`, whose bound needs `i = j`.

`app` ranges over the full hom type from the outset, the identity
2-cell having every component an identity.

The generated mathlib data are

```lean
def FinCat.Hom.toFunctor.{v, u} {S T : FinCat} (F : FinCat.Hom S T) :
    @Functor (FinCat.Obj.{u} S) (FinCat.Obj.category.{v, u} S)
             (FinCat.Obj.{u} T) (FinCat.Obj.category.{v, u} T)

def FinCat.Hom₂.toNatTrans.{v, u} {S T : FinCat}
    {F G : FinCat.Hom S T} (α : FinCat.Hom₂ F G) :
    F.toFunctor.{v, u} ⟶ G.toFunctor.{v, u}
```

`toFunctor`'s type is written with explicit instance arguments rather
than through `⥤`, so that `v` appears in the type and is not left to be
inferred from a hidden instance argument.

## The strict 2-category of specifications

Presented by module, since the construction spans three and the
dependency order follows the module order rather than a single list.

### In `Hom.lean`

Ordered so that each item's dependencies precede it. Items 2 to 4 are
statements about an arbitrary `F : FinCat.Hom S T`, and item 5 about
`mapTotalOf` applied to given data; all are therefore statable before
`FinCat.Hom.id` and `FinCat.Hom.comp` exist.

1. `@[ext]` on `FinCat.Hom`. Because `map`'s type mentions `objMap`,
   Lean's derived lemma is heterogeneous — `objMap` equality plus `HEq`
   of `map` — and is derived automatically; it is axiom-free. If a
   pointwise form is wanted later it is a separate lemma.
2. `FinCat.Hom.mapTotal_emb : F.mapTotal (S.emb f) = F.map i j f`. Not
   `rfl`: `mapTotal` dispatches on a `Nat.decLt` at variable naturals,
   the same obstruction
   [The checkers](#the-checkers-and-their-reflection-lemmas) records for
   `compTotal`. It is what reduces `FinCat.Hom.id_comp` below.
3. `FinCat.Hom.mapTotal_id : F.mapTotal (S.id i) = T.id (F.objMap i)`.
4. `FinCat.Hom.mapTotal_compTotal` — functoriality of `mapTotal` at
   **total** morphisms, extending `compCheck` off the client range. It
   comes before `FinCat.Hom.comp` because that definition needs it:
   discharging the composite's validity field reduces to
   `mapTotal_compTotal` for the outer 1-cell at two morphisms of the
   form `F.mapTotal (S.emb _)`, which need not lie in `T.emb`'s image,
   `F` being free to send a client morphism to an identity. The inner
   1-cell's own `compCheck` cannot reach them.
5. `FinCat.Hom.id_mapTotalOf` and `FinCat.Hom.comp_mapTotalOf`, the
   unbundled forms of item 7's two lemmas — that `mapTotalOf` at the
   identity's data is the identity, and that `mapTotalOf` at a
   composite's data factors as the outer applied to the inner. Both
   precede item 6 because item 6's two definitions consume them, and
   `comp_mapTotalOf`'s own proof consumes item 3.
6. `FinCat.Hom.id` and `FinCat.Hom.comp` as operations. `id`'s validity
   field discharges from `compCheck_eq_true_iff`, `id_mapTotalOf` and
   `val_eq_of_nonIdCount_le` — not from item 4, which is a statement
   about an existing `Hom S T` and so is unavailable here. `comp`'s
   discharges from `compCheck_eq_true_iff`, `comp_mapTotalOf` and then
   item 4 at each of the two 1-cells.
7. `FinCat.Hom.id_mapTotal` and `FinCat.Hom.comp_mapTotal`, the bundled
   forms of item 5's two lemmas.
8. The three strict equalities `FinCat.Hom.id_comp`,
   `FinCat.Hom.comp_id` and `FinCat.Hom.assoc`, written with
   `FinCat.Hom.comp` and `FinCat.Hom.id` rather than `≫` and `𝟙`: no
   `CategoryStruct FinCat` exists until `Bicategory.lean`. The
   `Bool`-equation fields contribute nothing, being proof-irrelevant.
   `id_comp` reduces to `mapTotal_emb`, `comp_id` to `id_mapTotal`, and
   `assoc` to `comp_mapTotal`.
9. `FinCat.Hom.toFunctor`, last because its `map_id` and `map_comp`
   fields are `mapTotal_id` and `mapTotal_compTotal`, items 3 and 4.

### In `Hom2.lean`

1. `FinCat.Hom.instCategory : Category (FinCat.Hom S T)` — vertical
   composition of 2-cells and the identity 2-cell — with
   `FinCat.Hom₂.app_id` and `FinCat.Hom₂.app_comp`. It comes first
   because it is the only source of `⟶` at the 2-cell level, on which
   items 2 and 4 depend. mathlib orders the same three the same way:
   `Cat.Hom.instQuiver` (`Cat.lean:118`), `Cat.Hom.instCategory`
   (`:127`), `Cat.Hom₂.ext` (`:154`).
2. A hand-written `@[ext]` lemma for `FinCat.Hom₂` phrased at
   `F ⟶ G`. The structure-derived one does not fire on goals stated
   through the hom notation, and mathlib writes the corresponding
   lemma by hand for the same reason (`Cat.Hom₂.ext`,
   `Cat.lean:153-155`).
3. `FinCat.Hom₂.natCheck_total` — naturality at **total** morphisms,
   extending `natCheck` off the client range. `whisker_exchange` is
   exactly this at `η.app i`, which ranges over the full hom type,
   so no default can supply it.
4. `FinCat.Hom₂.toNatTrans`.

### In `Bicategory.lean`

1. `FinCat.Hom₂.whiskerLeft` and `FinCat.Hom₂.whiskerRight` as
   standalone definitions, their result types written with `⟶` at the
   2-cell level and `FinCat.Hom.comp` for the 1-cell composite —
   `F.comp G ⟶ F.comp H` — following the convention of
   § In `Hom.lean` item 8. Writing them `F ≫ G ⟶ F ≫ H` does not
   elaborate: `≫` needs `CategoryStruct FinCat`, which item 4 below is
   the first to provide. Writing them `FinCat.Hom₂ _ _` elaborates but
   makes every later statement mentioning a whiskering need an
   `@`-ascription to unify against `_ ⟶ _`; written as above, none
   does. `whiskerLeft` is pure reindexing —
   `(F ◁ η).app i = η.app (F.objMap i)`; `whiskerRight` applies
   `mapTotal` — `(η ▷ H).app i = H.mapTotal (η.app i)`. That asymmetry
   decides the partition below.
2. `FinCat.Hom₂.eqToHom_app`. It cannot be stated in the form
   `(eqToHom p).app i = T.id (F.objMap i)`: `app`'s type mentions both
   `F.objMap` and `G.objMap`, so the two sides have different types.
   It is stated in `Fin.cast` form,

   ```lean
   theorem FinCat.Hom₂.eqToHom_app {F G : FinCat.Hom S T} (p : F = G) (i) :
       (eqToHom p : F ⟶ G).app i
         = Fin.cast (congrArg (fun H => T.homCount (F.objMap i) (H.objMap i)) p)
             (T.id (F.objMap i)) := by cases p; rfl
   ```

   The `cases` is available here, `p` being a hypothesis over variable
   `F` and `G`; it is *not* available inside the instance, `F`
   occurring on both sides of `FinCat.Hom.id _ |>.comp F = F`.
3. **Ten** coherence theorems — `id_whiskerLeft`, `comp_whiskerLeft`,
   `id_whiskerRight`, `comp_whiskerRight`, `whiskerRight_id`,
   `whiskerRight_comp`, `whisker_assoc`, `whisker_exchange`,
   `pentagon`, `triangle` — stated against `FinCat.Hom.instCategory`.

   Every proof stays at the `app` level. `FinCat.Hom₂`'s `@[ext]`
   lemma together with `funext` stops there; plain `ext` must be
   avoided, because `FinCat.Mor` is reducible and the `@[ext]` chain
   then descends through `Fin.ext` to `Fin.val`, at which point
   `natCheck_total` is out of rewriting range. No `Fin.val`-level lemma
   is needed: 1-cell composition is definitionally unital and
   associative on `objMap`, so the `Fin.cast` that `eqToHom_app`
   introduces is definitionally the identity at `Mor`, and
   `FinCat.id_comp` and `FinCat.comp_id` from
   [The checkers](#the-checkers-and-their-reflection-lemmas) close what
   remains.

   The inventory each consumes, beyond `eqToHom_app`, `app_id`,
   `app_comp`, `FinCat.id_comp` and `FinCat.comp_id`:
   `id_whiskerRight` and `pentagon` and `triangle` need `mapTotal_id`;
   `comp_whiskerRight` needs `mapTotal_compTotal`; `whiskerRight_id`
   needs `id_mapTotal`; `whiskerRight_comp` needs `comp_mapTotal`;
   `whisker_exchange` needs `natCheck_total`. `id_whiskerLeft`,
   `comp_whiskerLeft` and `whisker_assoc` need nothing further.
4. `FinCat.bicategory : Bicategory FinCat`: `id`, `comp`,
   `homCategory`, `whiskerLeft`, `whiskerRight`, the associator and
   unitors, and the ten fields above cited explicitly. Only
   `whiskerLeft_id` and `whiskerLeft_comp` are left to their defaults;
   both sides of each are definitionally equal, and both close by
   `rfl`. The associator and unitors are `eqToIso` of the strict
   equalities, and these do need the instance supplied by hand —
   `eqToIso (…)` inside the instance fails to synthesize
   `Category (a ⟶ d)`, the `homCategory` field not yet being available
   to instance search — so they are written
   `@eqToIso _ FinCat.Hom.instCategory _ _ (…)`. Note `eqToHom` takes a
   `CategoryStruct` where `eqToIso` takes a `Category`, so the two
   ascriptions differ.
5. `FinCat.bicategory_strict : Bicategory.Strict FinCat`. Three of its
   six fields are `id_comp`, `comp_id` and `assoc`, which are the
   strict equalities of `Hom.lean`. The other three —
   `leftUnitor_eqToIso`, `rightUnitor_eqToIso`, `associator_eqToIso` —
   hold by `rfl` after intros — `associator_eqToIso` takes three explicit
   arguments — even though those equalities do not, by
   definitional proof irrelevance of the `Eq` proofs inside `eqToIso`.
   The name is `snake_case` per `docs/rules/lean-coding.md` § Naming
   conventions, the class being `Prop`-valued; mathlib spells the
   corresponding instances `Cat.bicategory.strict` and
   `locallyDiscreteBicategory.strict`, which that rule would not admit.
6. `FinCat.category : Category FinCat`, defined as
   `StrictBicategory.category FinCat`. It is named rather than left to
   the anonymous priority-100 instance, following `Cat.category`.
   There are no universe parameters to pin: `FinCat`, `FinCat.Hom` and
   `FinCat.Hom₂` all live at `Type 0`.

### Why ten axioms are proved rather than defaulted

Measured on a faithful model — 1-cells a multi-field structure with a
`Bool` validity field, composition neither definitionally unital nor
definitionally associative, 2-cells a non-subsingleton hom-category —
ten of the twelve coherence axioms fail under their defaults. The
discharger is `aesop_cat`: `Mathlib/CategoryTheory/Category/Basic.lean`
switches `cat_disch` to `grind` under
`mathlib.tactic.category.grind`, which `lakefile.toml` does not set.
Under `grind` all twelve fail.

The operative cause is not that `eqToHom` fails to rewrite. `aesop`'s
normalisation does make progress — it rewrites `(eqToIso p).hom` to
`eqToHom p` in seven of the ten, and collapses `pentagon`'s right-hand
side to a single `eqToHom` — but it applies no extensionality rule to a
goal at `F ⟶ G`, so no `app`-level lemma is ever reached, whether or
not it is `@[simp]`, and adding the hand-written `@[ext]` lemma does not
change that. Under `grind` the goals do reach `.app i`, `cat_disch`'s
grind branch running `try ext`, and still fail. The defaults
therefore close only goals whose two sides are already definitionally
equal — which is exactly `whiskerLeft_id` and `whiskerLeft_comp`.
Three of the ten failures (`id_whiskerRight`, `comp_whiskerRight`,
`whisker_exchange`) contain no `eqToHom` at all.

`Cat.bicategory` is not a precedent for defaulting them. `Cat`'s 1-cell
composition *is* definitionally unital, `Cat.Hom` being a one-field
bundling of `Functor` — `Cat.lean:229-232` proves its `Strict` fields
by `cases F; rfl` for the two unit laws and `intros; rfl` for
associativity. This spec records at § Functor and 2-cell
specifications that `FinCat.Hom` is not such a bundling, which is why
the two differ.

### Why not `CatEnriched`

`Mathlib/CategoryTheory/Bicategory/CatEnriched.lean` builds
`Bicategory` and `Bicategory.Strict` from `EnrichedCategory Cat C`
data, with associator and unitors as `eqToIso` of the strict
equalities — the same design as above. A strict 2-category is a
`Cat`-enriched category, so per CONTRIBUTING § Code is cost this is the
existing abstraction to instantiate rather than parallel, and it was
priced: hom-objects come free from `FinCat.Hom.instCategory`, leaving a
unit functor, horizontal composition as a bifunctor
`Hom S T ⊗ Hom T U ⟶ Hom S U`, and three functor-level equalities —
materially fewer obligations than the hand-rolled construction.
`CatEnriched C` is a type alias, but that is not an obstacle: `Bicategory`,
`Bicategory.Strict`, `Category` and the hom-categories all transport
onto the carrier itself through `inferInstanceAs`, measured.

It is rejected on axiom hygiene. `EnrichedCategory Cat C` requires
`MonoidalCategory Cat`, which measures
`[propext, Classical.choice, Quot.sound]`, and so therefore do
`Bicategory (CatEnriched X)` and `Bicategory.Strict (CatEnriched X)`.
Taking that route would make `FinCat/Bicategory.lean` an allowlisted
module holding this development's own content, where the hand-rolled
construction stays within `GebMeta.standardAxioms` and needs no
allowlist entry. `Cat.of` itself is axiom-free; the taint is in `Cat`'s
monoidal structure, so it cannot be avoided while using the enriched
formulation.

## Decidable equality and `Repr`

The decision procedures are built on core's `Nat.decidableForallFin`,
which is axiom-free, and **not** on the repository's
`Geb/Mathlib/Data/FinEnum.lean`, whose instances require
`FinEnum (Fin n)` and so carry `Classical.choice`. This workstream
therefore adds nothing to that file. The primitive is

```lean
scoped instance FinCat.decidableEqPiFin {n : Nat} {Y : Fin n → Type v}
    [∀ i, DecidableEq (Y i)] : DecidableEq ((i : Fin n) → Y i) :=
  fun f g => decidable_of_iff (∀ i, f i = g i) funext_iff.symm
```

It is dependent from the outset — `funext_iff` already is — so it
covers the non-dependent case with no second instance of ours at the
same head symbol.

mathlib's `Fintype.decidablePiFintype` (`Mathlib/Data/Fintype/Defs.lean`)
*is* a competitor at that head symbol, is likewise dependent, and is
what default resolution selects in its absence, by way of `Fin.fintype`
— measured `[propext, Classical.choice, Quot.sound]`. Relying on a
later declaration winning at equal priority would make the axiom
content of this workstream an artifact of declaration order. Two
mitigations are therefore applied together: the instance is `scoped`,
so it does not alter selection for downstream importers of a
category-theory module; and the `DecidableEq` argument is supplied
explicitly at each use site rather than left to resolution. That is the
mitigation `Geb/Mathlib/Data/FinEnum.lean` documents for the same
hazard, and the reason it gives — that an instance which still
typechecks may silently acquire `Classical.choice` — applies verbatim.

Three layers follow, in dependency order.

1. Equality of `comp` fields at fixed `objCount` and `nonIdCount`: the
   instance above, applied at `Fin`.
2. `DecidableEq (FinCat.Hom S T)` and `DecidableEq (FinCat.Hom₂ F G)`.
   `map` has a type mentioning `objMap`, so its comparison follows a
   transport along the decided equality of `objMap`. The
   `Bool`-equation fields are proof-irrelevant and contribute no
   obligation.
3. `DecidableEq FinCat`: decide `objCount`, transport, decide
   `nonIdCount`, transport, decide `comp`.

`Repr` instances at all three levels render the count matrix and the
composition table as nested naturals, through `List.ofFn` and
`Fin.val`. `List.ofFn` is axiom-free and needs no import beyond core;
`Geb/Mathlib/Data/Vector/OfFn.lean` exists for choice-free *indexing
lemmas*, which rendering does not use, so it is not a dependency here.
`Repr` requires no transport at any level: it maps out of the dependent
structure into `Format`, discarding the types whose disagreement
obstructs equality.

## Axiom hygiene

The target is that every module of this workstream is choice-free
except one, whose dependence is forced by mathlib's definitions rather
than by anything in this design.

**Measured, on the pinned toolchain (`leanprover/lean4:v4.33.0-rc1`),
against a prototype of the design.** `compTotal` and `assocCheck`
depend on **no axioms at all**; `id_comp` depends on `propext` alone.
`decide (∀ i j : Fin n, …)` at variable `n` is axiom-free, resolving
through `Nat.decidableForallFin`. The `DecidableEq` primitive above and
its application at the `comp` field's type depend on `Quot.sound`
alone. All of these are within `GebMeta.standardAxioms`.

**Measured to be choice-dependent**, all reporting
`[propext, Classical.choice, Quot.sound]`: `Fintype` itself,
`Fintype.mk`, `Finset.instSetLike`, `Fin.fintype`, `ULift.fintype`,
`FinEnum.fin`, `Fintype.decidableForallFintype`,
`Fintype.decidablePiFintype`, and `CategoryTheory.Iso.refl`. By
contrast `Finset` is `[propext, Quot.sound]`, `Finite` is axiom-free,
`CategoryTheory.eqToIso` is `[propext]`, and
`CategoryTheory.StrictBicategory.category` is `[propext]`.

Three consequences.

- **`FinCat.Obj.finCategory` cannot be choice-free, at all.** The
  `Fintype` *class* is itself choice-dependent: its `complete` field
  routes membership through `Finset.instSetLike`, which carries the
  axiom. No choice of witness and no hand-rolled instance can avoid
  it, so this is a forced allowlist entry rather than a cost trade-off.
  `Finite` is axiom-free but is not an escape, `FinCategory`'s fields
  being `Fintype`s. The instance goes in
  `Geb/Mathlib/CategoryTheory/FinCat/FinCategory.lean`, a module
  containing that instance and nothing else, and that module and its
  test parallel are appended to `GebMeta.classicalAllowedModules`.
- **The checkers must not be routed through
  `Geb.Mathlib.Data.FinEnum`.** That file's premise — that mathlib
  decides a bounded `∀` through a choice-dependent `Fintype` — holds
  for a general type carrying a `FinEnum` hypothesis, which is how
  every existing caller in `Geb/` uses it. It does not hold at a
  concrete `Fin n`, where instantiating `FinEnum (Fin n)` introduces
  the very taint the file exists to avoid, and where core's default
  route is already clean. No change to that file is warranted; the
  restriction is on this workstream's use of it.
- **The hand-rolled bicategory layer is choice-free; the enriched one
  is not.** `Cat.bicategory`'s taint was traced to
  `CategoryTheory.Iso.refl`, reached through `Cat.Hom.isoMk` in its
  associator and unitor fields; `cat_disch` itself introduces no
  choice, and `Bicategory.lean` above uses `eqToIso`, not `Iso.refl`,
  so that route has no way in. The measured ingredients of the hand-rolled
  construction are: `eqToIso` is `[propext]`,
  `StrictBicategory.category` is `[propext]`, and `funext` — reached
  through the strict equalities, which are not `rfl` — is
  `[Quot.sound]`, all within `GebMeta.standardAxioms`. The instance
  figure `[propext, Quot.sound]` is therefore expected, and is listed
  outstanding below rather than discharged: the coherence proofs are
  themselves an ingredient, and their tactic content is settled by the
  implementation plan rather than here. By contrast
  `MonoidalCategory Cat` measures
  `[propext, Classical.choice, Quot.sound]`, and so do
  `Bicategory (CatEnriched X)` and `Bicategory.Strict (CatEnriched X)`
  — which is why § Why not `CatEnriched` rejects that route. No
  allowlist entry is planned for `FinCat/Bicategory.lean`.

`native_decide` is used nowhere. It introduces `Lean.ofReduceBool`,
which the axiom linter rejects.

## File layout

```text
Geb/Mathlib/CategoryTheory/FinCat.lean              index
Geb/Mathlib/CategoryTheory/FinCat/Basic.lean        homCountOf, embOf, the
                                                    unbundled arithmetic
                                                    lemmas, compTotalOf,
                                                    assocCheckOf; then the
                                                    specification and ext, the
                                                    bundled wrappers, the
                                                    identity laws, the
                                                    reflection lemma,
                                                    compTotal_assoc, and the
                                                    Inhabited derivation
Geb/Mathlib/CategoryTheory/FinCat/Category.lean     object type and its ext,
                                                    Category, DecidableEq on
                                                    Obj and on the generated
                                                    homs
Geb/Mathlib/CategoryTheory/FinCat/FinCategory.lean  diagonal FinCategory
                                                    (allowlisted)
Geb/Mathlib/CategoryTheory/FinCat/Hom.lean          functor specifications,
                                                    checker,
                                                    compCheck_eq_true_iff,
                                                    mapTotal, ext,
                                                    mapTotal_emb, mapTotal_id,
                                                    mapTotal_compTotal,
                                                    id_mapTotalOf,
                                                    comp_mapTotalOf,
                                                    id and comp, id_mapTotal,
                                                    comp_mapTotal,
                                                    strict equalities,
                                                    toFunctor
Geb/Mathlib/CategoryTheory/FinCat/Hom2.lean         2-cell specifications,
                                                    checker,
                                                    natCheck_eq_true_iff,
                                                    instCategory, app_id,
                                                    app_comp, ext lemma at
                                                    F to G, natCheck_total,
                                                    toNatTrans
Geb/Mathlib/CategoryTheory/FinCat/Bicategory.lean   whiskerings, eqToHom_app,
                                                    the ten coherence theorems,
                                                    Bicategory, Strict,
                                                    Category
Geb/Mathlib/CategoryTheory/FinCat/Decidable.lean    decidableEqPiFin,
                                                    DecidableEq layers 1-3
Geb/Mathlib/CategoryTheory/FinCat/Repr.lean         Repr
```

`Geb/Mathlib/CategoryTheory.lean` gains the `FinCat` index import, and
`GebTests/Mathlib/CategoryTheory/FinCat/` mirrors the tree.

Every file opens with the `module` keyword, which
`scripts/lint-imports.sh` requires of upstream-eligible files, and uses
`public import` for re-exported imports and plain `import` for
internally-used ones, per `docs/rules/lean-coding.md` § Lean 4 module
system. Each carries a module docstring with the section list that
`docs/rules/lean-coding.md` § Documentation mandates, `## Tags`
included.

The names follow `CategoryTheory.Cat`: the specification type is
`FinCat`, its 1-cells are `FinCat.Hom`, its 2-cells `FinCat.Hom₂`, and
the instances `FinCat.bicategory`, `FinCat.bicategory_strict` and
`FinCat.category`.

`Geb/Mathlib/CategoryTheory/FinCat/Basic.lean` needs no imports at all:
its `Fin` and `Nat` material is in the prelude, and
`scripts/lint-imports.sh` admits only `Mathlib.`, `Batteries.` and
`Geb.Mathlib.` prefixes in this subtree, so a core import would be a
lint violation. Nothing in its content mentions `Category`, so it must
not import `Mathlib.CategoryTheory.Category.Basic`; `lake shake` would
flag that. The specification type and its checker are usable
without any part of the mathlib category-theory hierarchy.

## Verification obligations

Items 1 to 4 are **discharged**, by measurement against a prototype on
the pinned toolchain, and are recorded here so the implementation
re-runs them rather than re-deriving them.

1. `compTotal` and `assocCheck` are axiom-free under the default
   `Decidable` resolution, given hand-written proofs of the two elided
   bounds. A proof written with `simpa`/`by_contra` instead measures
   `[propext]` — still standard, but the axiom-free result needs care.
2. `assocCheck` reduces in the kernel, so `rfl` — not the `decide`
   tactic — discharges the validity field. Confirmed on the terminal
   category, the walking arrow, and the walking isomorphism, the last
   being the case where a client composite lands on the reserved
   identity index.
3. The checker rejects as well as accepts: a two-object specification
   with one non-identity morphism at every index pair, composing each
   pair to the reserved identity exactly when its endpoints agree,
   gives `assocCheck … = false` by `rfl`.
4. The reduction of general associativity to client-triple
   associativity holds, including the case in which a composite of two
   client morphisms is an identity, and the identity laws are
   provable at variable indices though not by `rfl`.

Outstanding:

1. `FinCat.bicategory` and `FinCat.bicategory_strict` measure
   `[propext, Quot.sound]`. Every ingredient named in § Axiom hygiene is
   measured and leaves no route for `Classical.choice`, and a prototype
   with the remaining content stubbed measured
   `[propext, sorryAx, Quot.sound]`; the figure with nothing stubbed is
   not yet measured.
2. The `mapTotal` family holds: `mapTotal_emb`, which reduces
   `FinCat.Hom.id_comp`; `mapTotal_id`, which `mapTotal_compTotal`'s own
   proof consumes; `mapTotal_compTotal`, without which
   `FinCat.Hom.comp` cannot be defined; the unbundled `id_mapTotalOf`
   and `comp_mapTotalOf`, which discharge the two validity fields; the
   bundled `id_mapTotal` and `comp_mapTotal`, which reduce
   `FinCat.Hom.comp_id` and `FinCat.Hom.assoc`; and
   `FinCat.Hom₂.natCheck_total`, which is `whisker_exchange`. All are
   named content and all remain to be proved.
3. The three strict equalities `FinCat.Hom.id_comp`,
   `FinCat.Hom.comp_id` and `FinCat.Hom.assoc` hold; the validity
   fields of `FinCat.Hom.id` and `FinCat.Hom.comp` discharge as
   § In `Hom.lean` item 6 assigns them; and the `natValid` fields of the
   identity 2-cell and of the vertical composite in
   `FinCat.Hom.instCategory` discharge from `natCheck_eq_true_iff` and,
   for the composite, `compTotal_assoc` three times.
4. `DecidableEq` layers 2 and 3 construct as § Decidable equality and
   `Repr` describes, the heterogeneous `@[ext]` lemmas supplying the
   negative cases, and they and the `Repr` instances measure
   `[propext, Quot.sound]` or better. Layer 1 is measured; these two are
   the spec's only transport-based decision procedures and are not.

## Testing

`GebTests/Mathlib/CategoryTheory/FinCat/` mirrors the source tree. The
worked examples, each discharging its validity field by `rfl`:

- the terminal category: one object, no non-identity morphisms;
- the walking arrow: two objects, one non-identity morphism;
- the two-element monoid on an idempotent: one object, one
  non-identity morphism composing with itself to itself;
- the walking isomorphism: two objects, one non-identity morphism each
  way, each composite being an identity. This is the regression test
  for the case in which a client-supplied composition returns a value
  outside the client's own index range.

The negative test is the two-object specification of discharged
obligation 3, asserting `assocCheck … = false` by `rfl`. Its witness is
`f : 0 ⟶ 0`, `g : 0 ⟶ 1`, `h : 1 ⟶ 0`, where `(f ⬝ g) ⬝ h` is the
reserved identity of `0` and `f ⬝ (g ⬝ h)` is `f`, writing `⬝` for
`compTotal`.

Functor and 2-cell tests: the identity functor on each worked example,
the two functors from the terminal category into the walking arrow, and
the 2-cells between them. Bicategory tests assert the three strict
equalities on the worked examples. `DecidableEq` and `Repr` tests
assert decision and rendering on the same examples.

Axiom-hygiene tests run the existing linter over each module.

## Persistent documentation

`docs/index.md` § Implemented content gains one bullet per `FinCat`
module, in topological position and in the form the existing
`FinSetSkel` bullets take: module path, a summary of its content, and a
closing `Classical.choice`-free or allowlist clause. That section is a
flat list with no subsection level, so no heading is added.

`docs/references.bib` requires no new entry: [JohnsonYau2021] is
present.

## Deferred work

`TODO.md` carries three entries touching this workstream.

§ PRA functors over finite-specification base categories is the
consumer that keeps scope items 2 and 3 in scope under CONTRIBUTING
§ Code is cost: presheaf parametric-right-adjoint functors instantiated
at `FinCat`-presented base categories, with decidable equality on their
W-types and natural transformations among them. That entry also records
that this workstream supplies the finite `J`-hom-sets with decidable
equality which § Exhaustive verification of presheaf PRA laws for
finite instances records as missing, and that supplying a `FinEnum J`
field choice-free is a cost this workstream declines and that one must
price.

§ Finite categories as a full subcategory of `Cat` is the deferred
comparison: the object property on `Cat.{v, u}`, the 2-functor from
`FinCat` extending `FinCat.Hom.toFunctor`, and the equivalence onto the
full subcategory. It records that essential surjectivity is classical
through `Fintype.equivFin`, that the object bijection makes the result
an isomorphism in `Cat` rather than only an equivalence, and that the
hom-set bijections must carry each identity to the index reserved here.

§ Complexity of the decidable validity checkers gains `FinCat.assocCheck`,
which enumerates `Θ(objCount⁴) + O(M³)` tuples for `M` the total
non-identity morphism count: four object quantifiers stand outside the
three morphism quantifiers, so a discrete category on `n` objects costs
`n⁴` iterations even at `M = 0`.

## References

- [CONTRIBUTING.md](../../../CONTRIBUTING.md) — contributor rules.
- [docs/process.md](../../process.md) — rationale for the rules.
- [JohnsonYau2021] Johnson and Yau, *2-Dimensional Categories*, Oxford
  University Press, 2021; arXiv:2002.06055.
