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
outside this workstream, recorded as a `TODO.md` entry in the same
commit as this spec. Absent that entry, CONTRIBUTING § Code is cost
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
- Bicategory, strict bicategory, and the 2-category `Cat`:
  transcription, from [JohnsonYau2021] § 2.1, "Bicategories", and
  § 2.3, "2-Categories". mathlib's rendering is
  `CategoryTheory.Bicategory`, `CategoryTheory.Bicategory.Strict` and
  `CategoryTheory.Cat.bicategory`.
- Finiteness of a category — finitely many objects, finitely many
  morphisms in each hom-set — is a standard restriction on the
  transcribed notion of category rather than a transcription of any
  one source; [JohnsonYau2021] does not treat it. mathlib states the
  same restriction as `CategoryTheory.FinCategory`. It is recorded
  here as a restriction, not marked transcription or novel, because
  neither marking is accurate.
- The encoding below — the hom-count matrix, the reserved identity
  index, the checkers and their reflection lemmas — is novel. It is a
  presentation of the transcribed notions, not a new mathematical
  concept.

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
def FinCat.homCount (S : FinCat) (i j : Fin S.objCount) : Nat :=
  S.nonIdCount i j + if i = j then 1 else 0
```

so that the embedding of a client morphism into the full hom type is
index-preserving on and off the diagonal, and `𝟙 i` has index
`S.nonIdCount i i`.

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
      Fin (homCountOf objCount nonIdCount i k)
  assoc : assocCheckOf objCount nonIdCount comp = true
```

with the derived notions

```lean
def FinCat.Mor (S : FinCat) (i j : Fin S.objCount) : Type :=
  Fin (S.homCount i j)

def FinCat.emb {S : FinCat} {i j : Fin S.objCount} :
    Fin (S.nonIdCount i j) → S.Mor i j :=
  Fin.castLE (Nat.le_add_right _ _)

def FinCat.id (S : FinCat) (i : Fin S.objCount) : S.Mor i i :=
  ⟨S.nonIdCount i i, by simp [FinCat.homCount]⟩
```

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
theorem FinCat.eq_of_not_lt (S : FinCat) {i j : Fin S.objCount}
    (x : S.Mor i j) (h : ¬ x.val < S.nonIdCount i j) : i = j
theorem FinCat.eq_id_of_not_lt (S : FinCat) {i j : Fin S.objCount}
    (x : S.Mor i j) (h : ¬ x.val < S.nonIdCount i j) : x.val = S.nonIdCount j j
```

An index outside the client's range can only exist on the diagonal,
because off it the `if` in `homCount` contributes `0`. `eq_of_not_lt`
discharges both elided bounds; `eq_id_of_not_lt` is what `comp_id` and
the associativity reduction need. When both arguments are identities
the outermost `else` fires and returns the identity, which is correct.

Field types cannot mention the structure being defined, so `homCountOf`,
`assocCheckOf` and an unbundled `compTotalOf` take `objCount`,
`nonIdCount` and `comp` as explicit arguments. The same applies one
level up, to `FinCat.Hom`: its `compValid` field type needs unbundled
`mapTotalOf` and `compCheckOf` over `objMap` and `map`. The bundled
`FinCat.homCount`, `FinCat.Mor`, `FinCat.emb`, `FinCat.id`,
`FinCat.compTotal` and `FinCat.Hom.mapTotal` shown in this document are
the wrappers applying them to a given `S` or `F`, and are what every
later module uses.

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
`eq_id_of_not_lt`. Both are ordinary proofs, and the implementation
budgets for them rather than describing the laws as definitional.

Associativity is checked, and only on triples of client morphisms:

```lean
def FinCat.assocCheckOf … : Bool :=
  decide <| ∀ (i j k l : Fin objCount)
    (f : Fin (nonIdCount i j)) (g : Fin (nonIdCount j k))
    (h : Fin (nonIdCount k l)),
      compTotalOf (compTotalOf (emb f) (emb g)) (emb h)
        = compTotalOf (emb f) (compTotalOf (emb g) (emb h))
```

The composition appearing in the statement is the total one, so a
composite landing on the reserved identity index is covered.
Associativity of the total composition on all triples follows by cases
on which arguments are identities, using `id_comp`, `comp_id` and
`eq_id_of_not_lt`.

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
`natCheck_eq_true_iff`) relating it to the corresponding `Prop`. These
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
following `CategoryTheory.Cat.Hom₂` (`Cat.lean:111`) and avoiding a
name that collides visually with dot notation on a `FinCat.Hom` value.
`FinCat.Hom` is named for its position — the 1-cells of a 2-category —
not for its shape: unlike `Cat.Hom` it is not a one-field bundling.

`map` is given on client morphisms and lands in the target's full hom
type, since a functor may send a non-identity morphism to an identity;
every functor into the terminal category does. It extends to `mapTotal`
by sending `S.id i` to `T.id (F.objMap i)`, so preservation of
identities holds by construction and only the composition law is
checked. At `S.id i` the target type is already
`T.Mor (F.objMap i) (F.objMap i)`, so this extension involves no
object equation at all.

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

Dependency order is 1 → 2 → 4 → 5 → 6, with 3 independent of 2 and
required by 4.

1. Composition and identity of `FinCat.Hom` as operations, each
   discharging its validity field through the reflection lemmas. `FinCat`,
   `FinCat.Hom` and `FinCat.Hom₂` are all marked `@[ext]`, per
   `docs/rules/lean-coding.md` § Structure and typeclass patterns.
   Because `map`'s type mentions `objMap`, Lean's derived lemma is
   heterogeneous — `objMap` equality plus `HEq` of `map` — and is
   derived automatically; no lemma is written by hand. If a pointwise
   form is wanted later it is a separate lemma, not the `ext` one.
2. The three strict equalities as lemmas about `FinCat.Hom`:
   `𝟙 ≫ F = F`, `F ≫ 𝟙 = F`, `(F ≫ G) ≫ H = F ≫ (G ≫ H)`. The
   `Bool`-equation fields contribute nothing, being proof-irrelevant.
3. `FinCat.Hom.instCategory : Category (FinCat.Hom S T)` — vertical
   composition of 2-cells and the identity 2-cell. This instance lives
   in `Hom2.lean`, before `toNatTrans`, whose statement uses `⟶` at
   the 2-cell level and so depends on it.
4. `FinCat.bicategory : Bicategory FinCat`, following
   `CategoryTheory.Cat.bicategory`: `id`, `comp`, `homCategory`,
   `whiskerLeft`, `whiskerRight`, and the associator and unitors as
   `eqToIso` of step 2's equalities. The twelve coherence axioms of
   `CategoryTheory.Bicategory` carry `cat_disch` defaults, as
   `Cat.bicategory` relies on.
5. `FinCat.bicategory.strict : Bicategory.Strict FinCat`. Its
   `leftUnitor_eqToIso`, `rightUnitor_eqToIso` and
   `associator_eqToIso` fields hold by `rfl`, step 4 having defined
   those isomorphisms that way; `Bicategory.Strict` is `Prop`-valued,
   so the proof arguments need not match definitionally.
6. `FinCat.category : Category FinCat`, defined as
   `StrictBicategory.category FinCat`. It is named rather than left to
   the anonymous priority-100 instance, following `Cat.category`.
   There are no universe parameters to pin: `FinCat`, `FinCat.Hom` and
   `FinCat.Hom₂` all live at `Type 0`.

Steps 1 to 3 are this development's own content, proved here. Steps 4
to 6 package it into mathlib classes.

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
- **The bicategory layer is expected to be choice-free**, contrary to
  an earlier draft of this spec. `Cat.bicategory`'s taint was traced to
  `CategoryTheory.Iso.refl`, reached through `Cat.Hom.isoMk` in its
  associator and unitor fields; `cat_disch` itself introduces no
  choice, and a prototype bicategory with `eqToIso` coherence
  isomorphisms and all twelve axioms left to `cat_disch` measured
  `[propext]`, as did `Bicategory.Strict` and the derived `Category`
  on it. Step 4 of
  [the strict 2-category](#the-strict-2-category-of-specifications)
  uses `eqToIso`, not `Iso.refl`, so the taint has no route in. This
  is an expectation to confirm at `FinCat`, not a contingency: no
  allowlist entry is planned for `FinCat/Bicategory.lean`.

`native_decide` is used nowhere. It introduces `Lean.ofReduceBool`,
which the axiom linter rejects.

## File layout

```text
Geb/Mathlib/CategoryTheory/FinCat.lean              index
Geb/Mathlib/CategoryTheory/FinCat/Basic.lean        specification,
                                                    eq_of_not_lt,
                                                    eq_id_of_not_lt, identity,
                                                    total composition, identity
                                                    laws, checker, reflection
                                                    lemma
Geb/Mathlib/CategoryTheory/FinCat/Category.lean     object type, Category
Geb/Mathlib/CategoryTheory/FinCat/FinCategory.lean  diagonal FinCategory
                                                    (allowlisted)
Geb/Mathlib/CategoryTheory/FinCat/Hom.lean          functor specifications,
                                                    checker, toFunctor, strict
                                                    equalities
Geb/Mathlib/CategoryTheory/FinCat/Hom2.lean         2-cell specifications,
                                                    checker, instCategory,
                                                    toNatTrans
Geb/Mathlib/CategoryTheory/FinCat/Bicategory.lean   Bicategory, Strict, Category
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
the instances `FinCat.bicategory`, `FinCat.bicategory.strict` and
`FinCat.category`.

`Geb/Mathlib/CategoryTheory/FinCat/Basic.lean` imports core `Fin` and
`Nat` material only. Nothing in its content mentions `Category`, so it
must not import `Mathlib.CategoryTheory.Category.Basic`; `lake shake`
would flag that. The specification type and its checker are usable
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

1. `FinCat.bicategory` and `FinCat.bicategory.strict` are choice-free
   at `FinCat`, as the prototype measurement predicts, and the twelve
   coherence axioms close under `cat_disch` given `eqToIso` coherence
   isomorphisms.
2. `compCheck` and `natCheck`, stated over `mapTotal` and `compTotal`,
   admit the same reduction as `assocCheck`: the law holds on all
   morphisms given that it holds on client morphisms. This is the
   functor and naturality analogue of discharged item 4 and is not
   implied by it.

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
reserved identity of `0` and `f ⬝ (g ⬝ h)` is `f`.

Functor and 2-cell tests: the identity functor on each worked example,
the two functors from the terminal category into the walking arrow, and
the 2-cells between them. Bicategory tests assert the three strict
equalities on the worked examples. `DecidableEq` and `Repr` tests
assert decision and rendering on the same examples.

Axiom-hygiene tests run the existing linter over each module.

## Persistent documentation

`docs/index.md` gains a subsection under the category-theory heading
listing the `FinCat` modules and their contents, in the form the
existing `FinSetSkel` entries take. `docs/references.bib` requires no
new entry: [JohnsonYau2021] is present.

## Deferred work

`TODO.md` gains an entry for the comparison with `Cat`, comprising:

- the object property on `Cat.{v, u}` selecting the categories with
  finitely many objects and finitely many morphisms in each hom-set,
  stated as a `Prop` in the shape of
  `CategoryTheory.CountableCategory`, mathlib having no such property;
- the 2-functor from `FinCat` to `Cat.{v, u}` extending
  `FinCat.Hom.toFunctor`;
- the proof that it is an equivalence onto the corresponding full
  subcategory.

The entry records two observations from this workstream. Essential
surjectivity chooses `Obj ≃ Fin n` and a bijection on each hom-set, so
it depends on `Fintype.equivFin` and is classical; and because the
chosen map on objects is a bijection, the result is an isomorphism in
`Cat` rather than only an equivalence, as
`Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` obtains for its
own comparison. The hom-set bijections must be chosen to carry each
identity to the reserved index, which is a constraint the present
workstream's conventions impose on that one.

The existing `TODO.md` entry on the complexity of the decidable
validity checkers gains a note that `assocCheck` enumerates
`Θ(objCount⁴) + O(M³)` tuples, where `M` is the total non-identity
morphism count: four object quantifiers stand outside the three
morphism quantifiers, so a discrete category on `n` objects still costs
`n⁴` iterations with `M = 0`.

## References

- [CONTRIBUTING.md](../../../CONTRIBUTING.md) — contributor rules.
- [docs/process.md](../../process.md) — rationale for the rules.
- [JohnsonYau2021] Johnson and Yau, *2-Dimensional Categories*, Oxford
  University Press, 2021; arXiv:2002.06055.
