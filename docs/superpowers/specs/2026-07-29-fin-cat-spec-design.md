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

Out of scope, recorded under [Deferred work](#deferred-work): the
finiteness object property on `Cat` and the comparison between the
specifications and the corresponding full subcategory.

Also out of scope: notation for writing a specification's fields as
table literals. A client writes `nonIdCount` and `comp` as functions.
Notation is deferred until a client reports friction with that.

## Transcription status of the definitions

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing:

- Finite category, functor, natural transformation: transcription.
  mathlib states the finiteness condition as
  `CategoryTheory.FinCategory` in
  `Mathlib/CategoryTheory/FinCategory/Basic.lean`; the definitions of
  functor and natural transformation are mathlib's.
- Bicategory, strict bicategory, and the 2-category `Cat`:
  transcription, from [JohnsonYau2021]; mathlib's rendering is
  `CategoryTheory.Bicategory`, `CategoryTheory.Bicategory.Strict` and
  `CategoryTheory.Cat.bicategory`.
- The encoding below — the hom-count matrix, the reserved identity
  index, the checkers and their reflection lemmas — is novel. It is a
  presentation of the transcribed notions, not a new mathematical
  concept.

## Encoding of the morphisms

The objects are indexed by `Fin objCount` for `objCount : Nat`. Two
encodings of the morphisms were considered.

1. A hom-count matrix `Fin objCount → Fin objCount → Nat`.
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
the identities in their own counts was also rejected: it removes the
transport discussed below, but requires the client to write the
identity rows and columns of the composition table, whose entries are
determined by the identity laws.

A consequence of the adopted convention, recorded so that it is priced
rather than discovered: the total composition must case on whether each
argument is an identity, and in the branch where the first argument is
`FinCat.id i` it moves the second argument across the equation `i = j`
between two hom types. This is an `Eq.rec`, and it propagates into
lemmas about composition. It is confined by the pattern
`Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` establishes for its
own morphisms: a named transport with `@[simp]` application lemmas,
followed by `attribute [irreducible]`, so that no downstream module
unfolds it.

## The specification type

```lean
structure FinCat where
  objCount : Nat
  nonIdCount : Fin objCount → Fin objCount → Nat
  comp : (i j k : Fin objCount) →
    Fin (nonIdCount i j) → Fin (nonIdCount j k) →
      Fin (homCountOf objCount nonIdCount i k)
  assoc : assocCheck objCount nonIdCount comp = true
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

and the total composition `FinCat.compTotal : S.Mor i j → S.Mor j k →
S.Mor i k`, which returns its second argument when its first is
`S.id i`, its first argument when its second is `S.id j`, and `S.comp`
applied to the underlying client indices otherwise.

`homCountOf` and the unbundled `compTotal` used in the `comp` and
`assoc` field types take `objCount`, `nonIdCount` and `comp` as
explicit arguments, a structure's field types being unable to refer to
the structure. The `FinCat.homCount`, `FinCat.Mor`, `FinCat.emb`,
`FinCat.id` and `FinCat.compTotal` shown here are the bundled wrappers
that apply them to a given `S`, and are what every later module uses.

The client writes `objCount`, `nonIdCount` and `comp`, and discharges
`assoc`. The client designates no identities, states no identity laws,
and supplies no domain or codomain data. The composition a client
writes returns a value in the **full** hom type, because a composite of
two non-identity morphisms may be an identity — the walking isomorphism
is the smallest instance.

The specification type carries no universe parameters. Its content
lives at `Type 0`; universe levels enter only at the boundary described
under [The generated mathlib category](#the-generated-mathlib-category).

## The checkers and their reflection lemmas

Because the identity and its composition branches are defined here, the
identity laws hold by construction and are not checked. Associativity
is checked, and only on triples of client morphisms:

```lean
def FinCat.assocCheck … : Bool :=
  decide <| ∀ (i j k l : Fin objCount)
    (f : Fin (nonIdCount i j)) (g : Fin (nonIdCount j k))
    (h : Fin (nonIdCount k l)),
      compTotal (compTotal (emb f) (emb g)) (emb h)
        = compTotal (emb f) (compTotal (emb g) (emb h))
```

The composition appearing in the statement is the total one, so a
composite landing on an identity is covered. Associativity of the total
composition on all triples follows by cases on which arguments are
identities; in each of those cases both sides reduce by the definition
of `compTotal`.

Every quantifier ranges over a `Fin`. The `Decidable` instances are
therefore `FinEnum.decidableForallFinEnum` from
`Geb/Mathlib/Data/FinEnum.lean`, which routes through
`List.decidableBAll` over `FinEnum.toList`, and not
`Fintype.decidableForallFintype`, which depends on `Classical.choice`.
The `FinEnum (Fin n)` instance is mathlib's `FinEnum.fin`.

The validity field is a `Bool` equation, so a client with a concrete
category discharges it with `rfl`.

Each checker is accompanied by a reflection lemma:

```lean
theorem FinCat.assocCheck_eq_true_iff : assocCheck … = true ↔ ∀ …
theorem FinCat.Hom.compCheck_eq_true_iff : compCheck … = true ↔ ∀ …
theorem FinCat.Hom.natCheck_eq_true_iff : natCheck … = true ↔ ∀ …
```

These are required by the constructions of
[the strict 2-category](#the-strict-2-category-of-specifications), not
merely convenient. Vertical composition of 2-cells must produce a valid
2-cell, and its validity field cannot be discharged by `decide`,
because the source and target specifications are variables. Each such
construction proves the law at the `Prop` level from its hypotheses and
converts back through the reflection lemma.

## The generated mathlib category

```lean
structure FinCat.Obj.{u} (S : FinCat) : Type u where
  idx : ULift.{u} (Fin S.objCount)

instance FinCat.instCategory.{v, u} (S : FinCat) :
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

Where the object and morphism levels coincide the category is small,
and

```lean
instance FinCat.instFinCategory.{u} (S : FinCat) :
    FinCategory (FinCat.Obj.{u} S)
```

applies. `CategoryTheory.FinCategory` requires `SmallCategory`, so no
such instance exists at independent levels; this is the reason the
finiteness carried by a specification is not expressible through that
class in general. mathlib's universe-polymorphic analogue,
`CategoryTheory.CountableCategory`, is a `Prop` class over
`Category*` with `countableObj` and `countableHom` fields; no
corresponding finite class exists upstream.

The `Fintype` fields of `FinCat.instFinCategory` are to be supplied by
`Fin.fintype` and `ULift.fintype`, not by mathlib's
`FinEnum → Fintype` bridge. See
[Verification obligations](#verification-obligations).

`FinCat.Obj` and the generated hom types carry `DecidableEq` instances,
derived from `Fin` and `ULift`. A category whose purpose is that its
laws are decidable is of limited use if its objects and morphisms are
not comparable, and mathlib's `FinCategory` dropped its own
`DecidableEq` requirements, so the instances have to originate here.

## Functor and 2-cell specifications

```lean
structure FinCat.Hom (S T : FinCat) where
  objMap : Fin S.objCount → Fin T.objCount
  map : (i j : Fin S.objCount) →
    Fin (S.nonIdCount i j) → T.Mor (objMap i) (objMap j)
  compValid : compCheck objMap map = true

structure FinCat.Hom.Hom {S T : FinCat} (F G : FinCat.Hom S T) where
  app : (i : Fin S.objCount) → T.Mor (F.objMap i) (G.objMap i)
  natValid : natCheck F G app = true
```

`map` is given on client morphisms and lands in the target's full hom
type, since a functor may send a non-identity morphism to an identity;
every functor into the terminal category does. It extends to `mapTotal`
by sending `S.id i` to `T.id (F.objMap i)`, so preservation of
identities holds by construction and only the composition law is
checked. This extension requires no transport: at `S.id i` the target
type is already `T.Mor (F.objMap i) (F.objMap i)`. The transport
described under
[Encoding of the identities](#encoding-of-the-identities) does not
propagate into this module.

`app` ranges over the full hom type from the outset, the identity
2-cell having every component an identity. Naturality is checked on
client morphisms only, the identity case again holding by the
definition of `compTotal`.

The generated mathlib data are

```lean
def FinCat.Hom.toFunctor.{v, u} {S T : FinCat} (F : FinCat.Hom S T) :
    FinCat.Obj.{u} S ⥤ FinCat.Obj.{u} T

def FinCat.Hom.Hom.toNatTrans.{v, u} {S T : FinCat}
    {F G : FinCat.Hom S T} (α : F ⟶ G) :
    F.toFunctor.{v, u} ⟶ G.toFunctor.{v, u}
```

## The strict 2-category of specifications

Built in the order strictness imposes.

1. Composition and identity of `FinCat.Hom` as operations, each
   discharging its validity field through the reflection lemmas, with
   `@[ext]` lemmas: equality of specifications is `funext` on the map
   fields together with proof irrelevance on the `Bool` equations.
2. The three strict equalities as lemmas about `FinCat.Hom`:
   `𝟙 ≫ F = F`, `F ≫ 𝟙 = F`, `(F ≫ G) ≫ H = F ≫ (G ≫ H)`.
3. `FinCat.Hom.instCategory` — vertical composition of 2-cells and the
   identity 2-cell, with an `@[ext]` lemma on `app`.
4. `FinCat.bicategory : Bicategory FinCat`, following
   `CategoryTheory.Cat.bicategory`: `id`, `comp`, `homCategory`,
   `whiskerLeft`, `whiskerRight`, and the associator and unitors as
   `eqToIso` of step 2's equalities. The twelve coherence axioms of
   `CategoryTheory.Bicategory` carry defaults, as `Cat.bicategory`
   relies on.
5. `FinCat.bicategory.strict : Bicategory.Strict FinCat`. Its
   `leftUnitor_eqToIso`, `rightUnitor_eqToIso` and
   `associator_eqToIso` fields hold by `rfl`, step 4 having defined
   those isomorphisms that way.
6. `Category FinCat` follows from
   `CategoryTheory.StrictBicategory.category`, a priority-100 instance
   on any `Bicategory` that is `Strict`. It is not written by hand.

Steps 1 to 3 are equalities of `Fin`-valued functions and are proved
here. Steps 4 to 6 package them into mathlib classes.

## Decidable equality and `Repr`

`Geb/Mathlib/Data/FinEnum.lean` gains one instance, the dependent
sibling of its existing `FinEnum.decidablePiFinEnum`:

```lean
instance FinEnum.decidableDPiFinEnum {α : Type u} {Y : α → Type v}
    [∀ a, DecidableEq (Y a)] [FinEnum α] : DecidableEq ((a : α) → Y a)
```

proved as its non-dependent sibling is, `funext_iff` being already
dependent.

Three layers follow, in dependency order.

1. Equality of `comp` fields at fixed `objCount` and `nonIdCount`: the
   new instance, applied at `Fin`.
2. `DecidableEq (FinCat.Hom S T)` and
   `DecidableEq (FinCat.Hom.Hom F G)`. `objMap` is a non-dependent
   `Pi` and is decided by the existing instance; `map` has a type
   mentioning `objMap`, so its comparison follows a transport along
   that equality. The `Bool`-equation fields are proof-irrelevant and
   contribute no obligation.
3. `DecidableEq FinCat`: decide `objCount`, transport, decide
   `nonIdCount`, transport, decide `comp`.

`Repr` instances at all three levels render the count matrix and the
composition table as nested naturals, through `Vector.ofFnC`
(`Geb/Mathlib/Data/Vector/OfFn.lean`) and `Fin.val`. `Repr` requires no
transport at any level: it maps out of the dependent structure into
`Format`, discarding the types whose disagreement obstructs equality.

## Axiom hygiene

The target is that every module of this workstream is choice-free, so
that `GebMeta.classicalAllowedModules` gains no entries.

Two candidates for taint are known and are to be resolved by
measurement, not assumption.

- `FinCat.instFinCategory`. `CategoryTheory.FinCategory` is declared
  inside a `noncomputable section`, but the class itself is a pair of
  `Fintype` fields, and the intended witnesses — `Fin.fintype` and
  `ULift.fintype` — are choice-free. mathlib's
  `FinEnum → Fintype` bridge is not to be used, its `complete` field
  being closed by `simp`.
- `FinCat.bicategory` and `FinCat.bicategory.strict`.
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` records that
  `CategoryTheory.Cat.category` depends on `Classical.choice`, and
  that instance is obtained from `Cat.bicategory` through
  `StrictBicategory.category`. The default field values of
  `CategoryTheory.Bicategory`, discharged by `cat_disch`, are
  therefore a candidate source.

Should measurement show a taint, the modules added to
`GebMeta.classicalAllowedModules` are exactly those that package —
`Geb.Mathlib.CategoryTheory.FinCat.Category` or
`Geb.Mathlib.CategoryTheory.FinCat.Bicategory`, with their test
parallels — and no module in which a definition or a proof of this
workstream's own content resides. Where a taint is confirmed, the
affected instance is moved into a module of its own so that the
allowlisted surface is one instance rather than one file of mixed
content.

## File layout

```text
Geb/Mathlib/CategoryTheory/FinCat.lean             index
Geb/Mathlib/CategoryTheory/FinCat/Basic.lean       specification, identity,
                                                   total composition, checker,
                                                   reflection lemma
Geb/Mathlib/CategoryTheory/FinCat/Category.lean    object type, Category,
                                                   FinCategory
Geb/Mathlib/CategoryTheory/FinCat/Hom.lean         functor specifications,
                                                   checker, toFunctor
Geb/Mathlib/CategoryTheory/FinCat/Hom2.lean        2-cell specifications,
                                                   checker, toNatTrans
Geb/Mathlib/CategoryTheory/FinCat/Bicategory.lean  Bicategory, Strict
Geb/Mathlib/CategoryTheory/FinCat/Decidable.lean   DecidableEq, layers 1-3
Geb/Mathlib/CategoryTheory/FinCat/Repr.lean        Repr
```

together with one added instance in `Geb/Mathlib/Data/FinEnum.lean` and
a mirroring `GebTests/Mathlib/CategoryTheory/FinCat/` tree.

The names follow `CategoryTheory.Cat`: the specification type is
`FinCat`, its 1-cells are `FinCat.Hom` — as `Cat.Hom` is likewise a
one-field bundling of the notion it names — and its 2-cells are the
homs of `FinCat.Hom.instCategory`.

`Geb/Mathlib/CategoryTheory/FinCat/Basic.lean` imports only
`Mathlib.CategoryTheory.Category.Basic`,
`Geb.Mathlib.Data.FinEnum` and core `Fin` material, so that the
specification type and its checker are usable without the mathlib
category-theory hierarchy.

## Verification obligations

Discharged during implementation, before the corresponding artifact is
claimed complete.

1. `FinCat.instFinCategory` is choice-free, or is isolated and
   allowlisted.
2. `FinCat.bicategory` and `FinCat.bicategory.strict` are choice-free,
   or are isolated and allowlisted.
3. `assocCheck` reduces in the kernel on each worked example, so that
   `rfl` discharges the validity field without `decide` and without
   `native_decide`. `native_decide` is excluded: it introduces
   `Lean.ofReduceBool`, which the axiom linter rejects.
4. The reduction of general associativity to client-triple
   associativity holds as stated, including the case in which a
   composite of two client morphisms is an identity.
5. `Fin.castLE` is index-preserving definitionally, so that `emb` needs
   no simp lemma to compute on literals.

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

A negative test asserts `assocCheck … = false` on a specification
violating associativity, so that the checker is shown to reject as well
as accept.

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
validity checkers gains a note that `assocCheck` is bounded by the cube
of the non-identity morphism count, the reserved-identity convention
having removed the identity cases from the quantifier.

## References

- [CONTRIBUTING.md](../../../CONTRIBUTING.md) — contributor rules.
- [docs/process.md](../../process.md) — rationale for the rules.
- [JohnsonYau2021] Johnson and Yau, *2-Dimensional Categories*, Oxford
  University Press, 2021; arXiv:2002.06055.
