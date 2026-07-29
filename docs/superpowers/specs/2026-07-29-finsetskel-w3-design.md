# Spec: W3 — the topos structure other than coequalizers

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Decisions fixed here](#decisions-fixed-here)
- [Transcription and novelty](#transcription-and-novelty)
- [How axioms are measured](#how-axioms-are-measured)
- [Findings](#findings)
  - [Confirmed from the umbrella spec at the current revision](#confirmed-from-the-umbrella-spec-at-the-current-revision)
  - [The `Nat` division and order API is choice-taint-interleaved](#the-nat-division-and-order-api-is-choice-taint-interleaved)
  - [A choice-free product equivalence exists](#a-choice-free-product-equivalence-exists)
  - [The exponential recursion is choice-free end to end](#the-exponential-recursion-is-choice-free-end-to-end)
  - [`Equiv`'s domain transport is choice-tainted](#equivs-domain-transport-is-choice-tainted)
  - [`LawfulBEq` at `Fin n` is choice-tainted; W4 repairs it by supply](#lawfulbeq-at-fin-n-is-choice-tainted-w4-repairs-it-by-supply)
  - [The classifier consumes the W1 inversion](#the-classifier-consumes-the-w1-inversion)
  - [Row m is the adapter between `Mono` and the inversion](#row-m-is-the-adapter-between-mono-and-the-inversion)
  - [Every route through `incl` is choice-tainted](#every-route-through-incl-is-choice-tainted)
  - [The cartesian structure already supplies three `Prop` classes](#the-cartesian-structure-already-supplies-three-prop-classes)
  - [W1's index-function correspondence is not an `Equiv` and is `ULift`ed](#w1s-index-function-correspondence-is-not-an-equiv-and-is-ulifted)
  - [`truth` is index 1](#truth-is-index-1)
- [Shared declarations](#shared-declarations)
- [Module layout](#module-layout)
- [Exported names](#exported-names)
- [Deliverables](#deliverables)
  - [Rows a and b — the initial and terminal objects](#rows-a-and-b--the-initial-and-terminal-objects)
  - [Row c — binary coproducts](#row-c--binary-coproducts)
  - [Row d — binary products](#row-d--binary-products)
  - [Row e — finite coproducts](#row-e--finite-coproducts)
  - [Row g — exponentials](#row-g--exponentials)
  - [Row h — binary equalizers](#row-h--binary-equalizers)
  - [Row l — the subobject classifier](#row-l--the-subobject-classifier)
  - [Row m — monomorphisms](#row-m--monomorphisms)
  - [Tests](#tests)
  - [Documentation](#documentation)
- [Amendments to `TODO.md`](#amendments-to-todomd)
- [Out of scope](#out-of-scope)
- [Verification obligations](#verification-obligations)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope of this document

W3 of the workstream group whose roadmap is `TODO.md` § FinSetSkel as
an elementary topos. That entry is authoritative for the group: the
dependency order, the operation table, the class fields, the nine
cross-workstream interface constraints and the standing obligations
are read from it and are not restated here except where this document
amends them.

W3 delivers rows a, b, c, d, e, g, h, l and m of the operation table:
the initial and terminal objects, binary coproducts and products,
finite coproducts, exponentials, binary equalizers, the subobject
classifier, and the characterisation of monomorphisms. Rows f and j
are dropped rather than delivered; see § The cartesian structure
already supplies three `Prop` classes. Row i is W4's; row k and the
`ElementaryTopos FinSetSkel` instance are W5's.

This document is transient, per `CONTRIBUTING.md` § Concern shape. It
records the decisions W3 fixes for W5, the findings supporting them,
and the amendments W3 makes to `TODO.md`. What persists after the
branch is the Lean content and its `docs/index.md` entry.

Every finding below was measured at the repository's current mathlib
revision, `v4.33.0-rc1`, through the `lean-lsp` MCP. Findings inherited
from the umbrella spec (added and removed on branch
`docs/finsetskel-topos-roadmap`, `jj` change
`nkwoqxwytsvrlpnsklzzlzkxtovyxkzm`) were re-measured rather than
carried, and this document corrects three of them.

## Decisions fixed here

1. The exponential encoding is built by recursion on the arity over
   the product encoding, not by direct base-`n` digit arithmetic. The
   recursion is an explicit `Nat.rec` at the motive
   `fun k ↦ (Fin k → Fin y) ≃ Fin (y ^ k)`, per
   `docs/rules/lean-coding.md` § Recursion and induction through
   recursors, which forbids a self-calling `def` and `termination_by`.
2. The two choice-free `Equiv`s live in
   `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean`, mirroring where mathlib
   states `finProdFinEquiv`. The three `Fin` operations beneath them
   go to `Geb/Mathlib/Data/Fin/Basic.lean` instead: `Fin.divNat` and
   `Fin.modNat` are Lean core declarations, not mathlib ones, so that
   is where their choice-free counterparts mirror.
3. The carrier-level `simp` normal form is the named operations
   `Fin.pairC`, `Fin.divNatC`, `Fin.modNatC`, `Fin.funEncodeC` and
   `Fin.funDecodeC`, and the `@[simp]` lemmas are stated over those
   names rather than over the `Equiv`s. The two cases differ beneath
   that. For the product the three operations are primitive and
   `finProdFinEquivC` is assembled from them. For the exponential the
   `Nat.rec` of decision 1 produces the equivalence first, and it is
   named `finFunctionFinEquivC` directly; `funEncodeC` and
   `funDecodeC` are its `toFun` and `invFun`. No auxiliary
   equivalence is introduced beneath it.
4. Row m is proved directly over vectors, because every route through
   `incl` is choice-tainted and the umbrella spec's § W3 places row m
   in the choice-free layer.
5. `Ω` is the object of length 2, `truth` picks index `1`, and `χ`
   sends members of the subobject to `1`.
6. W3 splits into seven choice-free construction modules and four
   allowlisted wrapper modules. A wrapper is not necessarily
   packaging: `Exponential/Closed.lean` and `Classifier/Instance.lean`
   each carry content that cannot be stated choice-free.
7. Equality at `Fin n` is decided through the axiom-free
   `DecidableEq (Fin n)`. W3 needs no `LawfulBEq (Fin n)` and supplies
   none; the taint in that class is recorded as a finding for W4,
   which does need it.
8. Transport of a function type along an equivalence of its domain
   uses `Equiv.arrowCongrLeftC`, supplied by this group, never
   mathlib's `Equiv.arrowCongr` or the `piCongrLeft` family.
9. The declaration named in decision 8 is shared with W4 and lives on
   a branch off `main`, not on W3's branch; see § Shared declarations.
   Nothing else W3 introduces is shared.
10. `FinSetSkel.cartesianMonoidalCategory` is a global `instance`, not
    a `def` in W2's style; see § The cartesian structure already
    supplies three `Prop` classes.

## Transcription and novelty

Per `CONTRIBUTING.md` § Cite the literature when transcribing.

The mathematical content is a transcription: that the category of
finite sets is an elementary topos is classical, and the axiomatisation
W3's rows populate is [Freyd1972], already carried in
`docs/references.bib` by W2. The arithmetic bijections `Fin m × Fin n ≃
Fin (m * n)` and `(Fin m → Fin n) ≃ Fin (n ^ m)` are likewise standard,
and mathlib states both — `finProdFinEquiv` and `finFunctionFinEquiv`.

What is novel is only the presentation: the vector representation of
the morphisms (fixed by W1), and the choice-free construction of the
two encodings, which mathlib's versions are not. A choice-free proof
of a classical statement is a change of proof, not of theorem, so no
further citation is owed. W3 adds no `docs/references.bib` entry.

If the classifier's module docstring is to cite a textbook locator for
the subobject classifier beyond [Freyd1972], the standing obligation on
the skeleton locator applies to it: the locator is verified against the
primary source, not against a secondary attestation. The default is to
cite [Freyd1972] alone and add nothing.

The `C` suffix on `Fin.pairC`, `finProdFinEquivC`,
`Equiv.arrowCongrLeftC` and their siblings marks a choice-free
rebuild. It is W1's convention, not mathlib's, and mathlib's naming
guide has no such affix. These declarations are renamed at upstream
submission; the suffix is a local marker for the duration.

## How axioms are measured

`#print axioms` on a polymorphic constant measures the constant, not
any instantiation of it. Instance arguments are not part of what it
reports, so a constant with hypothesis `[LawfulBEq α]` can measure
`[propext]` while every use of it at `Fin n` collects
`Classical.choice` through the instance. The same holds for a functor
argument: `Functor.mono_map_iff_mono` depends on no axioms, and its
use at `FinSetSkel.incl` inherits that functor's taint.

The rule this document and the plan follow, stated in the one
direction in which it holds. It is also `TODO.md` constraint 9's, by
amendment 1, so it binds W4 and W5 equally:

> A measurement of a library constant in isolation does not establish
> that a declaration applying it is *clean*. Taint transfers upward —
> a consumer of a choice-dependent constant is choice-dependent — but
> cleanliness does not, because instance and functor arguments the
> measurement did not see may carry their own. A claim that something
> is choice-free is made only from a monomorphic `def` at the types
> and instances actually used.

A second rule, of the same kind but about scope rather than
instantiation:

> Each construction is measured whole. Measuring its named
> ingredients is not sufficient, because the combinator that
> introduces an axiom may be one the construction was never described
> as using.

## Findings

### Confirmed from the umbrella spec at the current revision

| Claim | Measurement |
| --- | --- |
| `finSumFinEquiv` is choice-free | `[propext, Quot.sound]` |
| `finProdFinEquiv` depends on `Classical.choice` | `[propext, Classical.choice, Quot.sound]` |
| `finFunctionFinEquiv` depends on `Classical.choice` | same |
| `Fin.divNat` depends on `Classical.choice` | same |

`finFunctionFinEquiv` is stated `(Fin n → Fin m) ≃ Fin (m ^ n)`, so the
exponential of the object of length `m` into the object of length `n`
is the object of length `n ^ m`, as the operation table's row g says.

`CartesianMonoidalCategory.ofChosenFiniteProducts` takes a
`LimitCone (Functor.empty C)` and a family
`(X Y : C) → LimitCone (pair X Y)`, so the cartesian structure reduces
to rows b and d with no associator, unitor or coherence obligation. It
depends on `Classical.choice`, as does the class it inhabits.

`Subobject.Classifier.mkOfTerminalΩ₀` takes `Ω₀`, a proof that `Ω₀` is
terminal, `Ω`, `truth`, the family `χ`, the pullback property and the
uniqueness property.

`Adjunction.adjunctionOfEquivRight` takes an object map, a family of
hom-level equivalences and one naturality equation, and returns the
adjunction. `Closed X` has exactly `rightAdj : C ⥤ C` and
`adj : tensorLeft X ⊣ rightAdj`; `MonoidalClosed C` has exactly
`closed : (X : C) → Closed X`. Row g therefore constructs no functor,
unit, counit or triangle identity by hand.

### The `Nat` division and order API is choice-taint-interleaved

The two lemmas that state the bounds row d needs directly are both
choice-tainted, and their immediate neighbours are not.

| Lemma | Axioms |
| --- | --- |
| `Nat.div_lt_of_lt_mul` | `propext`, `Classical.choice`, `Quot.sound` |
| `Nat.lt_of_mul_lt_mul_left` | `propext`, `Classical.choice`, `Quot.sound` |
| `Nat.div_mul_le_self` | `propext` |
| `Nat.add_mul_div_right` | `propext` |
| `Nat.div_add_mod'` | `propext` |
| `Nat.add_mul_mod_self_right` | `propext` |
| `Nat.div_eq_of_lt` | `propext` |
| `Nat.mod_eq_of_lt` | `propext` |
| `Nat.mod_lt` | none |
| `Nat.mul_le_mul_right` | none |
| `Nat.lt_of_le_of_lt` | none |
| `Fin.ext` | none |

Neither the name nor the namespace separates the two sets, and unlike
the `Vector.ofFn` family named in constraint 9 there is no closed list
to state. The route around them is `omega` over hypotheses named
individually, or case analysis on `Nat.lt_or_ge`; both are choice-free.
`Nat.add_comm` and `Nat.zero_add` are used alongside them.

This is constraint 9's general shape one level below where the
constraint states it, and it applies to W4 as well as W3: W4's fold
discharges `Fin self.size` obligations through the same API.

`GebMeta.detectNonstandardAxiom` rejects a violation at `lake lint`, on
CI and in the pre-push check, so a violation is caught rather than
silent. The linter reports the axiom, not the ingredient that
introduced it, and locating the ingredient is the costly step; the
record shortens it.

### A choice-free product equivalence exists

The roadmap states that W3 owes choice-free replacements without
establishing that they exist. They do. The following elaborated at
`[propext, Quot.sound]`.

```lean
def Fin.divNatC {m n : ℕ} (i : Fin (m * n)) : Fin m :=
  ⟨i / n, by
    rcases Nat.lt_or_ge ((i : ℕ) / n) m with h | h
    · exact h
    · have h3 : (i : ℕ) / n * n < m * n :=
        Nat.lt_of_le_of_lt (Nat.div_mul_le_self i n) i.isLt
      have h5 : m * n ≤ (i : ℕ) / n * n := Nat.mul_le_mul_right n h
      omega⟩

def Fin.modNatC {m n : ℕ} (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ (by
    have h := i.isLt
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · omega
    · exact hn)⟩

def Fin.pairC {m n : ℕ} (a : Fin m) (b : Fin n) : Fin (m * n) :=
  ⟨a * n + b, by
    have h1 : ((a : ℕ) + 1) * n ≤ m * n := Nat.mul_le_mul_right n a.isLt
    have h2 : ((a : ℕ) + 1) * n = a * n + n := by rw [Nat.add_mul, Nat.one_mul]
    have h3 := b.isLt
    omega⟩
```

with `divNatC_pairC`, `modNatC_pairC` and `pairC_divNatC_modNatC`
proved by `Fin.ext` followed by `change` and the `propext`-only
division lemmas above, and `finProdFinEquivC` assembled from those six.
The three round trips carry `@[simp]`. The assembled equivalence was
measured at `[propext, Quot.sound]`.

The names do not clash: `Fin.divNat` and `Fin.modNat` occupy the
unsuffixed names, and a search of mathlib finds none of the seven
suffixed names this section introduces, nor the five § Row g adds. That the
definitions elaborated in a probe without a duplicate-declaration
error is weaker evidence than it appears — a probe sees only its own
imports — so the check the plan runs is
`#check @Fin.pairC` and its siblings under each module's actual import
set.

### The exponential recursion is choice-free end to end

The recursion was built whole and measured. All three parts are
choice-free.

| Declaration | Axioms |
| --- | --- |
| base case, `(Fin 0 → Fin y) ≃ Fin (y ^ 0)` | `propext`, `Quot.sound` |
| successor step | `propext`, `Quot.sound` |
| the whole `Nat.rec` | `propext`, `Quot.sound` |

| Ingredient | Axioms |
| --- | --- |
| `Fin.consEquiv` | `propext`, `Quot.sound` |
| `Equiv.trans` | `Quot.sound` |
| `Equiv.prodCongr` | `propext`, `Quot.sound` |
| `Equiv.equivPUnit` | none |
| `finOneEquiv` | `propext` |
| `finCongr` | none |
| `Nat.pow_succ`, `Nat.pow_succ'` | none |

`Equiv.piFinSucc` does not exist at this revision; `Fin.consEquiv` is
the declaration stating
`α 0 × ((i : Fin n) → α i.succ) ≃ ((i : Fin (n + 1)) → α i)`.

`Equiv.funUnique` cannot serve the base case: `Unique (Fin 0)` does not
exist, `Fin 0` being empty rather than a singleton. The base case is
`(Fin 0 → Fin y) ≃ Fin (y ^ 0)`, whose left side is a singleton
because its *domain* is empty. The route that elaborates is
`Equiv.equivPUnit` on the function type, then `finOneEquiv.symm`, then
`finCongr (Nat.pow_zero y).symm`, the last because instance search will
not reduce `y ^ 0` to `1` at reducible transparency.

The successor step is `(Fin.consEquiv _).symm`, then
`Equiv.prodCongr (Equiv.refl _)` at the inductive hypothesis, then
`finProdFinEquivC`, then `finCongr (Nat.pow_succ' ..).symm`.

The direct base-`n` digit encoding, mirroring mathlib's
`finFunctionFinEquiv`, was rejected: its round trips run through
`Finset.sum` lemmas, each a separate choice audit against the
interleaving above, and mathlib's version of that construction is the
one that measured tainted.

### `Equiv`'s domain transport is choice-tainted

Row g transports a function type along an equivalence of its domain.
Every mathlib combinator doing so depends on `Classical.choice`; those
transporting the codomain do not.

| Combinator | Transports | Axioms |
| --- | --- | --- |
| `Equiv.arrowCongr` | domain and codomain | `propext`, `Classical.choice`, `Quot.sound` |
| `Equiv.arrowCongr'` | domain and codomain | `propext`, `Classical.choice`, `Quot.sound` |
| `Equiv.piCongrLeft` | domain | `propext`, `Classical.choice`, `Quot.sound` |
| `Equiv.piCongrLeft'` | domain | `propext`, `Classical.choice`, `Quot.sound` |
| `Equiv.piCongr` | domain and codomain | `propext`, `Classical.choice`, `Quot.sound` |
| `Equiv.piCongrRight` | codomain | `propext`, `Quot.sound` |
| `Equiv.curry` | — | `Quot.sound` |
| `Equiv.piComm` | — | none |
| `Equiv.ulift` | — | none |
| `Equiv.refl`, `Equiv.symm` | — | none |

The row-g composite stated with `Equiv.arrowCongr` measures
`[propext, Classical.choice, Quot.sound]`. With the replacement below
it measures `[propext, Quot.sound]`, and the replacement measures
`[Quot.sound]`:

```lean
def Equiv.arrowCongrLeftC {α : Sort u} {β : Sort v} {γ : Sort w}
    (e : α ≃ β) : (α → γ) ≃ (β → γ) where
  toFun g := g ∘ e.symm
  invFun h := h ∘ e
  left_inv g := funext fun a ↦ congrArg g (e.left_inv a)
  right_inv h := funext fun b ↦ congrArg h (e.right_inv b)
```

Three independent `Sort` levels, matching the polymorphism of
`Equiv.arrowCongr` which it replaces, per
`docs/rules/lean-coding.md` § Structure and typeclass patterns. The
maximally polymorphic form was measured at `[Quot.sound]`.

At least two independent levels are required. Its other use,
`homEquivIdxFun` below, applies it at
`α = ULift.{u} (Fin X.len) : Type u` and `β = Fin X.len : Type 0`,
which a signature over a single `Type u` does not admit. The third
level is not forced by either use — `γ` sits at `α`'s level in one and
at `Type 0` in the other — and is taken under
`docs/rules/lean-coding.md` § Structure and typeclass patterns, "make
universe levels as polymorphic as compiles", which also matches the
polymorphism of the `Equiv.arrowCongr` this replaces. The three
`universe` variables are declared explicitly; `autoImplicit` is off
repository-wide, so they do not auto-bind.

Only domain transport is needed, so only it is supplied; a two-sided
`arrowCongrC` is not measured and not in scope.

W4 needs this declaration too: renumbering union-find roots onto an
initial segment is a domain transport. It is therefore shared; see
§ Shared declarations.

### `LawfulBEq` at `Fin n` is choice-tainted; W4 repairs it by supply

The instance search finds for `LawfulBEq (Fin n)` is choice-tainted,
and everything stated over that class inherits it. W3 does not consume
it, for the reason given below; the finding is recorded because it
applies to W4 and belongs in constraint 9.

| Instantiation at `Fin n` | Resolved instance | Axioms |
| --- | --- | --- |
| `BEq (Fin n)` | `instBEqOfDecidableEq` | none |
| `DecidableEq (Fin n)` | — | none |
| `LawfulBEq (Fin n)` | `Std.LawfulBEqOrd.lawfulBEq` | `propext`, `Classical.choice`, `Quot.sound` |
| `l.contains j` at `List (Fin n)` | `List.elem`, `BEq` only | none |

The repair is to supply a choice-free instance, not to restate each
operation over the weaker class. Three lines over the
`DecidableEq`-derived `BEq` measured axiom-free, and with it pinned at
raised priority the `∈` form and the `List.contains_iff_mem` bridge
both measured `[propext]`:

```lean
instance (priority := 2000) (n : ℕ) : LawfulBEq (Fin n) where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
```

W3 does not consume this. Its only candidate was row l's
characteristic vector written as
`Vector.ofFnC (fun j ↦ if m.toVec.toList.contains j then 1 else 0)`,
and § Row l rejects that form on complexity grounds and scatters
instead, which uses `Vector.replicate` and `Vector.set` and no `BEq`.
Nothing else in W3 decides membership: row h's predicate is
`decide (_ = _)` over `DecidableEq (Fin n)`, and row l's remaining
statements are `Prop`-level `∈` throughout.
`List.Nodup.getEquivC` fixes its `BEq` at its own elaboration under
`[DecidableEq α]`, so instantiating W1's declarations at `Fin n`
performs no `LawfulBEq (Fin n)` search.

The finding is recorded because it applies to W4, which compares
union-find roots at `Fin self.size`, and because constraint 9 is
where such things live. W4 supplies and pins the instance in its own
module; it is not a shared declaration, W3 having no use for it.

Pinning it disturbs nothing else. With the instance in scope,
`DecidableEq (Fin n)` still resolves axiom-free, W1's deliberately
pinned morphism `DecidableEq` still measures `[propext, Quot.sound]`,
and `decide (f = g)` on morphisms measures the same. `LawfulBEq` is
`Prop`-valued, so the declaration is a `theorem`-shaped instance and
two inhabitants are propositionally equal; the axiom set still follows
the term instance search returns, which is why the priority matters.

This is constraint 9's closing-paragraph shape with one addition: the
choice-free term does not already exist to be named, so the module
supplies it. W1's pinning of morphism `DecidableEq` away from
`instDecidableEqOfLawfulBEq` is the same link one level down.

### The classifier consumes the W1 inversion

The umbrella spec's § Inverting an injective vector states that the
classifier "is not a third consumer at the data level", on the ground
that the fields which would use an inverse, `isPullback` and `uniq`,
are `Prop`. That is a correct statement about the fields and an
incorrect conclusion about the construction.

`IsPullback` bundles `Nonempty (IsLimit …)`, so the lift never runs;
what the umbrella spec's phrase most naturally denies is evaluation,
and on that reading it is right. The claim W3 makes is narrower: the
lift is a morphism somebody has to *author*, and the only construction
available for it is `Vector.invOfInjective`. For a mono `m : U ⟶ X`
and a
morphism `z : Z ⟶ X` whose image lies in that of `m`, the lift
`Z ⟶ U` is the inverse of `m` on its image, applied pointwise, which
is `Vector.invOfInjective`; its uniqueness follows from `Mono m`.

Row h does not consume it. The umbrella spec assigns the equalizer
"the inverse of the canonical injection", but row h builds its own
inverse vector directly, for the complexity reason § Row h gives, so
it needs no general inversion apparatus at all.

W3's single consumer of `Vector.invOfInjective` is therefore row l, not
row h. That conclusion rests on row h's construction rather than on any
correction to the umbrella spec.

`uniq` is a second correction to the same section, in the other
direction. Its statement is
`∀ (χ' : X ⟶ Ω), IsPullback m (t.from U) χ' truth → χ' = χ m`. The
direction giving `χ' j = 1` on the image of `m` follows from the
square's commutation; the direction giving `χ' j = 0` off the image
uses the pullback's universal property, taking the point of `X` at `j`,
obtaining a lift through `m`, and contradicting non-membership. That
argument mentions `IsPullback` and cannot be stated choice-free. W3
splits it: the core states uniqueness over the vector-level hypothesis
`χ'.toVec.get j = 1 ↔ j ∈ m.toVec.toList`, from which `Fin 2` case
analysis gives the conclusion, and the wrapper derives that hypothesis
from `IsPullback`. The derivation is a named deliverable of the
wrapper, not packaging.

### Row m is the adapter between `Mono` and the inversion

`Vector.invOfInjective` has hypothesis `Function.Injective ι.get`. Row
m's statement is that predicate, for `ι = m.toVec`. Row l's interface
supplies `[Mono m]` and nothing else, so row m converts the one into
the other; it is a prerequisite of row l rather than a free-standing
characterisation. `TODO.md` § Class fields records rows e, f and m as
prerequisites rather than field sources, and this is the mechanism
for m.

### Every route through `incl` is choice-tainted

The operation table offers row m two routes: directly over vectors, or
"through `SimplexCategory.mono_iff_injective` and W1's `incl`".

The named lemma is not the applicable one.
`SimplexCategory.mono_iff_injective` exists, at
`Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:623`, but it
concerns `SimplexCategory`, whose morphisms are monotone maps between
finite linear orders, and `incl` lands in `FintypeCat`. The lemma the
route would use is
`ConcreteCategory.mono_iff_injective_of_preservesPullback`
(`Mathlib/CategoryTheory/ConcreteCategory/EpiMono.lean:162`), whose
hypothesis at `FintypeCat` is derived from
`PreservesFiniteLimits (forget FintypeCat)`
(`Mathlib/CategoryTheory/Limits/FintypeCat.lean:67`, which is
`noncomputable`).

The route therefore exists. It is not choice-free, and the reason is
neither the taint of that lemma nor the taint of
`CategoryTheory.Equivalence` — both hold and neither is operative.
`FinSetSkel.incl` is itself `[propext, Classical.choice, Quot.sound]`,
so every route through it is tainted whatever lemma is applied. It is
defined in the allowlisted `Skeleton.lean`, which is why the linter
permits it there and not why it depends on choice.
`Functor.mono_map_iff_mono` depending on no axioms does not change
this, per § How axioms are measured.

The operation table's own text says this route "lands the row in W3's
wrapper", which is correct. W3 takes the direct route because the
umbrella spec's § W3 places row m in the choice-free layer, where only
the direct route is available. The forward direction tests `f` against
two morphisms out of a one-element object; the reverse is `hom_ext`.

### The cartesian structure already supplies three `Prop` classes

`Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean:498` registers
`instance (priority := 100) : HasFiniteProducts C` for
`[CartesianMonoidalCategory C]`. Elaborating `inferInstance` at
`[Category.{0} C] [CartesianMonoidalCategory C]` resolves all three of
`HasFiniteProducts C`, `HasTerminal C` and `HasBinaryProducts C`.

So row f's `hasFiniteProducts_of_has_binary_and_terminal`, and
separate `HasTerminal` and `HasBinaryProducts` registrations, restate
what the cartesian instance provides.

Row j has no consumer. `HasFiniteLimits` is not a field of
`ElementaryTopos`; W2 derives it from the class; and W5's row k needs
`HasFiniteCoproducts` and `HasCoequalizers`, not it. `TODO.md`
§ Class fields states the general form: "rows e, j and k are W2's
one-time derivations, and W3's and W5's assignments become redundant."

Row e is retained on constraint 5, which instructs W3 to register what
a later workstream consumes and names `HasFiniteCoproducts` by row.
That is a standing instruction of the roadmap, and `TODO.md` § Class
fields' remark that rows e, j and k become redundant does not withdraw
it — it says W2 derives them, which is a statement about availability
once `[ElementaryTopos FinSetSkel]` exists, and that instance is W5's
output rather than an input to it. The cost is one `Prop` instance.
Rows f and j carry no such instruction and are dropped.

Rows f and j are dropped, and
`HasTerminal` and `HasBinaryProducts` are not separately registered.
"Redundant `Prop` instances are harmless by proof irrelevance" answers
a correctness objection; it does not answer `CONTRIBUTING.md` § Code is
cost, which is the operative rule.

This turns on `FinSetSkel.cartesianMonoidalCategory` being a global
`instance`, so the priority-100 registration fires; the same is needed
for `X ⊗ Z` to elaborate in `Exponential/Closed.lean`. Decision 10
fixes that. W2's opposite convention — `@[instance_reducible] def`
plus `attribute [local instance]` — applies to accessors *from*
`[ElementaryTopos C]`, where two routes to data need not agree; here
there is one term and it is the definition. W5 holds both: it must
apply W2's `attribute [local instance]` and will then have two paths
to the same class. They agree, W5's `cartesian` field being this term
by name (§ Exported names), but W5's plan should expect the diamond.

### W1's index-function correspondence is not an `Equiv` and is `ULift`ed

Rows c, d, g and h state their universal properties over index
functions `Fin X.len → Fin Y.len`, while `ofChosenFiniteProducts`,
`adjunctionOfEquivRight` and `LimitCone` consume `X ⟶ Y`. W1 exports
`ofIdxFun` and `toIdxFun` (`Basic.lean:206,217`) with both round trips,
but over `ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)`, and exports
no `Equiv`.

Rows c, d, g and h therefore need
`FinSetSkel.homEquivIdxFun : (X ⟶ Y) ≃ (Fin X.len → Fin Y.len)`.
Rows l and m do not: row m's statement is over `f.toVec.get` and row
l's core over `m.toVec` and `χ'.toVec.get`, neither mentioning an
index function. Whether `Classifier/Core.lean` imports it is settled
per module by the plan under the unused-import test, not assumed here. It is
`homEquivIdxFunU.trans ((Equiv.arrowCongrLeftC Equiv.ulift).trans
(Equiv.piCongrRight fun _ ↦ Equiv.ulift))`, where `homEquivIdxFunU`
packages W1's two round trips; both were built and measured at
`[propext, Quot.sound]`. Note that it consumes `Equiv.arrowCongrLeftC`,
so `Shapes/Core.lean` depends on `feat/choice-free-primitives` as well
as on `Logic/Equiv/Fin/Basic.lean`.

It stays a W3 deliverable in `Shapes/Core.lean` rather than moving to
the shared branch. W4's session states that row i does not need it.
That is W4's claim about W4's design and is not verifiable from this
branch, so it is carried as an assumption. The plan confirms it by
reading W4's spec on W4's branch — not by waiting for W4 to merge,
which would invert the independence `TODO.md` § Workstreams gives the
two and defeat the purpose of the shared branch. Should the assumption
fail, `homEquivIdxFun` moves to a new
`Geb/Mathlib/CategoryTheory/FinSetSkel/Hom.lean` on
`feat/choice-free-primitives`, and § Shared declarations, § Module
layout and the artifact counts change with it.

### `truth` is index 1

Two locators bear directly on the orientation.

| Location | Statement |
| --- | --- |
| `Mathlib/Logic/Equiv/Defs.lean:910` | `finTwoEquiv` is `toFun i := i == 1`, `invFun b := bif b then 1 else 0` |
| `Mathlib/CategoryTheory/Topos/Sheaf.lean:57,172` | `Presheaf.truth` and `Sheaf.truth`, the two classifier instances mathlib builds, both pick the maximal sieve |

Surrounding conventions agree without being evidence of the same kind:
`Bool` has `top := true`, `Prop` has `Prop.top_eq_true`, and the usual
indicator function takes the value `1` on the set. The order on `Fin 2`
and the Heyting order on `Ω` then agree rather than oppose, `0 < 1`
matching `⊥ < ⊤`.

The consequence is about rewriting rather than semantics. With
`truth = 1`, `χ m` is the indicator of membership and every bridge to
`Bool`, `decide` or `Prop` is `finTwoEquiv` composed with nothing.
With `truth = 0` each such bridge carries a negation, and normal forms
on the two sides of it no longer match.

W3 does not route `χ` through `finTwoEquiv`; the literal `1` is
simpler, and the equivalence remains available to a later workstream
wanting the `Bool` bridge.

## Shared declarations

One declaration is consumed by both W3 and W4:
`Equiv.arrowCongrLeftC`. Constraint 7 places what W3 and W4 share on
its own branch off `main`, which both rebase onto, so that neither
waits for the other to merge.

That branch is `feat/choice-free-primitives`. It carries:

| Item | File |
| --- | --- |
| the constraint 9 amendment | `TODO.md` |
| `Equiv.arrowCongrLeftC` | `Geb/Mathlib/Logic/Equiv/Basic.lean` (existing, amended) |

It also amends that module's existing parallel
`GebTests/Mathlib/Logic/Equiv/Basic.lean` and the module's existing
`docs/index.md` entry. The module is choice-free and does not reach
`GebMeta.classicalAllowedModules`. The branch currently carries the
`TODO.md` amendment alone; the declaration is not written yet. This
document is that branch's artifact for the duration, per
`CONTRIBUTING.md` § Each phase produces an artifact, and governs its
contents. The branch is merged before W3's implementation begins and
is not part of W3's own module count or deliverables below.

The pinned `LawfulBEq (Fin n)` of § `LawfulBEq` at `Fin n` is *not*
here. W3 has no consumer for it, so by constraint 7's own test it is
not shared; W4 supplies it in its own module. `Geb/Mathlib/Data/Fin/`
is created by W3, for the three `Fin` operations, not by this branch.

## Module layout

Per constraint 8: constructions and the content of their universal
properties choice-free over vectors and `Fin`; mathlib structures and
`Prop` instances in wrappers over them. A wrapper may carry content
that cannot be stated choice-free, and two of W3's do.

| Module | Rows | Layer |
| --- | --- | --- |
| `Geb/Mathlib/Data/Fin/Basic.lean` | beneath d, g | choice-free |
| `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean` | beneath g | choice-free |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Core.lean` | a b c d | choice-free |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Shapes/Instances.lean` | a b c d e | wrapper |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential/Core.lean` | g | choice-free |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Exponential/Closed.lean` | g | wrapper |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Core.lean` | h | choice-free |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Equalizer/Limits.lean` | h | wrapper |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Mono.lean` | m | choice-free |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Classifier/Core.lean` | l | choice-free |
| `Geb/Mathlib/CategoryTheory/FinSetSkel/Classifier/Instance.lean` | l | wrapper |

The directory is `Shapes/`, not `Products/`: rows a and c are the
initial object and binary coproducts, and a directory named for
products that contains coproducts would not survive extraction to
mathlib, where these live under `Limits/Shapes/`. For the same reason
row l's core has its own module rather than sitting in `Mono.lean`,
whose subject is row m.

Both `Equiv`s share `Logic/Equiv/Fin/Basic.lean`, mirroring
`Mathlib/Logic/Equiv/Fin/Basic.lean`, where `finProdFinEquiv` is
stated. mathlib states `finFunctionFinEquiv` under
`Algebra/BigOperators/Fin.lean` instead, because its construction sums
over a `Finset`; the construction here does not, so that path is not
the right mirror. The repository precedent is
`Geb/Mathlib/Logic/Equiv/Basic.lean`, which mirrors
`Mathlib/Logic/Equiv/Basic.lean` exactly.

`Fin.divNatC`, `Fin.modNatC`, `Fin.pairC` and their three round trips
go elsewhere, to `Geb/Mathlib/Data/Fin/Basic.lean`, a new module. Their
unsuffixed counterparts `Fin.divNat` and `Fin.modNat` are not mathlib
declarations — no `def` for either exists under `Mathlib/`, which only
uses them — so mirroring `Logic/Equiv/Fin/Basic.lean` would place them
where their originals are not. Being core-targeted rather than
mathlib-targeted, that module's upstream destination falls under
`TODO.md` § Upstream destination of core- and Batteries-targeted
content. It brings with it the directory `Geb/Mathlib/Data/Fin/`, the
index file `Geb/Mathlib/Data/Fin.lean`, an amendment to
`Geb/Mathlib/Data.lean`, and the `GebTests/Mathlib/` parallels of
both.

Constraint 7 assigns both encodings to W3; W4 consumes neither.
Constraint 7's parenthetical that each has "a single consumer in W3"
holds of the two `Equiv`s at row level — row g is the only row
consuming either — but not of the three `Fin` operations beneath them,
which rows d and g both consume. Within row g, `finProdFinEquivC` is
used twice: in the arity recursion and at the
`Equiv.arrowCongrLeftC` step of the composite.
The assignment it justifies is unchanged, the operative reason being
that W4 consumes none of the five.

Dependency order within W3, with `feat/choice-free-primitives` and
W1's modules already in place:

```text
Data/Fin/Basic                 (divNatC, modNatC, pairC, 3 round trips)
  → Logic/Equiv/Fin/Basic      (finProdFinEquivC, finFunctionFinEquivC)
  → FinSetSkel/Shapes/Core     (uses Equiv.arrowCongrLeftC;
                                exports homEquivIdxFun, point)
      → FinSetSkel/Mono
          → FinSetSkel/Classifier/Core  (also Data/Vector/NodupEquivFin)
      → FinSetSkel/Exponential/Core     (also Logic/Equiv/Fin/Basic
                                         and Equiv.arrowCongrLeftC)
      → FinSetSkel/Equalizer/Core
      → FinSetSkel/Shapes/Instances
          → FinSetSkel/Exponential/Closed  (also Exponential/Core)
          → FinSetSkel/Classifier/Instance (also Classifier/Core)
FinSetSkel/Equalizer/Limits    (from Equalizer/Core only)
```

`Shapes/Core.lean` uses `Data/Fin/Basic.lean` and not
`Logic/Equiv/Fin/Basic.lean`: row d's projections are
`Fin.divNatC`/`Fin.modNatC`, its lift is `Fin.pairC`, and its
factorisation and uniqueness lemmas are the three round trips — all in
the former. `finProdFinEquivC` is consumed only inside
`Logic/Equiv/Fin/Basic.lean`'s own arity recursion and by
`Exponential/Core.lean`; `finFunctionFinEquivC` only by the latter.
Importing the encodings module into `Shapes/Core.lean` would be the
unused import ruled out below.

`Equiv.arrowCongrLeftC` is consumed by `Shapes/Core.lean`, through
`homEquivIdxFun`, and by `Exponential/Core.lean`, at the first step of
the row-g chain. Neither `Data/Fin/Basic.lean` nor
`Logic/Equiv/Fin/Basic.lean` uses it. The `feat/choice-free-primitives`
ordering constraint therefore binds `Shapes/Core.lean` onward, not the
two encoding modules, which can be written first.

`Exponential/Closed.lean` depends on `Shapes/Instances.lean` and not
only on `Exponential/Core.lean`, because the cartesian instance its
statements mention is declared there. `Classifier/Instance.lean`
depends on `Classifier/Core.lean` and on `Shapes/Instances.lean`, the
latter for the terminal object `Ω₀` and `isTerminalOne`.
`Equalizer/Limits.lean` depends on neither: `LimitCone (parallelPair f g)`
mentions no cartesian or monoidal structure, and an unused import
fails `lake shake`.

`Mono.lean` depends on `Shapes/Core.lean` for `homEquivIdxFun`, which
rows c, d, g and h use, and for `point`. The one-element object needs
no definition, being `FinSetSkel.mk 1`; what row m needs and
`Shapes/Core.lean` supplies is a map *out of* it.

New index files: `Geb/Mathlib/Data/Fin.lean`,
`Geb/Mathlib/Logic/Equiv/Fin.lean`, and
`FinSetSkel/Shapes.lean`, `FinSetSkel/Exponential.lean`,
`FinSetSkel/Equalizer.lean`, `FinSetSkel/Classifier.lean`.
`Geb/Mathlib/Logic/Equiv.lean` and
`Geb/Mathlib/CategoryTheory/FinSetSkel.lean` exist and are amended;
`Geb/Mathlib/Logic.lean` already imports `Geb.Mathlib.Logic.Equiv` and
needs no change. `FinSetSkel.lean` is a W3/W4 conflict point, covered
generically by the standing obligation's "any shared directory index
file" and named there explicitly by amendment 5.

The artifact count is therefore eleven content modules — the eleven in
the table — six new index files
(`Data/Fin.lean`, `Logic/Equiv/Fin.lean`, and the four under
`FinSetSkel/`), a mirrored `GebTests/Mathlib/` parallel for each of
those seventeen, and six amended index files:
`Geb/Mathlib/Data.lean`, `Geb/Mathlib/Logic/Equiv.lean`,
`Geb/Mathlib/CategoryTheory/FinSetSkel.lean` and their three
`GebTests/Mathlib/` parallels.

`Geb/Mathlib/Logic/Equiv/Basic.lean` is amended too, but by
`feat/choice-free-primitives` rather than by W3, and its accounting is
in § Shared declarations.

## Exported names

Constraint 5 requires each row's data term under a stable public name.
W5 assembles the `ElementaryTopos FinSetSkel` instance from these.

| Field of `ElementaryTopos` | W3's exported term |
| --- | --- |
| `cartesian` | `FinSetSkel.cartesianMonoidalCategory` |
| `closed` | `FinSetSkel.monoidalClosed` |
| `initialCocone` | `FinSetSkel.initialCocone` |
| `binaryCoproductCocone` | `FinSetSkel.binaryCoproductCocone` |
| `equalizerCone` | `FinSetSkel.equalizerCone` |
| `classifier` | `FinSetSkel.classifier` |

W2's `closed` field has type
`@MonoidalClosed C _ cartesian.toMonoidalCategory`, so it is well-typed
only when W5's `cartesian` is the same term W3 stated its
`MonoidalClosed` over. `FinSetSkel.monoidalClosed` is therefore stated
over `FinSetSkel.cartesianMonoidalCategory`, and W5 fills `cartesian`
with that same name. The requirement is that W3 declare no second
`CartesianMonoidalCategory FinSetSkel`, so that search within W3
cannot return a different term; under decision 10 there is exactly
one. W5 does hold two paths to the class, W2's accessor and this
instance, but they resolve to the same term — see § The cartesian
structure already supplies three `Prop` classes on the diamond. This
is the single place where two routes to the same data would fail to
typecheck rather than merely diverge.

Further exported terms, not fields but consumed by the fields or by
W5:

| Term | Consumed by |
| --- | --- |
| `FinSetSkel.terminalCone` | `ofChosenFiniteProducts` |
| `FinSetSkel.isTerminalOne` | `mkOfTerminalΩ₀`'s second argument |
| `FinSetSkel.binaryProductCone` | `ofChosenFiniteProducts` |
| `FinSetSkel.homEquivIdxFun` | rows c, d, g and h |
| `FinSetSkel.point` | row m's forward direction; row l's `truth` |
| `FinSetSkel.mono_iff_injective` | row l's core |

`isTerminalOne : IsTerminal (FinSetSkel.mk 1)` is named separately
because `mkOfTerminalΩ₀` takes `IsTerminal Ω₀` and not a `LimitCone`.
It is not constructed: `ofChosenFiniteProducts` sets
`tensorUnit := 𝒯.cone.pt` and supplies `isTerminalTensorUnit`, so
`CartesianMonoidalCategory.isTerminalTensorUnit` already has this type
once the cartesian instance is in scope, and `isTerminalOne` names it.
Per `docs/rules/lean-coding.md` § Higher-order constructions, the
existing abstraction is instantiated rather than a parallel one built.
The plan confirms the two objects are the same on the nose before
relying on it.

W4 exports `FinSetSkel.coequalizerCocone` for the remaining field;
that name is W4's to fix and is recorded here only so the table is
complete.

## Deliverables

### Rows a and b — the initial and terminal objects

Core, in `Shapes/Core.lean`: the objects of length 0 and 1, the
canonical morphisms `Fin 0 ⟶ Y` and `X ⟶ Fin 1`, their uniqueness
lemmas proved by `hom_ext` over an empty and a subsingleton index type,
the point constructor `FinSetSkel.point : Fin X.len → (Fin 1 ⟶ X)`
with its application lemma, and `homEquivIdxFun` per § W1's
index-function correspondence.

`point` is a separate deliverable from the canonical morphism *into*
the terminal object: row m's forward direction tests a morphism
against two maps *out of* a one-element object, and no other row
supplies those.

Wrapper, in `Shapes/Instances.lean`:
`ColimitCocone (Functor.empty.{0} FinSetSkel)`,
`LimitCone (Functor.empty.{0} FinSetSkel)`, `isTerminalOne`, and
`HasInitial`. `isTerminalOne` is declared after row d's cartesian
instance within that module, being `isTerminalTensorUnit` under a
name; the in-module order therefore inverts the row order.

Both cones are pinned at universe `0`:
`ofChosenFiniteProducts` binds only the category's two universe
parameters, so `Functor.empty`'s level is literally `0` there, and
`HasTerminal` unfolds at `Discrete PEmpty.{1}` exactly as `HasInitial`
does. `HasTerminal` is not registered; see § The cartesian structure
already supplies three `Prop` classes.

### Row c — binary coproducts

Core: the object of length `m + n`; injections `Vector.ofFnC` of
`finSumFinEquiv ∘ Sum.inl` and `∘ Sum.inr`; the descent morphism as
`Sum.elim` of the two argument morphisms' index functions, transported
through `finSumFinEquiv.symm`; the two factorisation lemmas and
uniqueness.

Wrapper: `ColimitCocone (pair X Y)` as a family, and
`HasBinaryCoproducts`.

### Row d — binary products

Core: `Geb/Mathlib/Data/Fin/Basic.lean` as above, then the
object of length `m * n`, projections `Vector.ofFnC Fin.divNatC` and
`Vector.ofFnC Fin.modNatC`, the lift by `Fin.pairC`, and the
factorisation and uniqueness lemmas, each discharged by one of the
three `@[simp]` round trips.

Wrapper: `LimitCone (pair X Y)` as a family, and
`CartesianMonoidalCategory FinSetSkel` as a global `instance` by
`ofChosenFiniteProducts` applied to row b's terminal cone and this
family.

### Row e — finite coproducts

Wrapper only, in `Shapes/Instances.lean`:
`hasFiniteCoproducts_of_has_binary_and_initial`. Registered per
constraint 5, which names it as something a later workstream consumes.

### Row g — exponentials

Core, in `Logic/Equiv/Fin/Basic.lean`: `Fin.funEncodeC`,
`Fin.funDecodeC`, their two `@[simp]` round trips and
`finFunctionFinEquivC {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n)`,
matching the implicit-argument roles of the `finFunctionFinEquiv` it
rebuilds — codomain `m`, domain `n` — rather than the domain-first
reading the composite above uses for its own variable names. A `C`
suffix advertises the same declaration rebuilt, and a silently swapped
implicit order is exactly what bites at the rename in § Transcription
and novelty. It is the
`Nat.rec` of decision 1 under that name; `funEncodeC` and `funDecodeC`
are its `toFun` and `invFun`, and the `@[simp]` round trips are stated
over those two names per decision 3.

Core, in `Exponential/Core.lean`: the hom-level equivalence and its
naturality, stated over the raw carrier and the explicit projections of
row d — never over `⊗` or `◁`, whose elaboration goes through the
choice-tainted `CartesianMonoidalCategory` instance and would take this
module out of the choice-free layer.

```text
(Fin (m * z) → Fin y)
  ≃  (Fin m × Fin z → Fin y)     -- Equiv.arrowCongrLeftC
  ≃  (Fin m → Fin z → Fin y)     -- Equiv.curry
  ≃  (Fin z → Fin m → Fin y)     -- Equiv.piComm
  ≃  (Fin z → Fin (y ^ m))       -- Equiv.piCongrRight, finFunctionFinEquivC
```

where the exponent object has length `m`, the parameter object length
`z` and the target length `y`. The composite was elaborated in this
form and measures `[propext, Quot.sound]`.

Two steps are not the obvious spelling. The domain transport is
`Equiv.arrowCongrLeftC`, not `Equiv.arrowCongr`, per § `Equiv`'s domain
transport is choice-tainted. The swap is required because the
adjunction `tensorLeft X ⊣ ihom X` varies in the parameter `Z`, so the
result must be a function of `Fin z`, while `X ⊗ Z` places `X` first
and `Equiv.curry` therefore produces `Fin m` outermost. It is a
consequence of which factor the adjunction is taken in, not of which
digit `Fin.pairC` makes high.

`Exponential/Core.lean` exports exactly three declarations:

- `FinSetSkel.expEquivIdx : (Fin (m * z) → Fin y) ≃ (Fin z → Fin (y ^ m))`,
  the chain above, over carriers only.
- `FinSetSkel.expEquivIdx_naturality`, the `φ`-form equation above,
  stated over `expEquivIdx`.
- `FinSetSkel.expEquivHom : (mk (m * z) ⟶ mk y) ≃ (mk z ⟶ mk (y ^ m))`,
  that equivalence conjugated by `homEquivIdxFun` on both sides. The
  object `mk (m * z)` is named directly; no `⊗` appears.

There is no hom-level naturality statement in the core: the wrapper
derives that form directly from `expEquivIdx_naturality` through the
whiskering bridge, so an intermediate would be stated twice and used
once. Nothing in the core mentions monoidal vocabulary; nothing in the
wrapper proves anything about indices except through the bridge.

The core states the naturality of that equivalence in the carrier
form, before any monoidal vocabulary enters. Writing `E z y` for
`expEquivIdx` and `φ : Fin z' → Fin z` for the index function of a
morphism `Z' ⟶ Z`, the equation is

```text
E z' y (fun i ↦ g (Fin.pairC (Fin.divNatC i) (φ (Fin.modNatC i))))
  = E z y g ∘ φ
```

for every `g : Fin (m * z) → Fin y`. This is the whole mathematical
content of the exponential's universal property, and it is stated and
proved here rather than in the wrapper: constraint 8 places content in
the choice-free layer and packaging in the wrapper, and a naturality
equation stated over `◁` would put the content in an allowlisted
module.

Wrapper, in `Exponential/Closed.lean`, in three named pieces:

1. The whiskering bridge. `ofChosenFiniteProducts` defines
   `whiskerLeft X g` as the chosen lift of `fst ≫ 𝟙` and `snd ≫ g`,
   so `X ◁ f` acts on indices by
   `(X ◁ f).toVec.get i = Fin.pairC (Fin.divNatC i)
   (f.toVec.get (Fin.modNatC i))`. `CartesianMonoidalCategory`'s
   `whiskerLeft_fst` and `whiskerLeft_snd` are the API for proving it.
   This lemma is what connects the core's `φ`-shaped equation to
   mathlib's `F.map f`.
2. The restatement of the equivalence at `X ⊗ Z ⟶ Y`, and of the
   naturality equation in the form
   `∀ Z' Z Y (f : Z' ⟶ Z) (g : X ⊗ Z ⟶ Y),
   e Z' Y (X ◁ f ≫ g) = f ≫ e Z Y g`
   that `adjunctionOfEquivRight` requires, discharged from the core
   equation by the bridge.
3. `Closed X` for each `X`, whose `rightAdj` field is
   `Adjunction.rightAdjointOfEquiv` applied to the object map
   `Y ↦ FinSetSkel.mk (Y.len ^ X.len)` and the equivalence, and whose
   `adj` field is `adjunctionOfEquivRight` at the same data; then
   `MonoidalClosed FinSetSkel`.

`X ⊗ Z` is the object of length `m * z` on the nose, the monoidal
structure having come from `ofChosenFiniteProducts` fed with row d's
cones, so the restatement in piece 2 transports along a definitional
equality rather than a comparison isomorphism.

Piece 1 is the largest single proof obligation in W3 and the plan
sizes it as its own task.

### Row h — binary equalizers

Core: for `f g : X ⟶ Y`, the predicate
`p i = decide (f.toVec.get i = g.toVec.get i)` over the axiom-free
`DecidableEq (Fin n)`; the agreement list `(List.finRange X.len).filter p`
and the carrier `mk k` of its length; the injection vector, built from
that list directly; an inverse vector `invVec : Vector ℕ X.len`, built
by one pass over the agreement list from a `Vector.replicate X.len 0`;
the bound lemma `p j = true → invVec.get j < k`; the equalising
equation; the lift; and uniqueness.

The inverse's element type is `ℕ`, not `Fin k`. `Vector (Fin k) X.len`
is uninhabited whenever `k = 0` and `X.len > 0` — `Fin 0` being empty
— and that case is reachable: any `f g : mk 3 ⟶ mk 2` differing at
every index gives `k = 0`. The `Fin k` is built at the lift site, where
`p (h.toVec.get t) = true` is available and the bound lemma applies.
`Vector.replicate` needs an inhabitant, and `0 : ℕ` is one where no
`Fin k` is.

The data is built this way rather than through W1's
`Fin.compressEquiv p`, whose components are not constant-time. That
equivalence is `List.Nodup.getEquivC` composed with a subtype
transport, and that declaration's `toFun` is `l.get i` while its
`invFun` is `l.idxOf ↑x` — linear in the index and in the list length
respectively. Routing the injection through `toFun` under
`Vector.ofFnC` costs `Θ(k²)` with the equivalence shared across
indices, and `Θ(k · X.len + k²)` without, since the `filter` then
re-runs per index and `X.len` is unbounded relative to `k`. The lift
through `invFun` costs `Θ(Z.len · k)`. The construction above is linear
in `X.len` for the injection and the inverse, and `Θ(Z.len)` for the
lift.

The data path was built and measured: the injection at `[propext]`,
the inverse and the lift at `[propext, Quot.sound]`. The lift is
`Vector.ofFnC`, not `Vector.ofFn`, per constraint 9 — the definitions
differ only in their lemmas, so a construction using the banned form
still measures clean and fails `lake lint` only once a `simp` meets it.

Correctness divides unevenly between the two. The injection's
membership property — that it lists exactly the indices satisfying `p`,
in order, without repetition — is `List.mem_filter`
(`[propext]`) and `List.nodup_finRange` (`[propext, Quot.sound]`)
composed with `List.getElem_toArray` (`[propext]`), over the
axiom-free `List.finRange`.

The inverse's is a fold-correctness lemma, and `Equalizer/Core.lean`
carries it by name. Two things about its statement are forced. First,
`List.rec` decomposes head-first, so a motive pinned to
`Vector.replicate X.len 0` and to absolute positions is not a valid
one: the recursive call speaks of the tail, renumbered from zero,
over whatever vector the head's `set` produced. The lemma is therefore
generalised over the starting vector and the starting counter,
`∀ v c, P (fold v c L)`, with the form the lift needs recovered by
specialising at `(Vector.replicate X.len 0, 0)`. Second, the invariant
is false without duplicate-freeness — `Vector.set` lets a later
occurrence overwrite an earlier one — so `L.Nodup` is a hypothesis. It
is available as `(List.nodup_finRange X.len).filter p`.

Per `docs/rules/lean-coding.md` § Recursion and induction through
recursors, the induction is an explicit `List.rec`, not the
`induction` tactic; the generalisation above is what makes that
possible rather than merely stylistic. The bound lemma
`p j = true → invVec.get j < k` follows from the specialised form.
This is a proof obligation of the same order as row g's whiskering
bridge and the plan sizes them together.

W1's `Fin.compressEquiv` is not used by this row: both properties are
stated directly, so `Equalizer/Core.lean` imports neither it nor
`Geb/Mathlib/Data/List/NodupEquivFin.lean`. An import retained for a
lemma nothing consumes would fail `lake shake` and
`CONTRIBUTING.md` § Code is cost alike. No W3 module consumes
`Fin.compressEquiv`; whether it retains a consumer elsewhere is W1's
concern, not amended here.

This is the same argument the group already made once. `TODO.md`
§ FinSetSkel as an elementary topos chooses root `Vector` over
`List.Vector` for the morphism representation precisely to avoid
quadratic composition, at the price of `Geb/Mathlib/Data/Vector/OfFn.lean`
and constraint 9's ban. A quadratic equalizer would contradict that
premise inside the same group.

Sharing remains an obligation for the pass that builds the inverse
vector, which is bound once and read per index. Measured with
`dbgTrace` at this toolchain: a definition whose result is a function,
with the `let` above the lambda, re-runs the bound computation on
every application of the partially applied function, while the same
`let` in a definition returning a value runs once. The construction is
therefore written to return the vector, with the agreement list and
the inverse bound outside anything function-valued.

Wrapper: `LimitCone (parallelPair f g)` as a family.
`HasEqualizers` is not registered: nothing in W3 consumes it,
constraint 5 names only `HasFiniteCoproducts` and `HasCoequalizers` as
later-workstream consumers, and W2 derives it generically from the
class. Rows a and c's `HasInitial` and `HasBinaryCoproducts` are
registered because they are the hypotheses of
`hasFiniteCoproducts_of_has_binary_and_initial`, which row e applies.

### Row l — the subobject classifier

Core, in `Classifier/Core.lean`: the characteristic vector, built by
scattering `(1 : Fin 2)` from `m.toVec` in one pass over
`Vector.replicate X.len (0 : Fin 2)`, with its fold-correctness lemma
in the shape row h's takes;
the pullback lift `(Vector.invOfInjective m.toVec _).symm` applied
pointwise, whose hypothesis comes from row m; the lift's uniqueness,
from `Mono m`; the square's commutation; and the vector-level
uniqueness statement, whose hypothesis is
`χ'.toVec.get j = 1 ↔ j ∈ m.toVec.toList` and whose conclusion follows
by `Fin 2` case analysis.

`χ` is scattered rather than written as
`Vector.ofFnC (fun j ↦ if m.toVec.toList.contains j then 1 else 0)`
for the reason row h rebuilds its injection: the latter rebuilds and
scans `m.toVec.toList` per index, costing `Θ(X.len · U.len)`. `χ` is a
data field of `Subobject.Classifier`, not a `Prop`, so it computes and
W5 exposes it, and the complexity discipline that forces row h's shape
applies to it identically. Scattering has no inhabitation difficulty,
`0 : Fin 2` being a default where no `Fin k` is; the construction was
built and measured at `[propext, Quot.sound]`. It scatters `1`
directly rather than through a `Vector Bool` stage, which would cost a
second pass, a second correctness lemma and a `Vector.map` audit for
nothing.

The pullback lift of § The classifier consumes the W1 inversion is not
subject to this discipline, and the reason is not that its type is
`Prop`. It is that nothing reaches it from an exposed data field of
`Subobject.Classifier`: `χ` is such a field and the lift is not, being
used only inside the wrapper's `IsPullback` proof, where
`Nonempty (IsLimit …)` erases it. `Vector.invOfInjective`'s `invFun`
is `l.idxOf`, linear per call, so were the lift reachable it would face
the same objection as the rejected `χ`.

Wrapper, in `Classifier/Instance.lean`: the derivation of that
hypothesis from `IsPullback`, which uses the pullback's universal
property and cannot be stated choice-free; then
`Subobject.Classifier FinSetSkel` by `mkOfTerminalΩ₀`, with `Ω₀` row
b's terminal object, `isTerminalOne` its terminality, `Ω` the object of
length 2, and `truth` the constant `1`.

Constraint 6 concerns the comparison of the cartesian unit with `Ω₀`.
Building `Ω₀` as row b's terminal object makes the two objects
identical, so the comparison is an isomorphism between an object and
itself, equal to `Iso.refl` by the uniqueness of maps into a terminal
object — a propositional equality, not a definitional one, since W2's
`tensorUnitIsoΩ₀` is `IsTerminal.uniqueUpToIso`, whose `hom` is
`t.from`. W3 does not state that lemma: `ElementaryTopos.tensorUnitIsoΩ₀` takes
`[ElementaryTopos C]`, an instance that does not exist until W5. The
lemma belongs to W5, which has it; W3 discharges constraint 6 by
construction and records that here.

### Row m — monomorphisms

Core, in `Mono.lean`:
`FinSetSkel.mono_iff_injective : Mono f ↔ Function.Injective
f.toVec.get`. `CategoryTheory.Mono` and `CategoryTheory.Category` are
both axiom-free, so the statement belongs in the choice-free layer.

### Tests

One `GebTests/Mathlib/` parallel per new file, mirroring the source
path, index files included. Each parallel of a *content* module names a
`def` value built from the module under test rather than using
`example` alone: `lake shake` cannot see an import used only inside an
`example`, since no constant reaches the olean, and reports a false
"remove import" with exit 1. Index parallels are import-only, as their
sources are; requiring a declaration in them would put a
`Classical`-tainted term in a test module that verification obligation
6 keeps off the allowlist.
Content is compositional per `docs/rules/lean-coding.md` § Structure
and typeclass patterns — calculate one value, assert it, reuse it —
covering the encodings at small sizes and the resolution of each `Prop`
instance.

### Documentation

A `docs/index.md` entry for the eleven content modules, in topological
order, per `CONTRIBUTING.md` § Each phase produces an artifact.

Module docstrings carrying the persistent decisions:

- `Data/Fin/Basic.lean` — the `Nat` division interleaving, whose bound
  proofs and round trips are where the constraint is discharged.
- `Equalizer/Core.lean` — that the agreement list and the inverse
  vector are bound outside anything function-valued, and why: the
  constraint is invisible in the source and a later refactor lifting
  the vector construction into a function-returning helper would break
  it silently. This is the most fragile of the three.
- `Classifier/Core.lean` and `Classifier/Instance.lean` — the `truth`
  orientation, which the two fix jointly, `χ` sending members to `1` in
  the core and `truth` being the constant `1` in the wrapper. Each
  states it; neither states it alone.

The shared declaration carries its own, on
`feat/choice-free-primitives`. Each states the constraint, not the
process that produced it, per `CONTRIBUTING.md` § Document only the
persistent.

## Amendments to `TODO.md`

1. Three edits to constraint 9, already applied on
   `feat/choice-free-primitives`. It gains three families: the `Nat`
   division and order API, the `LawfulBEq` instance at `Fin n` with
   the supply repair,
   and `Equiv`'s domain-transport combinators. This amendment is not
   made on W3's branch: all three apply to W4, and W4 is concurrent,
   so it is on `feat/choice-free-primitives` off `main` for both to
   rebase onto. Recorded here because this document is its evidence.
   It also adds the monomorphic-measurement rule of § How axioms are
   measured as a fourth paragraph, and extends the constraint's
   closing sentence to "leaving instance search to pick, and where the
   only instance in scope is choice-dependent it supplies its own".
   Both bind W3 through W5, not this workstream alone.
2. The status table's W3 row becomes Complete, with the eleven content
   module paths, and its row label becomes "Rows a–e, g, h, l, m" (see
   amendment 6). The table's duplicate `W1 … Not started` row, left
   from W1's merge, is deleted in the same edit: it is factually wrong,
   it sits in the table being rewritten, and leaving it would be the
   defect amendment 6 exists to remove one row away.
3. The operation table's row m alternative names the wrong lemma.
   `SimplexCategory.mono_iff_injective` is replaced by
   `ConcreteCategory.mono_iff_injective_of_preservesPullback`. The
   alternative itself is retained: it exists, and the table's remark
   that it "lands the row in W3's wrapper" is correct.
4. Constraint 7's parenthetical that the two replacements each have "a
   single consumer in W3" holds of the two `Equiv`s as written —
   `finProdFinEquivC` is consumed by row g alone, `finFunctionFinEquivC`
   likewise — but not of the three `Fin` operations beneath them, which
   rows d and g both consume. The parenthetical gains that
   distinction. The assignment it justifies is unchanged.
5. The standing obligation listing files both concurrent pairs append
   to already covers `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`
   under "any shared directory index file"; it names that instance
   explicitly, W3 and W4 both amending it.
6. The operation table's rows f and j are marked derived rather than
   assigned to W3, per § The cartesian structure already supplies three
   `Prop` classes. Two further statements of W3's scope in the same
   file are corrected with it, and both assign `f` as well as `j`
   because they state ranges: § Workstreams' W3 bullet becomes "rows a
   through e, g, h, l and m", and the status table's W3 row label
   becomes "Rows a–e, g, h, l, m". The operation table's row h loses
   its "and `HasEqualizers`", on the same ground: W2 derives it from
   the class and nothing consumes it in the interval, exactly as for
   j. The sentence below the operation table — "Rows e, j and k are
   reassigned to W2 below (§ Class fields); the table above states the
   plan's original per-field assignment" — is corrected too: the table
   no longer states the original assignment once rows f and j are
   marked derived, and its enumeration gains `f`.
7. Constraint 8 reads "mathlib structures and `Prop` instances in a
   wrapper whose fields are those terms". It gains the qualification
   that a wrapper may also carry content which cannot be stated
   choice-free — row g's whiskering bridge and row l's derivation of
   the characteristic-vector hypothesis from `IsPullback` are both
   such. The constraint binds W4 and W5 too, so the loosening is
   recorded rather than taken locally.
8. A `TODO.md` § Triggers entry records that `Fin.compressEquiv` has
   no consumer. W1 built it for row h, which no longer routes through
   it; besides its own module, its only remaining occurrences are
   its test parallel and its `docs/index.md` entry. This document is
   where that becomes known, and it is deleted at merge, so without the
   entry the observation is lost. The trigger's condition is the next
   occasion to revisit W1's helpers.

## Out of scope

- Row i, row k and the `ElementaryTopos FinSetSkel` instance.
- The constraint-6 comparison lemma, which requires
  `[ElementaryTopos C]` and so belongs to W5.
- Any relation between W3's encodings and mathlib's tainted
  `finProdFinEquiv` and `finFunctionFinEquiv`. An agreement lemma would
  mention the tainted declarations and would have to sit in a wrapper;
  nothing in W3, W4 or W5 consumes one.
- A two-sided `Equiv.arrowCongrC`. Only domain transport is needed.
- Chosen cones for `Fin n`-indexed families. The umbrella spec's
  § Chosen cones exist for the generators only records that the step
  functions exist and the recursions assembling them are not supplied;
  no row needs them.
- Upstream submission of any module here, and the renaming of the `C`
  suffix that submission entails.

## Verification obligations

The plan makes each a per-task acceptance criterion, so that the
search when the axiom linter fires spans one declaration.

1. `#print axioms` on every declaration in a choice-free module, as it
   is written rather than as a final pass, always from a monomorphic
   `def` at the instances actually used, per § How axioms are measured.
2. Each row's construction is measured whole, not only its named
   ingredients. `Vector.replicate` and `Vector.set`, which rows h and
   l newly depend on, are the two this document has not measured; the
   `List` lemmas beneath the injection are measured in § Row h.
3. Every name this group introduces is confirmed free by `#check`
   under the importing module's own import set, not in a probe.
4. The fold-correctness lemmas of rows h and l are stated in the
   generalised form § Row h describes, over an arbitrary starting
   vector and counter and under a `Nodup` hypothesis, and are proved
   by an explicit `List.rec`. The specialisation each row needs is
   derived from it rather than proved separately.
5. Every mathlib declaration this document names is re-elaborated
   before the plan's task that uses it, not taken from this document.
6. `GebMeta.classicalAllowedModules` gains exactly the four wrapper
   modules and their four `GebTests` parallels, and no core module.
7. `scripts/lint-imports.sh`, `lake build`, `lake test` and `lake lint`
   pass, and `scripts/pre-push.sh` is clean before review.
8. No scratch or probe module is left under `Geb/` or `GebTests/`;
   both are lake-globbed source roots.
9. Any row whose construction binds an expensive intermediate and
   returns a function is checked for sharing with `dbgTrace`, not by
   reading the source. The measurement recorded under § Row h — that a
   `let` above the lambda of a function-returning definition re-runs
   per application while the same `let` in a value-returning one does
   not — was taken at this toolchain and is re-taken on a bump, being
   a property of the code generator rather than of the logic. Row h's
   agreement list and inverse vector are the known instance, being the
   bindings § Documentation calls the most fragile; row g's
   `Fin.funDecodeC`, which returns `Fin m → Fin n`, is the other
   candidate.

## References

- `TODO.md` § FinSetSkel as an elementary topos — the authoritative
  roadmap for the group.
- The umbrella spec, `jj` change
  `nkwoqxwytsvrlpnsklzzlzkxtovyxkzm` on branch
  `docs/finsetskel-topos-roadmap`.
- W1's spec, `jj` change `qnkykqtqrtlvznoqznsrzzynvluwvuqz` on branch
  `feat/finsetskel`.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` — W1's morphism
  API and application-normal form.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` — `incl` and
  the comparison with mathlib's skeleton.
- `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` — W2's class and
  its field types.
- `Geb/Mathlib/Logic/Equiv/Basic.lean` — the repository's mirror of
  `Mathlib/Logic/Equiv/Basic.lean`.
- `Geb/Mathlib/Data/Vector/NodupEquivFin.lean` —
  `Vector.invOfInjective`, row l's only W1 inversion dependency.
