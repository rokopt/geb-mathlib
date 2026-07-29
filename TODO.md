# TODO

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [In progress](#in-progress)
- [Next up](#next-up)
  - [Polynomial functors](#polynomial-functors)
    - [1. Categorical wrappers for slice and presheaf W-types as initial algebras](#1-categorical-wrappers-for-slice-and-presheaf-w-types-as-initial-algebras)
    - [2. M-types and their categorical wrappers as terminal coalgebras](#2-m-types-and-their-categorical-wrappers-as-terminal-coalgebras)
    - [3. Universal morphisms](#3-universal-morphisms)
    - [4. Relative (co)free (co)monads](#4-relative-cofree-comonads)
    - [5. Composition and identity of polynomial functors](#5-composition-and-identity-of-polynomial-functors)
  - [FinSetSkel as an elementary topos](#finsetskel-as-an-elementary-topos)
    - [Workstreams](#workstreams)
    - [Operations](#operations)
    - [Class fields](#class-fields)
    - [Cross-workstream interface constraints](#cross-workstream-interface-constraints)
    - [Standing obligations](#standing-obligations)
    - [Status](#status)
  - [Complexity of the decidable validity checkers](#complexity-of-the-decidable-validity-checkers)
  - [Upstream placement of categorical wrappers](#upstream-placement-of-categorical-wrappers)
  - [Upstream destination of core- and Batteries-targeted content](#upstream-destination-of-core--and-batteries-targeted-content)
  - [Complete Theorem 2.4 for `IndRec`](#complete-theorem-24-for-indrec)
  - [Theorems 2 and 4 for `IR` codes](#theorems-2-and-4-for-ir-codes)
  - [Validate `PresheafPFunctor.functor` as a parametric right adjoint](#validate-presheafpfunctorfunctor-as-a-parametric-right-adjoint)
  - [Exhaustive verification of presheaf PRA laws for finite instances](#exhaustive-verification-of-presheaf-pra-laws-for-finite-instances)
- [Triggers (do when condition fires)](#triggers-do-when-condition-fires)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Active workstreams, in topological order. Workstreams complete →
removed; content merged into `docs/index.md`.

## In progress

(None.)

## Next up

### Polynomial functors

The polynomial-functor roadmap below is a partial order of
separate planning–implementation cycles. Items with disjoint file
sets that do not depend on one another may be taken in either
order. Each item's full spec and plan are written only after the
items it depends on are implemented: the project is too large to
fix every earlier
interface on the first attempt, so interface corrections in an
earlier item can invalidate a later item's plan. Each item lives
on its own topic branch and migrates to persistent documentation
under `docs/index.md` on completion.

The current stack, each layer expressed as restrictions or assignments on
the layer below: mathlib `PFunctor` (`Type` endofunctors) → slice
polynomial functors (`Geb/Mathlib/Data/PFunctor/Slice/`) →
presheaf parametric-right-adjoint functors
(`Geb/Mathlib/Data/PFunctor/Presheaf/`). Categorical
interpretations into mathlib's category theory are kept thin to
minimise the `Classical.choice` surface. Slice and presheaf W-types
(`Slice/W.lean`, `Presheaf/W.lean`) exist, with the existence half of
initiality only; the roadmap extends the stack upward.

#### 1. Categorical wrappers for slice and presheaf W-types as initial algebras

Characterise the slice and presheaf W-types as the initial objects
of the categories of algebras of their functors, reusing the
`PFunctor` and `WType` wrappers described under
`Geb/Mathlib/Data/PFunctor/Univariate/` in `docs/index.md`. Build the
presheaf initiality proof on the slice initiality proof, and the slice
proof on the `WType` initiality established there.

#### 2. M-types and their categorical wrappers as terminal coalgebras

Define the M-types (greatest fixed points) of the slice and
presheaf functors on mathlib's `PFunctor.M`, following mathlib's
standard construction of M-types on W-types, and characterise them
as the terminal coalgebras of their functors. Following the
base-layer-first pattern of the `PFunctor` wrappers and item 1,
build a categorical
wrapper for the terminality of mathlib's `PFunctor.M` first,
reusable in the slice and presheaf terminality proofs.

#### 3. Universal morphisms

Establish the universal morphisms of the slice and presheaf functors,
layering the slice constructions on mathlib's `PFunctor` and the
presheaf constructions on the slice constructions. Per the survey,
mathlib carries little or none of this for `PFunctor`, so a base layer
for mathlib's `PFunctor` is likely required. Model formulas for a
different representation, to be adapted, are in
[rokopt/geb `PolyUMorph.lean`](https://github.com/rokopt/geb/blob/main/geb-lean/GebLean/PolyUMorph.lean).

Implement in this order, each step layered across the three forms:

1. Representables (every representable is polynomial).
2. Small coproducts (indexed by any `Type u`): every polynomial is
   then a coproduct of representables; the first part of general
   colimits; includes the initial object (the coproduct over `Empty`).
3. Day convolution: the first part of general limits.
4. Commutativity of coproducts with Day convolution.
5. Small products, as an instantiation of Day convolution.
6. Small parallel products, as an instantiation of Day convolution.
7. Exponential objects.
8. Left Kan extension.
9. Equalizers.
10. All small limits, by instantiating mathlib's construction of
    limits from products and equalizers.
11. Coequalizers.
12. All small colimits, by instantiating mathlib's construction of
    colimits from coproducts and coequalizers.

Following the general definitions, implement the decidable-case
specializations of those universal morphisms with interesting
decidable forms, building on the `PFunctor.Finitary` layer documented
in `docs/index.md`.

#### 4. Relative (co)free (co)monads

Build the relative free monads and relative cofree comonads of the
slice and presheaf functors for all three forms, and prove the
relative universal property. A slice or presheaf functor is an
endofunctor only when its domain and codomain bases coincide, so the
relative notion [AltenkirchChapmanUustalu2015] is the appropriate one
for the general (non-endofunctor) case; the ordinary free monad and
cofree comonad are the `J = id` special case. The formal theory is
[ArkorMcDermott2024]. Model definitions: cslib's `PFunctor` free monad
(`Cslib/Foundations/Data/PFunctor/Free.lean`, the ordinary case) and
[rokopt/geb `RelativeMonad.lean`](https://github.com/rokopt/geb/blob/main/geb-lean/GebLean/Binding/RelativeMonad.lean)
(the relative case, in extension form). The first intended application
is generic syntaxes with binding [AllaisAtkeyChapmanMcBrideMcKinna2021],
which also supplies test material for the relative monads.

Open technical question, resolved when this item is taken up, that
determines implementation order: whether the relative (co)free
(co)monad can be built on top of the ordinary one — as the slice
functors are built on `PFunctor` and the presheaf functors on the
slice functors. The primary constraint is to avoid code duplication;
within that, build the simpler pieces first and the more complex on
top of them when that can be done without duplication. If the relative
version can be built on the ordinary one, do so (simpler-first with
reuse); otherwise build the relative version and define the ordinary
one as its `J = id` specialization — known achievable, the ordinary
case being the discrete degeneration. Relate each construction to the
corresponding slice/presheaf W-type (item 1) or M-type (item 2) and
show the definitions equivalent, as in the superseded free-monad and
cofree-comonad items.

#### 5. Composition and identity of polynomial functors

Establish that the interpretation of mathlib's `PFunctor` carries
`PFunctor.comp` to composition of the corresponding functors, and
supply the identity polynomial functor together with the isomorphism
identifying its interpretation with the identity functor. mathlib
defines `comp`, `comp.mk`, and `comp.get` and states no lemma about
them, so the mutual-inverse laws `comp.get_mk` and `comp.mk_get` are
part of the item.

This is the 1-cell composition of `Cat`, a 2-categorical operation,
not a universal morphism. It is independent of the items above and may
be taken in any order relative to them. Two design points are settled:
the identity polynomial functor is `protected def PFunctor.id`, since
an unprotected `id` shadows `_root_.id` throughout the `PFunctor`
namespace and breaks uses such as `P.map id`; and both isomorphisms
admit an ambient universe beyond the parameters of the functors
involved.

### FinSetSkel as an elementary topos

Geb requires a category of finite sets whose morphisms are data:
values that can be pattern-matched, serialised, and compared.
mathlib's skeletal model `FintypeCat.Skeleton` takes morphisms to be
functions, whose equality is decidable only through
`Classical.choice`, so this group builds `FinSetSkel` — objects
corresponding to ℕ as `FintypeCat.Skeleton`'s do, morphisms as
length-indexed vectors of codomain indices — and the elementary-topos
structure on it.

The two object carriers differ although the objects correspond:
`FinSetSkel` is a one-field structure with a named `len`, where
`FintypeCat.Skeleton` is `ULift ℕ`, whose projection is `down`. W3, W4
and W5 all state constructions over `Fin X.len`, and the structure
supplies both that name and, under `@[ext]`, an extensionality lemma.

The spec recording the research findings and the argument that the
workstreams compose was added and removed on branch
`docs/finsetskel-topos-roadmap` (PR #97); recover it from there when
re-verifying a finding, since the findings are pinned to the mathlib
revision current when they were taken. W1's spec, added and removed on
branch `feat/finsetskel` (`jj` change
`qnkykqtqrtlvznoqznsrzzynvluwvuqz`), is the later document of the two
and records the re-verification of the findings W1 consumes. It
corrects four of the umbrella spec's findings — the `Functor.ext`
route for the comparison, the choice-free isomorphism in `Cat`, W0's
shortening of W1, and the `ULift`-transport plan for the index
equivalences — and adds the index-equivalence choice-taint that the
operation table assumed away.

Two names are fixed for the group. `FinSetSkel` is the category, the
`Skel` recording that it is the skeletal model, parallel to
`FintypeCat.Skeleton`. `ElementaryTopos` is the class, the qualifier
distinguishing it from a Grothendieck topos, mathlib using `Topos`
for sheaf-theoretic material. W1 through W5 place their modules under
`Geb/Mathlib/`, with test parallels under `GebTests/Mathlib/`; W0
adds no modules.

Morphisms are root-namespace `Vector`, not `List.Vector`, on the
ground that composition is the operation the category exists to run.
Composing `f : X ⟶ Y` with `g : Y ⟶ Z`, writing `X.len = m` and
`Y.len = n`, costs `O(m)` over root `Vector`'s constant-time indexing
and `O(m² + m · n)` over `List.Vector`'s linear indexing. The axiom
comparison runs the other way on every count: root `Vector`'s derived
`DecidableEq` costs `propext`/`Quot.sound` where
`List.Vector.instDecidableEq` depends on no axioms, and root
`Vector`'s `ofFn`, `range` and `finRange` lemmas depend on
`Classical.choice` where `List.Vector`'s do not. Root `Vector` is
chosen against that, at the price of the declarations of
`Geb/Mathlib/Data/Vector/OfFn.lean` and of constraint 9's ban. This
fixes W1's morphism type and every downstream carrier.

#### Workstreams

W0 precedes W4. W1 and W2 are independent of each other and of W0; W3
and W4 both depend on W1 and are independent of each other and of W2; W5
depends on W1 through W4. Each of W1 through W5 writes its spec and
plan only after the workstreams it depends on are merged, each
through brainstorming, adversarial review to convergence, user
review, planning, adversarial review, user review, and
subagent-driven development. Each of their deliverable lists includes
a `docs/index.md` entry, per `CONTRIBUTING.md` § Each phase produces
an artifact. W0 carries no spec, no plan and no `docs/index.md`
entry, adding no Lean content.

- **W0** _(complete)_ — `Batteries.` admitted to the `Geb/Mathlib/` and
  `GebTests/Mathlib/` allow-lists in every place that states them:
  `scripts/lint-imports.sh` and its comment header,
  `docs/rules/upstream-eligible.md` § Subtree import rules, the
  `Geb/Mathlib/` line of `docs/index.md` § Directory structure, and a
  case in `scripts/tests/test-lint-imports.sh`. W4 requires it,
  needing `Batteries.Data.UnionFind`.
- **W1** _(complete)_ — the `SmallCategory` instance at an arbitrary
  universe, its objects the one-field structure above and its morphism
  type `ULift.{u} (Vector (Fin Y.len) X.len)`, the lift outside the
  vector rather than on its entries. Its deliverables, and with them
  the decisions it fixes for W3 through W5:
  - The morphism API: `FinSetSkel.Hom`, the `ofVec`/`toVec` pair with
    both round trips `toVec_ofVec` and `ofVec_toVec`, `@[ext]`
    extensionality, and `attribute [irreducible] FinSetSkel.Hom`
    sealing the representation once the API is in place. No
    downstream construction projects the representation; all route
    through `ofVec`, `toVec` and `ofIdxFun`.
  - Morphism extensionality and the identity and composition
    application lemmas, whose `@[simp]` orientation fixes
    `f.toVec.get i`, with `i : Fin X.len`, as the shared
    application-normal form for W3 and W4.
  - The three properties of morphisms this entry requires —
    pattern-matched, serialised and compared — each discharged on
    `f.toVec`, since the seal makes `Hom` itself opaque. Morphism
    `DecidableEq` and `Repr` are the terms W1 exports, pinned through
    `hom_ext` and `toVec` rather than left to `inferInstance`:
    instance search does not unfold the `Hom` definition, and the
    `instDecidableEqOfLawfulBEq` route inhabits the same class and is
    choice-tainted.
  - `Geb/Mathlib/Data/Vector/OfFn.lean`, exporting `Vector.ofFnC`,
    `getElem_ofFnC`, `get_ofFnC`, `ofFnC_get` and the `rfl` bridge
    `get_eq_getElem` to the `getElem` API. The two `get`-form round
    trips carry `@[simp]`; `getElem_ofFnC` and the bridge do not,
    neither the `getElem` form nor either orientation of the bridge
    being the normal form.
  - `Geb/Mathlib/Data/List/NodupEquivFin.lean`, the choice-free
    rebuild of `List.Nodup.getEquiv` and the predicate compression
    over it; and `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`,
    exporting `Vector.invOfInjective`, the vector-level inversion
    `Fin k ≃ {j : Fin n // j ∈ ι.toList}` of an injective
    `ι : Vector (Fin n) k` under the hypothesis
    `Function.Injective ι.get`, stated over the normal form.
  - The comparison functors to `FintypeCat.Skeleton`, the isomorphism
    in `Cat`, the equivalence, and the transported `Skeletal` and
    `IsSkeletonOf`, all in an allowlisted wrapper:
    `CategoryTheory.Cat.category` depends on `Classical.choice`, so an
    isomorphism in `Cat` is not choice-free by any route.
  - A module docstring recording the morphism-representation choice
    with the evidence against it.
- **W2** — the `ElementaryTopos` class, its derived accessors and
  derived `Prop` instances, the `docs/references.bib` citations, and
  a module docstring carrying constraint 3 and constraint 5's
  accessor rule.
- **W3** — rows a through h, j, l and m of the operation table.
- **W4** — row i, by folding `Batteries.UnionFind.union` over the
  domain; plus a `TODO.md` § Triggers entry recording the
  mathlib-to-Batteries dependency-edge question against W4's upstream
  submission, which outlives this group.
- **W5** — row k and the `ElementaryTopos FinSetSkel` instance.
  Removes this entry, its content moving to `docs/index.md`.

#### Operations

`Fin k` abbreviates the object of length `k`.

| | Operation | Carrier or source | Workstream |
| --- | --- | --- | --- |
| a | Initial object | `Fin 0` | W3 |
| b | Terminal object | `Fin 1` | W3 |
| c | Binary coproducts | `m + n`, via `finSumFinEquiv`, which is choice-free and usable as it stands | W3 |
| d | Binary products | `m * n`, via `finProdFinEquiv`, which depends on `Classical.choice` through `Fin.divNat`; W3 owes a choice-free replacement | W3 |
| e | Finite coproducts (`Prop`) | from a and c | W3 |
| f | Finite products (`Prop`) | from b and d | W3 |
| g | Exponentials (`MonoidalClosed`) | `Fin m ⟹ Fin n` is `Fin (n ^ m)`, via `finFunctionFinEquiv`, which depends on `Classical.choice`; W3 owes a choice-free replacement | W3 |
| h | Binary equalizers, and `HasEqualizers` | agreement subset | W3 |
| i | Binary coequalizers, and `HasCoequalizers` | union-find | W4 |
| j | Finite limits (`Prop`) | from f and h | W3 |
| k | Finite colimits (`Prop`) | from e and i | W5 |
| l | Subobject classifier | `Fin 2`, via `mkOfTerminalΩ₀` | W3 |
| m | `Mono` is an injective vector | either directly over vectors, W1 supplying `Vector.invOfInjective` as the ingredient, or through `SimplexCategory.mono_iff_injective` and W1's `incl`, which lands the row in W3's wrapper; W3 chooses | W3 |

#### Class fields

`ElementaryTopos C` carries data for its generators and `Prop` for
finite (co)limits, which is the most that is available: chosen cones
for an arbitrary finite diagram are not computably derivable, since
`FinCategory` carries no enumeration and every route to one is either
`noncomputable` or `Trunc`-valued.

| Field | mathlib type | Supplies rows |
| --- | --- | --- |
| cartesian | `CartesianMonoidalCategory C` | b, d, and hence f |
| closed | `MonoidalClosed C`, over the cartesian field | g |
| initial | `ColimitCocone` over `Discrete PEmpty` | a, and with binary coproducts hence e |
| binary coproducts | `ColimitCocone` over `Discrete WalkingPair`, a family | c, and with initial hence e |
| equalizers | `LimitCone` over `WalkingParallelPair`, a family | h |
| coequalizers | `ColimitCocone` over `WalkingParallelPair`, a family | i |
| classifier | `Subobject.Classifier C` | l |
| finite limits | `HasFiniteLimits C` | j |
| finite colimits | `HasFiniteColimits C` | k |

Data is carried rather than `Prop` for the same reason at two scales:
a `Prop` form is indifferent to a distinction that matters
computationally, all limits of a diagram being isomorphic and none of
them running. Within a construction, carrying a `LimitCone` rather
than its `Nonempty` decides whether anything computes at all.
Across constructions, carrying the coequalizer as data decides which
algorithm runs: finite colimits are redundant as an axiom — that an elementary
topos has them is Mikkelsen's theorem [Mikkelsen1976], presented
at Oberwolfach in July 1972, of which [Pare1974] gives a published
proof by the tripleability of the power-object functor — but a
derived construction is whichever one the general proof yields, and
that is not union-find.

W2 may instead expose the two `Prop` fields as derived instances.
That is not free: deriving them generically obliges W2 to derive
`HasFiniteCoproducts` generically too, so rows e, j and k become
W2's one-time derivations and leave W3's and W5's assignments. The
operation table assumes the field form, and W3 and W5 proceed on it
regardless of W2's eventual choice; redundant `Prop` instances are
harmless by proof irrelevance. W2 took the derived-instance route, so
the finite-limits and finite-colimits rows of the table above are not
fields of the class: rows e, j and k are W2's one-time derivations,
and W3's and W5's assignments become redundant.

#### Cross-workstream interface constraints

1. Data for generators, `Prop` for finite (co)limits. Binds W2
   through W5.
2. Field types for the topos structure are mathlib types — no bespoke bundle of
   W2's own, since W3 and W4 must produce the fields without importing W2.
3. `ElementaryTopos` is stated over `(C : Type u) [Category.{v} C]`,
   matching mathlib convention. `SmallCategory C` is `Category.{u} C`,
   so a formulation over it would admit `FinSetSkel` but foreclose
   every non-small instance.
4. W1 settles the `ULift` placement in the morphism type.
5. W3 and W4 register as instances what they consume and what a later
   workstream consumes — including `HasFiniteCoproducts` (W3, row e)
   and `HasCoequalizers` (W4, row i, via
   `hasCoequalizers_of_hasColimit_parallelPair`), which are row k's
   two hypotheses. Rows b and d are exposed only through the
   cartesian instance. Each row's data term is exported under a
   stable public name. W2's accessors from `[ElementaryTopos C]` are
   instances for the `Prop` classes, two resolution routes being
   harmless there by proof irrelevance, and definitions for the
   data-carrying classes, two routes to data not needing to agree
   definitionally.
6. The class enforces that the classifier field's `Ω₀` is the
   cartesian field's terminal object, by a mechanism W2 chooses that
   leaves the field's type `Subobject.Classifier C`. W3 builds row l
   over its own row b as exposed through the cartesian instance, so
   the coherence obligation is `rfl`.
7. `DecidableEq` on morphisms and the injective-vector inversion live
   in W1. A shared lemma
8. The classifier field's `Ω₀` and the cartesian field's terminal
   object are both terminal, hence canonically and uniquely
   isomorphic; W2 exports the comparison as
   `ElementaryTopos.tensorUnitIsoΩ₀`. The class enforces no
   identification between them, an equality of objects not being
   invariant under equivalence. W3 builds row l over its own row b
   through `mkOfTerminalΩ₀`, as the operation table assigns, so the
   two coincide there as a matter of construction rather than of
   obligation.
9. `DecidableEq` on morphisms, the injective-vector inversion and the
   transported index equivalences live in W1. A shared lemma
   discovered after W1 merges goes on its own branch off `main`,
   which W3 and W4 both rebase onto. The choice-free replacements for
   `finProdFinEquiv` and `finFunctionFinEquiv` are deliberately
   W3-local, each having a single consumer in W3: this constraint
   places in W1 what W3 and W4 share, and W4's row i touches neither.
8. Every workstream splits its modules: constructions and the content
   of their universal properties choice-free over vectors and `Fin`;
   mathlib structures and `Prop` instances in a wrapper whose fields
   are those terms. Only wrapper modules reach
   `GebMeta.classicalAllowedModules`. A workstream whose entire
   deliverable is packaging — W2 and W5 — is a wrapper throughout.
9. Constructions in choice-free modules use `Vector.ofFnC` and never
   `Vector.ofFn`, `Vector.range` or `Vector.finRange`, nor the
   `Array.toList_ofFn` / `List.toArray_ofFn` bridges. Binds W3
   through W5. The definitions themselves depend on `propext` alone;
   what is banned with them is their lemmas. Those that fire
   automatically — `Vector.getElem_ofFn`, `Vector.getElem_range`,
   `Vector.getElem_finRange`, `Vector.ofFn_getElem`,
   `Array.getElem_ofFn` and the two `Array` bridges — are `@[simp]`,
   most also `@[grind =]`, and all depend on `Classical.choice`, as
   do the `ofFn` lemmas carrying no attribute at all. A bare `simp`
   or `grind` meeting such a term therefore introduces
   `Classical.choice` into a module required to be choice-free. It is
   not an elaboration error: it surfaces at `lake lint`, on the
   branch's own CI run and pre-push check. Batteries' `get`-form
   counterparts are equally tainted and are not in scope: no
   `Mathlib.*` module reaches `Batteries.Data.Vector.Lemmas`, and the
   bare umbrella `import Mathlib` that would is forbidden in
   upstream-eligible files by `scripts/lint-imports.sh`. W0 permits a
   direct `Batteries.` import, so this is a standing choice rather
   than an impossibility: a workstream that adds one admits the same
   family into the `get` normal form.

   The general shape binds as well as the instances, which are not a
   closed list: where two routes inhabit one class and only one is
   choice-free, a choice-free module names the term rather than
   leaving instance search to pick. Morphism `DecidableEq` is one
   such, pinned by W1. Deciding a proposition quantified over `Fin n`
   is another, and W3 and W4 both need it: `inferInstance` gives an
   axiom-free term, while `Fintype.decidableForallFintype`, which
   inhabits the same class, depends on `Classical.choice`.

Beyond W1's application-normal form, W3 and W4 each add carrier-level
`simp` lemmas that first meet at W5; neither marks a transport lemma
`simp` in a direction that rewrites the other's normal form.

#### Standing obligations

- A textbook locator for the skeleton of a category is verified
  against the primary source before any Lean docstring cites one, on
  the [Pare1974] precedent below. The nLab entry cited by
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` attests Mac Lane,
  _Categories for the Working Mathematician_ (1971), p. 91 and Riehl,
  _Category Theory in Context_ (2017), p. 34, but attestation by a
  secondary source is not verification.
- `GebMeta.classicalAllowedModules` gains each new wrapper module and
  its `GebTests` parallel, appended by the workstream introducing it;
  W1 through W5 each entail such an amendment, W0 none.
- Both concurrent pairs — W1 with W2, W3 with W4 — append to files
  the other also appends to: `GebMeta.classicalAllowedModules`, the
  status table below, `docs/index.md`, and any shared directory index
  file. These are ordinary textual conflicts, resolved by rebasing
  the later sibling before merge.

#### Status

| Workstream | Depends on | State | Code |
| --- | --- | --- | --- |
| W0 `Batteries.` allow-list | — | Complete | — |
| W1 `FinSetSkel` | — | Complete | `Geb/Mathlib/Data/Vector/OfFn.lean`, `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`, `Geb/Mathlib/Data/List/NodupEquivFin.lean`, `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`, `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` |
| W2 `ElementaryTopos` | — | Not started | — |
| W3 Rows a–h, j, l, m | W1 | Not started | — |
| W4 Row i, union-find | W0, W1 | Not started | — |
| W5 Row k, unification | W1–W4 | Not started | — |

### Complexity of the decidable validity checkers

Prove the complexity bounds conjectured, but not proved, for the
checkers in `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean` and
`Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean` (see
`docs/index.md`). With `n` the number of nodes of the input term, `h`
its height, `k` the branching bound, `κ` the number of objects of `I`,
and `H` the maximal hom-set size, and taking equality in `I`, in
`dom`, and in the presheaf's value types to cost `O(1)`: the four
single-step checks are constant-time in `n`, with node-level factors
`1` for the two fiber predicates, `k` for `Compatible`, and `κ²Hk` for
`IsNatural`; `WValid` runs in `O(k · n)`, a single fold with an
`O(1)` accumulator; and `IsHereditarilyNatural` runs in
`O(κ²Hk · n · h)`, worst case `O(n²)`, because each node's local
condition is an equation between a subtree and the root-restriction
of a sibling, whose decision cost is linear in subtree size. All six
are polynomial time, and the functor's data enters as multiplicative
constants rather than as a change of complexity class. Upper bounds
only: a `Bool` fold short-circuits, so no matching lower bound is
claimed on rejecting inputs.

A sharing or hash-consing representation would reduce
`IsHereditarilyNatural`'s checker to linear time, each subtree
comparison becoming a pointer comparison; building that
representation is out of scope for this item.

[Leivant1999], [DalLagoMartiniZorzi2010], and [AvanziniDalLago2018]
place the checkers' complexity: every recursion here is a
non-dependent fold at a first-order carrier, the regime those results
place in first-order polynomial time, as against the higher-order and
word-algebra regimes in which they identify an elementary or
exponential jump.

### Upstream placement of categorical wrappers

Settle where the categorical wrappers under `Geb/Mathlib/Data/` belong
upstream. No file under mathlib's `Mathlib/Data/` imports
`Mathlib.CategoryTheory.*`; mathlib packages category-theoretic
material under `Mathlib/Algebra/Category/` and
`Mathlib/CategoryTheory/`. In scope is every file under
`Geb/Mathlib/Data/` that directly imports `Mathlib.CategoryTheory.*`
or `Geb.Mathlib.CategoryTheory.*`, the latter because it extracts to
the former: currently `PFunctor/Slice/Functor.lean`,
`PFunctor/Presheaf/Basic.lean`, `PFunctor/Presheaf/Functor.lean`,
`PFunctor/Univariate/Functor.lean`, `PFunctor/Univariate/W.lean`,
`PFunctor/Univariate/Initial.lean`, `PFunctor/IndRec/Basic.lean`, and
`PFunctor/IndRec/Naturality.lean`. Files importing those transitively —
`PFunctor/Presheaf/W.lean`, the rest of the `IndRec` family — follow
whatever placement is settled for them. Scoping the item by that
criterion
rather than by a module list keeps it from being settled
incompletely.

### Upstream destination of core- and Batteries-targeted content

Settle where content under `Geb/Mathlib/` whose upstream target is
Lean core or Batteries rather than mathlib4 belongs. Such content
exists because `docs/rules/upstream-eligible.md` § Subtree import
rules restricts `Geb/Mathlib/` modules to `Mathlib.*`, `Batteries.*`
and `Geb.Mathlib.*` imports: a dependency of a `Geb/Mathlib/` module
cannot live in `Geb/Internal/`, so a module restating core or
Batteries API sits under `Geb/Mathlib/` while its upstream is neither
mathlib4 nor CSLib. In scope is every module under `Geb/Mathlib/`, and
every `GebTests/Mathlib/` parallel, whose declarations restate or
replace declarations of Lean core or Batteries rather than of mathlib:
currently `Geb/Mathlib/Data/Vector/OfFn.lean` and its test parallel.
Scoping the item by that criterion rather than by a module list keeps
it from being settled incompletely; the criterion does not reach
`Geb/Mathlib/Data/Vector/NodupEquivFin.lean`, whose statement is an
`Equiv` and so has no core or Batteries home.

`scripts/extract-pr.sh` is the enforcer: its `Geb/Mathlib/*` arm maps
unconditionally to `Mathlib/` and its `GebTests/Mathlib/*` arm to
`MathlibTest/`, so a core-targeted module extracts to the wrong
upstream silently. Changing either mapping waits on this item's
outcome.

### Complete Theorem 2.4 for `IndRec`

Layered like the polynomial-functor code (constructive core first, thin
`Classical.choice`-enabled categorical wrapper second). The two remaining
layers for Theorem 2.4 of [GhaniNordvallForsbergMalatesta2015] follow.

In the existing constructive files, without `Classical.choice`,
remaining: the uniqueness properties of `IR.elim` and `IR.rec` as
algebra morphisms, constructively stated (the Theorem 3 development
does not need this item).

In a separate sibling file wrapping the constructive proofs in
mathlib `Category`/`Functor` interfaces (pretty much everything
involving mathlib's `Category` pulls in `Classical.choice`, so the
wrapper is kept thin, following `Slice/Functor.lean` and
`Presheaf/Functor.lean`):

1. `FreeCoprodCompDisc` as a `Category` and the interpretation of a
   code as a `Functor`.
2. The initiality of `IR` in the category of algebras (mathlib's
   `CategoryTheory.Endofunctor.Algebra`), wrapping the constructive
   uniqueness proofs.

### Theorems 2 and 4 for `IR` codes

Parallel to "Complete Theorem 2.4 for `IndRec`", and building on the
category of `IR` codes in `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
(see `docs/index.md`). Two results of
[HancockMcBrideGhaniMalatestaAltenkirch2013] remain: Theorem 2,
the left-Kan-extension characterization of the `δ`-code
interpretation, and Theorem 4, the equivalence with dependent
polynomial functors.

### Validate `PresheafPFunctor.functor` as a parametric right adjoint

Establish the natural isomorphism confirming that `PresheafPFunctor.functor`
is the parametric right adjoint determined by its generic data `(T1, E_T)`.

### Exhaustive verification of presheaf PRA laws for finite instances

The `FinitePresheafPFunctor` structure bundles `FinEnum J` alongside the
domain finiteness. With both index categories finite, the functor laws
(`ShapeRestrId`, `ShapeRestrComp`, `ReindexNaturality`, `ReindexId`,
`ReindexComp`, and the domain-side `DirectionRestrId`,
`DirectionRestrComp`) are exhaustively verifiable by enumeration: each
law quantifies over finitely many objects, morphisms, shapes, and
directions, and the equalities are decidable (shapes and directions
have `DecidableEq` from the bundled `FinEnum` evidence). A `decide`-
based test harness can confirm that a concrete `FinitePresheafPFunctor`
satisfies all laws without manual proof, turning the law fields from
trusted input into checked input. The laws quantifying over
`J`-morphisms additionally need finite `J`-hom-sets, which the structure
does not currently bundle: a `finEnumHomJ` field is added by the commit
that first consumes it. This is a testing/verification concern (not a
new decidability instance) and is distinct from the decidability of
fiber membership already implemented.

## Triggers (do when condition fires)

- **Slice polynomial functor natural isomorphism**: when a
  constructive (computable) `Type`-is-locally-cartesian-closed
  structure is available, in mathlib or built here, establish the
  natural isomorphism between `SlicePFunctor.functor` and the
  categorical composite `Σ_t ∘ Π_f ∘ Δ_s`.
- **Adopt `leanprover-community/upstreaming-dashboard-action`**:
  when we judge we have enough novel and interesting content that
  members of the mathlib community would likely want to be made
  aware of the project — a standing question, revisited as content
  grows. Then add the action to CI plus a Pages-published
  dashboard following FLT's pattern.
- **`downstream-reports` registration**: a manual periodic
  checkpoint by the user. Trigger: "do we have enough substantive
  content that registration would be informative for the
  community, given the daily Zulip notification cost?" The pipeline
  and its trigger are described in `docs/process.md` § LKG/FKB
  pipeline.
- **Verso adoption** (three scopes with distinct gates; doc-gen4
  and Verso are complementary, not alternatives — doc-gen4
  generates the API reference, Verso authors hand-written prose):
  1. Docstrings in `.lean` files: gated on doc-gen4 gaining
     Verso-aware rendering and mathlib migrating to Verso;
     contraindicated for `Geb/Mathlib/` and `Geb/Cslib/` until
     both hold (Verso-markup docstrings would read as foreign to
     mathlib reviewers and would not render on the doc-gen4 site).
  2. Persistent prose (`docs/`, a future Geb-language exposition):
     gated on the prose growing substantial and describing stable,
     existing code. `CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`,
     `docs/process.md`, and `docs/rules/*` remain Markdown
     regardless (GitHub rendering, tool and `@import` consumption,
     markdownlint, doctoc).
  3. Transient design docs on feature branches: no external gate;
     candidate for a local-only Verso build to evaluate authoring
     ergonomics and type-checking of embedded Lean.

  Currently using Markdown rendered by doc-gen4. A local pilot
  (2026-07-02) validated the mechanism: Verso and mathlib coexist in
  one lake project at v4.32.0-rc1, embedded Lean type-checks (a
  mismatch fails the build with a locatable error), and
  within-document references resolve. Two follow-up workstreams, each
  its own spec/plan cycle when taken up:
  - Persistent Geb-language exposition seed chapter in Verso
    (scope 2), once exposition-worthy prose exists.
  - Verso for transient feature-branch design docs (scope 3); a
    change to the current Markdown-based brainstorming and
    writing-plans flow, so it needs its own scoping.
- **Project-specific `geb-development` skill**: when recurring
  patterns accumulate that fit neither `CONTRIBUTING.md`,
  `AGENTS.md`, `CLAUDE.md`, `docs/process.md`,
  `docs/rules/*.md`, nor existing `.claude/rules/*.md`. Default
  is to wait for friction.
- **Author `.github/PULL_REQUEST_TEMPLATE/` for our repo**:
  trigger when the first PR against our own repo is opened (most
  likely the bump-PR cron).
- **Curated `notes` / `journal` directory**: trigger if recurring
  ad-hoc explorations accumulate that don't fit `docs/`.
- **Migrate `update.yml` from `GITHUB_TOKEN` to a PAT**: trigger
  if the manual close-and-reopen-to-fire-CI overhead on cron-
  created bump-PRs becomes burdensome.
- **Reconcile test-module import visibility**:
  `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean` uses
  `public import` for its module-under-test while every sibling
  test module uses plain `import`; `GebTests/Internal/`'s
  `public meta import` lines are in the same category. Import
  visibility changes what a module re-exports, so it is deferred.
  Trigger: the next branch that revises the test modules'
  interfaces.
- **Decide a test-declaration privacy discipline**: test modules
  mix `private` and public declarations with no uniform rule;
  the IndRec test's type-valued definitions must stay `@[expose]`
  public for cross-module compilation, so blanket privatization
  is not obviously desirable. Privacy changes module-interface
  visibility, so it is deferred. Trigger: the next branch that
  revises the test modules' interfaces.
- **Add `ext_iff` companions**: mathlib's naming guide
  (§ Extensionality) prescribes bidirectional
  `f = g ↔ ∀ x, f x = g x` companions alongside `ext` lemmas;
  none exist for `GrothendieckOp.hom_ext`,
  `CoGrothendieck.hom_ext`, or `IR.ext` (`IR.snd_eq_of_eq` is a
  converse but is not packaged as `ext_iff`). Adding them alters
  the theorem-set, so it is deferred. Trigger: the next branch
  that revises these interfaces.
- **Extract a shared presheaf test-fixtures module**: the
  `presheafWitness : PresheafPFunctor (Fin 2) (Fin 2)` fixture is
  duplicated in `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`
  and `.../Presheaf/W.lean` because the `Basic` test module has no
  `public section`. Trigger when a third consumer appears: introduce a
  `public`-exported `GebTests/Mathlib/Data/PFunctor/Presheaf/Fixtures.lean`
  and import it from each. The condition has been met:
  `.../Presheaf/Decidable.lean` re-declares the same fixture data as a
  third consumer. Take the extraction together with the two items
  above (test-module import visibility, test-declaration privacy
  discipline); the extraction entails both, since the fixtures module
  can only be shared by making the currently-private fixture data
  public and importing it from every consumer.
- **Choice-free `Array.ofFn` lemmas**: when an upstream submission
  touching root `Vector`'s `ofFn` API is prepared, give
  `Array.getElem_ofFn_go` (`Init/Data/Array/Lemmas.lean`) a
  choice-free proof in Lean core, from which `Array.getElem_ofFn`,
  `Array.toList_ofFn`, `List.toArray_ofFn`, `Vector.getElem_ofFn`,
  `Vector.ofFn_getElem`, `Vector.getElem_range` and
  `Vector.getElem_finRange` all follow, retiring `Vector.ofFnC` and
  its round trips. It does not retire the `get`/`getElem` bridge in
  the same module: core states no `Vector.get_eq_getElem`, and a
  repaired core lemma is still in `getElem` form. The bridge goes only
  if the direct `Batteries.Data.Vector.Lemmas` import is taken at the
  same time, which the repair would make safe by de-tainting
  Batteries' `get_ofFn` and `get_range`; that is a second decision,
  not a consequence of this one. This is a Lean core submission, not a
  mathlib one, and it does not reach
  `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`, whose statement is an
  `Equiv` and so has no core or Batteries home.
- **Choice-free `Skeletal FinSetSkel`**: when a use for it arises
  outside an allowlisted module, prove it directly rather than
  transporting it along the isomorphism to `FintypeCat.Skeleton`. That
  needs a choice-free pigeonhole, mathlib's `Fin.equiv_iff_eq`,
  `Fintype.card_congr` and `Fintype.card_fin` all depending on
  `Classical.choice`. There is no such use while `Skeletal` is
  consumed only by the wrapper.
