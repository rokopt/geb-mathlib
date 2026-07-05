# Presheaf (PRA) W-types design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Scope](#scope)
- [Structural model](#structural-model)
- [Universes](#universes)
- [Guiding discipline: recursion through recursors](#guiding-discipline-recursion-through-recursors)
- [Design](#design)
  - [Part A — Policy: recursion through recursors (`docs/rules/lean-coding.md`)](#part-a--policy-recursion-through-recursors-docsruleslean-codingmd)
  - [Part B — Slice-layer completion (`Slice/W.lean`)](#part-b--slice-layer-completion-slicewlean)
  - [Part C — Functor-layer generalization (`Presheaf/Basic.lean`)](#part-c--functor-layer-generalization-presheafbasiclean)
  - [Part D — Presheaf W-type (`Presheaf/W.lean`)](#part-d--presheaf-w-type-presheafwlean)
- [Artifacts](#artifacts)
- [Branch and lifespan](#branch-and-lifespan)
- [Constraints](#constraints)
- [Decisions](#decisions)
- [Open questions](#open-questions)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Purpose

Roadmap item 2 (`TODO.md`): define the W-types (initial algebras) of the
presheaf polynomial (parametric-right-adjoint) functors as a restriction of
the slice polynomial W-types in `Geb/Mathlib/Data/PFunctor/Slice/W.lean`,
mirroring how the presheaf functors are a restriction of the slice functors
and the slice functors a restriction of mathlib's `PFunctor`. It is the last of
the four functor/W-type layers: `PresheafPFunctor.W` stands to
`SlicePFunctor.W` as `PresheafPFunctor.obj` stands to `SlicePFunctor.Obj`.

The mathematical object is the initial algebra of a polynomial /
parametric-right-adjoint endofunctor on a presheaf category (this workstream
establishes its existence half; see Scope). Each cited source underwrites a
distinct part: the existence of the W-type (initial algebra) of a
dependent-polynomial endofunctor on a locally cartesian closed category, of
which a presheaf category is an instance, is [GambinoHyland2004],
[GambinoKock2013]; the parametric-right-adjoint presentation `(T1, E_T)` being
restricted is [Weber2007]; the subtype-by-predicate engineering has its
discrete-index-set analogue in the indexed-container W-types of
[AltenkirchGhaniHancockMcBrideMorris2015]. The layered Lean realization —
building the carrier as a subtype of the slice W-type through the slice-W
recursor — is novel engineering, not a transcription of a specific published
construction.

## Scope

The existence half of initiality, matching the boundary already set in
`Slice/W.lean`: the carrier presheaf, its fixed-point structure (`mk`/`dest`),
and the catamorphism `elim` with its computation and over-`I` laws.
Uniqueness of `elim` and the categorical initial-object wrapper are out of
scope; they are roadmap item 4.

Endofunctor restriction: as an initial algebra requires an endofunctor, the
domain and codomain categories coincide (`I = J`), exactly as `Slice/W.lean`
forces `dom = cod`.

## Structural model

Take `I = J`. For `F : PresheafPFunctor I I`:

- The underlying object-level slice endofunctor `F.toSlicePFunctor :
  SlicePFunctor I₀ I₀` (`I₀` the object type of `I`) is already a field of
  `F`. Its slice W-type `F.toSlicePFunctor.W` is the underlying `I₀`-indexed
  tree family of the presheaf W-type.
- The presheaf W-type carrier is a **subtype** of that slice W-type, fibred
  over each object `j` by `windex`, cut out by a hereditary naturality
  predicate.
- The presheaf restriction map is **root-only** (non-recursive): for
  `g : j' ⟶ j` and a tree destructing to shape `a` and direction-assignment
  `φ`, restriction is `(shapeRestr g a, φ ∘ reindex g a)`. Because `reindex g a`
  preserves the base index, every subtree already sits at the correct index; no
  subtree is touched. This is the tree-level image of the functor-layer
  `objRestrElt` (the raw rewiring, which Part C generalizes and the W layer
  reuses; the subtype-level `objRestr` is `IsNatural`-specific and not reused).
- The recursion lives entirely in the hereditary naturality predicate, the
  tree-level analog of the functor-layer `IsNatural`.

This is the direct W-type transcription of the parametric-right-adjoint formula
`W(j) = Σ_{a ∈ T1(j)} Nat(E_T(a), W)`.

## Universes

The p.r.a. functor is not a fixed-universe endofunctor: for
`Z : Iᵒᵖ ⥤ Type uZ`, `objPresheaf Z : Iᵒᵖ ⥤ Type (max uI uZ uA uB)`, the `uI`
entering through the total space `Σ i : I, Z.obj ⟨i⟩` of `elemProj`. The
slice W-type carrier sits at `Type (max uA uB)` — it carries no `uI`, since
`windex` is a separate map `F.W → I`, not stored in the type. So the fixed
point lives at the least universe closed under the functor,
`uW := max uI uA uB`.

The presheaf W-type is therefore a presheaf `Iᵒᵖ ⥤ Type uW`, with fibres
`ULift.{uI}` of the `Type (max uA uB)` tree subtype. The lift is definitionally
trivial, so `mk` / `dest` / `elim` thread `ULift.up` / `ULift.down` around the
reused slice `mk` / `dest`; with it, `objPresheaf W` and `W` inhabit the one
category `Iᵒᵖ ⥤ Type uW`, so the algebra structure and `elim` are genuine
morphisms there. (The slice layer avoided this because `Over dom` does not pin a
value universe the way `Iᵒᵖ ⥤ Type v` does.) The alternative — assuming
`uI ≤ max uA uB` to drop the lift — is rejected as an unmotivated constraint on
the base category.

## Guiding discipline: recursion through recursors

All recursion and induction in this work is expressed through recursors —
mathlib's (`WType.elim`, `WType.rec`), Lean's auto-generated ones, and the
slice-W recursor added here (itself a wrapped `WType.rec`). No `induction`
tactic, no self-calling `def`, no self-referential datatype. This keeps every
datatype and recursion expressed as a polynomial functor and its recursor, so
each participates in the category of polynomial functors — composable with the
standard combinators, assemblable à la carte, with every morphism between two
such datatypes taking the one uniform form of a natural transformation of
polynomial functors. The rule is being written into
`docs/rules/lean-coding.md` as part of this work (Part A below).

## Design

### Part A — Policy: recursion through recursors (`docs/rules/lean-coding.md`)

Add a subsection under *Coding technique* stating the discipline above with its
full polynomial-functor rationale inline. The rationale is sited inline (rather
than deferred to `docs/process.md` with a terse pointer, the usual house
pattern) because the discipline is pervasive: it governs every datatype and
every recursion in the project, so the reason it holds belongs where every
`.lean`-editing contributor meets the rule.

### Part B — Slice-layer completion (`Slice/W.lean`)

The one API the presheaf construction needs and the slice W-type does not yet
expose: **structural recursion** for `SlicePFunctor.W`, wrapping `WType.rec` /
`WType.elim` so downstream code recurses on `F.W` (children arriving already as
`F.W` values, as `dest` yields them) without touching mathlib's `WType`. Two
forms are needed:

- `SlicePFunctor.W.ind` — the induction principle (`Prop` motive), a theorem:
  from a step `∀ (x : Obj windex), (∀ b, motive (x.1.2 b)) → motive (W.mk x)`,
  conclude `∀ z, motive z`. Derivable from `WType.rec` + `mk_dest` +
  `wValid_mk`; being a `Prop`-motive theorem, the `WType.rec` application is
  unproblematic (as in `elimData_valid`). Used for the presheaf `elim`
  naturality proof and the carrier functor laws.
- A **subtree-exposing** recursor for *defining* the hereditary predicate. This
  is the decisive point of Part D: the local naturality equation compares whole
  child *subtrees* (`x.1.2 (directionRestr a f b).1 = «rewire» f (x.1.2 b)`), so
  a plain `WType.elim` fold into `fun _ => Prop` is insufficient — it hands the
  algebra only the children's folded `Prop` values, not the subtrees (the same
  obstruction `Slice/W.lean` documents for `OverInput`). The primary encoding
  is a `WType.elim` fold into a small structure carrying the reconstructed
  subtree alongside the `Prop` (mirroring `ElimData`'s `value` / `over`), so it
  is a code-generatable fold and stays `{propext, Quot.sound}`; a `WType.rec`
  application directly into `Prop` is the fallback if it verifies clean (a
  `Prop`-valued predicate is erased, so it need not incur the `noncomputable`
  flag that a data-valued `WType.rec` `def` does). A `WType.rec` proof relating
  the fold's carried subtree to the original tree — the reconstruction lemma,
  analogous to `elimData_valid` — supports the predicate's unfolding. The exact
  decl shape is settled against the axiom linter at implementation.

### Part C — Functor-layer generalization (`Presheaf/Basic.lean`)

Generalize the element-level rewiring over its projection so the W-layer reuses
it verbatim rather than duplicating it:

- `objRestrElt`, `objRestrElt_id`, `objRestrElt_comp` — generalize from the
  pinned `elemProj Z` to an arbitrary projection `{p : X → I}`. Their bodies
  use only `shapeRestr` / `reindex` / `compatible_iff`, never `Z`, so the
  generalization is faithful.
- `objRestr`, `value_objRestrElt`, and the `objPresheaf` naturality remain
  presheaf-`Z`-specific (their payload is an `IsNatural`/`value` fact) and are
  unchanged.

The functor layer instantiates the generalized rewiring at `p := elemProj Z`
(as now); the W layer instantiates it at `p := windex`.

### Part D — Presheaf W-type (`Presheaf/W.lean`)

New file, mirroring `Slice/W.lean` (recursor/fixed-point machinery) and
`Presheaf/Basic.lean` (`shapeRestr`/`reindex`/naturality bookkeeping).

Main definitions (namespace `PresheafPFunctor`; `SliceW := F.toSlicePFunctor.W`):

- `PresheafPFunctor.IsHereditarilyNatural : SliceW → Prop` — the tree-level
  `IsNatural` (named with the `Is` prefix to match its functor-layer sibling),
  defined via the subtree-exposing slice-W recursor (Part B): at each node the
  local naturality equation `x.1.2 (directionRestr a f b).1 = «rewire» f
  (x.1.2 b)` holds and every child is hereditarily natural. The rewiring
  (`«rewire» : SliceW → SliceW`) is the root-only, one-level operation
  `objRestrElt` (generalized, at `p := windex`) conjugated by `dest` / `mk`.
- `PresheafPFunctor.W` — the carrier presheaf `Iᵒᵖ ⥤ Type uW`
  (`uW = max uI uA uB`; see Universes), with `W.obj ⟨j⟩` the `ULift.{uI}` of
  `{ w : SliceW // windex w = j ∧ IsHereditarilyNatural w }`,
  and restriction maps from the generalized `objRestrElt` at `p := windex`,
  packaged with `IsHereditarilyNatural`-preservation. Its `map_id` / `map_comp`
  transport from the `shapeRestr` / `reindex` laws exactly as `objPresheaf`'s do
  (reusing the generalized `objRestrElt_id` / `objRestrElt_comp`).
- `PresheafPFunctor.W.mk` / `W.dest` — the fixed-point structure making `W` an
  `F.functor`-algebra: mutually-inverse maps between `(objPresheaf W).obj ⟨j⟩`
  and `W.obj ⟨j⟩`, reusing the slice `mk` / `dest` (threaded through
  `ULift.up` / `ULift.down`) and matching `IsNatural` (one level) against
  `IsHereditarilyNatural` unfolded one level (mirroring `wValid_mk`).
- `PresheafPFunctor.W.elim` — the morphism into any presheaf algebra
  `(Y : Iᵒᵖ ⥤ Type uW, α : F.functor.obj Y ⟶ Y)`: the slice `elim` supplies the
  underlying family map, whose naturality (that it is a presheaf morphism) is
  proved by `SlicePFunctor.W.ind`.

Main statements:

- `W.dest_mk` / `W.mk_dest` — `mk` and `dest` mutually inverse (`W` a fixed
  point of the presheaf endofunctor).
- `W.elim_mk` — the computation rule: `elim` is a morphism of presheaf algebras.
- naturality/over-`I` laws for `mk` and `elim`, mirroring `windex_mk` /
  `comp_elim`.

## Artifacts

- `Geb/Mathlib/Data/PFunctor/Presheaf/W.lean` — the construction.
- `GebTests/Mathlib/Data/PFunctor/Presheaf/W.lean` — its test mirror.
- Edits: `Slice/W.lean` (Part B), `Presheaf/Basic.lean` (Part C),
  `Presheaf.lean` index, `docs/index.md` entry, `docs/rules/lean-coding.md`
  (Part A), `TODO.md` (item 2 removed on completion, per the roadmap).

## Branch and lifespan

Two stacked branches, since Part A is a universal policy change with a
lifespan distinct from the feature code:

1. `doc/recursor-discipline` — a single commit making Part A's edit to
   `docs/rules/lean-coding.md`. This is a self-contained concern (one rule,
   applying repo-wide) and merges independently.
2. `feat/presheaf-w-types` — stacked on top of (1); carries this spec, the
   implementation plan, Parts B–D, and the persistent documentation. This spec
   and the plan are transient and removed in the branch's final commits (per
   `CONTRIBUTING.md` § Concern shape); the code and its `docs/` entries persist.

The stacking (rather than one branch) keeps the policy change reviewable and
mergeable on its own while the feature builds on it. If Part A merges first, the
feature branch rebases onto the updated `main`.

The two branches are logically independent — the feature code follows the
Part A discipline but does not import or code-depend on the rule text — so
under strict partial-order preservation they could equally be siblings off
`main`. Stacking is chosen deliberately: the recursor discipline potentially
affects every piece of code written thereafter, so all subsequent code is to be
written atop a tree in which that instruction is already present. This takes
precedence over the sibling default here.

## Constraints

- Constructive: no `noncomputable`; `Classical.choice` confined to the
  categorical-wrapper surface already allow-listed in
  `GebMeta.classicalAllowedModules`. The core `Presheaf/W.lean` construction
  targets `{propext, Quot.sound}`.
- Recursor-only discipline (Part A) throughout.
- Naming uniform with existing code (`windex*`, `objRestr*`, `directionRestr`,
  `shapeRestr`); no bare `restr`; `Is`-prefixed Prop predicates
  (`IsHereditarilyNatural`, matching `IsNatural`).
- Style, docstring, and module-system rules per `docs/rules/lean-coding.md`.

## Decisions

- Part A rationale is sited inline in `lean-coding.md` (§ Part A).
- Part A ships as a standalone commit on `doc/recursor-discipline`, with
  `feat/presheaf-w-types` stacked on top (§ Branch and lifespan). Stacking
  (over the sibling default) is chosen so all subsequent code is written atop a
  tree in which the recursor discipline is already present.

## Open questions

1. Exact decl shape of the subtree-exposing slice-W recursor (Part B) — the
   `WType.elim` fold-with-reconstructed-subtree encoding versus a direct
   `WType.rec`-into-`Prop` — settled against the axiom linter at
   implementation. The definability itself is not open (§ Part B); only which
   of the two `{propext, Quot.sound}`-clean realizations reads most directly.

## References

- [Weber2007] — parametric right adjoints, familial functors; the
  `(T1, E_T)` presentation restricted here.
- [GambinoKock2013] — polynomial functors and polynomial monads; initial
  algebras of polynomial endofunctors.
- [GambinoHyland2004] — well-founded trees and dependent polynomial functors;
  W-types on a locally cartesian closed category.
- [AltenkirchGhaniHancockMcBrideMorris2015] — indexed containers; the
  discrete-index-set analogue of the subtype-by-predicate W-type.
