# Design: polynomial-functor roadmap additions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Design: polynomial-functor roadmap additions](#design-polynomial-functor-roadmap-additions)
  - [Summary](#summary)
  - [Design decisions (settled in brainstorming)](#design-decisions-settled-in-brainstorming)
  - [Concrete `TODO.md` changes](#concrete-todomd-changes)
    - [New item 1](#new-item-1)
    - [Restructured universal-morphisms item](#restructured-universal-morphisms-item)
    - [Unified relative-(co)free-(co)monad item](#unified-relative-cofree-comonad-item)
  - [New `docs/references.bib` entries](#new-docsreferencesbib-entries)
  - [Scope](#scope)
  - [Non-goals](#non-goals)
  - [Verification](#verification)
  - [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Transient spec for the topic branch expanding the polynomial-functor
roadmap in `TODO.md`. Removed from the working tree in the branch's
final commits per CONTRIBUTING.md § Concern shape.

## Summary

Update the `TODO.md § Next up` polynomial-functor roadmap: retire the
completed terminology item, add a decidable-specialization item,
restructure the universal-morphisms item into an explicit ordered
sequence, and unify the free-monad and cofree-comonad items into a
single relative-(co)free-(co)monad item. Documentation only: no code,
no `.lean` change; add three `docs/references.bib` entries for the new
literature references.

## Design decisions (settled in brainstorming)

- **Retire old item 1** ("Standardise slice and polynomial-diagram
  terminology"): completed and merged; its outcome is in the code and
  `docs/index.md`.
- **Decidable specializations go early**, right after the definitions:
  they specialize the definitions themselves, depend only on the
  existing functors, and make the decidable functors available for the
  universal-morphism phase.
- **Universal morphisms fold Day convolution and left Kan into a
  restructured item 6** (not a separate item — not every universal
  morphism comes from them), with the explicit 12-step order below,
  each step layered across the three forms.
- **Free/cofree monads unify into one relative-(co)free-(co)monad
  item**: a slice/presheaf functor is an endofunctor only when its
  domain and codomain bases coincide, so the relative notion is the
  correct general one and the ordinary (co)free (co)monad is the
  `J = id` case. Implementation order turns on an open technical
  question (below), governed by: avoid code duplication first;
  simpler-first within that.

## Concrete `TODO.md` changes

Delete old `### 1. Standardise slice and polynomial-diagram
terminology` (lines 48–63) and put the new decidable item in its
place. Items 2–5 (presheaf W-types; `PFunctor`/`WType` wrappers; W-type
initiality; M-types) keep their numbers unchanged. Old items 7 (free
monads) and 8 (cofree comonads) merge into the single new item 7. The
`Validate PresheafPFunctor.functor …` trigger is unchanged. The new and
restructured entries read:

### New item 1

```markdown
### 1. Decidable-property specializations of the functor definitions

The slice and presheaf functors are specializations of mathlib's
`PFunctor`: a restriction to a domain by a compatibility property on
the direction-input map, together with a shape-output map assigning
each shape a codomain index. Add explicit specializations for the case
where the compatibility property is decidable (typically the finitary
case; the exact conditions are settled when this item is taken up). This specializes the functor definitions
directly, so it depends only on the existing definitions and precedes
the constructions built on them; the decidable functors are then
available downstream, in particular for the decidable-case
specializations of the universal morphisms (item 6).
```

### Restructured universal-morphisms item

```markdown
### 6. Universal morphisms

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
specializations (item 1) of those universal morphisms with interesting
decidable forms.
```

### Unified relative-(co)free-(co)monad item

```markdown
### 7. Relative (co)free (co)monads

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
(the relative case, in extension form).

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
corresponding slice/presheaf W-type (item 4) or M-type (item 5) and
show the definitions equivalent, as in the superseded free-monad and
cofree-comonad items.
```

## New `docs/references.bib` entries

Add (bibliographic detail verified against nLab and arXiv):

- `AltenkirchChapmanUustalu2015` — Altenkirch, Chapman, Uustalu,
  "Monads need not be endofunctors", LMCS 11(1:3), 2015,
  arXiv:1412.7148, doi:10.2168/LMCS-11(1:3)2015 (conference version
  FoSSaCS 2010, LNCS 6014, pp. 297–311).
- `ArkorMcDermott2024` — Arkor, McDermott, "The formal theory of
  relative monads", J. Pure Appl. Algebra, 2024, arXiv:2302.14014,
  doi:10.1016/j.jpaa.2024.107676.
- `DePascalisUustaluVeltri2025` — De Pascalis, Uustalu, Veltri,
  "Monoid Structures on Indexed Containers", 2025, arXiv:2509.25879
  (indexed-container monads, free monads, and product of monads;
  relevant to items 6–7).

## Scope

- `TODO.md` — the roadmap edits above.
- `docs/references.bib` — the three entries.

Documentation only. No `.lean` file, no build/test surface.

## Non-goals

- No code, no implementation of any roadmap item — this branch only
  records the plan.
- The exact decidable conditions (item 1), the item-6 layering
  details, and the item-7 build-order question are deferred to each
  item's own planning cycle, as the roadmap's discipline prescribes.

## Verification

- `markdownlint-cli2` passes on `TODO.md` and this spec; the `TODO.md`
  doctoc TOC is regenerated (`doctoc --update-only`).
- The three new `.bib` keys resolve for any `[Key]` reference (only
  the spec references them here; the `.lean` citations come with each
  item's implementation).
- Grep confirms old item 1's terminology text is gone from `TODO.md`
  and the renumbering is consistent (items 1–7 plus the trigger).

## References

- [AltenkirchChapmanUustalu2015], [ArkorMcDermott2024],
  [DePascalisUustaluVeltri2025] — new entries above.
- [rokopt/geb `PolyUMorph.lean`, `RelativeMonad.lean`] — exploratory
  models (reference-only; formulas adapted to our representation).
