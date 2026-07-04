# Design: polynomial-functor terminology standardisation

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Summary](#summary)
- [Terminology decisions](#terminology-decisions)
  - [Retained (settled or confirmed standard)](#retained-settled-or-confirmed-standard)
  - [The two indexing maps](#the-two-indexing-maps)
  - [The presheaf actions](#the-presheaf-actions)
  - [Retired "leg", "tag", "constraint"](#retired-leg-tag-constraint)
  - [Base / total / projection](#base--total--projection)
  - [Incidental local variables](#incidental-local-variables)
- [Scope](#scope)
- [Non-goals](#non-goals)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Transient spec for the topic branch executing roadmap item 1
(TODO.md § "Standardise slice and polynomial-diagram
terminology"). Removed from the working tree in the branch's final
commits per CONTRIBUTING.md § Concern shape.

## Summary

Replace the non-standard names and comments in the slice and
presheaf polynomial-functor sources with terms drawn from the
named presentations these structures instantiate, and make the
existing base/total/projection vocabulary consistent. No semantic
change: identifiers are renamed and docstrings and comments are
reworded; no definition, statement, or proof is altered.

The two named presentations, verified against primary sources:

- The slice layer is the indexed container `(S, P, q, r)` of
  [AltenkirchGhaniHancockMcBrideMorris2015], itself a notational
  variant of the dependent polynomial functors of
  [GambinoHyland2004] and [GambinoKock2013]. Its two indexing
  arrows are `q : S → O` (each shape's output index) and
  `r : P → I` (each position's input index).
- The presheaf layer is the parametric right adjoint of
  [Weber2007], whose data are the presheaf `T1` and the functor
  `E_T` on `el(T1)` — notation retained verbatim.

## Terminology decisions

### Retained (settled or confirmed standard)

`shape` (`A`) and `direction` (`B`); `dom` / `cod`; `Obj` / `obj`
/ `map`; `Compatible` / `compatible_iff`; `reindex` (reindexing =
base change, standard in fibred categories); `DirectionOver` /
`ShapeOver` / `Direction` / `Shape`; `T1`, `E_T`, `el(T1)`
([Weber2007]).

### The two indexing maps

Renamed to the [AltenkirchGhaniHancockMcBrideMorris2015] letters
and given explicit `(defined-on)-(lands-in)` descriptors:

| Was | Now | Descriptor in prose |
| --- | --- | --- |
| field `s`, `sCurried` | `r`, `rCurried` | `direction-input` map |
| field `t` | `q` | `shape-output` map |

"input" / "output" match both [AltenkirchGhaniHancockMcBrideMorris2015]
(a functor `Set^I → Set^O`) and the existing "input presheaf" /
"output presheaf" wording in `Presheaf/Basic.lean`. The retired
"source" / "target" mnemonic is unattested in the cited sources
(the word "target" does not occur in [GambinoKock2013]).

### The presheaf actions

Both `restr` and `tagRestr` are presheaf restriction maps
("restriction map" is the standard term; [Stacks 006D]). Named by
the presheaf each restricts:

| Was | Now |
| --- | --- |
| `restr`, `RestrId`, `RestrComp` | `directionRestr`, `DirectionRestrId`, `DirectionRestrComp` |
| `tagRestr`, `TagRestrId`, `TagRestrComp` | `shapeRestr`, `ShapeRestrId`, `ShapeRestrComp` |

`reindex` and `Compatible` are unchanged: "reindexing" is
standard for `E_T`'s base-change action, and "compatible" is a
local name for the section condition (the extension's dependent
product has no single standard word for this predicate form).

### Retired "leg", "tag", "constraint"

These are coinages with no provenance in the cited sources.

| Was | Now |
| --- | --- |
| `OverLeg` | `OverInput` (child index family equals `rCurried a`) |
| `tag_triangle` (private) | `output_triangle` |
| "constraint leg" (prose, for `s`) | "direction-input map" |
| "tag leg" (prose, for `t`); "the tag", "`t`-tag", "tagging" | "shape-output map"; "output index" |
| "middle leg of a … diagram" | "middle map of a … diagram" |

### Base / total / projection

Apply the settled slice-object vocabulary uniformly, resolving the
current split (`Presheaf/Basic.lean` already says "total-space
projection" while `Slice/Basic.lean` calls `p` a "base map"):

- `dom` / `cod` and a slice object's carrier: "base space" /
  "total space" ("object" where "space" reads awkwardly).
- `p : X → dom`: "projection" (was "base map").
- a point `i : dom`: "base point" (unchanged).

### Incidental local variables

Adopting `q` / `r` for the fields frees those letters from their
incidental local uses. Move the affected locals to the primed
projection convention already present in the sources:

- `Slice/Basic.lean` `map_comp`: base projections
  `{p} {q : Y → dom} {r : Z → dom}` become `{p} {p'} {p''}`.
- `Slice/W.lean`: the slice-algebra structure map `q : Y → I`
  becomes `p'`.

## Scope

Ten `.lean` files (five source, five test) under the
polynomial-functor subtree, plus two documentation files.

Source:

- `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`
- `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean`
- `Geb/Mathlib/Data/PFunctor/Slice/W.lean`
- `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`
- `Geb/Mathlib/Data/PFunctor/Presheaf/Functor.lean` — prose only:
  retired "tag" wording and docstring `` `t` `` field references
  (no code field access).

Test (mirrors):

- `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean`
- `GebTests/Mathlib/Data/PFunctor/Slice/Functor.lean`
- `GebTests/Mathlib/Data/PFunctor/Slice/W.lean`
- `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`
- `GebTests/Mathlib/Data/PFunctor/Presheaf/Functor.lean` — prose
  only.

Documentation:

- `docs/references.bib` gains the
  [AltenkirchGhaniHancockMcBrideMorris2015] entry.
- `docs/index.md` — one paragraph of retired prose. No other file
  under `docs/` is touched; "tag"/"leg"/"constraint" elsewhere
  refers to git tags, commit types, and unrelated prose.

`Slice/Basic.lean`'s `## References` section gains the key, and its
module docstring names the structure as the indexed container
`(A, B, q, r)`; that citation and the `.bib` entry land in the same
commit.

The module-index roots `Slice.lean` and `Presheaf.lean` are empty
umbrella files carrying none of the renamed tokens and are
unaffected (verified by grep).

## Non-goals

- No change to any definition, statement, proof, universe
  signature, `@[expose]` attribution, or import.
- The TODO.md roadmap additions (relative monads, Day convolution,
  decidable specialisations) are a separate concern on a separate
  branch, written after this rename so they use the settled terms.

## Verification

- `lake build` and `lake test` remain green (a rename touches no
  proof).
- `lake lint` (the `GebMeta.detectNonstandardAxiom` env-linter)
  reports the same permitted-axiom set — a rename cannot change
  axiom dependencies.
- `markdownlint-cli2` passes on `docs/index.md` and this spec.
- Grep confirms the retired terms are absent, scoped to
  `Geb/Mathlib/Data/PFunctor`, `GebTests/Mathlib/Data/PFunctor`, and
  `docs/index.md` (not the wider `docs/` tree): the phrases
  `constraint leg` / `tag leg` / `base map`; the inflected coinages
  `tag` / `tagged` / `retag` / `\bleg\b` (excluding the legitimate
  `## Tags` docstring heading); the identifiers `sCurried` /
  `tagRestr` / `\brestr\b` / `OverLeg` / `tag_triangle`; and field
  access `\.s` / `\.t` on these structures.

## References

- [AltenkirchGhaniHancockMcBrideMorris2015] — indexed containers;
  the `(S, P, q, r)` presentation and the `q` / `r` indexing
  arrows.
- [GambinoHyland2004], [GambinoKock2013] — dependent polynomial
  functors.
- [Weber2007] — parametric right adjoints; `T1`, `E_T`, `el(T1)`.
- [Stacks 006D] — "restriction map" for a presheaf's action.
