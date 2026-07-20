# Handoff: IR-code morphisms, Universes/Container relocation branch

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Background — workstream status](#background--workstream-status)
- [What this branch does](#what-this-branch-does)
- [Critical instructions (hard constraints, unchanged)](#critical-instructions-hard-constraints-unchanged)
- [Process (phase-driven, per CLAUDE.md)](#process-phase-driven-per-claudemd)
- [VCS and mechanics (verified across branches 1–2b)](#vcs-and-mechanics-verified-across-branches-12b)
- [After this branch — branch 2c (next session but one)](#after-this-branch--branch-2c-next-session-but-one)
- [After 2c — branch 2d (final)](#after-2c--branch-2d-final)
- [Where everything is](#where-everything-is)
- [Retention](#retention)
- [First action](#first-action)
- [References](#references)

<!-- END doctoc -->

You are continuing the IR-code morphisms workstream in the geb-mathlib
repository (Lean 4 + mathlib, strict constructive discipline). Start
the relocation branch on a fresh topic branch off `main`. This handoff
supersedes `2026-07-20-indrec-morphisms-2b.md` (branch 2b is merged);
both files remain in the tree until the workstream's last branch
removes all transient documents (see Retention).

## Background — workstream status

The workstream formalizes the category of IR codes from
[HancockMcBrideGhaniMalatestaAltenkirch2013] ("Small Induction
Recursion", TLCA 2013) through Corollary 2, with the interpretation
semantics of [GhaniNordvallForsbergMalatesta2015]. Merged so far:

- Branch 1 (PR #75): precomposition `IR.precomp` (the paper's `γ^i`),
  Lemmas 3 and 4 (`IR.interpDeltaIso`, `IR.interpPrecompIso`,
  pointwise), and the `FreeCoprodCompDisc` coproduct machinery.
- Branch 2a (PR #76): the homset `IR.Hom` (Definition 8) and the
  syntactic identity `IR.id` —
  `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`.
- Branch 2b (PR #77): the Theorem 2.4 functoriality content —
  `FreeCoprodCompDisc.Hom.id` + category laws +
  `coprodMor_id`/`coprodMor_comp`; the propositional computation rule
  `IR.rec_mk` (with `IR.elim_mk` and per-constructor forms) in
  `Basic.lean`; `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean` with
  the characterizing equations `IR.interpMor_mk`/`_iota`/`_sigma`/
  `_delta` and the functor laws `IR.interpMor_id`/`IR.interpMor_comp`.

The remaining branches, dependency-ordered (spec § Branch
decomposition): this relocation branch (after 2b), then 2c
(naturality and Theorem 3, depends on 2b), then 2d (composition and
the category laws by transfer, depends on 2a and 2c).

## What this branch does

A single-concern refactor discharging the spec's placement
requirement (spec § Placement and documentation): the morphism
development must precede the `Universes` and `Container` sections, so
later workstreams can extend those sections with morphism uses
without import cycles into `Basic.lean`.

1. Move `section Universes` of
   `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` (declarations
   `univBinder`, `univSigma`, `univPi`, `univIota`,
   `UnivConstructor`, `univConstructorCode`, `univCode`, `univEndo`,
   `univEndoMor`; local `universe uK uT`) into a new sibling module
   `Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean`.
2. Move `section Container` (declaration `contCode`) into a new
   sibling module `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean`.
3. Move their tests out of
   `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean` into mirrored
   new test modules. The test file interleaves core-IR tests with
   universe/container tests; the plan fixes the split (universe
   name-constructor tests, iterated-endofunctor tests, and container
   tests move; core `IR`/`interpObj`/`interpMor`/`precomp`/`rec`
   tests stay).
4. Register every new module in BOTH umbrellas
   (`Geb/Mathlib/Data/PFunctor/IndRec.lean` and
   `GebTests/Mathlib/Data/PFunctor/IndRec.lean`) — a missed source
   umbrella is a known failure mode caught only by `pre-push.sh`.
5. Module docstrings: the new modules take over the moved sections'
   documentation and citations (`univCode`: Examples 2.5–2.6 of
   [GhaniNordvallForsbergMalatesta2015]; `contCode`: Example 1 of
   [HancockMcBrideGhaniMalatestaAltenkirch2013]); `Basic.lean`'s
   module docstring drops the moved entries; `docs/index.md` splits
   the corresponding entry.

The mathematical content is fixed: every moved declaration keeps its
name, statement, and proof term exactly (the repository's
math-content-fixed rule; a reviewer should be able to verify the move
with `git diff --color-moved`). No new mathematics, no renames, no
proof changes, no morphism uses of universes or containers yet.

Design decision left to the plan: the new modules' imports. Importing
only `Geb.Mathlib.Data.PFunctor.IndRec.Basic` compiles today and
satisfies `lake shake` (an unused `Functor` import would be flagged);
the placement requirement is discharged by the extraction itself,
since a later branch can add a `Functor` import to the new modules
without creating a cycle. Recommend minimal imports; record the
rationale in the plan.

## Critical instructions (hard constraints, unchanged)

1. Recursor-only recursion; no `induction` tactic; no self-recursive
   `def`; no `termination_by`. (Moot for a pure move, but binding on
   any incidental edits.)
2. Explicit proof terms — no `by` blocks in committed code.
3. Constructive and axiom discipline: no `noncomputable`, no
   `Classical`; `lake lint` runs the `GebMeta` axiom linter
   ({propext, Quot.sound} only).
4. Universe discipline: full-or-absent `.{…}` lists; no auto-bound
   `u_1`; the moved declarations' existing lists are kept verbatim.
5. mathlib style throughout; commit messages in mathlib conventional
   form (`refactor(indrec): …` for the move).

## Process (phase-driven, per CLAUDE.md)

1. Brainstorming (`superpowers:brainstorming`): brief — the spec
   already specifies the branch; confirm the file split and the
   import decision, adversarially review the delta with a
   fresh-context subagent if any design question surfaces.
2. Writing-plans (`superpowers:writing-plans`): model the plan on
   `docs/superpowers/plans/2026-07-20-indrec-morphisms-2b.md` (the
   latest model: global constraints, file structure, per-task TDD
   with `jj`, both-umbrella registration). For a move, the
   adversarial reviewer verifies content preservation (declaration
   lists identical before/after; `git diff --color-moved`) and that
   the gates pass, rather than re-deriving proofs.
3. Executing (`superpowers:subagent-driven-development`): fresh
   implementer per task; per-task review; final whole-branch review;
   then `lean4:review` and `pr-review-toolkit:review-pr`;
   `scripts/pre-push.sh` before handing to the user. Do NOT push.

## VCS and mechanics (verified across branches 1–2b)

- `jj` for all mutations (a PreToolUse hook blocks mutating `git`;
  read-only `git` is fine). `jj absorb`/`squash --into` folds
  review-fixes into their owning task commits.
- Red (test-first) steps run `lake test` (bare `lake build` does not
  build `GebTests`).
- Durable progress ledger: `.superpowers/sdd/progress.md` (retire the
  2b ledger section as done; keep its Minor-findings list — see next
  paragraph).
- Pitfalls bank (verified during 2b): partial universe lists stall
  unification (`interpMorIota` needs full `.{uA, uB, uI, uO}` at use
  sites whose arguments do not mention `uA`/`uB`); declarations whose
  separated `uA uB` occur only under `max` trip `checkUnivs` AND
  stall inference — use a single index-universe parameter; deep
  `.trans` chains mis-parse when an application argument lands at
  lower indentation — factor into named theorems; new modules need
  BOTH umbrella imports.

Open Minor items from 2b's reviews, recorded in the 2b ledger, that
this or a later branch may pick up (the user left them unfixed at
merge): the `coprodMor` samples never exercise a non-identity
reindexing; `Functor.lean` deliberately omits `## Main definitions`
(its defs are proof scaffolding).

## After this branch — branch 2c (next session but one)

Naturality and Theorem 3, on its own topic branch, with its own
brainstorm → plan → execute cycle. Its handoff should carry this
section's content forward. Key context:

- Deliverables (spec § Naturality and Theorem 3): a notion of natural
  transformation between interpretations (families of
  `FreeCoprodCompDisc.Hom` commuting with the morphism maps, with
  identity and vertical composition), and Theorem 3: the
  interpretation extended to morphisms, `Hom γ γ' → Nat(⟦γ⟧, ⟦γ'⟧)`,
  full and faithful, by induction on the homset structure using
  Lemmas 3 and 4 plus 2b's characterizing equations.
- Closure gate: the constructive, `Classical`-free proof of Theorem 3
  in the `FreeCoprodCompDisc` encoding. The 2c plan derives the
  induction before implementation; if it fails to close, return to
  design.
- 2c must budget the upgrade of Lemma 3 (`IR.interpDeltaIso`) and
  Lemma 4 (`IR.interpPrecompIso`) from pointwise to natural
  isomorphisms — recorded in `TODO.md` § Category of `IR` codes; it
  is in no branch's plan yet.
- De-risk result (2026-07-19, session prototype, ephemeral — the
  scratch file is gone; reconstruct from the spec if needed): the
  forward map's `δ`-case discharges via Lemmas 3/4 and
  `interpMor` applications, with no analogue of the syntactic `sup2`
  obstruction that killed the syntactic composition route.
- Candidate to fold into 2c: the `TODO.md` "Tests:" item under
  § Complete Theorem 2.4 (a morphism-action sample with a
  propositionally nontrivial commutation proof, exercising the
  `homOfEq` transport in `IR.interpMorDelta` observably) — natural
  there because naturality statements manufacture exactly such
  transports.
- Statement universes: the uniform instantiation
  (`γ : IR.{max uA uB, uB, uI, uO}`, `interpObj` landing in
  `FreeCoprodCompDisc.Map.{max uA uB, uI, uO}`) — see the spec's
  Universe scheme section; verify committed forms at the real scheme,
  never only `Type 0`.

## After 2c — branch 2d (final)

Composition and the category laws (Corollary 2), by transfer through
Theorem 3's full-and-faithful interpretation (spec § Composition and
the category laws): `IR.comp` as the image under fullness of the
vertical composite of transported natural transformations; the laws
from the natural-transformation laws plus faithfulness. Depends on 2a
and 2c. Notes: 2a deliberately deferred a homset codomain transport
`IR.Hom.homOfEq` to 2d (2a's plan, Placement note) — build it there
if the derivations need it; the syntactic `supMor`/`sup2` operations
are subsumed by Lemma 4's semantic functoriality and need no
construction. 2d's final commits remove ALL transient workstream
documents from the working tree, per CONTRIBUTING § Concern shape:
`docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`, every
plan under `docs/superpowers/plans/` belonging to this workstream
(`2026-07-18-indrec-precomp.md`, `2026-07-19-indrec-morphisms-2a.md`,
`2026-07-20-indrec-morphisms-2b.md`, and the relocation/2c/2d plans),
and every handoff under `docs/superpowers/handoffs/`.

Still deferred beyond this workstream: the mathlib
`Category`/`Functor` wrapper (`TODO.md` § Complete Theorem 2.4),
`IR.elim`/`IR.rec` uniqueness/initiality (2c's route does not need
it), Theorem 2 (left Kan extension), and Theorem 4 (equivalence with
dependent polynomial functors).

## Where everything is

All on `main`.

- Design spec (all branches):
  `docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md` —
  read § Branch decomposition, § Placement and documentation, and for
  2c/2d their design sections.
- Model plans: `docs/superpowers/plans/2026-07-20-indrec-morphisms-2b.md`
  (latest; recursor-only, term-mode, per-task TDD, verified-code
  discipline), with `2026-07-18-indrec-precomp.md` and
  `2026-07-19-indrec-morphisms-2a.md` as earlier models.
- Code: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` (the two
  sections to move sit at the end of the file, after the Lemma 3/4
  development); `Geb/Mathlib/Data/PFunctor/IndRec/{Hom,Functor}.lean`;
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`; mirrored
  `GebTests/` files.
- Work tracking: `TODO.md` § Complete Theorem 2.4 for `IndRec` and
  § Category of `IR` codes.

## Retention

The spec, all plans, and all handoffs (including this one and the
superseded 2b handoff) remain in the working tree until the final
commits of branch 2d remove them. Each session ends by writing the
next session's handoff into `docs/superpowers/handoffs/`, carrying
the After-this-branch sections forward so the chain never loses the
full-workstream context.

## First action

Read the spec's § Branch decomposition and § Placement and
documentation, skim the two sections at the end of `Basic.lean` and
their tests, invoke `superpowers:brainstorming` (brief), and settle
the two open points — the test-file split and the new modules'
imports — before writing the plan.

## References

- [HancockMcBrideGhaniMalatestaAltenkirch2013]
- [GhaniNordvallForsbergMalatesta2015]
