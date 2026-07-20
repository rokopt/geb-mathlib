# Handoff: IR-code morphisms, branch 2c (naturality and Theorem 3)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Background — workstream status](#background--workstream-status)
- [What branch 2c does](#what-branch-2c-does)
- [Critical instructions (hard constraints, unchanged)](#critical-instructions-hard-constraints-unchanged)
- [Process (phase-driven, per CLAUDE.md)](#process-phase-driven-per-claudemd)
- [VCS and mechanics (verified across branches 1–relocation)](#vcs-and-mechanics-verified-across-branches-1relocation)
- [After 2c — branch 2d (final)](#after-2c--branch-2d-final)
- [Where everything is](#where-everything-is)
- [Retention](#retention)
- [First action](#first-action)
- [References](#references)

<!-- END doctoc -->

You are continuing the IR-code morphisms workstream in the geb-mathlib
repository (Lean 4 + mathlib, strict constructive discipline). Start
branch 2c on a fresh topic branch off `main` once the relocation
branch has merged. This handoff supersedes
`2026-07-20-indrec-relocation.md` (whose branch is complete on
`refactor/indrec-relocation`, awaiting the user's line-by-line review
and merge); both files remain in the tree until the workstream's last
branch removes all transient documents (see Retention).

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
- Relocation branch (`refactor/indrec-relocation`, complete, awaiting
  user review/merge): `section Universes` and `section Container`
  moved out of `Basic.lean` into sibling modules
  `Geb/Mathlib/Data/PFunctor/IndRec/{Universes,Container}.lean` with
  mirrored `GebTests/` modules, discharging the spec's placement
  requirement — later branches can add morphism uses (and a `Functor`
  or `Naturality` import) to those modules without import cycles.

The remaining branches, dependency-ordered (spec § Branch
decomposition): 2c (naturality and Theorem 3, depends on 2b), then 2d
(composition and the category laws by transfer, depends on 2a and
2c).

## What branch 2c does

Naturality and Theorem 3, with its own brainstorm → plan → execute
cycle:

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
  (`γ : IR.{max uA uB, uB, uI, uO} I O`, `interpObj` landing in
  `FreeCoprodCompDisc.Map.{max uA uB, uI, uO}`) — see the spec's
  Universe scheme section; verify committed forms at the real scheme,
  never only `Type 0`.

## Critical instructions (hard constraints, unchanged)

1. Recursor-only recursion; no `induction` tactic; no self-recursive
   `def`; no `termination_by`.
2. Explicit proof terms — no `by` blocks in committed code.
3. Constructive and axiom discipline: no `noncomputable`, no
   `Classical`; `lake lint` runs the `GebMeta` axiom linter
   ({propext, Quot.sound} only).
4. Universe discipline: full-or-absent `.{…}` lists; no auto-bound
   `u_1`.
5. mathlib style throughout; commit messages in mathlib conventional
   form.

## Process (phase-driven, per CLAUDE.md)

1. Brainstorming (`superpowers:brainstorming`): derive the Theorem 3
   induction (the closure gate) before any plan; adversarially review
   the design delta with a fresh-context subagent.
2. Writing-plans (`superpowers:writing-plans`): model the plan on
   `docs/superpowers/plans/2026-07-20-indrec-morphisms-2b.md` (global
   constraints, file structure, per-task TDD with `jj`, both-umbrella
   registration). Budget the Lemma-3/Lemma-4 naturality upgrade.
3. Executing (`superpowers:subagent-driven-development`): fresh
   implementer per task; per-task review; final whole-branch review;
   then `lean4:review` and `pr-review-toolkit:review-pr`;
   `scripts/pre-push.sh` before handing to the user. Do NOT push.

## VCS and mechanics (verified across branches 1–relocation)

- `jj` for all mutations (a PreToolUse hook blocks mutating `git`;
  read-only `git` is fine). `jj absorb`/`squash --into` folds
  review-fixes into their owning task commits.
- Red (test-first) steps run `lake test` (bare `lake build` does not
  build `GebTests`).
- Durable progress ledger: `.superpowers/sdd/progress.md` (retire the
  relocation section as done; keep the carried Minor-findings list).
- Pitfalls bank (verified during 2b): partial universe lists stall
  unification (`interpMorIota` needs full `.{uA, uB, uI, uO}` at use
  sites whose arguments do not mention `uA`/`uB`); declarations whose
  separated `uA uB` occur only under `max` trip `checkUnivs` AND
  stall inference — use a single index-universe parameter; deep
  `.trans` chains mis-parse when an application argument lands at
  lower indentation — factor into named theorems; new modules need
  BOTH umbrella imports.

Open Minor items carried in the progress ledger that this or a later
branch may pick up: the `coprodMor` samples never exercise a
non-identity reindexing; `Functor.lean` deliberately omits
`## Main definitions` (its defs are proof scaffolding); the
relocation branch's final review noted two docstring nits left to the
user (the `## Tags` polynomial-functor inconsistency between
`Universes.lean` and `Container.lean`; the `@[expose]` rationale
comment not carried into the new test modules).

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
`2026-07-20-indrec-morphisms-2b.md`,
`2026-07-20-indrec-relocation.md`, and the 2c/2d plans), and every
handoff under `docs/superpowers/handoffs/`.

Still deferred beyond this workstream: the mathlib
`Category`/`Functor` wrapper (`TODO.md` § Complete Theorem 2.4),
`IR.elim`/`IR.rec` uniqueness/initiality (2c's route does not need
it), Theorem 2 (left Kan extension), and Theorem 4 (equivalence with
dependent polynomial functors).

## Where everything is

Branches 1–2b on `main`; the relocation branch on
`refactor/indrec-relocation` (merge before starting 2c).

- Design spec (all branches):
  `docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md` —
  read § Naturality and Theorem 3, § Universe scheme, and for 2d
  § Composition and the category laws.
- Model plans:
  `docs/superpowers/plans/2026-07-20-indrec-morphisms-2b.md`
  (latest full-feature model) and
  `docs/superpowers/plans/2026-07-20-indrec-relocation.md` (the
  relocation branch).
- Code: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` (core codes,
  interpretation, Lemmas 3/4, `rec_mk`);
  `Geb/Mathlib/Data/PFunctor/IndRec/{Hom,Functor}.lean`;
  `Geb/Mathlib/Data/PFunctor/IndRec/{Universes,Container}.lean`
  (relocated examples);
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`; mirrored
  `GebTests/` files.
- Work tracking: `TODO.md` § Complete Theorem 2.4 for `IndRec` and
  § Category of `IR` codes.

## Retention

The spec, all plans, and all handoffs (including this one and the
superseded relocation handoff) remain in the working tree until the
final commits of branch 2d remove them. Each session ends by writing
the next session's handoff into `docs/superpowers/handoffs/`,
carrying the After-this-branch sections forward so the chain never
loses the full-workstream context.

## First action

Read the spec's § Naturality and Theorem 3 and § Universe scheme,
skim `Functor.lean` (the characterizing equations and functor laws
2c builds on) and `Basic.lean`'s Lemma 3/4 sections, invoke
`superpowers:brainstorming`, and derive the Theorem 3 induction (the
closure gate) before writing the plan.

## References

- [HancockMcBrideGhaniMalatestaAltenkirch2013]
- [GhaniNordvallForsbergMalatesta2015]
