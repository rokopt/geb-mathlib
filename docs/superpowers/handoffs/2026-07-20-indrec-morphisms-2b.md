# Handoff: IR-code morphisms, branch 2b (Theorem 2.4 functoriality)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Background — how we got here](#background--how-we-got-here)
- [What branch 2b builds](#what-branch-2b-builds)
- [Where everything is](#where-everything-is)
- [The hard part — and the plan-phase gate](#the-hard-part--and-the-plan-phase-gate)
- [Critical instructions (hard constraints, same as 2a)](#critical-instructions-hard-constraints-same-as-2a)
- [Constructive and axiom discipline (non-negotiable)](#constructive-and-axiom-discipline-non-negotiable)
- [Universe scheme](#universe-scheme)
- [Process (phase-driven, per CLAUDE.md)](#process-phase-driven-per-claudemd)
- [VCS and mechanics (verified this workstream)](#vcs-and-mechanics-verified-this-workstream)
- [Placement](#placement)
- [Retention](#retention)
- [First action](#first-action)
- [References](#references)

<!-- END doctoc -->

You are continuing the IR-code morphisms workstream in the geb-mathlib
repository (Lean 4 + mathlib, strict constructive discipline). Start
branch 2b on a fresh topic branch off `main`.

## Background — how we got here

The workstream formalizes the category of IR codes from
[HancockMcBrideGhaniMalatestaAltenkirch2013] ("Small Induction
Recursion", TLCA 2013). Branch 1 (precomposition `IR.precomp` = the
paper's `γ^i`, plus Lemmas 3 and 4) is merged. The original branch-2 plan
was to build the homset (Definition 8) and then `id`/`comp`/laws
syntactically. A closure gate established that composition does not close
by syntactic induction on codes — it needs `supMor` (precomposition's
action on morphisms) and `sup2` (associativity of iterated precomposition)
at the codomain, which the domain-recursive homset never exposes to
recursion (this matches the paper, which obtains Corollary 2 by transfer
through the full-and-faithful interpretation, Theorem 3, not
syntactically). So branch 2 was expanded into four dependency-ordered
branches:

- 2a (merged): the homset (`IR.Hom`, Definition 8) and the identity
  `IR.id`, built syntactically via a list-generalized pre-unit —
  `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`.
- 2b (this handoff): Theorem 2.4 functoriality — makes `⟦γ⟧` a genuine
  functor.
- 2c: natural transformations between interpretations, and Theorem 3
  (full and faithful `⟦⟧`). Depends on 2b. Carries its own constructive
  closure gate, already de-risked: a verified prototype showed the
  forward map's `δ`-case discharges via Lemmas 3/4 with no `sup2`-analogue.
- 2d: composition and the category laws (Corollary 2), by transfer through
  Theorem 3. Depends on 2a and 2c.

## What branch 2b builds

The functoriality content of Theorem 2.4 of
[GhaniNordvallForsbergMalatesta2015] for the interpretation,
constructively. This is the existing `TODO.md` item "Complete Theorem 2.4
for `IndRec`" (constructive part):

1. The propositional computation rule of `IR.rec`, and from it the
   characterizing equations of `IR.interpMor` at `IR.iota`/`IR.sigma`/
   `IR.delta`.
2. `FreeCoprodCompDisc.Hom` identity and the category laws (left identity,
   right identity, associativity). Composition
   `FreeCoprodCompDisc.Hom.comp` already exists (branch 1); the identity
   and the three laws do not — branch-1's Task-1 note explicitly deferred
   them to "branch 2 if its derivations require them", and 2c requires
   them.
3. The functor laws of `IR.interpMor`: preservation of identity and
   composition.

Out of scope for 2b: the `Classical`-permitted wrapper (mathlib
`Category`/`Functor` instances — the TODO lists this separately for a
later file); the `IR.elim`/`IR.rec` uniqueness/initiality properties (the
TODO's item 3 — decide in the 2b plan whether 2c actually needs them,
otherwise leave to 2c or a later branch); and everything in 2c/2d.

Branch 2b is independent of 2a — it builds directly on branch-1 content
(`IR.rec`, `interpObj`/`interpMor`, `FreeCoprodCompDisc`) and does not use
the syntactic homset. It is a prerequisite for 2c.

## Where everything is

All on `main`.

- Design spec (covers 2a–2d):
  `docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`. Read
  "Closure gate result", "Theorem 2.4 functoriality (branch 2b)", and
  "Naturality and Theorem 3 (branch 2c)".
- Model plans:
  `docs/superpowers/plans/2026-07-18-indrec-precomp.md` (branch 1) and
  `docs/superpowers/plans/2026-07-19-indrec-morphisms-2a.md` (branch 2a).
  Pattern the 2b plan on these — they demonstrate the recursor-only,
  term-mode discipline, per-task TDD, universe handling, and the
  verified-prototype-then-plan flow.
- Code you build on:
  - `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` — the IR codes;
    `IR.elim`/`IR.rec` (and `IR.induction`, the `Prop` recursor);
    `interpObj`/`interpMor`/`interpObjAlg`/`interpMorStep`;
    `IR.ext`/`IR.snd_eq_of_eq`/`sigmaRec`/`sigmaRec_fst`/
    `sigmaFstSectionElim`. Its module docstring's Implementation notes
    state exactly what 2b closes: "the functor laws … are not yet stated.
    Neither is the propositional computation rule of `IR.rec`, which would
    characterize `IR.interpMor` at each code constructor."
  - `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` — `Hom`,
    `Hom.comp`, `homOfEq`, `coprodPair`/`plus`, `copower`, `lift`, `Iso`.
    (`Hom` identity and laws are the 2b additions here.)

## The hard part — and the plan-phase gate

`IR.rec` is not defined as a raw `WType.rec`; it is
`sigmaFstSectionElim (sigmaRec …) (sigmaRec_fst …)` — a dependent
recursor built from the non-dependent `IR.elim` (= `WType.elim`) via a
propositional first-projection section. Consequently `IR.rec` does not
satisfy a definitional computation rule (this is precisely why 2a's tests
that route through `IR.rec` were typecheck-only, not `rfl`). The core 2b
deliverable is the propositional computation rule:

```text
IR.rec mk' (IR.mk s d) = mk' s d (fun x => IR.rec mk' (d x))
```

(and its `iota`/`sigma`/`delta` specializations). Deriving it requires
reasoning about `sigmaRec`/`sigmaFstSectionElim` and the section proof
`sigmaRec_fst`. The 2b plan must derive this rule on paper (or a verified
prototype) before any implementation — it is the crux everything else
depends on; if it resists, return to design. The functor laws then follow
from it plus the `FreeCoprodCompDisc.Hom` category laws plus the
`interpMorIota`/`Sigma`/`Delta` structure, proved by `IR.induction`
(`Prop`-valued). All such equality proofs stay term-mode (`Eq.rec`/
`congrArg`/`funext` chains factored into named lemmas, in the manner of
`IR.ext`).

## Critical instructions (hard constraints, same as 2a)

1. Recursor-only recursion — all recursion/induction through recursors
   (`IR.elim`/`IR.rec`/`IR.induction`, `WType.elim`/`rec`, `List.rec`, or
   a recursor built by wrapping those). No `induction`/`induction'`
   tactic; no self-recursive `def`; no `termination_by`. The computation
   rule and functor laws are `Prop`-valued, so they go through
   `IR.induction`.
2. Explicit proof terms — no `by` blocks in committed code (`cast`/`▸`/
   term-`match` are fine). Rationale (unchanged): this development is
   destined to be self-referential — fixed points of IR types describing
   IR syntax, including these proofs — so tactic scripts obscure the proof
   terms that syntax must describe.
3. Factor every step into a named declaration, types included (reducible
   `abbrev`s for spelled-out type families, so definitional unfolding is
   preserved).

## Constructive and axiom discipline (non-negotiable)

No `noncomputable`, no `Classical`. `lake lint` runs the `GebMeta` axiom
linter and fails if any `Geb`/`GebTests` declaration depends on an axiom
outside `{propext, Quot.sound}`. Before reusing any mathlib declaration
inside a definition, `#print axioms` it and reject `Classical.choice`.
Known trap: `Equiv.sigmaCongr`/`Equiv.sigmaCongrRight` are choice-tainted
— use branch-1's choice-free `sigmaCongrRight'`.

## Universe scheme

`interpObj` lands in `FreeCoprodCompDisc.Map.{max uA uB, uI, uO}` and
`interpMor` over it; state the functor laws at that instantiation.
Branch-1 universe discipline applies (full-or-absent `.{…}` lists; no
auto-bound `u_1`). Verify committed forms at the real universe scheme, not
just `Type 0` — 2a's `Type 0` prototype hid `ULift`/`PLift` lifts and
universe-pin needs that only surfaced on generalization (see the 2a plan's
Global Constraints, "universe pitfalls").

## Process (phase-driven, per CLAUDE.md)

1. Brainstorming (`superpowers:brainstorming`): re-read the spec's 2b
   section; adversarially review it with a fresh-context subagent before
   planning; begin working out the `IR.rec` computation rule (the gate).
2. Writing-plans (`superpowers:writing-plans`): author the 2b plan modeled
   on the branch-1/2a plans; adversarially review to convergence with
   reviewers compiling snippets against the toolchain (`lean_run_code` +
   `#print axioms`); clear the computation-rule gate before
   implementation.
3. Executing (`superpowers:subagent-driven-development`): fresh implementer
   subagent per task; per-task spec and quality review; final whole-branch
   review; subagents as build-runners (keep `lake` logs out of the
   controller's context; gate on build-success). Then run `lean4:review`
   and `pr-review-toolkit:review-pr` before declaring done.

## VCS and mechanics (verified this workstream)

- `jj` for all mutations (a PreToolUse hook blocks mutating `git`;
  read-only `git` is fine). Commit messages in mathlib conventional form
  (`feat|fix|doc|refactor|test|chore(scope): imperative`, no capital, no
  period).
- Red (test-first) steps run `lake test` (bare `lake build` does not build
  `GebTests`).
- New modules must be registered in BOTH the source umbrella
  (`Geb/Mathlib/Data/PFunctor/IndRec.lean` and any parent index up to
  `Geb.lean`) AND the test umbrella (`GebTests/…`). In 2a the
  source-umbrella registration was missed by the implementer and the
  review agents, and only `pre-push.sh`'s `test-lint-driver` caught it (a
  module escaping the umbrella escapes the linter). The plan's
  file-structure section must list both.
- `scripts/pre-push.sh` is the authoritative pre-push gate — run it before
  declaring the branch done.
- A durable progress ledger under `.superpowers/sdd/progress.md` survives
  compaction; `jj absorb`/`squash` folds review-fixes into their owning
  task commits.
- Do NOT push; the user reviews line-by-line and pushes/merges.

## Placement

Per the spec, sibling `IndRec` modules
(`Hom`/`Functor`/`Naturality`/`Category`). The `IR.rec` computation rule is
a fact about `IR.rec` (likely belongs in `Basic.lean` or a small new
module); the `interpMor` functor laws suggest
`Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean`; the
`FreeCoprodCompDisc.Hom` identity and laws go in `FreeCoprodCompDisc.lean`.
The 2b plan fixes exact placement.

## Retention

The spec and all plans (branch-1, 2a, and the forthcoming 2b plan) remain
in the working tree; they are removed only in the final commits of the
workstream's last branch (2d), per CONTRIBUTING § Concern shape. This
handoff file is likewise transient and is removed with them.

## First action

Read the spec's "Theorem 2.4 functoriality (branch 2b)" section and the
branch-1 plan, invoke `superpowers:brainstorming`, and begin by deriving
the `IR.rec` propositional computation rule — that derivation is the gate
everything else depends on.

## References

- [HancockMcBrideGhaniMalatestaAltenkirch2013]
- [GhaniNordvallForsbergMalatesta2015]
