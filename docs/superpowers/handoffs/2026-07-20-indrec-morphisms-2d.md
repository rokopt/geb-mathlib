# Handoff: IR-code morphisms, branch 2d (composition and the category laws)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Background — workstream status](#background--workstream-status)
- [What branch 2d does](#what-branch-2d-does)
- [Critical instructions (hard constraints, unchanged)](#critical-instructions-hard-constraints-unchanged)
- [Process (phase-driven, per CLAUDE.md)](#process-phase-driven-per-claudemd)
- [VCS and mechanics (verified across branches 1–2c)](#vcs-and-mechanics-verified-across-branches-12c)
- [After 2d — workstream close](#after-2d--workstream-close)
- [Where everything is](#where-everything-is)
- [Retention](#retention)
- [First action](#first-action)
- [References](#references)

<!-- END doctoc -->

You are continuing the IR-code morphisms workstream in the geb-mathlib
repository (Lean 4 + mathlib, strict constructive discipline). Start
branch 2d — the workstream's final branch — on a fresh topic branch
off `main` once branch 2c has merged. This handoff supersedes
`2026-07-20-indrec-morphisms-2c.md` (whose branch is complete on
`feat/indrec-morphisms-2c`, awaiting the user's line-by-line review
and merge); all handoffs remain in the tree until branch 2d's final
commits remove every transient workstream document (see Retention).

## Background — workstream status

The workstream formalizes the category of IR codes from
[HancockMcBrideGhaniMalatestaAltenkirch2013] ("Small Induction
Recursion", TLCA 2013) through Corollary 2, with the interpretation
semantics of [GhaniNordvallForsbergMalatesta2015]. Merged: branch 1
(PR #75, `IR.precomp`, Lemmas 3 and 4 pointwise,
`FreeCoprodCompDisc` coproduct machinery), branch 2a (PR #76, the
homset `IR.Hom` and syntactic identity `IR.id`), branch 2b (PR #77,
Theorem 2.4 functoriality: `IR.rec_mk`, the `IR.interpMor`
characterizing equations and functor laws), and the relocation
branch (PR #78, `Universes`/`Container` as sibling modules).

Branch 2c (complete on `feat/indrec-morphisms-2c`, 14 commits,
awaiting user review/merge) delivered:

- `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` additions:
  initial object (`emptyObj`/`emptyDesc`/`emptyDesc_unique`), the
  indexed-coproduct universal property (`coprodInj`/`coprodDesc`/
  `coprodHomEquiv` plus five composition compatibilities),
  `coprodPairMor` with five lemmas, `Iso.hom`/`Iso.invHom` with
  inverse laws, and `homSingletonEquiv`.
- `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`
  (new module): `IsNatTrans`/`NatTrans`, `NatTrans.id`/`vcomp` and
  the vertical laws, `PreservesId`/`PreservesComp`,
  `mapComp`/`mapMorComp`, whiskering and horizontal composition
  with orientation agreement, identity coherences (including
  `idMap` and the identity-functor whiskering laws), interchange,
  inverse pairs (`IsInverse`, iso-family conversion,
  `equivOfInverseTarget`/`Source`, `congrSource`),
  `natCoprodEquiv`, and the copower–Yoneda adjunction
  `natCopowerPlusEquiv`.
- `Geb/Mathlib/Logic/Equiv/Basic.lean`: `sigmaSubtypeEquiv`,
  `arrowPEmptyEquiv`.
- `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean` (new module):
  the per-summand Lemma 3 decomposition (`deltaInto`/`deltaDesc`
  with computation, uniqueness, joint epicness, naturality;
  `natDeltaEquiv`), the Lemma 4 naturality upgrade
  (`precompRhsMap`/`precompRhsMapMor`,
  `interpPrecompIso_natural`), the initial-object evaluation
  (`natIotaEquiv`) and `InnerHom` fiber equivalence
  (`innerHomEquiv`), the plus-lift bridge
  (`plusLiftBridgeNat`/`NatInv`/`_isInverse`), and Theorem 3:
  `IR.interpHomEquiv : Hom γ γ' ≃ NatTrans ⟦γ⟧ ⟦γ'⟧` with the
  named directions `IR.interpHom`/`IR.natToHom` and round-trip
  laws `interpHom_natToHom`/`natToHom_interpHom`. Axioms:
  {propext, Quot.sound} throughout.
- Mirrored `GebTests/` modules (note: the sample `δ`-code in the
  Naturality test file is `sampleNaturalityDeltaCode` — the
  planned name collided with `GebTests/.../Basic.lean`'s
  `sampleDeltaCode`), `docs/index.md` entries, and the `TODO.md`
  reduction (morphism-action test item discharged; Theorem 3
  attribution corrected to the TLCA 2013 paper).

## What branch 2d does

Composition and the category laws (the paper's Corollary 2), by
transfer through Theorem 3 (spec § Composition and the category
laws), with its own brainstorm → plan → execute cycle:

- `IR.comp : Hom γ γ' → Hom γ' γ'' → Hom γ γ''` as
  `natToHom (NatTrans.vcomp (interpHom f) (interpHom g))`.
- Associativity from `NatTrans.vcomp_assoc` plus the round-trip
  laws (conjugation by the equivalence; no new induction).
- Left and right identity require the equation sending
  `interpHom (IR.id γ)` to `NatTrans.id ⟦γ⟧` — deliberately NOT
  proved in 2c (it consumes branch 2a's `preUnitStack`
  construction, on which 2c does not depend). This is 2d's
  principal proof obligation and its closure-gate analogue:
  derive its induction (over `preUnitStack`'s stack recursion,
  through the `deltaNav`/`msigmaPush` tower) before planning; if
  it fails to close, return to design. The 2c de-risk note: the
  characterizing equations (`interpMor_mk` family, `rec_mk`) and
  the 2c decomposition equivalences are the available tools; the
  identity at an `ι`-code is `natIotaEquiv`-evaluable at `∅`.
- 2a deferred a homset codomain transport `IR.Hom.homOfEq` to 2d
  (2a's plan, Placement note) — build it there if the derivations
  need it. The syntactic `supMor`/`sup2` remain subsumed by
  Lemma 4's semantic functoriality; construct nothing syntactic.
- Placement: a `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
  module per the spec's one-module-per-branch split, with the
  mirrored test module and both umbrella registrations.

## Critical instructions (hard constraints, unchanged)

1. Recursor-only recursion; no `induction` tactic; no
   self-recursive `def`; no `termination_by`.
2. Explicit proof terms — no `by` blocks in committed code.
3. Constructive and axiom discipline: no `noncomputable`, no
   `Classical`; `lake lint` axiom linter ({propext, Quot.sound}).
4. Universe discipline: full-or-absent `.{…}` lists; uniform
   instantiation `IR.{max uA uB, uB, uI, uO}`.
5. mathlib style throughout; mathlib-conventional commit messages
   (`feat(indrec)`/`feat(cat)`/`feat(equiv)`/`doc(indrec)` per
   the touched subtree's precedent).

## Process (phase-driven, per CLAUDE.md)

1. Brainstorming (`superpowers:brainstorming`): derive the
   `interpHom (IR.id γ) = NatTrans.id` induction before any plan;
   adversarially review the design delta with a fresh-context
   subagent to convergence; user review gate.
2. Writing-plans (`superpowers:writing-plans`): compile a session
   prototype of every nontrivial declaration first (the 2b/2c
   pattern: the plan embeds only verified code; scratch file at
   the repo root, never committed, deleted before implementation);
   model the plan on
   `docs/superpowers/plans/2026-07-20-indrec-morphisms-2c.md`;
   adversarial review to convergence; user execution gate.
3. Executing (`superpowers:subagent-driven-development`): fresh
   implementer per task; per-task review with byte-verification
   against the plan; final whole-branch review; then
   `lean4:review` and `pr-review-toolkit:review-pr`;
   `scripts/pre-push.sh`. Do NOT push.
4. Final commits of 2d: remove ALL transient workstream documents
   (see Retention), then the docs/TODO closure.

## VCS and mechanics (verified across branches 1–2c)

- `jj` for all mutations; `jj absorb` routes review fixes to
  owning commits; `jj commit <paths>` scopes a commit to named
  files; bookmarks do NOT auto-advance — `jj bookmark set` after
  building commits.
- Red steps run `lake test` (bare `lake build` skips `GebTests`).
- Durable ledger: `.superpowers/sdd/progress.md` (retire the 2c
  section as done; keep the carried list below).
- Pitfalls bank (2b/2c-verified): partial universe lists stall
  unification — `iota.{max uA uB, uB, uI, uO}`,
  `interpMor_iota.{…}`, `InnerHom.{uA, uB, uI, uO}`,
  `lift.{uB, uI, max uA uB}`, `plus.{uI, uB, max uA uB}` (section
  variable first); `congrArg` lambdas applying a rewritten term
  need explicit binder types (`fun (t : MorMapSig I O …) ↦ …`);
  anonymous-constructor `Hom`s as arguments need ascription;
  `Eq.rec` motives at projection-reduced types with dependent
  `rfl`-proofs `∀`-quantified inside when their types mention the
  generalized index; elimination order — rewrite the recursor's
  own computation rule first (both sides), eliminate the
  commutation equality, split the shape, THEN apply the
  `interpMor` equations (a `precomp` of an unsplit `mk` is a
  stuck match); `Hom.comp` is definitionally associative/unital;
  definitional proof irrelevance collapses casts along proofs of
  defeq `Prop`s; ULift/Sigma/Subtype eta are definitional;
  `elim`-built operations compute definitionally at `mk`-codes,
  `IR.rec`-built ones only propositionally via `rec_mk`;
  `unusedVariables` lint is an error (`_` binders); new modules
  register in BOTH umbrellas; test files share one root namespace
  across the umbrella — check for sample-name collisions before
  planning test names.

Open Minor items carried in the progress ledger (this or a later
branch may pick up): a `rfl`-checked `innerHomEquiv` sample at a
`σ`- or `δ`-shaped codomain (only the `ι` branch has a direct
computational test); a value-level (`rfl`-pinned) `interpHom`
sample at a `σ`- or `δ`-domain morphism (the round trips hold
generically and do not pin the branch wiring); a sample code
containing a `σ` node fed through `interpPrecompIso_natural` (the
Lemma 4 induction's `σ` case is kernel-verified but never
elaborated concretely); a `sampleEquivOfInverseSource_roundtrip`
(the source-side transport is untested; its target-side twin is);
samples for `hcomp_id_right`/`hcomp_id_left`,
`coprodPair_inr_desc`, and `Iso.invHom_hom` at the non-trivial
iso (tested twins exist for each); the interchange law's file
position (after the `idMap` kit; the plan's grouping listed it
with the other coherences); the `coprodMor` samples never exercise
a non-identity reindexing (from 2b); `Functor.lean` deliberately
omits `## Main definitions`; the relocation branch's two docstring
nits (`## Tags` inconsistency between `Universes.lean` and
`Container.lean`; the `@[expose]` rationale comment not carried
into the relocated test modules); the `plus` docstring's `(+i)`
section notation names the fixed object on the left while the
definition fixes the left summand (the `NatTrans` module's
`plusMap` writes `(c +)` for the same shape — verify against the
paper's notation before changing either); the
`Geb/Mathlib/Logic/Equiv/Basic.lean` module docstring omits the
`arrowSum*` family from `## Main definitions` although
`Naturality.lean` consumes it by name.

## After 2d — workstream close

2d is the final branch. Its last commits remove from the working
tree: `docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`,
every workstream plan under `docs/superpowers/plans/`
(`2026-07-18-indrec-precomp.md`, `2026-07-19-indrec-morphisms-2a.md`,
`2026-07-20-indrec-morphisms-2b.md`,
`2026-07-20-indrec-relocation.md`,
`2026-07-20-indrec-morphisms-2c.md`, and 2d's own plan), and every
handoff under `docs/superpowers/handoffs/` (including this one),
per CONTRIBUTING § Concern shape. `TODO.md` § Category of `IR`
codes closes (content merged into `docs/index.md`); still deferred
beyond the workstream: the mathlib `Category`/`Functor` wrapper
(`TODO.md` § Complete Theorem 2.4), `IR.elim`/`IR.rec`
uniqueness/initiality, Theorem 2 (left Kan extension), and
Theorem 4 (equivalence with dependent polynomial functors).

## Where everything is

Branches 1–2b and the relocation on `main`; branch 2c on
`feat/indrec-morphisms-2c` (merge before starting 2d).

- Design spec (all branches):
  `docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md` —
  read § Composition and the category laws, § Universe scheme, and
  the branch-2c subsections (the delivered API).
- Model plan: `docs/superpowers/plans/2026-07-20-indrec-morphisms-2c.md`.
- Code: `Geb/Mathlib/Data/PFunctor/IndRec/{Basic,Hom,Functor,
  Naturality,Universes,Container}.lean`;
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` and
  `FreeCoprodCompDisc/NatTrans.lean`;
  `Geb/Mathlib/Logic/Equiv/Basic.lean`; mirrored `GebTests/`.
- Work tracking: `TODO.md` § Category of `IR` codes (2d's scope)
  and § Complete Theorem 2.4 for `IndRec` (deferred wrapper).

## Retention

The spec, all plans, and all handoffs remain in the working tree
until the final commits of branch 2d remove them. Each session ends
by writing the next session's handoff into
`docs/superpowers/handoffs/`, carrying the After-this-branch
sections forward so the chain never loses the full-workstream
context.

## First action

Read the spec's § Composition and the category laws and the
branch-2c subsections, skim `Naturality.lean`'s Theorem 3 section
and `Hom.lean`'s `preUnitStack`/`deltaNav` construction (the
identity whose image under `interpHom` must be shown to be
`NatTrans.id`), invoke `superpowers:brainstorming`, and derive the
`interpHom (IR.id γ) = NatTrans.id ⟦γ⟧` induction (2d's closure
gate) before writing the plan.

## References

- [HancockMcBrideGhaniMalatestaAltenkirch2013]
- [GhaniNordvallForsbergMalatesta2015]
