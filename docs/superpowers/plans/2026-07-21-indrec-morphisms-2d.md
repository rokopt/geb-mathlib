# IR-code morphisms branch 2d (composition and the laws) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [File structure](#file-structure)
- [Task outline](#task-outline)
- [Prototype-file discipline](#prototype-file-discipline)
- [Task 1: universe-generalized coproduct-pair injections](#task-1-universe-generalized-coproduct-pair-injections)
- [Task 2: name the recursor steps of the homset injections](#task-2-name-the-recursor-steps-of-the-homset-injections)
- [Task 3: the `Category` module and the semantic tower](#task-3-the-category-module-and-the-semantic-tower)
- [Task 4: the characterizing equations of `IR.interpHom`](#task-4-the-characterizing-equations-of-irinterphom)
- [Task 5: the `IR.sigmaPush` characterization](#task-5-the-irsigmapush-characterization)
- [Task 6: the `IR.deltaEmptyPush` characterization](#task-6-the-irdeltaemptypush-characterization)
- [Task 7: the navigation characterizations](#task-7-the-navigation-characterizations)
- [Task 8: the identity-image induction](#task-8-the-identity-image-induction)
- [Task 9: composition and the category laws](#task-9-composition-and-the-category-laws)
- [Task 10: documentation and TODO closure](#task-10-documentation-and-todo-closure)
- [Task 11: removal of the transient workstream documents](#task-11-removal-of-the-transient-workstream-documents)
- [Final verification (whole branch)](#final-verification-whole-branch)

<!-- END doctoc -->

**Goal:** the composition of `IR`-code morphisms and the category
laws — Corollary 2 of
[HancockMcBrideGhaniMalatestaAltenkirch2013] — obtained by transfer
through the full-and-faithful interpretation of Theorem 3, together
with the identity-image equation
`IR.interpHom γ γ (IR.id γ) = NatTrans.id ⟦γ⟧` that the identity
laws consume.

**Architecture:** per the design spec
(`docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`,
§ Composition and the category laws (branch 2d)). Composition is
`natToHom (NatTrans.vcomp (interpHom f) (interpHom g))`;
associativity is conjugation of `NatTrans.vcomp_assoc` by the
Theorem 3 equivalence. The identity laws reduce to the
identity-image equation, which is proved at the component level by
`IR.induction` on the domain code with the pre-unit's stack
generalized: the semantic counterpart of the stack is an iterated
coproduct tower (`IR.mplus`, `IR.mplusInj`, `IR.mprecompIso`), the
characterizing equations of `IR.interpHom` expose each case as a
cotuple, and each branch-2a injection helper (`IR.sigmaPush`,
`IR.deltaEmptyPush`, `IR.msigmaPush`, `IR.deltaNavBase`,
`IR.deltaNav`) is characterized as composition with an explicit
inclusion, so the cotuple eta laws collapse every case.

**Verification status:** the declarations of Tasks 3–9 are
reproduced below in the form compiled — at the real universe scheme,
term-mode — against the built branch-1/2a/2b/2c code, with zero
diagnostics, and `IR.interpHom_id`, `IR.id_comp`, `IR.comp_id`, and
`IR.comp_assoc` each depend on `propext` and `Quot.sound` only
(session scratch `proto_2d_gate.lean`; deleted before any commit).
Three classes of committed text were not compiled in their committed
form, the prototype being unable to edit merged modules: Task 1's
universe-generalized
`FreeCoprodCompDisc.coprodPairInl`/`coprodPairInr` (compiled as
primed siblings inside `namespace IR`), Task 2's body replacements
`sigmaPush := rec I O (sigmaPushStep I O)` and its two siblings (the
prototype declared the named motives and steps alongside the merged
inline-lambda definitions rather than in place of them), and the 35
universe lists rewritten at the call sites of the renamed
injections. Each is first elaborated by the build step of the task
that introduces it, which is why Task 2 carries the bridge theorems
of its Step 3. The `.{v, uX, uY}` universe order of the generalized
injections was confirmed separately, by compiling a scratch module
against the built tree. Two further classes are also absent from the
pinned prototype: the sample tests of every task, and the
`Category.lean` header, module docstring, `universe`/`namespace`/
`variable` skeleton of Task 3. The samples were each elaborated
against the prototype while being drafted and then removed from it,
so the prototype as pinned does not contain them; the skeleton
follows `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean` line for
line. The residual work is docstrings, docs entries, and gates.

**Tech Stack:** Lean 4, mathlib, the project's `IndRec` and
`FreeCoprodCompDisc` developments (branches 1, 2a, 2b, relocation,
2c).

## Global Constraints

Copied from the design spec and the verified prototype; every
task's requirements include these.

- Constructive only: no `noncomputable`, no `Classical`; the axiom
  linter (`lake lint`) permits `{propext, Quot.sound}` only for
  `Geb`/`GebTests`.
- Recursor-only recursion: `IR.rec` drives the Type-valued
  recursions, `IR.induction` the `Prop`-valued ones, `List.rec` the
  stack recursions; `match` only for non-recursive case analysis
  and `Eq.rec` for equality elimination. No `induction`/`induction'`
  tactic, no self-referential `def`, no `termination_by`.
- Explicit proof terms: committed declarations are term-mode, no
  `by` blocks. Motives are named `UpperCamelCase` `def`s; steps and
  laws are named declarations. `IR.rec_mk` does not unify against
  an inline step lambda, which is why Task 2 names the three
  branch-2a steps.
- Universe discipline: full-or-absent `.{…}` lists, at the uniform
  instantiation `IR.{max uA uB, uB, uI, uO}`. No auto-bound `u_1`;
  remove unused `universe`/`variable`. Two
  `set_option linter.checkUnivs false in` lines are required, on
  `IR.comp_isoOfEq_hom` and `IR.isoOfEq_symm_hom_comp` (Task 8),
  with `Basic.lean`'s precedent.
- `_root_.id` inside the `IR` namespace: never bare `id` (the
  namespace has its own `IR.id`). The identity morphism is
  correspondingly written `IR.id` at its use sites in Task 9, a
  deliberate exception to the rule against namespace-qualified
  identifiers in declaration bodies
  (`docs/rules/lean-coding.md` § Naming conventions): it
  disambiguates against `_root_.id` at the same call sites.
  `Basic.lean`'s `IR.pFunctor` is the merged precedent.
- Transcription: every Lean block below is byte-exact from the
  verified prototype. Do not retype, reformat, or rename beyond the
  renames Tasks 1 and 2 state explicitly. The prototype's lambda
  arrow is `=>`, matching `Hom.lean`; transcribe it unchanged.
- mathlib style: 2-space indent, 100-column lines, mandatory module
  docstring with its non-vacuous sections, mandatory docstrings on
  every `def` and every theorem of public interest, naming per
  mathlib. `unusedVariables` lint is an error: use `_` binders.
- Citations: [HancockMcBrideGhaniMalatestaAltenkirch2013] appears in
  the docstring of `IR.comp` and in the `Category` module
  docstring — its `## Main statements` entry for the three laws and
  its `## References` section. That module docstring is what carries
  the citation for `IR.id_comp`, `IR.comp_id`, and `IR.comp_assoc`,
  whose own docstrings do not repeat it; CONTRIBUTING § Cite the
  literature when transcribing admits either location. The tower and
  helper characterizations are the project's own construction.
- Test namespace: the `GebTests` modules share ONE root namespace
  across the test umbrella, so every sample name must be unique
  repository-wide. Already taken (non-exhaustive): `sampleDeltaCode`,
  `sampleDeltaId`, `sampleDeltaIdNat`, `sampleIotaHom`,
  `sampleInterpHom_component`, `sampleInterpHom_natToHom`,
  `sampleNaturalityDeltaCode`, `sampleObj`, `sampleObjHom`,
  `samplePoint`, `sampleActHom`, `sampleActX`, `sampleActY`,
  `sampleIObj`, `sampleDeltaSub`, `sampleSigmaToIotaHom`,
  `sampleNatToHom_interpHom`, `sampleSigmaNatToHom_interpHom`. The
  full list is
  `grep -rho '^\(def\|theorem\) sample[A-Za-z_0-9'"'"']*' GebTests/ | sort -u`;
  run it before adding any sample. `Category.lean`'s test module
  uses the distinct prefixes `sampleCategory…`, `sampleMplus…`,
  `sampleComp…`, `sampleIdComp…`; each task's test step below gives
  concrete non-colliding names.
- Module system: new modules get `module` headers, `public import`,
  and registration in BOTH the source umbrella
  (`Geb/Mathlib/Data/PFunctor/IndRec.lean`) AND the test umbrella
  (`GebTests/Mathlib/Data/PFunctor/IndRec.lean`);
  `scripts/lint-imports.sh` passes.
- Gates per task: `lake test` (not bare `lake build`, which skips
  `GebTests`) passes before each commit; red steps run `lake test`.
  `sorry` only transiently, never committed.
- VCS: `jj` only for mutations (a PreToolUse hook blocks raw
  mutating `git`); commit messages in mathlib conventional form —
  `feat(cat)` for `FreeCoprodCompDisc`, `feat(indrec)` for
  `IndRec`, `doc(indrec)` for the documentation task;
  `jj absorb`/`squash --into` folds review fixes into owning task
  commits. Bookmarks do not auto-advance: run
  `jj bookmark set feat/indrec-morphisms-2d` after each commit. No
  pushes.
- Commit with the bare `jj commit -m "…"` form, never
  `jj commit <paths>`. Each task begins from a clean working copy
  and commits everything it changed, so path scoping is
  unnecessary; and path scoping applied while the working copy is
  already a described commit repurposes that description and
  splits the commit's content.

## File structure

- Modify `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` —
  universe-generalize the coproduct-pair injections in place
  (Task 1).
- Modify `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean` — name the
  motives and steps of `IR.sigmaPush`, `IR.deltaEmptyPush`, and
  `IR.preUnitStack`, and add their applied `mk`-computation
  equations (Task 2).
- Create `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean` — the
  branch's development: the semantic tower, the characterizing
  equations of `IR.interpHom`, the helper characterizations, the
  identity-image equation, `IR.comp`, and the category laws
  (Tasks 3–9), importing `Naturality`.
- Create `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean` —
  mirrored tests (Tasks 3–9).
- Modify both `IndRec` umbrellas (Task 3).
- Modify the mirrored test modules of the two edited source
  modules (Tasks 1–2).
- Modify `docs/index.md` and `TODO.md` (Task 10).
- Remove the workstream's transient documents (Task 11).

(Placement rationale: the injections' generalization extends the
existing module's concern rather than adding a primed sibling; the
named steps belong with the operations they define; the branch's
own development is the spec's `Category` module, one module per
branch.)

Six of the `Category` module's statements — `IR.emptyHom_ext`,
`IR.eq_comp_invHom`, `IR.comp_isoOfEq_hom`,
`IR.isoOfEq_symm_hom_comp`, `IR.coprodPairInr_mor`, and
`IR.deltaDesc_comp` — are about `FreeCoprodCompDisc` morphisms and
cotuples rather than about this branch's constructions. They are
committed under `namespace IR` as transcribed. Relocating them to
`FreeCoprodCompDisc` is deferred; the design spec § FreeCoprodCompDisc
additions anticipates hom-extensionality at an empty-name domain as
a `FreeCoprodCompDisc` addition, which is the relocation that would
carry the rest.

## Task outline

Tasks below are dependency-ordered; each carries its own TDD cycle
and commit. Exact code per task is reproduced from the verified
prototype.

- Task 1: universe-generalized coproduct-pair injections
  (`FreeCoprodCompDisc.coprodPairInl`/`coprodPairInr`).
- Task 2: named recursor motives and steps for `IR.sigmaPush`,
  `IR.deltaEmptyPush`, and `IR.preUnitStack`, with their applied
  `mk`-computation equations and `IR.preUnitDeltaData`
  (`Hom.lean`).
- Task 3: the `Category` module skeleton and the semantic tower
  (`IR.mplus` … `IR.preUnitComponent_nil`, `IR.mplusInj_snoc`,
  `IR.mprecompIso_snoc_hom`/`_invHom`, `IR.mplusMorMap`,
  `IR.mprecompIso_natural`), both umbrella registrations, and the
  mirrored test module.
- Task 4: the characterizing equations of `IR.interpHom`
  (`IR.congrSource_symm_fst`, `IR.interpHomEquiv_mk`,
  `IR.interpHom_iota`, `IR.interpHom_sigma`,
  `IR.interpHomDeltaSummand`, `IR.interpHom_delta`) and the generic
  squares (`IR.deltaDesc_comp`, `IR.interpMor_sigma_inj`,
  `IR.innerHomEquiv_mk`) — prototype sections E and G0.
- Task 5: the `IR.sigmaPush` characterization — prototype G1–G3.
- Task 6: the `IR.deltaEmptyPush` characterization — prototype
  section H.
- Task 7: the navigation characterizations (`IR.msigmaPush`,
  `IR.deltaNavBase`, `IR.deltaNav`) — prototype section I after the
  tower lemmas taken in Task 3.
- Task 8: the identity-image induction — prototype section J.
- Task 9: composition and the category laws (`IR.comp`,
  `IR.interpHom_comp`, `IR.comp_assoc`, `IR.interpHom_id`,
  `IR.id_comp`, `IR.comp_id`) with samples — prototype section K.
- Task 10: `docs/index.md` entries and the `TODO.md` § Category of
  `IR` codes closure (content merged into `docs/index.md`), with
  the final docstring sweep; the still-deferred items stay listed
  (the mathlib `Category`/`Functor` wrapper, `IR.elim`/`IR.rec`
  uniqueness, Theorem 2, Theorem 4).
- Task 11: removal of ALL transient workstream documents — the
  spec `docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`,
  every plan under `docs/superpowers/plans/`
  (`2026-07-18-indrec-precomp.md`,
  `2026-07-19-indrec-morphisms-2a.md`,
  `2026-07-20-indrec-morphisms-2b.md`,
  `2026-07-20-indrec-relocation.md`,
  `2026-07-20-indrec-morphisms-2c.md`, and this plan), and every
  handoff under `docs/superpowers/handoffs/`, per CONTRIBUTING
  § Concern shape.

---

## Prototype-file discipline

The session prototype `proto_2d_gate.lean` at the repository root
is the verified source of every declaration below, and every
declaration is reproduced verbatim in the task bodies. It is
working-copy scratch: no commit may contain it. Delete it from the
working tree before Task 1 begins (the 2b/2c precedent), and check
`jj status` before each commit to confirm it is absent.

---

## Task 1: universe-generalized coproduct-pair injections

`IR.mplusInj` (Task 3) injects an object at `max uA uB` into a
coproduct pair whose left summand sits at `uB`, which the existing
single-universe injections do not accept. The prototype worked
around this with primed siblings `IR.coprodPairInl'`/`coprodPairInr'`
(prototype section A) so as not to edit merged code; the committed
form instead generalizes the existing
`FreeCoprodCompDisc.coprodPairInl`/`coprodPairInr` in place to
`.{uX, uY}`, in the manner of the existing
`FreeCoprodCompDisc.coprodPairMor.{uX, uY, uX', uY'}`. The primed
names therefore do not exist in committed code: every prototype
occurrence of `coprodPairInl'`/`coprodPairInr'` becomes the
unqualified generalized declaration, and the prototype's universe
list `.{uA, uB, uI}` becomes `.{uI, uB, max uA uB}` (the committed
list is `.{v, uX, uY}`, decoding universe first). The prototype's
`comp_coprodPairInr'_cast` is renamed `comp_coprodPairInr_cast`
accordingly (Task 3).

This widens a merged signature: the underlying terms
`⟨Sum.inl, rfl⟩`/`⟨Sum.inr, rfl⟩` elaborate heterogeneously, and
the arity of the universe list rises from two to three, so every
existing call site is re-elaborated in Step 4.

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`

**Interfaces:**

- Consumes: `FreeCoprodCompDisc.coprodPair.{uX, uY}`,
  `FreeCoprodCompDisc.Hom`, the generalization model
  `FreeCoprodCompDisc.coprodPairMor.{uX, uY, uX', uY'}`.
- Produces (in `namespace FreeCoprodCompDisc`,
  `variable (D : Type v)`):

  ```lean
  coprodPairInl.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
    (Y : FreeCoprodCompDisc.{uY, v} D) :
    Hom D X (coprodPair.{v, uX, uY} D X Y)
  coprodPairInr.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
    (Y : FreeCoprodCompDisc.{uY, v} D) :
    Hom D Y (coprodPair.{v, uX, uY} D X Y)
  ```

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` (after
  `sampleIsoNot_hom_invHom`; `sampleX : FreeCoprodCompDisc.{0, 0} Bool`
  and `sampleXLift : FreeCoprodCompDisc.{1, 0} Bool` already exist
  there):

  ```lean
  /-- The left injection into a coproduct pair whose summands sit at
  different index universes. -/
  theorem sampleCoprodPairInl_hetero_apply :
      (FreeCoprodCompDisc.coprodPairInl.{0, 0, 1} Bool sampleX sampleXLift).1
          true =
        Sum.inl true :=
    rfl

  /-- The right injection into a coproduct pair whose summands sit at
  different index universes. -/
  theorem sampleCoprodPairInr_hetero_apply :
      (FreeCoprodCompDisc.coprodPairInr.{0, 0, 1} Bool sampleX sampleXLift).1
          (ULift.up true) =
        Sum.inr (ULift.up true) :=
    rfl
  ```

  Extend the test file's module docstring summary with one
  sentence: "The coproduct-pair injections are exercised across two
  index universes."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL — `coprodPairInl` is applied to three universe
  levels while its declaration binds two.

- [ ] **Step 3: Implement.** In
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`, replace the
  two declarations (currently between `plus` and `coprodPairDesc`)
  with:

  ```lean
  /-- The left injection into a binary coproduct. The two summands
  may sit at different index universes, mirroring `coprodPair`. -/
  def coprodPairInl.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
      (Y : FreeCoprodCompDisc.{uY, v} D) :
      Hom D X (coprodPair.{v, uX, uY} D X Y) :=
    ⟨Sum.inl, rfl⟩

  /-- The right injection into a binary coproduct. The two summands
  may sit at different index universes, mirroring `coprodPair`. -/
  def coprodPairInr.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
      (Y : FreeCoprodCompDisc.{uY, v} D) :
      Hom D Y (coprodPair.{v, uX, uY} D X Y) :=
    ⟨Sum.inr, rfl⟩
  ```

  The module docstring's `## Main definitions` entry for
  `coprodPair` already names the injections without a universe
  claim and needs no change; the `docs/index.md` sentence is
  revised in Task 10.

- [ ] **Step 4: Run the tests to verify success, and re-elaborate
  every existing call site.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files. The build
  covers every existing use — `coprodPairDesc`'s laws and
  `coprodPairMor_inr_desc_inl` in the same module,
  `FreeCoprodCompDisc/NatTrans.lean`'s `natCopowerPlusEquiv`
  development, and the two test modules — all of which pass the two
  summands at one universe and are unaffected by the widening.
  Confirm no site passes an explicit universe list to either name:

  Run: `grep -rn 'coprodPairInl\.{\|coprodPairInr\.{' --include=*.lean .`
  Expected: only the two new test theorems.

- [ ] **Step 5: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent from the working tree (see
  § Prototype-file discipline), then:

  ```bash
  jj commit -m "feat(cat): generalize the coproduct-pair injection universes"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 2: name the recursor steps of the homset injections

`IR.rec_mk` (branch 2b) rewrites `rec I O step (mk I O s d)` to
`step s d (fun x => rec I O step (d x))` only when `step` is a named
declaration: it does not unify against the inline step lambdas that
`IR.sigmaPush`, `IR.deltaEmptyPush`, and `IR.preUnitStack` currently
carry. Each is therefore re-expressed with a named motive and a
named step, in the manner of `IR.interpMorStep` (`Basic.lean`) and
`IR.interpHomEquivStep` (`Naturality.lean`), and defined as
`rec I O (…Step I O)`.

The change is intended to be mathematically inert: the three
operations' statements are unchanged (the signatures below are the
existing ones verbatim) and their values are to be unchanged. Nothing
downstream re-checks that. The `*_mk_*` equations below hold of
whatever step the operation is defined at, and
`GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`'s existing `example`s
check typing rather than value — that file's own comment records that
the `ι` homset is a subsingleton, so its `rfl` does not witness the
value of `IR.id`. A step function that mistranscribed the body it
replaces would therefore typecheck and silently change the values of
the merged `IR.id`, `IR.sigmaPush`, `IR.deltaEmptyPush`, and
`IR.preUnitStack`.

The implementation is two-phase for that reason. Step 3 inserts the
motives, the steps, and three bridge theorems
`sigmaPush_eq_rec`/`deltaEmptyPush_eq_rec`/`preUnitStack_eq_rec`,
each stating that the operation equals `rec I O (…Step I O)` and
each proved `rfl`, while the original inline-lambda bodies are still
in place; the Step 4 build is then what checks each named step
against the body it will replace. Step 5 replaces the three bodies
and deletes the three bridges, which are vacuous once the bodies are
the recursor applications. Since this edits a merged module,
`lake test` must pass unchanged, with no edit to the existing tests.

The applied `mk`-computation equations belong here rather than in
`Category.lean`: they are the characterizing equations of
`Hom.lean`'s own operations.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`

**Interfaces:**

- Consumes: `IR.rec`, `IR.rec_mk`, `IR.RecStep`, `IR.mk`,
  `IR.Direction`, `IR.Shape`, `IR.Hom`, `IR.precomp`,
  `IR.precompMerge`, `IR.mprecomp`, `IR.mprecomp_snoc`,
  `IR.mprecomp_iota_mk`, `IR.msigmaPush`, `IR.deltaNav`.
- Produces (in `namespace IR`):

  ```lean
  SigmaPushMotive / sigmaPushStep
  sigmaPush_mk_iota / sigmaPush_mk_sigma / sigmaPush_mk_delta
  DeltaEmptyPushMotive / deltaEmptyPushStep
  deltaEmptyPush_mk_iota / deltaEmptyPush_mk_sigma /
    deltaEmptyPush_mk_delta
  PreUnitStackMotive / preUnitStackStep
  preUnitStack_mk_iota / preUnitStack_mk_sigma / preUnitDeltaData /
    preUnitStack_mk_delta
  ```

- Produces transiently, in Step 3, and deletes in Step 5:
  `sigmaPush_eq_rec`, `deltaEmptyPush_eq_rec`,
  `preUnitStack_eq_rec`.

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean` (after
  `idSample`):

  ```lean
  /-- The `ι`-shaped computation equation of `IR.sigmaPush` at
  `PUnit` data. -/
  theorem sampleSigmaPush_mk_iota
      (d : Direction PUnit PUnit (Sum.inl PUnit.unit : Shape.{0, 0, 0} PUnit) →
        IR.{0, 0, 0, 0} PUnit PUnit)
      (K' : PUnit → IR.{0, 0, 0, 0} PUnit PUnit)
      (f : IR.Hom PUnit PUnit (mk PUnit PUnit (Sum.inl PUnit.unit) d)
        (K' PUnit.unit)) :
      sigmaPush PUnit PUnit (mk PUnit PUnit (Sum.inl PUnit.unit) d) PUnit K'
          PUnit.unit f =
        ⟨PUnit.unit, f⟩ :=
    sigmaPush_mk_iota PUnit PUnit PUnit.unit d PUnit K' PUnit.unit f

  /-- The `ι`-shaped computation equation of `IR.deltaEmptyPush` at
  `PEmpty` directions. -/
  theorem sampleDeltaEmptyPush_mk_iota
      (d : Direction PUnit PUnit (Sum.inl PUnit.unit : Shape.{0, 0, 0} PUnit) →
        IR.{0, 0, 0, 0} PUnit PUnit)
      (M : (PEmpty.{1} → PUnit) → IR.{0, 0, 0, 0} PUnit PUnit)
      (f : IR.Hom PUnit PUnit (mk PUnit PUnit (Sum.inl PUnit.unit) d)
        (M (fun x => (_root_.id x).elim))) :
      deltaEmptyPush PUnit PUnit (mk PUnit PUnit (Sum.inl PUnit.unit) d)
          PEmpty.{1} _root_.id M f =
        ⟨_root_.id, f⟩ :=
    deltaEmptyPush_mk_iota PUnit PUnit PUnit.unit d PEmpty.{1} _root_.id M f

  /-- The `δ`-shaped computation equation of `IR.preUnitStack` names
  its summand datum. -/
  theorem samplePreUnitStack_mk_delta
      (d : Direction PUnit PUnit
          (Sum.inr (Sum.inr PUnit) : Shape.{0, 0, 0} PUnit) →
        IR.{0, 0, 0, 0} PUnit PUnit)
      (L : List (SupObj.{0, 0} PUnit)) (i : PUnit → PUnit) :
      preUnitStack PUnit PUnit (mk PUnit PUnit (Sum.inr (Sum.inr PUnit)) d) L
          i =
        preUnitDeltaData PUnit PUnit PUnit d L i :=
    preUnitStack_mk_delta PUnit PUnit PUnit d L i
  ```

  Extend the test file's module docstring summary with one
  sentence: "The `IR.mk`-computation equations of the injection
  helpers and of the pre-unit are exercised at `PUnit` data."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.sigmaPush_mk_iota`.

- [ ] **Step 3: Implement, phase one — the named motives and steps,
  their bridge theorems, and the computation equations, with the
  three inline-lambda bodies left as they stand.** In
  `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`, insert around
  `IR.sigmaPush` (whose definition is untouched in this step) its
  named motive and step:

  ```lean
  /-- The motive of `IR.sigmaPush` (named so `IR.rec_mk` applies). -/
  def SigmaPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
      Type (max (max uA uB + 1) uI uO) :=
    ∀ (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
      (a' : A'), Hom I O γ (K' a') → Hom I O γ (sigma I O A' K')

  /-- The step of `IR.sigmaPush` (named so `IR.rec_mk` applies). -/
  def sigmaPushStep :
      RecStep.{max uA uB, uB, uI, uO, max (max uA uB + 1) uI uO} I O
        (SigmaPushMotive I O) :=
    fun s _c m => match s with
    | Sum.inl _ => fun _ _ a' f => ⟨a', f⟩
    | Sum.inr (Sum.inl _) => fun A' K' a' f b => m (ULift.up b) A' K' a' (f b)
    | Sum.inr (Sum.inr B) => fun A' K' a' f i =>
        m (ULift.up i) (ULift.{uB} A')
          (fun x => precomp I O B i (K' x.down)) (ULift.up a') (f i)
  ```

  its bridge theorem, which is what checks the step against the body
  it will replace in Step 5:

  ```lean
  /-- `IR.sigmaPush` is the recursor at `IR.sigmaPushStep`. -/
  theorem sigmaPush_eq_rec :
      sigmaPush.{uA, uB, uI, uO} I O = rec I O (sigmaPushStep I O) := rfl
  ```

  and the computation equations:

  ```lean
  /-- The characterizing equation of `IR.sigmaPush` at an `ι`-shaped
  `IR.mk`: the target data pairs with the argument. -/
  theorem sigmaPush_mk_iota (o : O)
      (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
      (a' : A') (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inl o) d) (K' a')) :
      sigmaPush I O (mk I O (Sum.inl o) d) A' K' a' f = ⟨a', f⟩ :=
    congrFun (congrFun (congrFun (congrFun
      (rec_mk I O (sigmaPushStep I O) (Sum.inl o) d) A') K') a') f

  /-- The characterizing equation of `IR.sigmaPush` at a `σ`-shaped
  `IR.mk`: componentwise recursion. -/
  theorem sigmaPush_mk_sigma (A : Type (max uA uB))
      (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
      (a' : A')
      (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inr (Sum.inl A)) d) (K' a')) :
      sigmaPush I O (mk I O (Sum.inr (Sum.inl A)) d) A' K' a' f =
        fun b => sigmaPush I O (d (ULift.up b)) A' K' a' (f b) :=
    congrFun (congrFun (congrFun (congrFun
      (rec_mk I O (sigmaPushStep I O) (Sum.inr (Sum.inl A)) d) A') K') a') f

  /-- The characterizing equation of `IR.sigmaPush` at a `δ`-shaped
  `IR.mk`: recursion at the precomposed target. -/
  theorem sigmaPush_mk_delta (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
      (a' : A')
      (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inr (Sum.inr B)) d) (K' a')) :
      sigmaPush I O (mk I O (Sum.inr (Sum.inr B)) d) A' K' a' f =
        fun i => sigmaPush I O (d (ULift.up i)) (ULift.{uB} A')
          (fun x => precomp I O B i (K' x.down)) (ULift.up a') (f i) :=
    congrFun (congrFun (congrFun (congrFun
      (rec_mk I O (sigmaPushStep I O) (Sum.inr (Sum.inr B)) d) A') K') a') f
  ```

  Then the same treatment for `IR.deltaEmptyPush`:

  ```lean
  /-- The motive of `IR.deltaEmptyPush` (named so `IR.rec_mk` applies). -/
  def DeltaEmptyPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
      Type (max (max uA uB + 1) uI uO) :=
    ∀ (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O),
      Hom I O γ (M (fun x => (e x).elim)) → Hom I O γ (delta I O E M)

  /-- The step of `IR.deltaEmptyPush` (named so `IR.rec_mk` applies). -/
  def deltaEmptyPushStep :
      RecStep.{max uA uB, uB, uI, uO, max (max uA uB + 1) uI uO} I O
        (DeltaEmptyPushMotive I O) :=
    fun s c m => match s with
    | Sum.inl _ => fun _ e _ f => ⟨e, f⟩
    | Sum.inr (Sum.inl _) => fun E e M f b => m (ULift.up b) E e M (f b)
    | Sum.inr (Sum.inr B) => fun E e M f i =>
        sigmaPush I O (c (ULift.up i)) (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
          (fun cl => delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
            (fun j => precomp I O B i (M (precompMerge I B i cl.down j))))
          (ULift.up (fun x => (e x).elim))
          (m (ULift.up i) {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
            (fun z => (e z.1).elim)
            (fun j => precomp I O B i (M (precompMerge I B i (fun x => (e x).elim) j)))
            (cast (congrArg
              (fun a => Hom I O (c (ULift.up i)) (precomp I O B i (M a)))
              (funext (fun x => (e x).elim) :
                (fun x => (e x).elim) = precompMerge I B i (fun x => (e x).elim)
                      (fun z : {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                        => ((e z.1).elim : PEmpty.{1}).elim)))
              (f i)))
  ```

  its bridge theorem:

  ```lean
  /-- `IR.deltaEmptyPush` is the recursor at `IR.deltaEmptyPushStep`. -/
  theorem deltaEmptyPush_eq_rec :
      deltaEmptyPush.{uA, uB, uI, uO} I O = rec I O (deltaEmptyPushStep I O) := rfl
  ```

  and:

  ```lean
  /-- The characterizing equation of `IR.deltaEmptyPush` at an `ι`-shaped
  `IR.mk`: the empty witness pairs with the argument. -/
  theorem deltaEmptyPush_mk_iota (o : O)
      (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inl o) d)
        (M (fun x => (e x).elim))) :
      deltaEmptyPush I O (mk I O (Sum.inl o) d) E e M f = ⟨e, f⟩ :=
    congrFun (congrFun (congrFun (congrFun
      (rec_mk I O (deltaEmptyPushStep I O) (Sum.inl o) d) E) e) M) f

  /-- The characterizing equation of `IR.deltaEmptyPush` at a `σ`-shaped
  `IR.mk`: componentwise recursion. -/
  theorem deltaEmptyPush_mk_sigma (A : Type (max uA uB))
      (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inr (Sum.inl A)) d)
        (M (fun x => (e x).elim))) :
      deltaEmptyPush I O (mk I O (Sum.inr (Sum.inl A)) d) E e M f =
        fun b => deltaEmptyPush I O (d (ULift.up b)) E e M (f b) :=
    congrFun (congrFun (congrFun (congrFun
      (rec_mk I O (deltaEmptyPushStep I O) (Sum.inr (Sum.inl A)) d) E) e) M) f

  /-- The characterizing equation of `IR.deltaEmptyPush` at a `δ`-shaped
  `IR.mk`: injection through the all-resolved classifier summand of the
  precomposed `δ`-code, recursing at the unresolved subtype. -/
  theorem deltaEmptyPush_mk_delta (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inr (Sum.inr B)) d)
        (M (fun x => (e x).elim))) :
      deltaEmptyPush I O (mk I O (Sum.inr (Sum.inr B)) d) E e M f =
        fun i => sigmaPush I O (d (ULift.up i))
          (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
          (fun cl => delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
            (fun j => precomp I O B i (M (precompMerge I B i cl.down j))))
          (ULift.up (fun x => (e x).elim))
          (deltaEmptyPush I O (d (ULift.up i))
            {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
            (fun z => (e z.1).elim)
            (fun j => precomp I O B i (M (precompMerge I B i (fun x => (e x).elim) j)))
            (cast (congrArg
              (fun a => Hom I O (d (ULift.up i)) (precomp I O B i (M a)))
              (funext (fun x => (e x).elim) :
                (fun x => (e x).elim) = precompMerge I B i (fun x => (e x).elim)
                      (fun z : {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                        => ((e z.1).elim : PEmpty.{1}).elim)))
              (f i))) :=
    congrFun (congrFun (congrFun (congrFun
      (rec_mk I O (deltaEmptyPushStep I O) (Sum.inr (Sum.inr B)) d) E) e) M) f
  ```

  Then the same treatment for `IR.preUnitStack` (which sits after
  `IR.deltaNav`):

  ```lean
  /-- The motive of `IR.preUnitStack` (named so `IR.rec_mk` applies). -/
  def PreUnitStackMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
      Type (max uA (uB + 1) uI) :=
    ∀ L : List (SupObj.{uB, uI} I), Hom.{uA, uB, uI, uO} I O γ (mprecomp I O L γ)

  /-- The step of `IR.preUnitStack` (named so `IR.rec_mk` applies). -/
  def preUnitStackStep :
      RecStep.{max uA uB, uB, uI, uO, max uA (uB + 1) uI} I O
        (PreUnitStackMotive I O) :=
    fun s c m => match s with
    | Sum.inl o => fun L =>
        cast (congrArg (InnerHom.{uA, uB, uI, uO} I O o)
            (mprecomp_iota_mk I O L o c).symm)
          (ULift.up (PLift.up rfl) : InnerHom.{uA, uB, uI, uO} I O o (iota I O o))
    | Sum.inr (Sum.inl A) => fun L a =>
        msigmaPush I O (c (ULift.up a)) A (fun a' => c (ULift.up a')) a L
          (m (ULift.up a) L)
    | Sum.inr (Sum.inr B) => fun L i =>
        cast (congrArg (Hom I O (c (ULift.up i)))
               (mprecomp_snoc I O L ⟨B, i⟩ (mk I O (Sum.inr (Sum.inr B)) c)))
          (deltaNav I O (c (ULift.up i)) B i B (fun i' => c (ULift.up i')) _root_.id L
            (m (ULift.up i) (L ++ [⟨B, i⟩])))
  ```

  its bridge theorem:

  ```lean
  /-- `IR.preUnitStack` is the recursor at `IR.preUnitStackStep`. -/
  theorem preUnitStack_eq_rec :
      preUnitStack.{uA, uB, uI, uO} I O = rec I O (preUnitStackStep I O) := rfl
  ```

  and:

  ```lean
  /-- The characterizing equation of `IR.preUnitStack` at an `ι`-shaped
  `IR.mk`: the transported reflexivity witness. -/
  theorem preUnitStack_mk_iota (o : O)
      (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (L : List (SupObj.{uB, uI} I)) :
      preUnitStack I O (mk I O (Sum.inl o) d) L =
        cast (congrArg (InnerHom.{uA, uB, uI, uO} I O o)
            (mprecomp_iota_mk I O L o d).symm)
          (ULift.up (PLift.up rfl) : InnerHom.{uA, uB, uI, uO} I O o (iota I O o)) :=
    congrFun (rec_mk I O (preUnitStackStep I O) (Sum.inl o) d) L

  /-- The characterizing equation of `IR.preUnitStack` at a `σ`-shaped
  `IR.mk`: the subcode's pre-unit pushed along the stack `σ`-injection. -/
  theorem preUnitStack_mk_sigma (A : Type (max uA uB))
      (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (L : List (SupObj.{uB, uI} I)) (a : A) :
      preUnitStack I O (mk I O (Sum.inr (Sum.inl A)) d) L a =
        msigmaPush I O (d (ULift.up a)) A (fun a' => d (ULift.up a')) a L
          (preUnitStack I O (d (ULift.up a)) L) :=
    congrFun (congrFun
      (rec_mk I O (preUnitStackStep I O) (Sum.inr (Sum.inl A)) d) L) a

  /-- The `δ`-domain pre-unit's summand datum: the subcode's pre-unit at
  the extended stack, navigated up the tower and transported by
  `IR.mprecomp_snoc`. -/
  def preUnitDeltaData (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (L : List (SupObj.{uB, uI} I)) (i : B → I) :
      Hom.{uA, uB, uI, uO} I O (d (ULift.up i))
        (precomp I O B i (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))) :=
    cast (congrArg (Hom I O (d (ULift.up i)))
        (mprecomp_snoc I O L ⟨B, i⟩ (mk I O (Sum.inr (Sum.inr B)) d)))
      (deltaNav I O (d (ULift.up i)) B i B (fun i' => d (ULift.up i')) _root_.id L
        (preUnitStack I O (d (ULift.up i)) (L ++ [⟨B, i⟩])))

  /-- The characterizing equation of `IR.preUnitStack` at a `δ`-shaped
  `IR.mk`: the summand datum `IR.preUnitDeltaData` at every assignment. -/
  theorem preUnitStack_mk_delta (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (L : List (SupObj.{uB, uI} I)) (i : B → I) :
      preUnitStack I O (mk I O (Sum.inr (Sum.inr B)) d) L i =
        preUnitDeltaData I O B d L i :=
    congrFun (congrFun
      (rec_mk I O (preUnitStackStep I O) (Sum.inr (Sum.inr B)) d) L) i
  ```

  Update the module docstring. Append to `## Main definitions`:

  ```markdown
  * `IR.SigmaPushMotive`, `IR.sigmaPushStep`,
    `IR.DeltaEmptyPushMotive`, `IR.deltaEmptyPushStep`,
    `IR.PreUnitStackMotive`, `IR.preUnitStackStep` — the named
    motives and recursor steps of the three `IR.rec`-built
    operations, at which `IR.rec_mk` applies.
  * `IR.preUnitDeltaData` — the `δ`-domain pre-unit's summand datum.
  ```

  and to `## Main statements`:

  ```markdown
  * `IR.sigmaPush_mk_iota`, `IR.sigmaPush_mk_sigma`,
    `IR.sigmaPush_mk_delta`, `IR.deltaEmptyPush_mk_iota`,
    `IR.deltaEmptyPush_mk_sigma`, `IR.deltaEmptyPush_mk_delta`,
    `IR.preUnitStack_mk_iota`, `IR.preUnitStack_mk_sigma`,
    `IR.preUnitStack_mk_delta` — the computation equations of the
    three operations at an `IR.mk`-built domain code.
  ```

- [ ] **Step 4: Build phase one.**

  Run: `lake build`
  Expected: PASS. `IR.sigmaPush_eq_rec`,
  `IR.deltaEmptyPush_eq_rec`, and `IR.preUnitStack_eq_rec` each
  elaborate their `rfl` against the operation's original
  inline-lambda body, so this build is the check that each named
  step is definitionally the body Step 5 substitutes for it. A `rfl`
  failure here is a mistranscribed step: correct the step, not the
  bridge.

- [ ] **Step 5: Implement, phase two — replace the three bodies and
  delete the three bridge theorems.** In
  `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`, replace the body of
  `IR.sigmaPush`, its signature and docstring unchanged:

  ```lean
  def sigmaPush : (γ : IR.{max uA uB, uB, uI, uO} I O) →
        ∀ (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A'),
          Hom I O γ (K' a') → Hom I O γ (sigma I O A' K') :=
    rec I O (sigmaPushStep I O)
  ```

  and likewise `IR.deltaEmptyPush`'s body with
  `rec I O (deltaEmptyPushStep I O)` and `IR.preUnitStack`'s with
  `rec I O (preUnitStackStep I O)`, each under its unchanged
  signature and docstring. Then delete `IR.sigmaPush_eq_rec`,
  `IR.deltaEmptyPush_eq_rec`, and `IR.preUnitStack_eq_rec`: each now
  states that a recursor application equals itself, and carries no
  content. They enter neither the committed module nor its
  docstring.

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files, and no edit to
  any pre-existing test: the three operations' types and values are
  unchanged, so `GebTests/.../Hom.lean`'s existing definitional
  checks (`IR.sigmaPush`, `IR.deltaEmptyPush`, `IR.deltaNav`,
  `IR.id`) still hold by `rfl`.

- [ ] **Step 6: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent, then:

  ```bash
  jj commit -m "feat(indrec): name the recursor steps of the homset injections"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 3: the `Category` module and the semantic tower

The branch's module, and the semantic counterpart of the pre-unit's
stack: the iterated coproduct object `IR.mplus`, the iterated
injection `IR.mplusInj`, the iterated Lemma 4 isomorphism
`IR.mprecompIso`, and the semantic pre-unit component
`IR.preUnitComponent` against which the identity-image induction
(Task 8) states its motive. The snoc lemmas describe each of the
three at a right-appended superscript — the direction in which the
`δ`-case of that induction extends the stack — and
`IR.mprecompIso_natural` upgrades the tower isomorphism to a natural
one, over the tower action on morphisms `IR.mplusMorMap`.

`IR.mplusMorMap` and `IR.mprecompIso_natural` extend the spec's
tower subsection, which names `IR.mplus`, `IR.mplusInj`, and
`IR.mprecompIso` only: the `δ`-case of Task 8's induction requires
the tower action on morphisms and the naturality of the tower
isomorphism in the interpreted object, and both were identified
while prototyping that case.

The prototype's `coprodPairInr'` is Task 1's generalized
`FreeCoprodCompDisc.coprodPairInr`; its universe list `.{uA, uB, uI}`
becomes `.{uI, uB, max uA uB}`, and `comp_coprodPairInr'_cast` is
named `comp_coprodPairInr_cast`. Both renames are applied in the
code below.

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec.lean` (add
  `public import Geb.Mathlib.Data.PFunctor.IndRec.Category`)
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec.lean` (add
  `import GebTests.Mathlib.Data.PFunctor.IndRec.Category`)

  Register in BOTH umbrellas, inserting the `Category` line after
  `Naturality` and before `Universes`, so the import order continues
  to follow the development order (`Basic`, `Hom`, `Functor`,
  `Naturality`, `Category`, `Universes`, `Container`);
  `scripts/pre-push.sh` is the only gate that catches a missing
  registration.

**Interfaces:**

- Consumes: `IR.SupObj`, `IR.mprecomp`, `IR.mprecomp_snoc`,
  `IR.precomp`, `IR.interpObj`, `IR.interpMor`, `IR.interpMor_id`,
  `IR.interpPrecompIso`, `IR.interpPrecompIso_natural`,
  `FreeCoprodCompDisc.plus`, `FreeCoprodCompDisc.coprodPairInr`
  (Task 1), `FreeCoprodCompDisc.coprodPairMor`,
  `FreeCoprodCompDisc.Hom.id`/`comp`/`id_comp`/`comp_id`/`comp_assoc`,
  `FreeCoprodCompDisc.Iso.refl`/`trans`/`hom`/`invHom`,
  `FreeCoprodCompDisc.isoOfEq`.
- Produces (in `namespace IR`): `mplus`, `mplus_snoc`, `mplusInj`,
  `comp_coprodPairInr_cast`, `mplusInj_snoc`, `mprecompIso`,
  `interpPrecompIso_hom_isoOfEq`, `interpPrecompIso_invHom_isoOfEq`,
  `mprecompIso_snoc_hom`, `mprecompIso_snoc_invHom`, `mplusMorMap`,
  `mprecompIso_natural`, `preUnitComponent`, `preUnitComponent_nil`.

- [ ] **Step 1: Create the test file (failing).**
  `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Category

  /-!
  # Tests for the category of IR codes

  A sample object, superscript, and `ι`-code over the Booleans
  exercise the semantic tower: the iterated coproduct object and its
  injection at the empty and singleton stacks and at a right-appended
  superscript, the tower action on morphisms, the iterated Lemma 4
  isomorphism at the empty stack, at a right-appended superscript,
  and in the interpreted object, and the semantic pre-unit component
  at the empty stack. Named theorems give the `GebMeta` axiom linter
  declarations to inspect.

  ## Tags

  inductive-recursive, morphism, category
  -/

  @[expose] public section

  open CategoryTheory
  open IndRec IndRec.IR

  /-- A sample object over the Boolean index type. -/
  def sampleCategoryObj : FreeCoprodCompDisc.{0, 0} Bool :=
    ⟨Bool, fun b ↦ b⟩

  /-- A sample superscript object over the Boolean index type. -/
  def sampleCategorySup : SupObj.{0, 0} Bool :=
    ⟨Bool, fun b ↦ b⟩

  /-- A sample `ι`-code over the Booleans. -/
  def sampleCategoryCode : IR.{0, 0, 0, 0} Bool Bool :=
    iota Bool Bool true

  /-- The tower object at a singleton stack, exercising `IR.mplus`. -/
  def sampleMplusObj : FreeCoprodCompDisc.{0, 0} Bool :=
    mplus Bool [sampleCategorySup] sampleCategoryObj

  /-- The tower at the empty stack is its base. -/
  theorem sampleMplus_nil :
      mplus Bool [] sampleCategoryObj = sampleCategoryObj :=
    rfl

  /-- The tower injection at a singleton stack is the right injection. -/
  theorem sampleMplusInj_apply :
      (mplusInj Bool [sampleCategorySup] sampleCategoryObj).1 true =
        Sum.inr true :=
    rfl

  /-- The tower action on morphisms fixes the stacked superscript. -/
  theorem sampleMplusMorMap_apply :
      (mplusMorMap Bool [sampleCategorySup] sampleCategoryObj sampleCategoryObj
          (FreeCoprodCompDisc.Hom.id Bool sampleCategoryObj)).1 (Sum.inl true) =
        Sum.inl true :=
    rfl

  /-- The tower isomorphism at the empty stack is the identity. -/
  theorem sampleMprecompIso_nil :
      FreeCoprodCompDisc.Iso.hom Bool
          (mprecompIso Bool Bool [] sampleCategoryCode sampleCategoryObj) =
        FreeCoprodCompDisc.Hom.id Bool
          (interpObj Bool Bool sampleCategoryCode sampleCategoryObj) :=
    Subtype.ext rfl

  /-- The semantic pre-unit component at the empty stack is the
  identity. -/
  theorem samplePreUnitComponent_nil :
      preUnitComponent Bool Bool sampleCategoryCode [] sampleCategoryObj =
        FreeCoprodCompDisc.Hom.id Bool
          (interpObj Bool Bool sampleCategoryCode sampleCategoryObj) :=
    preUnitComponent_nil Bool Bool sampleCategoryCode sampleCategoryObj

  /-- The tower at a right-appended superscript. -/
  theorem sampleMplus_snoc :
      mplus Bool ([sampleCategorySup] ++ [sampleCategorySup]) sampleCategoryObj =
        mplus Bool [sampleCategorySup]
          (FreeCoprodCompDisc.plus Bool sampleCategorySup sampleCategoryObj) :=
    mplus_snoc Bool [sampleCategorySup] sampleCategorySup sampleCategoryObj

  /-- The tower injection at a right-appended superscript. -/
  theorem sampleMplusInj_snoc :
      cast (congrArg (FreeCoprodCompDisc.Hom Bool sampleCategoryObj)
          (mplus_snoc Bool [sampleCategorySup] sampleCategorySup sampleCategoryObj))
          (mplusInj Bool ([sampleCategorySup] ++ [sampleCategorySup]) sampleCategoryObj) =
        FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.coprodPairInr Bool sampleCategorySup sampleCategoryObj)
          (mplusInj Bool [sampleCategorySup]
            (FreeCoprodCompDisc.plus Bool sampleCategorySup sampleCategoryObj)) :=
    mplusInj_snoc Bool [sampleCategorySup] sampleCategorySup sampleCategoryObj

  /-- The forward component of the tower isomorphism at a right-appended
  superscript. -/
  theorem sampleMprecompIso_snoc_hom :
      FreeCoprodCompDisc.Iso.hom Bool
          (mprecompIso Bool Bool ([sampleCategorySup] ++ [sampleCategorySup])
            sampleCategoryCode sampleCategoryObj) =
        FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Hom.comp Bool
            (FreeCoprodCompDisc.Iso.hom Bool (FreeCoprodCompDisc.isoOfEq Bool
              (congrArg (fun c => interpObj Bool Bool c sampleCategoryObj)
                (mprecomp_snoc Bool Bool [sampleCategorySup] sampleCategorySup
                  sampleCategoryCode))))
            (FreeCoprodCompDisc.Iso.hom Bool
              (interpPrecompIso Bool Bool
                (mprecomp Bool Bool [sampleCategorySup] sampleCategoryCode)
                sampleCategorySup.1 sampleCategorySup.2 sampleCategoryObj)))
          (FreeCoprodCompDisc.Hom.comp Bool
            (FreeCoprodCompDisc.Iso.hom Bool
              (mprecompIso Bool Bool [sampleCategorySup] sampleCategoryCode
                (FreeCoprodCompDisc.plus Bool sampleCategorySup sampleCategoryObj)))
            (FreeCoprodCompDisc.Iso.hom Bool (FreeCoprodCompDisc.isoOfEq Bool
              (congrArg (interpObj Bool Bool sampleCategoryCode)
                (mplus_snoc Bool [sampleCategorySup] sampleCategorySup
                  sampleCategoryObj).symm)))) :=
    mprecompIso_snoc_hom Bool Bool [sampleCategorySup] sampleCategorySup
      sampleCategoryCode sampleCategoryObj

  /-- The inverse component of the tower isomorphism at a right-appended
  superscript. -/
  theorem sampleMprecompIso_snoc_invHom :
      FreeCoprodCompDisc.Iso.invHom Bool
          (mprecompIso Bool Bool ([sampleCategorySup] ++ [sampleCategorySup])
            sampleCategoryCode sampleCategoryObj) =
        FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Hom.comp Bool
            (FreeCoprodCompDisc.Iso.hom Bool (FreeCoprodCompDisc.isoOfEq Bool
              (congrArg (interpObj Bool Bool sampleCategoryCode)
                (mplus_snoc Bool [sampleCategorySup] sampleCategorySup
                  sampleCategoryObj))))
            (FreeCoprodCompDisc.Iso.invHom Bool
              (mprecompIso Bool Bool [sampleCategorySup] sampleCategoryCode
                (FreeCoprodCompDisc.plus Bool sampleCategorySup sampleCategoryObj))))
          (FreeCoprodCompDisc.Hom.comp Bool
            (FreeCoprodCompDisc.Iso.invHom Bool
              (interpPrecompIso Bool Bool
                (mprecomp Bool Bool [sampleCategorySup] sampleCategoryCode)
                sampleCategorySup.1 sampleCategorySup.2 sampleCategoryObj))
            (FreeCoprodCompDisc.Iso.hom Bool (FreeCoprodCompDisc.isoOfEq Bool
              (congrArg (fun c => interpObj Bool Bool c sampleCategoryObj)
                (mprecomp_snoc Bool Bool [sampleCategorySup] sampleCategorySup
                  sampleCategoryCode).symm)))) :=
    mprecompIso_snoc_invHom Bool Bool [sampleCategorySup] sampleCategorySup
      sampleCategoryCode sampleCategoryObj

  /-- Naturality of the tower isomorphism at a singleton stack. -/
  theorem sampleMprecompIso_natural
      (h : FreeCoprodCompDisc.Hom Bool sampleCategoryObj sampleCategoryObj) :
      FreeCoprodCompDisc.Hom.comp Bool
          (interpMor Bool Bool
            (mprecomp Bool Bool [sampleCategorySup] sampleCategoryCode)
            sampleCategoryObj sampleCategoryObj h)
          (FreeCoprodCompDisc.Iso.hom Bool
            (mprecompIso Bool Bool [sampleCategorySup] sampleCategoryCode
              sampleCategoryObj)) =
        FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Iso.hom Bool
            (mprecompIso Bool Bool [sampleCategorySup] sampleCategoryCode
              sampleCategoryObj))
          (interpMor Bool Bool sampleCategoryCode
            (mplus Bool [sampleCategorySup] sampleCategoryObj)
            (mplus Bool [sampleCategorySup] sampleCategoryObj)
            (mplusMorMap Bool [sampleCategorySup] sampleCategoryObj sampleCategoryObj
              h)) :=
    mprecompIso_natural Bool Bool [sampleCategorySup] sampleCategoryCode
      sampleCategoryObj sampleCategoryObj h
  ```

  (The five appended theorems are transcribed from the prototype's
  scratch tests; the prototype's `coprodPairInr'.{0, 0, 0} Bool` is
  Task 1's `FreeCoprodCompDisc.coprodPairInr Bool`, whose universes
  the arguments determine.)

  Register the module in BOTH `IndRec` umbrellas as listed under
  **Files**.

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL — `Geb.Mathlib.Data.PFunctor.IndRec.Category` does
  not exist yet.

- [ ] **Step 3: Implement.** Create
  `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean` with the header
  and module docstring:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Naturality

  /-!
  # The category of IR codes

  Corollary 2 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: `IR`
  codes and the homsets of Definition 8 form a category. Composition
  is transferred through the full-and-faithful interpretation of
  Theorem 3 — the code morphism carried by the vertical composite of
  the interpreted transformations — and the category laws follow from
  the vertical laws together with the round-trip laws of the Theorem 3
  equivalence. The identity laws additionally consume the
  identity-image equation `IR.interpHom_id`, proved by induction on
  the domain code over the stack of `IR.preUnitStack`, against the
  semantic counterpart of that stack: an iterated coproduct tower with
  its iterated Lemma 4 isomorphism.

  ## Main definitions

  * `IR.mplus`, `IR.mplusInj`, `IR.mplusMorMap` — the iterated
    coproduct object of a stack of superscripts, its iterated
    injection, and its action on morphisms.
  * `IR.mprecompIso` — the iterated Lemma 4 isomorphism between the
    interpretation of an iterated precomposition and the
    interpretation at `IR.mplus`.
  * `IR.preUnitComponent` — the semantic pre-unit component: the
    interpretation image of `IR.mplusInj`, composed with the inverse
    of `IR.mprecompIso`.

  ## Main statements

  * `IR.mplus_snoc`, `IR.mplusInj_snoc`, `IR.mprecompIso_snoc_hom`,
    `IR.mprecompIso_snoc_invHom` — the tower at a right-appended
    superscript, the direction in which the `δ`-case of the
    identity-image induction extends the stack.
  * `IR.mprecompIso_natural` — naturality of the tower isomorphism in
    the interpreted object.
  * `IR.preUnitComponent_nil` — the semantic pre-unit component at the
    empty stack is the identity.

  ## Implementation notes

  The tower constructions recurse on the stack through `List.rec`, not
  on codes; the snoc lemmas are the corresponding `List.rec`
  inductions, with the motive quantified over the code where the
  recursion changes it (`IR.mprecompIso` and its snoc lemmas). Object
  equalities entering the tower (`IR.mplus_snoc`, `IR.mprecomp_snoc`)
  are carried as `FreeCoprodCompDisc.isoOfEq` transports and commuted
  across the Lemma 4 isomorphism by elimination of the generalized
  equality.

  ## References

  * [HancockMcBrideGhaniMalatestaAltenkirch2013]

  ## Tags

  inductive-recursive, morphism, category
  -/

  @[expose] public section

  universe uA uB uI uO

  namespace IndRec

  open CategoryTheory

  variable (I : Type uI) (O : Type uO)

  namespace IR
  ```

  and, in that namespace, the tower:

  ```lean
  /-- The iterated coproduct object: fold `plus` over the stack. -/
  def mplus (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.{max uA uB, uI} I :=
    L.rec X (fun b _L ih => FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b ih)

  /-- `mplus` at a right-appended superscript feeds the coproduct at the
  inner position. -/
  theorem mplus_snoc (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      mplus.{uA, uB, uI} I (L ++ [b]) X =
        mplus.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X) :=
    L.rec (motive := fun L => mplus.{uA, uB, uI} I (L ++ [b]) X =
        mplus.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
      rfl
      (fun a _L ih => congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) ih)

  /-- The iterated right injection into `mplus`. -/
  def mplusInj (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom I X (mplus.{uA, uB, uI} I L X) :=
    L.rec (motive := fun L => FreeCoprodCompDisc.Hom I X (mplus.{uA, uB, uI} I L X))
      (FreeCoprodCompDisc.Hom.id I X)
      (fun b _L ih => FreeCoprodCompDisc.Hom.comp I ih
        (FreeCoprodCompDisc.coprodPairInr I b (mplus.{uA, uB, uI} I _L X)))

  /-- The iterated Lemma 4 isomorphism between the interpretation of an
  iterated precomposition and the interpretation at `mplus`. -/
  def mprecompIso (L : List (SupObj.{uB, uI} I)) :
      ∀ (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I),
        FreeCoprodCompDisc.Iso O (interpObj I O (mprecomp I O L γ) X)
          (interpObj I O γ (mplus.{uA, uB, uI} I L X)) :=
    L.rec (motive := fun L => ∀ γ X,
        FreeCoprodCompDisc.Iso O (interpObj I O (mprecomp I O L γ) X)
          (interpObj I O γ (mplus.{uA, uB, uI} I L X)))
      (fun γ X => FreeCoprodCompDisc.Iso.refl O (interpObj I O γ X))
      (fun b _L ih γ X =>
        FreeCoprodCompDisc.Iso.trans O (ih (precomp I O b.1 b.2 γ) X)
          (interpPrecompIso I O γ b.1 b.2 (mplus.{uA, uB, uI} I _L X)))

  /-- The semantic pre-unit component: the interpretation image of the
  iterated injection, composed with the inverse of the iterated Lemma 4
  isomorphism. -/
  def preUnitComponent (γ : IR.{max uA uB, uB, uI, uO} I O)
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom O (interpObj I O γ X)
        (interpObj I O (mprecomp I O L γ) X) :=
    FreeCoprodCompDisc.Hom.comp O
      (interpMor I O γ X (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X))
      (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O L γ X))

  /-- At the empty stack the semantic pre-unit component is the
  identity. -/
  theorem preUnitComponent_nil (γ : IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      preUnitComponent I O γ [] X = FreeCoprodCompDisc.Hom.id O (interpObj I O γ X) :=
    (congrArg (fun t => FreeCoprodCompDisc.Hom.comp O t
        (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O [] γ X)))
      (interpMor_id I O γ X)).trans
      (FreeCoprodCompDisc.Hom.id_comp O
        (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O [] γ X)))
  ```

  then the snoc lemmas:

  ```lean
  /-- Transport of a composite with a fresh right injection along an
  equality of the inner object, by elimination of the generalized
  equality: the cast passes to the left factor. -/
  theorem comp_coprodPairInr_cast (a : SupObj.{uB, uI} I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W')
        (u : FreeCoprodCompDisc.Hom I X W),
        cast (congrArg (FreeCoprodCompDisc.Hom I X)
            (congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) e))
          (FreeCoprodCompDisc.Hom.comp I u
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W)) =
        FreeCoprodCompDisc.Hom.comp I
          (cast (congrArg (FreeCoprodCompDisc.Hom I X) e) u)
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W') :=
    fun W _W' e =>
      Eq.rec (motive := fun W'' e' => ∀ u : FreeCoprodCompDisc.Hom I X W,
          cast (congrArg (FreeCoprodCompDisc.Hom I X)
              (congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) e'))
            (FreeCoprodCompDisc.Hom.comp I u
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W)) =
          FreeCoprodCompDisc.Hom.comp I
            (cast (congrArg (FreeCoprodCompDisc.Hom I X) e') u)
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W''))
        (fun _ => rfl) e

  /-- `IR.mplusInj` at a right-appended superscript, transported along
  `IR.mplus_snoc`: the fresh inner injection followed by the tower
  injection at the enlarged base. -/
  theorem mplusInj_snoc (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      cast (congrArg (FreeCoprodCompDisc.Hom I X) (mplus_snoc.{uA, uB, uI} I L b X))
          (mplusInj.{uA, uB, uI} I (L ++ [b]) X) =
        FreeCoprodCompDisc.Hom.comp I
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
          (mplusInj.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)) :=
    L.rec (motive := fun L' =>
        cast (congrArg (FreeCoprodCompDisc.Hom I X) (mplus_snoc.{uA, uB, uI} I L' b X))
            (mplusInj.{uA, uB, uI} I (L' ++ [b]) X) =
          FreeCoprodCompDisc.Hom.comp I
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
            (mplusInj.{uA, uB, uI} I L'
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
      ((FreeCoprodCompDisc.Hom.id_comp I
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)).trans
        (FreeCoprodCompDisc.Hom.comp_id I
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)).symm)
      (fun a _L ih =>
        (comp_coprodPairInr_cast I a X (mplus.{uA, uB, uI} I (_L ++ [b]) X)
            (mplus.{uA, uB, uI} I _L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
            (mplus_snoc.{uA, uB, uI} I _L b X)
            (mplusInj.{uA, uB, uI} I (_L ++ [b]) X)).trans
          ((congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp I t
                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                  (mplus.{uA, uB, uI} I _L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
              ih).trans
            (FreeCoprodCompDisc.Hom.comp_assoc I
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
              (mplusInj.{uA, uB, uI} I _L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                (mplus.{uA, uB, uI} I _L
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))))

  /-- The Lemma 4 isomorphism commutes object-equality transports across
  its two sides (forward direction), by elimination of the generalized
  equality. -/
  theorem interpPrecompIso_hom_isoOfEq (γ : IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (q : Q → I) :
      ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W'),
        FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O (precomp I O Q q γ)) e)))
            (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W')) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg
                (fun w => interpObj I O γ
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
                e))) :=
    fun W _W' e =>
      Eq.rec (motive := fun W'' e' =>
          FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O (precomp I O Q q γ)) e')))
              (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W'')) =
            FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg
                  (fun w => interpObj I O γ
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
                  e'))))
        rfl e

  /-- The Lemma 4 isomorphism commutes object-equality transports across
  its two sides (inverse direction), by elimination of the generalized
  equality. -/
  theorem interpPrecompIso_invHom_isoOfEq (γ : IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (q : Q → I) :
      ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W'),
        FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg
                (fun w => interpObj I O γ
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
                e)))
            (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W')) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O (precomp I O Q q γ)) e))) :=
    fun W _W' e =>
      Eq.rec (motive := fun W'' e' =>
          FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg
                  (fun w => interpObj I O γ
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
                  e')))
              (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W'')) =
            FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O (precomp I O Q q γ)) e'))))
        rfl e

  /-- The forward component of `IR.mprecompIso` at a right-appended
  superscript: one Lemma 4 layer at the base of the tower, conjugated by
  the `IR.mprecomp_snoc` and `IR.mplus_snoc` transports. -/
  theorem mprecompIso_snoc_hom (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
      (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [b]) γ X) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun c => interpObj I O c X) (mprecomp_snoc I O L b γ))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X)))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X).symm)))) :=
    L.rec (motive := fun L' => ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
        FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O (L' ++ [b]) γ' X) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun c => interpObj I O c X) (mprecomp_snoc I O L' b γ'))))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (mprecomp I O L' γ') b.1 b.2 X)))
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L' γ'
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O γ')
                  (mplus_snoc.{uA, uB, uI} I L' b X).symm)))))
      (fun _ => rfl)
      (fun a _L ih γ' =>
        (congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
            (ih (precomp I O a.1 a.2 γ'))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun c => interpObj I O c X)
                    (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')))))
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                    b.1 b.2 X)))
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                    (mplus_snoc.{uA, uB, uI} I _L b X).symm))))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X)))).trans
            (congrArg
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                    (congrArg (fun c => interpObj I O c X)
                      (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')))))
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O
                      (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))))
              ((FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                  (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                    (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                      (mplus_snoc.{uA, uB, uI} I _L b X).symm)))
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O γ' a.1 a.2
                      (mplus.{uA, uB, uI} I (_L ++ [b]) X)))).trans
                ((congrArg
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O a.1 a.2 γ')
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
                    (interpPrecompIso_hom_isoOfEq I O γ' a.1 a.2
                      (mplus.{uA, uB, uI} I _L
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
                      (mplus.{uA, uB, uI} I (_L ++ [b]) X)
                      (mplus_snoc.{uA, uB, uI} I _L b X).symm)).trans
                  (FreeCoprodCompDisc.Hom.comp_assoc O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O γ' a.1 a.2
                        (mplus.{uA, uB, uI} I _L
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
                    (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                      (congrArg
                        (fun w => interpObj I O γ'
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a w))
                        (mplus_snoc.{uA, uB, uI} I _L b X).symm)))).symm)))))
      γ

  /-- The inverse component of `IR.mprecompIso` at a right-appended
  superscript: the inverse of one Lemma 4 layer at the base of the
  tower, conjugated by the `IR.mplus_snoc` and `IR.mprecomp_snoc`
  transports. -/
  theorem mprecompIso_snoc_invHom (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
      (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Iso.invHom O
          (mprecompIso.{uA, uB, uI, uO} I O (L ++ [b]) γ X) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X))))
            (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O L γ
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.invHom O
              (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun c => interpObj I O c X)
                (mprecomp_snoc I O L b γ).symm)))) :=
    L.rec (motive := fun L' => ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
        FreeCoprodCompDisc.Iso.invHom O
            (mprecompIso.{uA, uB, uI, uO} I O (L' ++ [b]) γ' X) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O γ') (mplus_snoc.{uA, uB, uI} I L' b X))))
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O L' γ'
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.invHom O
                (interpPrecompIso I O (mprecomp I O L' γ') b.1 b.2 X))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun c => interpObj I O c X)
                  (mprecomp_snoc I O L' b γ').symm)))))
      (fun _ => rfl)
      (fun a _L ih γ' =>
        (congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.invHom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
            (ih (precomp I O a.1 a.2 γ'))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.invHom O
                  (interpPrecompIso I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
              (FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                    (mplus_snoc.{uA, uB, uI} I _L b X))))
                (FreeCoprodCompDisc.Iso.invHom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.invHom O
                    (interpPrecompIso I O
                      (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))
                  (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                    (congrArg (fun c => interpObj I O c X)
                      (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')).symm)))))).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Iso.invHom O
                  (interpPrecompIso I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I (_L ++ [b]) X)))
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                    (mplus_snoc.{uA, uB, uI} I _L b X))))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.invHom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O
                        (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))
                    (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                      (congrArg (fun c => interpObj I O c X)
                        (mprecomp_snoc I O _L b
                          (precomp I O a.1 a.2 γ')).symm)))))).symm.trans
              ((congrArg
                  (fun t => FreeCoprodCompDisc.Hom.comp O t
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.invHom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O a.1 a.2 γ')
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.invHom O
                          (interpPrecompIso I O
                            (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                            b.1 b.2 X))
                        (FreeCoprodCompDisc.Iso.hom O
                          (FreeCoprodCompDisc.isoOfEq O
                            (congrArg (fun c => interpObj I O c X)
                              (mprecomp_snoc I O _L b
                                (precomp I O a.1 a.2 γ')).symm))))))
                  (interpPrecompIso_invHom_isoOfEq I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I (_L ++ [b]) X)
                    (mplus.{uA, uB, uI} I _L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
                    (mplus_snoc.{uA, uB, uI} I _L b X)).symm).trans
                ((FreeCoprodCompDisc.Hom.comp_assoc O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                        (congrArg
                          (fun w => interpObj I O γ'
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a w))
                          (mplus_snoc.{uA, uB, uI} I _L b X))))
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O γ' a.1 a.2
                          (mplus.{uA, uB, uI} I _L
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O a.1 a.2 γ')
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O
                          (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                          b.1 b.2 X))
                      (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                        (congrArg (fun c => interpObj I O c X)
                          (mprecomp_snoc I O _L b
                            (precomp I O a.1 a.2 γ')).symm))))).trans
                  ((congrArg
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.hom O
                          (FreeCoprodCompDisc.isoOfEq O
                            (congrArg
                              (fun w => interpObj I O γ'
                                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                  I a w))
                              (mplus_snoc.{uA, uB, uI} I _L b X)))))
                      (FreeCoprodCompDisc.Hom.comp_assoc O
                        (FreeCoprodCompDisc.Iso.invHom O
                          (interpPrecompIso I O γ' a.1 a.2
                            (mplus.{uA, uB, uI} I _L
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                I b X))))
                        (FreeCoprodCompDisc.Iso.invHom O
                          (mprecompIso.{uA, uB, uI, uO} I O _L
                            (precomp I O a.1 a.2 γ')
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                        (FreeCoprodCompDisc.Hom.comp O
                          (FreeCoprodCompDisc.Iso.invHom O
                            (interpPrecompIso I O
                              (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                              b.1 b.2 X))
                          (FreeCoprodCompDisc.Iso.hom O
                            (FreeCoprodCompDisc.isoOfEq O
                              (congrArg (fun c => interpObj I O c X)
                                (mprecomp_snoc I O _L b
                                  (precomp I O a.1 a.2 γ')).symm)))))).symm.trans
                    (FreeCoprodCompDisc.Hom.comp_assoc O
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.hom O
                          (FreeCoprodCompDisc.isoOfEq O
                            (congrArg
                              (fun w => interpObj I O γ'
                                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                  I a w))
                              (mplus_snoc.{uA, uB, uI} I _L b X))))
                        (FreeCoprodCompDisc.Hom.comp O
                          (FreeCoprodCompDisc.Iso.invHom O
                            (interpPrecompIso I O γ' a.1 a.2
                              (mplus.{uA, uB, uI} I _L
                                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                  I b X))))
                          (FreeCoprodCompDisc.Iso.invHom O
                            (mprecompIso.{uA, uB, uI, uO} I O _L
                              (precomp I O a.1 a.2 γ')
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                I b X)))))
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O
                          (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                          b.1 b.2 X))
                      (FreeCoprodCompDisc.Iso.hom O
                        (FreeCoprodCompDisc.isoOfEq O
                          (congrArg (fun c => interpObj I O c X)
                            (mprecomp_snoc I O _L b
                              (precomp I O a.1 a.2 γ')).symm))))))))))
      γ

  /-- The tower action on morphisms: the identity on every stacked
  superscript, the given morphism at the base. -/
  def mplusMorMap (L : List (SupObj.{uB, uI} I))
      (X Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h : FreeCoprodCompDisc.Hom I X Y) :
      FreeCoprodCompDisc.Hom I (mplus.{uA, uB, uI} I L X) (mplus.{uA, uB, uI} I L Y) :=
    L.rec (motive := fun L' =>
        FreeCoprodCompDisc.Hom I (mplus.{uA, uB, uI} I L' X) (mplus.{uA, uB, uI} I L' Y))
      h
      (fun b _L ih =>
        FreeCoprodCompDisc.coprodPairMor I (FreeCoprodCompDisc.Hom.id I b) ih)

  /-- The iterated Lemma 4 naturality: `IR.mprecompIso` is natural in the
  interpreted object, between the tower interpretation's morphism map and
  the direct interpretation's at the `IR.mplusMorMap` image. -/
  theorem mprecompIso_natural (L : List (SupObj.{uB, uI} I))
      (γ : IR.{max uA uB, uB, uI, uO} I O)
      (X Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h : FreeCoprodCompDisc.Hom I X Y) :
      FreeCoprodCompDisc.Hom.comp O
          (interpMor I O (mprecomp I O L γ) X Y h)
          (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ Y)) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ X))
          (interpMor I O γ (mplus.{uA, uB, uI} I L X) (mplus.{uA, uB, uI} I L Y)
            (mplusMorMap.{uA, uB, uI} I L X Y h)) :=
    L.rec (motive := fun L' => ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
        FreeCoprodCompDisc.Hom.comp O
            (interpMor I O (mprecomp I O L' γ') X Y h)
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O L' γ' Y)) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O L' γ' X))
            (interpMor I O γ' (mplus.{uA, uB, uI} I L' X)
              (mplus.{uA, uB, uI} I L' Y) (mplusMorMap.{uA, uB, uI} I L' X Y h)))
      (fun γ' =>
        (FreeCoprodCompDisc.Hom.comp_id O (interpMor I O γ' X Y h)).trans
          (FreeCoprodCompDisc.Hom.id_comp O (interpMor I O γ' X Y h)).symm)
      (fun a _L ih γ' =>
        (FreeCoprodCompDisc.Hom.comp_assoc O
            (interpMor I O (mprecomp I O _L (precomp I O a.1 a.2 γ')) X Y h)
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ') Y))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O γ' a.1 a.2
                (mplus.{uA, uB, uI} I _L Y)))).symm.trans
          ((congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O t
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O γ' a.1 a.2 (mplus.{uA, uB, uI} I _L Y))))
              (ih (precomp I O a.1 a.2 γ'))).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ') X))
                (interpMor I O (precomp I O a.1 a.2 γ') (mplus.{uA, uB, uI} I _L X)
                  (mplus.{uA, uB, uI} I _L Y) (mplusMorMap.{uA, uB, uI} I _L X Y h))
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I _L Y)))).trans
              ((congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O a.1 a.2 γ') X)))
                  (interpPrecompIso_natural I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I _L X) (mplus.{uA, uB, uI} I _L Y)
                    (mplusMorMap.{uA, uB, uI} I _L X Y h))).trans
                (FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O a.1 a.2 γ') X))
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O γ' a.1 a.2 (mplus.{uA, uB, uI} I _L X)))
                  (interpMor I O γ'
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                      (mplus.{uA, uB, uI} I _L X))
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                      (mplus.{uA, uB, uI} I _L Y))
                    (FreeCoprodCompDisc.coprodPairMor I
                      (FreeCoprodCompDisc.Hom.id I a)
                      (mplusMorMap.{uA, uB, uI} I _L X Y h)))).symm))))
      γ
  ```

  Close the file with:

  ```lean
  end IR

  end IndRec
  ```

  Each later task appends its declarations to this module and its
  entries to the module docstring's `## Main definitions` and
  `## Main statements`.

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the new files.

  Run: `scripts/lint-imports.sh`
  Expected: PASS. This task adds a module to an upstream-eligible
  subtree and registers it in two umbrellas, which is what
  CONTRIBUTING § Floodgate test gates.

- [ ] **Step 5: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent, then:

  ```bash
  jj commit -m "feat(indrec): add the category module and the semantic tower"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 4: the characterizing equations of `IR.interpHom`

`IR.interpHomEquiv` is `IR.rec` at `IR.interpHomEquivStep`, so
`IR.rec_mk` reduces it at an `IR.mk`-built domain code; specializing
that reduction at each shape gives the component of `IR.interpHom` in
cotuple form — the singleton morphism carried by the inner hom at an
`ι`-domain, the coproduct cotuple of the subcode components at a
`σ`-domain, and the `IR.deltaDesc` cotuple of the transported summand
transformations at a `δ`-domain. Every case of the inductions of
Tasks 5–8 rewrites by these equations and then discharges the goal by
cotuple uniqueness, so the two squares those cotuples travel through
are stated here as well: right-composition of the `δ`-cotuple, and
the commutation of a semantic `σ`-injection with the morphism map of
a `σ`-interpretation. `IR.innerHomEquiv_mk` is the corresponding
reduction of the inner-hom equivalence, consumed by the `ι`-cases.

The equations are also the client-facing description of
`IR.interpHom`: they state what the interpretation of a code morphism
is at each shape of domain code without reference to the recursor, so
they enter the module docstring's `## Main statements`.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean`

**Interfaces:**

- Consumes: `IR.interpHomEquiv`, `IR.interpHomEquivStep`,
  `IR.innerHomEquiv`, `IR.innerHomEquivStep`, `IR.interpHom`,
  `IR.rec_mk`, `IR.interpMor_sigma`, `IR.interpMor_id`,
  `IR.interpMor_comp`, `IR.interpPrecompIso`,
  `IR.interpPrecompIso_natural`, `IR.plusLiftBridgeNatInv`,
  `IR.deltaInto`, `IR.deltaDesc`, `IR.deltaInto_desc`,
  `IR.deltaHom_ext`, `IR.MorMapSig`,
  `FreeCoprodCompDisc.NatTrans.congrSource`,
  `FreeCoprodCompDisc.natCoprodEquiv`,
  `FreeCoprodCompDisc.natCopowerPlusEquiv`,
  `FreeCoprodCompDisc.NatTrans.vcomp`,
  `FreeCoprodCompDisc.NatTrans.ofIsoFamily`,
  `FreeCoprodCompDisc.homSingletonEquiv`,
  `FreeCoprodCompDisc.coprodDesc`, `FreeCoprodCompDisc.coprodInj`,
  `FreeCoprodCompDisc.coprodInj_mor`,
  `FreeCoprodCompDisc.emptyObj`, `FreeCoprodCompDisc.emptyDesc`.
- Produces (in `namespace IR`): `congrSource_symm_fst`,
  `interpHomEquiv_mk`, `interpHom_iota`, `interpHom_sigma`,
  `interpHomDeltaSummand`, `interpHom_delta`, `deltaDesc_comp`,
  `interpMor_sigma_inj`, `innerHomEquiv_mk`.

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean` (after
  `sampleMprecompIso_natural`):

  ```lean
  /-- The component of `IR.interpHom` at the sample `ι`-domain. -/
  theorem sampleInterpHomIota_component
      (f : InnerHom.{0, 0, 0, 0} Bool Bool true sampleCategoryCode) :
      (interpHom Bool Bool (iota Bool Bool true) sampleCategoryCode f).1
          sampleCategoryObj =
        FreeCoprodCompDisc.Hom.comp Bool
          ((FreeCoprodCompDisc.homSingletonEquiv Bool true
              (interpObj Bool Bool sampleCategoryCode
                (FreeCoprodCompDisc.emptyObj Bool))).symm
            (innerHomEquiv Bool Bool true sampleCategoryCode f))
          (interpMor Bool Bool sampleCategoryCode
            (FreeCoprodCompDisc.emptyObj Bool) sampleCategoryObj
            (FreeCoprodCompDisc.emptyDesc Bool sampleCategoryObj)) :=
    interpHom_iota Bool Bool true sampleCategoryCode f sampleCategoryObj

  /-- The `σ`-injection square at the sample object. -/
  theorem sampleInterpMorSigmaInj (A' : Type)
      (K' : A' → IR.{0, 0, 0, 0} Bool Bool) (a' : A')
      (h : FreeCoprodCompDisc.Hom Bool sampleCategoryObj sampleCategoryObj) :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.coprodInj Bool A'
            (fun a => interpObj Bool Bool (K' a) sampleCategoryObj) a')
          (interpMor Bool Bool (sigma Bool Bool A' K') sampleCategoryObj
            sampleCategoryObj h) =
        FreeCoprodCompDisc.Hom.comp Bool
          (interpMor Bool Bool (K' a') sampleCategoryObj sampleCategoryObj h)
          (FreeCoprodCompDisc.coprodInj Bool A'
            (fun a => interpObj Bool Bool (K' a) sampleCategoryObj) a') :=
    interpMor_sigma_inj Bool Bool A' K' a' sampleCategoryObj sampleCategoryObj h

  /-- The reduction of the Theorem 3 equivalence at an `ι`-shaped
  `IR.mk` domain. -/
  theorem sampleInterpHomEquiv_mk
      (d : Direction Bool Bool (Sum.inl true : Shape.{0, 0, 0} Bool) →
        IR.{0, 0, 0, 0} Bool Bool) :
      interpHomEquiv Bool Bool (mk Bool Bool (Sum.inl true) d) sampleCategoryCode =
        interpHomEquivStep Bool Bool (Sum.inl true) d
          (fun x => interpHomEquiv Bool Bool (d x)) sampleCategoryCode :=
    interpHomEquiv_mk Bool Bool (Sum.inl true) d sampleCategoryCode

  /-- The reduction of the inner-hom equivalence at an `ι`-shaped
  `IR.mk` domain. -/
  theorem sampleInnerHomEquiv_mk
      (d : Direction Bool Bool (Sum.inl true : Shape.{0, 0, 0} Bool) →
        IR.{0, 0, 0, 0} Bool Bool) :
      innerHomEquiv Bool Bool true (mk Bool Bool (Sum.inl true) d) =
        innerHomEquivStep Bool Bool true (Sum.inl true) d
          (fun x => innerHomEquiv Bool Bool true (d x)) :=
    innerHomEquiv_mk Bool Bool true (Sum.inl true) d

  /-- The component of `IR.interpHom` at a `σ`-domain, at the sample
  codomain and object. -/
  theorem sampleInterpHom_sigma (A : Type) (K : A → IR.{0, 0, 0, 0} Bool Bool)
      (f : Hom.{0, 0, 0, 0} Bool Bool (sigma Bool Bool A K) sampleCategoryCode) :
      (interpHom Bool Bool (sigma Bool Bool A K) sampleCategoryCode f).1
          sampleCategoryObj =
        FreeCoprodCompDisc.coprodDesc Bool A
          (fun a => interpObj Bool Bool (K a) sampleCategoryObj)
          (interpObj Bool Bool sampleCategoryCode sampleCategoryObj)
          (fun a => (interpHom Bool Bool (K a) sampleCategoryCode (f a)).1
            sampleCategoryObj) :=
    interpHom_sigma Bool Bool A K sampleCategoryCode f sampleCategoryObj

  /-- The component of `IR.interpHom` at a `δ`-domain, at the sample
  codomain and object. -/
  theorem sampleInterpHom_delta (B : Type)
      (c : (B → Bool) → IR.{0, 0, 0, 0} Bool Bool)
      (f : Hom.{0, 0, 0, 0} Bool Bool (delta Bool Bool B c) sampleCategoryCode) :
      (interpHom Bool Bool (delta Bool Bool B c) sampleCategoryCode f).1
          sampleCategoryObj =
        deltaDesc Bool Bool B c sampleCategoryObj
          (interpObj Bool Bool sampleCategoryCode sampleCategoryObj)
          (fun i => (interpHomDeltaSummand Bool Bool B c sampleCategoryCode i (f i)).1
            sampleCategoryObj) :=
    interpHom_delta Bool Bool B c sampleCategoryCode f sampleCategoryObj

  /-- Right-composition of the `δ`-cotuple at the sample object. -/
  theorem sampleDeltaDesc_comp (B : Type)
      (c : (B → Bool) → IR.{0, 0, 0, 0} Bool Bool)
      (Z W : FreeCoprodCompDisc.{0, 0} Bool)
      (m : (i : B → Bool) → FreeCoprodCompDisc.Hom Bool
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift Bool ⟨B, i⟩) (interpObj Bool Bool (c i))
          sampleCategoryObj) Z)
      (g : FreeCoprodCompDisc.Hom Bool Z W) :
      FreeCoprodCompDisc.Hom.comp Bool
          (deltaDesc Bool Bool B c sampleCategoryObj Z m) g =
        deltaDesc Bool Bool B c sampleCategoryObj W
          (fun i => FreeCoprodCompDisc.Hom.comp Bool (m i) g) :=
    deltaDesc_comp Bool Bool B c sampleCategoryObj Z W m g
  ```

  Extend the test file's module docstring summary with one sentence:
  "The reductions of the two equivalences at an `IR.mk`-built domain,
  the component of `IR.interpHom` at each shape of domain code, the
  `σ`-injection square, and right-composition of the `δ`-cotuple are
  exercised at the sample object."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.interpHom_iota`.

- [ ] **Step 3: Implement.** Append to
  `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`, above `end IR`,
  the characterizing equations:

  ```lean
  /-- Components pass through `NatTrans.congrSource` unchanged. -/
  theorem congrSource_symm_fst {F G : FreeCoprodCompDisc.Map.{uA, uI, uO} I O}
      {mF mF' : FreeCoprodCompDisc.MapMor I O F} (e : mF = mF')
      (mG : FreeCoprodCompDisc.MapMor I O G)
      (η : FreeCoprodCompDisc.NatTrans I O F G mF' mG) :
      ((FreeCoprodCompDisc.NatTrans.congrSource e mG).symm η).1 = η.1 :=
    Eq.rec (motive := fun mF'' e' =>
        ∀ η' : FreeCoprodCompDisc.NatTrans I O F G mF'' mG,
          ((FreeCoprodCompDisc.NatTrans.congrSource e' mG).symm η').1 = η'.1)
      (fun _ => rfl) e η

  /-- The characterizing equation of `IR.interpHomEquiv` at `IR.mk`. -/
  theorem interpHomEquiv_mk (s : Shape.{max uA uB, uB, uO} O)
      (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O)
      (γ' : IR.{max uA uB, uB, uI, uO} I O) :
      interpHomEquiv I O (mk I O s d) γ' =
        interpHomEquivStep I O s d (fun x => interpHomEquiv I O (d x)) γ' :=
    congrFun (rec_mk I O (interpHomEquivStep I O) s d) γ'

  /-- The component of `IR.interpHom` at an `ι`-domain: the singleton
  morphism carried by the inner hom, composed with the codomain's image
  of the unique morphism out of the initial object. -/
  theorem interpHom_iota (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O)
      (f : InnerHom.{uA, uB, uI, uO} I O o γ')
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      (interpHom I O (iota.{max uA uB, uB, uI, uO} I O o) γ' f).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((FreeCoprodCompDisc.homSingletonEquiv O o
              (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))).symm
            (innerHomEquiv I O o γ' f))
          (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
            (FreeCoprodCompDisc.emptyDesc I X)) :=
    congrArg (fun e => (e f).1 X)
      (interpHomEquiv_mk I O (Sum.inl o) PEmpty.elim γ')

  /-- The component of `IR.interpHom` at a `σ`-domain: the cotuple of the
  subcode components. -/
  theorem interpHom_sigma (A : Type (max uA uB))
      (K : A → IR.{max uA uB, uB, uI, uO} I O)
      (γ' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O (sigma I O A K) γ')
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      (interpHom I O (sigma I O A K) γ' f).1 X =
        FreeCoprodCompDisc.coprodDesc O A (fun a => interpObj I O (K a) X)
          (interpObj I O γ' X)
          (fun a => (interpHom I O (K a) γ' (f a)).1 X) :=
    (congrArg (fun e => (e f).1 X)
        (interpHomEquiv_mk I O (Sum.inr (Sum.inl A)) (K ∘ ULift.down) γ')).trans
      (congrFun
        (congrSource_symm_fst.{max uA uB, uI, uO} I O
          (interpMor_sigma.{max uA uB, uB, uI, uO} I O A K) _
          (FreeCoprodCompDisc.natCoprodEquiv.{max uA uB, uI, uO} A
              (fun a => interpObj I O (K a))
              (fun a => interpMor I O (K a)) (interpObj I O γ')
              (interpMor I O γ')
            |>.symm (fun a => interpHomEquiv I O (K a) γ' (f a))))
        X)

  /-- The per-summand transport of the `δ`-domain case of
  `IR.interpHomEquiv`: the interpretation of a clause 3 component,
  transported to a transformation out of the copower summand by the
  Lemma 4 pair, the bridge pair, and the copower adjunction. -/
  def interpHomDeltaSummand (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (γ' : IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
      (g : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i γ')) :
      FreeCoprodCompDisc.NatTrans I O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpObj I O (c i)))
        (interpObj I O γ')
        (FreeCoprodCompDisc.copowerHomMapMor
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpMor I O (c i)))
        (interpMor I O γ') :=
    (FreeCoprodCompDisc.natCopowerPlusEquiv
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpMor I O (c i)) (interpMor I O γ')
        (interpMor_id I O (c i)) (interpMor_comp I O (c i))
        (interpMor_id I O γ') (interpMor_comp I O γ')).symm
      (FreeCoprodCompDisc.NatTrans.vcomp
        (FreeCoprodCompDisc.NatTrans.vcomp
          (interpHom I O (c i) (precomp I O B i γ') g)
          (FreeCoprodCompDisc.NatTrans.ofIsoFamily
            (fun k => interpPrecompIso I O γ' B i k)
            (interpPrecompIso_natural I O γ' B i)))
        (plusLiftBridgeNatInv I O B i γ'))

  /-- The component of `IR.interpHom` at a `δ`-domain: the cotuple of the
  transported subcode components. -/
  theorem interpHom_delta (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (γ' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O (delta I O B c) γ')
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      (interpHom I O (delta I O B c) γ' f).1 X =
        deltaDesc I O B c X (interpObj I O γ' X)
          (fun i => (interpHomDeltaSummand I O B c γ' i (f i)).1 X) :=
    congrArg (fun e => (e f).1 X)
      (interpHomEquiv_mk I O (Sum.inr (Sum.inr B)) (c ∘ ULift.down) γ')
  ```

  then the two generic squares:

  ```lean
  /-- `IR.deltaDesc` composes on the right componentwise. -/
  theorem deltaDesc_comp (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (Z W : FreeCoprodCompDisc.{max uA uB, uO} O)
      (m : (i : B → I) → FreeCoprodCompDisc.Hom O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpObj I O (c i)) X) Z)
      (g : FreeCoprodCompDisc.Hom O Z W) :
      FreeCoprodCompDisc.Hom.comp O (deltaDesc I O B c X Z m) g =
        deltaDesc I O B c X W (fun i => FreeCoprodCompDisc.Hom.comp O (m i) g) :=
    deltaHom_ext I O B c X W _ _ (fun i =>
      ((FreeCoprodCompDisc.Hom.comp_assoc O (deltaInto I O B c i X)
          (deltaDesc I O B c X Z m) g).symm.trans
        (congrArg (fun t => FreeCoprodCompDisc.Hom.comp O t g)
          (deltaInto_desc I O B c i X Z m))).trans
      (deltaInto_desc I O B c i X W
        (fun i' => FreeCoprodCompDisc.Hom.comp O (m i') g)).symm)

  /-- The `σ`-injection square: a semantic `σ`-injection commutes the
  morphism map of a `σ`-interpretation with the summand's. -/
  theorem interpMor_sigma_inj (A' : Type (max uA uB))
      (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
      (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I Z W) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) Z) a')
          (interpMor I O (sigma I O A' K') Z W h) =
        FreeCoprodCompDisc.Hom.comp O (interpMor I O (K' a') Z W h)
          (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) W) a') :=
    (congrArg
        (fun (t : MorMapSig I O (sigma I O A' K')) =>
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) Z) a')
            (t Z W h))
        (interpMor_sigma.{max uA uB, uB, uI, uO} I O A' K')).trans
      (FreeCoprodCompDisc.coprodInj_mor O A' A' _root_.id
          (fun a => interpObj I O (K' a) Z) (fun a => interpObj I O (K' a) W)
          (fun a => interpMor I O (K' a) Z W h) a').symm
  ```

  and the inner-hom reduction:

  ```lean
  /-- The characterizing equation of `IR.innerHomEquiv` at `IR.mk`. -/
  theorem innerHomEquiv_mk (o : O) (s : Shape.{max uA uB, uB, uO} O)
      (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O) :
      innerHomEquiv I O o (mk I O s d) =
        innerHomEquivStep I O o s d (fun x => innerHomEquiv I O o (d x)) :=
    rec_mk I O (innerHomEquivStep I O o) s d
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `IR.interpHomDeltaSummand` — the per-summand transport of the
    `δ`-domain case of `IR.interpHomEquiv`.
  ```

  and to `## Main statements`:

  ```markdown
  * `IR.interpHomEquiv_mk`, `IR.innerHomEquiv_mk` — the reductions of
    the Theorem 3 equivalence and of the inner-hom equivalence at an
    `IR.mk`-built domain code.
  * `IR.interpHom_iota`, `IR.interpHom_sigma`, `IR.interpHom_delta` —
    the component of `IR.interpHom` at each shape of domain code.
  * `IR.deltaDesc_comp`, `IR.interpMor_sigma_inj` — right-composition
    of the `δ`-cotuple, and the commutation of a semantic
    `σ`-injection with the morphism map of a `σ`-interpretation.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files.

- [ ] **Step 5: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent, then:

  ```bash
  jj commit -m "feat(indrec): add the characterizing equations of interpHom"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 5: the `IR.sigmaPush` characterization

`IR.sigmaPush` injects a morphism into a `σ`-codomain at a named
summand; semantically the injection is the coproduct injection at that
summand, and the content of the branch is that `IR.interpHom` sends
one to the other. The statement is `IR.InterpHomSigmaPushMotive`,
quantified over the summand data and the interpreted object, and is
proved by `IR.induction` on the domain code, following
`IR.sigmaPush`'s own recursion.

The `ι`-case is a computation on the transported `ι`-branch
equivalence of the Theorem 3 step: `IR.interpHomIotaComposite` names
that equivalence, `IR.interpHomIotaCast` its transport along a code
equality, and `IR.interpHomIotaCast_sigmaPush` records the effect of
the push on it, over the factorization
`IR.homSingletonEquiv_symm_inj` of a singleton morphism at a
`σ`-summand name. The `σ`-case is componentwise by the inductive
hypotheses, then `FreeCoprodCompDisc.coprodDesc_comp`. The
`δ`-case pushes the injection through the Lemma 4 isomorphism
(`IR.interpPrecompIso_sigma_inj`) and the bridge, per summand
(`IR.interpHomDeltaSummand_theta`, `IR.interpHomDeltaSummand_inj`),
and then through `IR.deltaDesc_comp`.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean`

**Interfaces:**

- Consumes: Task 4's `IR.interpHomEquiv_mk`, `IR.innerHomEquiv_mk`,
  `IR.interpHom_sigma`, `IR.interpHom_delta`,
  `IR.interpHomDeltaSummand`, `IR.deltaDesc_comp`,
  `IR.interpMor_sigma_inj`; Task 2's `IR.sigmaPush_mk_iota`,
  `IR.sigmaPush_mk_sigma`, `IR.sigmaPush_mk_delta`; `IR.induction`,
  `IR.sigmaPush`, `IR.interpHom`, `IR.interpObj`, `IR.interpMor`,
  `IR.innerHomEquiv`, `IR.natIotaEquiv`, `IR.interpPrecompIso`,
  `IR.interpPrecompIso_mk`, `IR.plusLiftBridgeNatInv`,
  `IR.deltaDesc`, `FreeCoprodCompDisc.homSingletonEquiv`,
  `FreeCoprodCompDisc.coprodInj`, `FreeCoprodCompDisc.coprodDesc`,
  `FreeCoprodCompDisc.coprodDesc_comp`,
  `FreeCoprodCompDisc.coprodPairDesc`,
  `FreeCoprodCompDisc.emptyObj`, `FreeCoprodCompDisc.emptyDesc`,
  `FreeCoprodCompDisc.lift`, `FreeCoprodCompDisc.plus`.
- Produces (in `namespace IR`): `InterpHomSigmaPushMotive`,
  `interpHomIotaComposite`, `interpHomIotaCast`,
  `homSingletonEquiv_symm_inj`, `interpHomIotaCast_sigmaPush`,
  `interpHom_sigmaPush_mk_iota`, `interpHom_sigmaPush_mk_sigma`,
  `interpPrecompIso_sigma_inj`, `interpHomDeltaSummand_theta`,
  `interpHomDeltaSummand_inj`, `interpHom_sigmaPush_mk_delta`,
  `interpHom_sigmaPush`.

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean` (after
  `sampleDeltaDesc_comp`):

  ```lean
  /-- The `IR.sigmaPush` characterization at the sample code. -/
  theorem sampleSigmaPushChar :
      InterpHomSigmaPushMotive Bool Bool sampleCategoryCode :=
    interpHom_sigmaPush Bool Bool sampleCategoryCode

  /-- The `IR.sigmaPush` characterization at the sample code, applied
  at the sample object. -/
  theorem sampleSigmaPushChar_apply (A' : Type)
      (K' : A' → IR.{0, 0, 0, 0} Bool Bool) (a' : A')
      (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode (K' a')) :
      (interpHom Bool Bool sampleCategoryCode (sigma Bool Bool A' K')
          (sigmaPush Bool Bool sampleCategoryCode A' K' a' f)).1
          sampleCategoryObj =
        FreeCoprodCompDisc.Hom.comp Bool
          ((interpHom Bool Bool sampleCategoryCode (K' a') f).1
            sampleCategoryObj)
          (FreeCoprodCompDisc.coprodInj Bool A'
            (fun a => interpObj Bool Bool (K' a) sampleCategoryObj) a') :=
    interpHom_sigmaPush Bool Bool sampleCategoryCode A' K' a' f
      sampleCategoryObj
  ```

  Extend the test file's module docstring summary with one sentence:
  "The `IR.sigmaPush` characterization is exercised at the sample
  code."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.InterpHomSigmaPushMotive`.

- [ ] **Step 3: Implement.** Append to
  `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`, above `end IR`,
  the motive and the `ι`-case:

  ```lean
  /-- The statement of the `IR.sigmaPush` characterization at one code:
  `IR.interpHom` sends a pushed morphism to the composite with the
  semantic `σ`-injection. -/
  def InterpHomSigmaPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
    ∀ (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
      (a' : A') (f : Hom.{uA, uB, uI, uO} I O γ (K' a'))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I),
      (interpHom I O γ (sigma I O A' K') (sigmaPush I O γ A' K' a' f)).1 X =
        FreeCoprodCompDisc.Hom.comp O ((interpHom I O γ (K' a') f).1 X)
          (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) X) a')

  /-- The `ι`-composite of the Theorem 3 step at codomain `γ'`
  (definitionally the equivalence the step transports). -/
  def interpHomIotaComposite (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
      InnerHom.{uA, uB, uI, uO} I O o γ' ≃
        FreeCoprodCompDisc.NatTrans I O
          (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpObj I O γ')
          (interpMor I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpMor I O γ') :=
    (innerHomEquiv I O o γ').trans
      ((FreeCoprodCompDisc.homSingletonEquiv O o
          (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))).symm.trans
        (natIotaEquiv I O o γ').symm)

  /-- The transport of `IR.interpHomIotaComposite` along a code equality
  (definitionally the `ι`-branch of `IR.interpHomEquivStep`). -/
  def interpHomIotaCast (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O)
      (ir : IR.{max uA uB, uB, uI, uO} I O)
      (e : iota.{max uA uB, uB, uI, uO} I O o = ir) :
      InnerHom.{uA, uB, uI, uO} I O o γ' ≃
        FreeCoprodCompDisc.NatTrans I O (interpObj I O ir) (interpObj I O γ')
          (interpMor I O ir) (interpMor I O γ') :=
    Eq.rec (motive := fun ir' _ =>
        InnerHom.{uA, uB, uI, uO} I O o γ' ≃
          FreeCoprodCompDisc.NatTrans I O (interpObj I O ir') (interpObj I O γ')
            (interpMor I O ir') (interpMor I O γ'))
      (interpHomIotaComposite I O o γ') e

  /-- The singleton morphism at a `σ`-summand name factors through the
  semantic `σ`-injection. -/
  theorem homSingletonEquiv_symm_inj (o : O) (A' : Type (max uA uB))
      (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
      (z : {z : (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I)).1 //
        (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I)).2 z = o}) :
      (FreeCoprodCompDisc.homSingletonEquiv O o
          (interpObj I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I))).symm
          ⟨⟨a', z.1⟩, z.2⟩ =
        FreeCoprodCompDisc.Hom.comp O
          ((FreeCoprodCompDisc.homSingletonEquiv O o
              (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I))).symm z)
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a => interpObj I O (K' a) (FreeCoprodCompDisc.emptyObj I)) a') :=
    Subtype.ext (funext (fun _ => rfl))

  /-- The `σ`-push equation for the transported `ι`-composite, by
  elimination of the code equality: at the reflexive instance both sides
  compute to singleton morphisms into the initial-object fiber, related
  by `IR.homSingletonEquiv_symm_inj` and the `σ`-injection square. -/
  theorem interpHomIotaCast_sigmaPush (o : O) (A' : Type (max uA uB))
      (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
      (f : InnerHom.{uA, uB, uI, uO} I O o (K' a'))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (ir : IR.{max uA uB, uB, uI, uO} I O)
      (e : iota.{max uA uB, uB, uI, uO} I O o = ir) :
      ((interpHomIotaCast I O o (sigma I O A' K') ir e) ⟨a', f⟩).1 X =
        FreeCoprodCompDisc.Hom.comp O
          (((interpHomIotaCast I O o (K' a') ir e) f).1 X)
          (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) X) a') :=
    Eq.rec (motive := fun ir' e' =>
        ((interpHomIotaCast I O o (sigma I O A' K') ir' e') ⟨a', f⟩).1 X =
          FreeCoprodCompDisc.Hom.comp O
            (((interpHomIotaCast I O o (K' a') ir' e') f).1 X)
            (FreeCoprodCompDisc.coprodInj O A'
              (fun a => interpObj I O (K' a) X) a'))
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O
            ((FreeCoprodCompDisc.homSingletonEquiv O o
                (interpObj I O (sigma I O A' K')
                  (FreeCoprodCompDisc.emptyObj I))).symm (t ⟨a', f⟩))
            (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
              (FreeCoprodCompDisc.emptyDesc I X)))
          (innerHomEquiv_mk I O o (Sum.inr (Sum.inl A')) (K' ∘ ULift.down))).trans
        ((congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X)))
            (homSingletonEquiv_symm_inj I O o A' K' a'
              (innerHomEquiv I O o (K' a') f))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              ((FreeCoprodCompDisc.homSingletonEquiv O o
                  (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I))).symm
                (innerHomEquiv I O o (K' a') f))
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a) (FreeCoprodCompDisc.emptyObj I)) a')
              (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  ((FreeCoprodCompDisc.homSingletonEquiv O o
                      (interpObj I O (K' a')
                        (FreeCoprodCompDisc.emptyObj I))).symm
                    (innerHomEquiv I O o (K' a') f)))
                (interpMor_sigma_inj I O A' K' a'
                  (FreeCoprodCompDisc.emptyObj I) X
                  (FreeCoprodCompDisc.emptyDesc I X))).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                ((FreeCoprodCompDisc.homSingletonEquiv O o
                    (interpObj I O (K' a')
                      (FreeCoprodCompDisc.emptyObj I))).symm
                  (innerHomEquiv I O o (K' a') f))
                (interpMor I O (K' a') (FreeCoprodCompDisc.emptyObj I) X
                  (FreeCoprodCompDisc.emptyDesc I X))
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a) X) a')).symm))))
      e

  /-- The `ι`-case of the `IR.sigmaPush` characterization. -/
  theorem interpHom_sigmaPush_mk_iota (o : O)
      (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O) :
      InterpHomSigmaPushMotive I O (mk I O (Sum.inl o) d) :=
    fun A' K' a' f X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inl o) d)
            (sigma I O A' K') t).1 X)
          (sigmaPush_mk_iota I O o d A' K' a' f)).trans
        ((congrArg (fun e => (e (⟨a', f⟩ :
              InnerHom.{uA, uB, uI, uO} I O o (sigma I O A' K'))).1 X)
            (interpHomEquiv_mk I O (Sum.inl o) d (sigma I O A' K'))).trans
          ((interpHomIotaCast_sigmaPush I O o A' K' a' f X
              (mk I O (Sum.inl o) d)
              (mk_congr I O (Sum.inl o)
                (funext (fun x => nomatch x)) :
                  mk I O (Sum.inl o) PEmpty.elim = mk I O (Sum.inl o) d)).trans
            (congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O t
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a) X) a'))
              (congrArg (fun e => (e f).1 X)
                (interpHomEquiv_mk I O (Sum.inl o) d (K' a'))).symm)))
  ```

  then the `σ`-case and the Lemma 4 `σ`-square:

  ```lean
  /-- The `σ`-domain case of the `IR.sigmaPush` characterization:
  componentwise by the inductive hypotheses, then the cotuple
  compatibility. -/
  theorem interpHom_sigmaPush_mk_sigma (A : Type (max uA uB))
      (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomSigmaPushMotive I O (d x)) :
      InterpHomSigmaPushMotive I O (mk I O (Sum.inr (Sum.inl A)) d) :=
    fun A' K' a' f X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inr (Sum.inl A)) d)
            (sigma I O A' K') t).1 X)
          (sigmaPush_mk_sigma I O A d A' K' a' f)).trans
        ((interpHom_sigma I O A (fun a => d (ULift.up a)) (sigma I O A' K')
            (fun b => sigmaPush I O (d (ULift.up b)) A' K' a' (f b)) X).trans
          ((congrArg
              (FreeCoprodCompDisc.coprodDesc O A
                (fun a => interpObj I O (d (ULift.up a)) X)
                (interpObj I O (sigma I O A' K') X))
              (funext (fun b => ih (ULift.up b) A' K' a' (f b) X))).trans
            ((FreeCoprodCompDisc.coprodDesc_comp O A
                (fun a => interpObj I O (d (ULift.up a)) X)
                (interpObj I O (K' a') X) (interpObj I O (sigma I O A' K') X)
                (fun b => (interpHom I O (d (ULift.up b)) (K' a') (f b)).1 X)
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a) X) a')).symm.trans
              (congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O t
                  (FreeCoprodCompDisc.coprodInj O A'
                    (fun a => interpObj I O (K' a) X) a'))
                (interpHom_sigma I O A (fun a => d (ULift.up a))
                  (K' a') f X).symm))))

  /-- The Lemma 4 `σ`-square: the isomorphism of `IR.interpPrecompIso`
  at a `σ`-code commutes the lifted-summand injection with the direct
  summand injection. -/
  theorem interpPrecompIso_sigma_inj (A' : Type (max uA uB))
      (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
      (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
            (fun x => interpObj I O (precomp I O Q q (K' x.down)) k)
            (ULift.up a'))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (sigma I O A' K') Q q k)) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (K' a') Q q k))
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a => interpObj I O (K' a)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) a') :=
    (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
            (fun x => interpObj I O (precomp I O Q q (K' x.down)) k)
            (ULift.up a'))
          (FreeCoprodCompDisc.Iso.hom O (t Q q k)))
        (interpPrecompIso_mk I O (Sum.inr (Sum.inl A')) (K' ∘ ULift.down))).trans
      (Subtype.ext (funext (fun _ => rfl)))
  ```

  then the `δ`-case and the induction:

  ```lean
  /-- The transported-composite equation behind the `δ`-domain case: a
  `σ`-injection pushed through the Lemma 4 isomorphism and the bridge
  factors out of the transported composite. -/
  theorem interpHomDeltaSummand_theta (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
      (a' : A') (i : B → I)
      (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (sigma I O A' K')))
      (v : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (K' a')))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (hu : (interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
          (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
            (fun x => interpObj I O (precomp I O B i (K' x.down)) X)
            (ULift.up a'))) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (sigma I O A' K') B i X)))
          ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K' a') B i X)))
            ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a => interpObj I O (K' a)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
            a') :=
    (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (sigma I O A' K') B i X)))
          ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X))
        hu).trans
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O t
            ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X))
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
                (fun x => interpObj I O (precomp I O B i (K' x.down)) X)
                (ULift.up a'))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (sigma I O A' K') B i X))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X))
                (interpPrecompIso_sigma_inj I O A' K' a' B i X)).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (K' a') B i X))
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                  a')).symm))).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K' a') B i X)))
            (FreeCoprodCompDisc.coprodInj O A'
              (fun a => interpObj I O (K' a)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)) a')
            ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X)).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (K' a') B i X))))
              (interpMor_sigma_inj I O A' K' a'
                (FreeCoprodCompDisc.plus I ⟨B, i⟩ X)
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                (plusLiftBridgeInvHom I B i X))).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (K' a') B i X)))
              ((plusLiftBridgeNatInv I O B i (K' a')).1 X)
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a)
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
                a')).symm)))

  /-- The per-summand transport of a `σ`-injection through the `δ`-case
  target transports, given the summand's own push equation. -/
  theorem interpHomDeltaSummand_inj (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
      (a' : A') (i : B → I)
      (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (sigma I O A' K')))
      (v : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (K' a')))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (hu : (interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
          (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
            (fun x => interpObj I O (precomp I O B i (K' x.down)) X)
            (ULift.up a'))) :
      (interpHomDeltaSummand I O B c (sigma I O A' K') i u).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHomDeltaSummand I O B c (K' a') i v).1 X)
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a => interpObj I O (K' a) X) a') :=
    (congrArg
        (FreeCoprodCompDisc.coprodDesc O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          (fun _ => interpObj I O (c i) X)
          (interpObj I O (sigma I O A' K') X))
        (funext (fun e =>
          (congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O t
                (interpMor I O (sigma I O A' K')
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X))))
              (interpHomDeltaSummand_theta I O B c A' K' a' i u v X hu)).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K' a') B i X)))
                  ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a)
                    (FreeCoprodCompDisc.plus I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
                  a')
                (interpMor I O (sigma I O A' K')
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X)))).trans
              ((congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Hom.comp O
                        ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                        (FreeCoprodCompDisc.Iso.hom O
                          (interpPrecompIso I O (K' a') B i X)))
                      ((plusLiftBridgeNatInv I O B i (K' a')).1 X)))
                  (interpMor_sigma_inj I O A' K' a'
                    (FreeCoprodCompDisc.plus I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                    X
                    (FreeCoprodCompDisc.coprodPairDesc I e
                      (FreeCoprodCompDisc.Hom.id I X)))).trans
                (FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K' a') B i X)))
                    ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
                  (interpMor I O (K' a')
                    (FreeCoprodCompDisc.plus I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                    X
                    (FreeCoprodCompDisc.coprodPairDesc I e
                      (FreeCoprodCompDisc.Hom.id I X)))
                  (FreeCoprodCompDisc.coprodInj O A'
                    (fun a => interpObj I O (K' a) X) a')).symm))))).trans
      (FreeCoprodCompDisc.coprodDesc_comp O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          (fun _ => interpObj I O (c i) X) (interpObj I O (K' a') X)
          (interpObj I O (sigma I O A' K') X)
          (fun e => FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (K' a') B i X)))
              ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
            (interpMor I O (K' a')
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) X
              (FreeCoprodCompDisc.coprodPairDesc I e
                (FreeCoprodCompDisc.Hom.id I X))))
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a => interpObj I O (K' a) X) a')).symm

  /-- The `δ`-domain case of the `IR.sigmaPush` characterization. -/
  theorem interpHom_sigmaPush_mk_delta (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomSigmaPushMotive I O (d x)) :
      InterpHomSigmaPushMotive I O (mk I O (Sum.inr (Sum.inr B)) d) :=
    fun A' K' a' f X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inr (Sum.inr B)) d)
            (sigma I O A' K') t).1 X)
          (sigmaPush_mk_delta I O B d A' K' a' f)).trans
        ((interpHom_delta I O B (fun j => d (ULift.up j)) (sigma I O A' K')
            (fun i => sigmaPush I O (d (ULift.up i)) (ULift.{uB} A')
              (fun x => precomp I O B i (K' x.down)) (ULift.up a') (f i)) X).trans
          ((congrArg
              (deltaDesc I O B (fun j => d (ULift.up j)) X
                (interpObj I O (sigma I O A' K') X))
              (funext (fun i =>
                interpHomDeltaSummand_inj I O B (fun j => d (ULift.up j))
                  A' K' a' i
                  (sigmaPush I O (d (ULift.up i)) (ULift.{uB} A')
                    (fun x => precomp I O B i (K' x.down)) (ULift.up a') (f i))
                  (f i) X
                  (ih (ULift.up i) (ULift.{uB} A')
                    (fun x => precomp I O B i (K' x.down)) (ULift.up a')
                    (f i) X)))).trans
            ((deltaDesc_comp I O B (fun j => d (ULift.up j)) X
                (interpObj I O (K' a') X) (interpObj I O (sigma I O A' K') X)
                (fun i => (interpHomDeltaSummand I O B (fun j => d (ULift.up j))
                  (K' a') i (f i)).1 X)
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a) X) a')).symm.trans
              (congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O t
                  (FreeCoprodCompDisc.coprodInj O A'
                    (fun a => interpObj I O (K' a) X) a'))
                (interpHom_delta I O B (fun j => d (ULift.up j))
                  (K' a') f X).symm))))

  /-- `IR.interpHom` sends `IR.sigmaPush` to composition with the
  semantic `σ`-injection, by `IR.induction`. -/
  theorem interpHom_sigmaPush (γ : IR.{max uA uB, uB, uI, uO} I O) :
      InterpHomSigmaPushMotive I O γ :=
    induction I O (InterpHomSigmaPushMotive I O)
      (fun s => match s with
        | Sum.inl o => fun d _ => interpHom_sigmaPush_mk_iota I O o d
        | Sum.inr (Sum.inl A) => fun d ih => interpHom_sigmaPush_mk_sigma I O A d ih
        | Sum.inr (Sum.inr B) => fun d ih => interpHom_sigmaPush_mk_delta I O B d ih)
      γ
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `IR.InterpHomSigmaPushMotive` — the statement of the
    `IR.sigmaPush` characterization at one code.
  * `IR.interpHomIotaComposite`, `IR.interpHomIotaCast` — the
    `ι`-branch equivalence of the Theorem 3 step and its transport
    along a code equality.
  ```

  and to `## Main statements`:

  ```markdown
  * `IR.interpHom_sigmaPush` — `IR.interpHom` sends `IR.sigmaPush` to
    composition with the semantic `σ`-injection.
  * `IR.interpPrecompIso_sigma_inj` — the Lemma 4 `σ`-square.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files.

- [ ] **Step 5: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent, then:

  ```bash
  jj commit -m "feat(indrec): characterize the interpretation of the sigma-push"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 6: the `IR.deltaEmptyPush` characterization

`IR.deltaEmptyPush` injects a morphism into a `δ`-codomain at the
direction assignment forced by an empty name family; semantically the
injection is `IR.deltaEmptyInj`, the copower injection at the
canonical weight `IR.deltaEmptyWeight` followed by the summand
inclusion `IR.deltaInto`. The statement is
`IR.InterpHomDeltaEmptyPushMotive`, proved by `IR.induction` on the
domain code, following `IR.deltaEmptyPush`'s own recursion.

Every weight out of the lift of an empty-witnessed family equals the
canonical one (`IR.emptyHom_ext`), which is what makes the inclusion
independent of the weight and lets the naturality square
`IR.interpMor_deltaEmpty_inj` and the Lemma 4 `δ`-square
`IR.interpPrecompIso_deltaEmpty_inj` be stated at it; the latter is
computed at the name level by `IR.deltaEmpty_strip` over the
transported summand isomorphism `IR.deltaEmptySummandHom`. The
`δ`-case of the induction is the `σ`-push of the previous task
composed with the empty push at the unresolved subtype, so it
consumes `IR.interpHom_sigmaPush` as well as the per-summand transports
`IR.interpHomDeltaSummand_deltaEmpty_theta` and
`IR.interpHomDeltaSummand_deltaEmptyInj`.

The named motive, step, and `IR.mk`-computation equations of
`IR.deltaEmptyPush` itself are Task 2's, in `Hom.lean`; this task
consumes them.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean`

**Interfaces:**

- Consumes: Task 5's `IR.interpHom_sigmaPush`, `IR.interpHomIotaCast`;
  Task 4's `IR.interpHomEquiv_mk`, `IR.innerHomEquiv_mk`,
  `IR.interpHom_sigma`, `IR.interpHom_delta`,
  `IR.interpHomDeltaSummand`, `IR.deltaDesc_comp`; Task 2's
  `IR.deltaEmptyPush_mk_iota`, `IR.deltaEmptyPush_mk_sigma`,
  `IR.deltaEmptyPush_mk_delta`; `IR.induction`, `IR.deltaEmptyPush`,
  `IR.sigmaPush`, `IR.interpHom`, `IR.interpObj`, `IR.interpMor`,
  `IR.deltaInto`, `IR.deltaDesc`, `IR.innerHomEquivCast`,
  `IR.interpPrecompIso`, `IR.interpPrecompIso_mk`,
  `IR.plusLiftBridgeNatInv`, `IR.precompMerge`,
  `FreeCoprodCompDisc.lift`, `FreeCoprodCompDisc.copowerHomMapMor`,
  `FreeCoprodCompDisc.coprodInj`,
  `FreeCoprodCompDisc.coprodInj_mor`,
  `FreeCoprodCompDisc.coprodDesc`,
  `FreeCoprodCompDisc.coprodDesc_comp`,
  `FreeCoprodCompDisc.coprodPairDesc`,
  `FreeCoprodCompDisc.homSingletonEquiv`,
  `FreeCoprodCompDisc.isoOfEq`, `FreeCoprodCompDisc.emptyObj`,
  `FreeCoprodCompDisc.emptyDesc`, `FreeCoprodCompDisc.plus`.
- Produces (in `namespace IR`): `emptyHom_ext`, `deltaEmptyWeight`,
  `deltaEmptyInj`, `interpMor_deltaEmpty_inj`,
  `interpObj_isoOfEq_cast`, `deltaEmptySummandHom`,
  `deltaEmpty_strip`, `interpPrecompIso_deltaEmpty_inj`,
  `InterpHomDeltaEmptyPushMotive`, `innerHomEquivCast_fst_cast`,
  `homSingletonEquiv_symm_deltaEmptyInj`,
  `interpHomIotaCast_deltaEmptyPush`,
  `interpHom_deltaEmptyPush_mk_iota`,
  `interpHom_deltaEmptyPush_mk_sigma`,
  `interpHom_deltaEmptySummand_cast`,
  `interpHomDeltaSummand_deltaEmpty_theta`,
  `interpHomDeltaSummand_deltaEmptyInj`,
  `interpHom_deltaEmptyPush_mk_delta`, `interpHom_deltaEmptyPush`.

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean` (after
  `sampleSigmaPushChar_apply`):

  ```lean
  /-- The `IR.deltaEmptyPush` characterization at the sample code. -/
  theorem sampleDeltaEmptyPushChar :
      InterpHomDeltaEmptyPushMotive Bool Bool sampleCategoryCode :=
    interpHom_deltaEmptyPush Bool Bool sampleCategoryCode

  /-- The `IR.deltaEmptyPush` characterization at the sample code,
  applied at `PEmpty` directions and the sample object. -/
  theorem sampleDeltaEmptyPushChar_apply
      (M : (PEmpty.{1} → Bool) → IR.{0, 0, 0, 0} Bool Bool)
      (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
        (M (fun x => (_root_.id x).elim))) :
      (interpHom Bool Bool sampleCategoryCode
          (delta Bool Bool PEmpty.{1} M)
          (deltaEmptyPush Bool Bool sampleCategoryCode PEmpty.{1} _root_.id
            M f)).1 sampleCategoryObj =
        FreeCoprodCompDisc.Hom.comp Bool
          ((interpHom Bool Bool sampleCategoryCode
            (M (fun x => (_root_.id x).elim)) f).1 sampleCategoryObj)
          (deltaEmptyInj Bool Bool PEmpty.{1} _root_.id M
            sampleCategoryObj) :=
    interpHom_deltaEmptyPush Bool Bool sampleCategoryCode PEmpty.{1}
      _root_.id M f sampleCategoryObj
  ```

  Extend the test file's module docstring summary with one sentence:
  "The `IR.deltaEmptyPush` characterization is exercised at the sample
  code."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant
  `IR.InterpHomDeltaEmptyPushMotive`.

- [ ] **Step 3: Implement.** Append to
  `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`, above `end IR`,
  the empty-summand inclusion and its naturality square:

  ```lean
  /-- Hom-extensionality at an empty-name domain: any two morphisms out
  of the lift of an empty-witnessed family are equal. -/
  theorem emptyHom_ext (E : Type uB) (e : E → PEmpty.{1})
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (f g : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x => (e x).elim⟩) X) :
      f = g :=
    Subtype.ext (funext (fun z => (e z.down).elim))

  /-- The canonical weight: the morphism out of the lift of an
  empty-witnessed family given by elimination at every name. -/
  def deltaEmptyWeight (E : Type uB) (e : E → PEmpty.{1})
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x => (e x).elim⟩) X :=
    ⟨fun z => (e z.down).elim, funext (fun z => (e z.down).elim)⟩

  /-- The semantic inclusion of the empty-witnessed summand into the
  `delta` interpretation: the copower injection at the canonical weight
  followed by the summand inclusion `IR.deltaInto`. -/
  def deltaEmptyInj (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom O (interpObj I O (M (fun x => (e x).elim)) X)
        (interpObj I O (delta I O E M) X) :=
    FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x => (e x).elim⟩) X)
        (fun _ => interpObj I O (M (fun x => (e x).elim)) X)
        (deltaEmptyWeight I E e X))
      (deltaInto I O E M (fun x => (e x).elim) X)

  /-- The generic injection square: the semantic empty-summand inclusion
  commutes the morphism map of the `delta` interpretation with the
  summand's. -/
  theorem interpMor_deltaEmpty_inj (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I Z W) :
      FreeCoprodCompDisc.Hom.comp O (deltaEmptyInj I O E e M Z)
          (interpMor I O (delta I O E M) Z W h) =
        FreeCoprodCompDisc.Hom.comp O
          (interpMor I O (M (fun x => (e x).elim)) Z W h)
          (deltaEmptyInj I O E e M W) :=
    (FreeCoprodCompDisc.Hom.comp_assoc O
        (FreeCoprodCompDisc.coprodInj O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x => (e x).elim⟩) Z)
          (fun _ => interpObj I O (M (fun x => (e x).elim)) Z)
          (deltaEmptyWeight I E e Z))
        (deltaInto I O E M (fun x => (e x).elim) Z)
        (interpMor I O (delta I O E M) Z W h)).trans
      ((congrArg
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                  ⟨E, fun x => (e x).elim⟩) Z)
              (fun _ => interpObj I O (M (fun x => (e x).elim)) Z)
              (deltaEmptyWeight I E e Z)))
          (deltaInto_natural I O E M (fun x => (e x).elim) Z W h).symm).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                  ⟨E, fun x => (e x).elim⟩) Z)
              (fun _ => interpObj I O (M (fun x => (e x).elim)) Z)
              (deltaEmptyWeight I E e Z))
            (FreeCoprodCompDisc.copowerHomMapMor
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨E, fun x => (e x).elim⟩)
              (interpMor I O (M (fun x => (e x).elim))) Z W h)
            (deltaInto I O E M (fun x => (e x).elim) W)).symm.trans
          ((congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O t
                (deltaInto I O E M (fun x => (e x).elim) W))
              (FreeCoprodCompDisc.coprodInj_mor O
                (FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                    ⟨E, fun x => (e x).elim⟩) Z)
                (FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                    ⟨E, fun x => (e x).elim⟩) W)
                (fun e' => FreeCoprodCompDisc.Hom.comp I e' h)
                (fun _ => interpObj I O (M (fun x => (e x).elim)) Z)
                (fun _ => interpObj I O (M (fun x => (e x).elim)) W)
                (fun _ => interpMor I O (M (fun x => (e x).elim)) Z W h)
                (deltaEmptyWeight I E e Z))).trans
            ((congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (interpMor I O (M (fun x => (e x).elim)) Z W h)
                    (FreeCoprodCompDisc.coprodInj O
                      (FreeCoprodCompDisc.Hom I
                        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                          ⟨E, fun x => (e x).elim⟩) W)
                      (fun _ => interpObj I O (M (fun x => (e x).elim)) W) t))
                  (deltaInto I O E M (fun x => (e x).elim) W))
                (emptyHom_ext I E e W
                  (FreeCoprodCompDisc.Hom.comp I (deltaEmptyWeight I E e Z) h)
                  (deltaEmptyWeight I E e W))).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                (interpMor I O (M (fun x => (e x).elim)) Z W h)
                (FreeCoprodCompDisc.coprodInj O
                  (FreeCoprodCompDisc.Hom I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                      ⟨E, fun x => (e x).elim⟩) W)
                  (fun _ => interpObj I O (M (fun x => (e x).elim)) W)
                  (deltaEmptyWeight I E e W))
                (deltaInto I O E M (fun x => (e x).elim) W))))))
  ```

  then the Lemma 4 `δ`-square at the inclusion and the induction:

  ```lean
  /-- Transport of a summand interpretation along an equality of
  assignments: the object-level `isoOfEq` agrees with the name-level
  cast, for any proofs of the assignment equality. -/
  theorem interpObj_isoOfEq_cast (E : Type uB)
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) (a : E → I) :
      ∀ (c : E → I) (s : a = c) (s' : a = c)
        (y : (interpObj I O (M a) X).1),
        (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m => interpObj I O (M m) X) s)).1 y =
          cast (congrArg (fun m => (interpObj I O (M m) X).1) s') y :=
    fun _ s =>
      Eq.rec (motive := fun c' s'' => ∀ (s' : a = c')
          (y : (interpObj I O (M a) X).1),
          (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun m => interpObj I O (M m) X) s'')).1 y =
            cast (congrArg (fun m => (interpObj I O (M m) X).1) s') y)
        (fun _ _ => rfl) s

  /-- The transported summand isomorphism of the Lemma 4 `δ`-square at
  the empty inclusion: the summand's Lemma 4 isomorphism followed by the
  transport along the collapse of the merged assignment. -/
  def deltaEmptySummandHom (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom O
        (interpObj I O
          (precomp I O Q q (M (precompMerge I Q q (fun x => (e x).elim)
            (fun z : {z : E // (fun x => (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
                Sum.inr PUnit.unit} =>
              (((e z.1).elim : PEmpty.{1}).elim : I))))) k)
        (interpObj I O (M (fun x => (e x).elim))
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) :=
    FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIso I O
          (M (precompMerge I Q q (fun x => (e x).elim)
            (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k))
      (FreeCoprodCompDisc.Iso.hom O
        (FreeCoprodCompDisc.isoOfEq O
          (congrArg
            (fun a => interpObj I O (M a)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
            (funext (fun x => (e x).elim) :
              (fun x => ((e x).elim : I)) =
                precompMerge I Q q (fun x => (e x).elim)
                  (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))).symm)))

  /-- The name-level computation of the Lemma 4 `δ`-square at the empty
  inclusion, with every empty-derived assignment equality generalized:
  both routes transport the summand's Lemma 4 image along propositionally
  equal paths, identified by proof irrelevance at the base. -/
  theorem deltaEmpty_strip (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
      ∀ (j' : {z : E // (fun x => (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
          Sum.inr PUnit.unit} → I)
        (hj : (fun z : {z : E // (fun x => (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
            Sum.inr PUnit.unit} => (((e z.1).elim : PEmpty.{1}).elim : I)) = j')
        (w₁ : E → Q ⊕ k.1)
        (s₁ : precompMerge I Q q (fun x => (e x).elim) j' = Sum.elim q k.2 ∘ w₁)
        (w₂ : E → Q ⊕ k.1) (_hw : w₁ = w₂)
        (b₂ : E → I)
        (r₂ : precompMerge I Q q (fun x => (e x).elim)
            (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)) = b₂)
        (s₂ : b₂ = Sum.elim q k.2 ∘ w₂)
        (n : (interpObj I O (precomp I O Q q (M (precompMerge I Q q
          (fun x => (e x).elim)
          (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) k).1),
        (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m => interpObj I O (M m)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O
                (M (precompMerge I Q q (fun x => (e x).elim) j')) Q q k)).1
              (cast (congrArg (fun t => (interpObj I O (precomp I O Q q
                (M (precompMerge I Q q (fun x => (e x).elim) t))) k).1) hj) n))⟩ :
          (interpObj I O (delta I O E M)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
        ⟨w₂, cast (congrArg (fun m => (interpObj I O (M m)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
          ((FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m => interpObj I O (M m)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) r₂)).1
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (M (precompMerge I Q q (fun x => (e x).elim)
                (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k)).1 n))⟩ :=
    fun _ hj =>
      Eq.rec (motive := fun j'' hj' => ∀ (w₁ : E → Q ⊕ k.1)
          (s₁ : precompMerge I Q q (fun x => (e x).elim) j'' = Sum.elim q k.2 ∘ w₁)
          (w₂ : E → Q ⊕ k.1) (_hw : w₁ = w₂) (b₂ : E → I)
          (r₂ : precompMerge I Q q (fun x => (e x).elim)
              (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)) = b₂)
          (s₂ : b₂ = Sum.elim q k.2 ∘ w₂)
          (n : (interpObj I O (precomp I O Q q (M (precompMerge I Q q
            (fun x => (e x).elim)
            (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) k).1),
          (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun m => interpObj I O (M m)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
              ((FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O
                  (M (precompMerge I Q q (fun x => (e x).elim) j'')) Q q k)).1
                (cast (congrArg (fun t => (interpObj I O (precomp I O Q q
                  (M (precompMerge I Q q (fun x => (e x).elim) t))) k).1) hj') n))⟩ :
            (interpObj I O (delta I O E M)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
          ⟨w₂, cast (congrArg (fun m => (interpObj I O (M m)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
            ((FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun m => interpObj I O (M m)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) r₂)).1
              ((FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (M (precompMerge I Q q (fun x => (e x).elim)
                  (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k)).1
                n))⟩)
        (fun w₁ s₁ _ hw =>
          Eq.rec (motive := fun w₂' _ => ∀ (b₂ : E → I)
              (r₂ : precompMerge I Q q (fun x => (e x).elim)
                  (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)) = b₂)
              (s₂ : b₂ = Sum.elim q k.2 ∘ w₂')
              (n : (interpObj I O (precomp I O Q q (M (precompMerge I Q q
                (fun x => (e x).elim)
                (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) k).1),
              (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun m => interpObj I O (M m)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
                  ((FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (M (precompMerge I Q q
                      (fun x => (e x).elim)
                      (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k)).1
                    n)⟩ :
                (interpObj I O (delta I O E M)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
              ⟨w₂', cast (congrArg (fun m => (interpObj I O (M m)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
                ((FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun m => interpObj I O (M m)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) r₂)).1
                  ((FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (M (precompMerge I Q q
                      (fun x => (e x).elim)
                      (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))) Q q k)).1
                    n))⟩)
            (fun _ r₂ =>
              Eq.rec (motive := fun b₂' r₂' => ∀ (s₂ : b₂' = Sum.elim q k.2 ∘ w₁)
                  (n : (interpObj I O (precomp I O Q q (M (precompMerge I Q q
                    (fun x => (e x).elim)
                    (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) k).1),
                  (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
                      (congrArg (fun m => interpObj I O (M m)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                        s₁)).1
                      ((FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (M (precompMerge I Q q
                          (fun x => (e x).elim)
                          (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))
                          Q q k)).1 n)⟩ :
                    (interpObj I O (delta I O E M)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
                  ⟨w₁, cast (congrArg (fun m => (interpObj I O (M m)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1)
                      s₂)
                    ((FreeCoprodCompDisc.isoOfEq O
                      (congrArg (fun m => interpObj I O (M m)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                        r₂')).1
                      ((FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (M (precompMerge I Q q
                          (fun x => (e x).elim)
                          (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))
                          Q q k)).1 n))⟩)
                (fun s₂ n =>
                  congrArg
                    (fun t => (⟨w₁, t⟩ :
                      (interpObj I O (delta I O E M)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                          ⟨Q, q⟩ k)).1))
                    (interpObj_isoOfEq_cast I O E M
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)
                      (precompMerge I Q q (fun x => (e x).elim)
                        (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))
                      (Sum.elim q k.2 ∘ w₁) s₁ s₂
                      ((FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (M (precompMerge I Q q
                          (fun x => (e x).elim)
                          (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))
                          Q q k)).1 n)))
                r₂)
            hw)
        hj

  /-- The Lemma 4 `δ`-square at the empty inclusion: the syntactic
  injection at the precomposed level, pushed through the Lemma 4
  isomorphism, is the transported summand isomorphism followed by the
  semantic empty-summand inclusion at the coproduct object. -/
  theorem interpPrecompIso_deltaEmpty_inj (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (deltaEmptyInj I O
              {z : E // (fun x => (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
                Sum.inr PUnit.unit}
              (fun z => (e z.1).elim)
              (fun j => precomp I O Q q
                (M (precompMerge I Q q (fun x => (e x).elim) j)))
              k)
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (E → Q ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp I O Q q
                    (M (precompMerge I Q q cl.down j)))) k)
              (ULift.up (fun x => (e x).elim))))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (delta I O E M) Q q k)) =
        FreeCoprodCompDisc.Hom.comp O (deltaEmptySummandHom I O E e M Q q k)
          (deltaEmptyInj I O E e M
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) :=
    (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (deltaEmptyInj I O
              {z : E // (fun x => (e x).elim : E → Q ⊕ PUnit.{uB + 1}) z =
                Sum.inr PUnit.unit}
              (fun z => (e z.1).elim)
              (fun j => precomp I O Q q
                (M (precompMerge I Q q (fun x => (e x).elim) j)))
              k)
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (E → Q ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp I O Q q
                    (M (precompMerge I Q q cl.down j)))) k)
              (ULift.up (fun x => (e x).elim))))
          (FreeCoprodCompDisc.Iso.hom O (t Q q k)))
        (interpPrecompIso_mk I O (Sum.inr (Sum.inr E)) (M ∘ ULift.down))).trans
      (Subtype.ext (funext (fun n =>
        deltaEmpty_strip I O E e M Q q k
          (fun z => k.2 (((e z.1).elim : PEmpty.{1}).elim))
          (funext (fun z => (e z.1).elim))
          (arrowSumMerge (fun x => (e x).elim)
            (fun z => (((e z.1).elim : PEmpty.{1}).elim : k.1)))
          (precompMerge_elim I Q q k E (fun x => (e x).elim)
            (fun z => (((e z.1).elim : PEmpty.{1}).elim : k.1)))
          (fun x => ((e x).elim : Q ⊕ k.1))
          (funext (fun x => (e x).elim))
          (fun x => ((e x).elim : I))
          (funext (fun x => (e x).elim)).symm
          (funext (fun x => (e x).elim))
          n)))

  /-- The statement of the `IR.deltaEmptyPush` characterization at one
  code: `IR.interpHom` sends a pushed morphism to the composite with the
  semantic empty-summand inclusion. -/
  def InterpHomDeltaEmptyPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
    ∀ (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O γ (M (fun x => (e x).elim)))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I),
      (interpHom I O γ (delta I O E M) (deltaEmptyPush I O γ E e M f)).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O γ (M (fun x => (e x).elim)) f).1 X)
          (deltaEmptyInj I O E e M X)

  /-- The name component of `IR.innerHomEquivCast` at an empty-witnessed
  direction, as a cast of the untransported name, for any proofs of the
  assignment equality. -/
  theorem innerHomEquivCast_fst_cast (o : O) (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O) :
      ∀ (j : E → I) (pf : (fun b => ((e b).elim : I)) = j)
        (h' : (fun b => ((e b).elim : I)) = j)
        (f : InnerHom.{uA, uB, uI, uO} I O o (M (fun b => (e b).elim))),
        ((innerHomEquivCast I O o E (M ∘ ULift.down)
            (fun x => innerHomEquiv I O o ((M ∘ ULift.down) x))
            (fun b => (e b).elim) j pf) f).1 =
          cast
            (congrArg
              (fun t => (interpObj I O (M t) (FreeCoprodCompDisc.emptyObj I)).1) h')
            ((innerHomEquiv I O o (M (fun b => (e b).elim)) f).1) :=
    fun _ pf =>
      Eq.rec (motive := fun j' pf' => ∀ (h' : (fun b => ((e b).elim : I)) = j')
          (f : InnerHom.{uA, uB, uI, uO} I O o (M (fun b => (e b).elim))),
          ((innerHomEquivCast I O o E (M ∘ ULift.down)
              (fun x => innerHomEquiv I O o ((M ∘ ULift.down) x))
              (fun b => (e b).elim) j' pf') f).1 =
            cast
              (congrArg
                (fun t => (interpObj I O (M t)
                  (FreeCoprodCompDisc.emptyObj I)).1) h')
              ((innerHomEquiv I O o (M (fun b => (e b).elim)) f).1))
        (fun _ _ => rfl) pf

  /-- The singleton morphism at the empty-witnessed `δ`-name factors
  through the semantic empty-summand inclusion. -/
  theorem homSingletonEquiv_symm_deltaEmptyInj (o : O) (E : Type uB)
      (e : E → PEmpty.{1}) (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (f : InnerHom.{uA, uB, uI, uO} I O o (M (fun x => (e x).elim))) :
      (FreeCoprodCompDisc.homSingletonEquiv O o
          (interpObj I O (delta I O E M) (FreeCoprodCompDisc.emptyObj I))).symm
          (innerHomEquiv I O o (delta I O E M) ⟨e, f⟩) =
        FreeCoprodCompDisc.Hom.comp O
          ((FreeCoprodCompDisc.homSingletonEquiv O o
              (interpObj I O (M (fun x => (e x).elim))
                (FreeCoprodCompDisc.emptyObj I))).symm
            (innerHomEquiv I O o (M (fun x => (e x).elim)) f))
          (deltaEmptyInj I O E e M (FreeCoprodCompDisc.emptyObj I)) :=
    (congrArg
        (fun (t : InnerHom.{uA, uB, uI, uO} I O o (delta I O E M) ≃
            {z : (interpObj I O (delta I O E M)
                (FreeCoprodCompDisc.emptyObj I)).1 //
              (interpObj I O (delta I O E M)
                (FreeCoprodCompDisc.emptyObj I)).2 z = o}) =>
          (FreeCoprodCompDisc.homSingletonEquiv O o
            (interpObj I O (delta I O E M)
              (FreeCoprodCompDisc.emptyObj I))).symm (t ⟨e, f⟩))
        (innerHomEquiv_mk I O o (Sum.inr (Sum.inr E)) (M ∘ ULift.down))).trans
      (Subtype.ext (funext (fun _ =>
        congrArg
          (fun t => (⟨fun x => (e x).elim, t⟩ :
            (interpObj I O (delta I O E M) (FreeCoprodCompDisc.emptyObj I)).1))
          (innerHomEquivCast_fst_cast I O o E e M
            ((FreeCoprodCompDisc.emptyObj I).2 ∘ (fun b => (e b).elim))
            (funext (fun b => (e b).elim)) (funext (fun b => (e b).elim)) f))))

  /-- The empty-push equation for the transported `ι`-composite, by
  elimination of the code equality: at the reflexive instance both sides
  compute to singleton morphisms into the initial-object fiber, related
  by `IR.homSingletonEquiv_symm_deltaEmptyInj` and the injection
  square. -/
  theorem interpHomIotaCast_deltaEmptyPush (o : O) (E : Type uB)
      (e : E → PEmpty.{1}) (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (f : InnerHom.{uA, uB, uI, uO} I O o (M (fun x => (e x).elim)))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (ir : IR.{max uA uB, uB, uI, uO} I O)
      (eIr : iota.{max uA uB, uB, uI, uO} I O o = ir) :
      ((interpHomIotaCast I O o (delta I O E M) ir eIr) ⟨e, f⟩).1 X =
        FreeCoprodCompDisc.Hom.comp O
          (((interpHomIotaCast I O o (M (fun x => (e x).elim)) ir eIr) f).1 X)
          (deltaEmptyInj I O E e M X) :=
    Eq.rec (motive := fun ir' eIr' =>
        ((interpHomIotaCast I O o (delta I O E M) ir' eIr') ⟨e, f⟩).1 X =
          FreeCoprodCompDisc.Hom.comp O
            (((interpHomIotaCast I O o (M (fun x => (e x).elim)) ir' eIr') f).1 X)
            (deltaEmptyInj I O E e M X))
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O t
            (interpMor I O (delta I O E M) (FreeCoprodCompDisc.emptyObj I) X
              (FreeCoprodCompDisc.emptyDesc I X)))
          (homSingletonEquiv_symm_deltaEmptyInj I O o E e M f)).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
              ((FreeCoprodCompDisc.homSingletonEquiv O o
                  (interpObj I O (M (fun x => (e x).elim))
                    (FreeCoprodCompDisc.emptyObj I))).symm
                (innerHomEquiv I O o (M (fun x => (e x).elim)) f))
              (deltaEmptyInj I O E e M (FreeCoprodCompDisc.emptyObj I))
              (interpMor I O (delta I O E M) (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  ((FreeCoprodCompDisc.homSingletonEquiv O o
                      (interpObj I O (M (fun x => (e x).elim))
                        (FreeCoprodCompDisc.emptyObj I))).symm
                    (innerHomEquiv I O o (M (fun x => (e x).elim)) f)))
                (interpMor_deltaEmpty_inj I O E e M
                  (FreeCoprodCompDisc.emptyObj I) X
                  (FreeCoprodCompDisc.emptyDesc I X))).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                ((FreeCoprodCompDisc.homSingletonEquiv O o
                    (interpObj I O (M (fun x => (e x).elim))
                      (FreeCoprodCompDisc.emptyObj I))).symm
                  (innerHomEquiv I O o (M (fun x => (e x).elim)) f))
                (interpMor I O (M (fun x => (e x).elim))
                  (FreeCoprodCompDisc.emptyObj I) X
                  (FreeCoprodCompDisc.emptyDesc I X))
                (deltaEmptyInj I O E e M X)).symm)))
      eIr

  /-- The `ι`-case of the `IR.deltaEmptyPush` characterization. -/
  theorem interpHom_deltaEmptyPush_mk_iota (o : O)
      (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O) :
      InterpHomDeltaEmptyPushMotive I O (mk I O (Sum.inl o) d) :=
    fun E e M f X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inl o) d)
            (delta I O E M) t).1 X)
          (deltaEmptyPush_mk_iota I O o d E e M f)).trans
        ((congrArg (fun eq => (eq (⟨e, f⟩ :
              InnerHom.{uA, uB, uI, uO} I O o (delta I O E M))).1 X)
            (interpHomEquiv_mk I O (Sum.inl o) d (delta I O E M))).trans
          ((interpHomIotaCast_deltaEmptyPush I O o E e M f X
              (mk I O (Sum.inl o) d)
              (mk_congr I O (Sum.inl o)
                (funext (fun x => nomatch x)) :
                  mk I O (Sum.inl o) PEmpty.elim = mk I O (Sum.inl o) d)).trans
            (congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O t
                (deltaEmptyInj I O E e M X))
              (congrArg (fun eq => (eq f).1 X)
                (interpHomEquiv_mk I O (Sum.inl o) d
                  (M (fun x => (e x).elim)))).symm)))

  /-- The `σ`-domain case of the `IR.deltaEmptyPush` characterization:
  componentwise by the inductive hypotheses, then the cotuple
  compatibility. -/
  theorem interpHom_deltaEmptyPush_mk_sigma (A : Type (max uA uB))
      (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomDeltaEmptyPushMotive I O (d x)) :
      InterpHomDeltaEmptyPushMotive I O (mk I O (Sum.inr (Sum.inl A)) d) :=
    fun E e M f X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inr (Sum.inl A)) d)
            (delta I O E M) t).1 X)
          (deltaEmptyPush_mk_sigma I O A d E e M f)).trans
        ((interpHom_sigma I O A (fun a => d (ULift.up a)) (delta I O E M)
            (fun b => deltaEmptyPush I O (d (ULift.up b)) E e M (f b)) X).trans
          ((congrArg
              (FreeCoprodCompDisc.coprodDesc O A
                (fun a => interpObj I O (d (ULift.up a)) X)
                (interpObj I O (delta I O E M) X))
              (funext (fun b => ih (ULift.up b) E e M (f b) X))).trans
            ((FreeCoprodCompDisc.coprodDesc_comp O A
                (fun a => interpObj I O (d (ULift.up a)) X)
                (interpObj I O (M (fun x => (e x).elim)) X)
                (interpObj I O (delta I O E M) X)
                (fun b => (interpHom I O (d (ULift.up b))
                  (M (fun x => (e x).elim)) (f b)).1 X)
                (deltaEmptyInj I O E e M X)).symm.trans
              (congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O t
                  (deltaEmptyInj I O E e M X))
                (interpHom_sigma I O A (fun a => d (ULift.up a))
                  (M (fun x => (e x).elim)) f X).symm))))

  /-- Elimination of the assignment cast in the `δ`-domain step of
  `IR.deltaEmptyPush`: composing the transported morphism's
  interpretation with the transported summand isomorphism recovers the
  untransported composite. -/
  theorem interpHom_deltaEmptySummand_cast (γ : IR.{max uA uB, uB, uI, uO} I O)
      (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (q : Q → I) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      ∀ (a : E → I) (h : (fun x => ((e x).elim : I)) = a)
        (f : Hom.{uA, uB, uI, uO} I O γ
          (precomp I O Q q (M (fun x => (e x).elim)))),
        FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O γ (precomp I O Q q (M a))
              (cast (congrArg (fun a' => Hom I O γ (precomp I O Q q (M a'))) h)
                f)).1 X)
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (M a) Q q X))
              (FreeCoprodCompDisc.Iso.hom O
                (FreeCoprodCompDisc.isoOfEq O
                  (congrArg
                    (fun a' => interpObj I O (M a')
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ X))
                    h.symm)))) =
          FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O γ (precomp I O Q q (M (fun x => (e x).elim))) f).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (M (fun x => (e x).elim)) Q q X)) :=
    fun _ h =>
      Eq.rec (motive := fun a' h' => ∀ (f : Hom.{uA, uB, uI, uO} I O γ
          (precomp I O Q q (M (fun x => (e x).elim)))),
          FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O γ (precomp I O Q q (M a'))
                (cast
                  (congrArg (fun a'' => Hom I O γ (precomp I O Q q (M a''))) h')
                  f)).1 X)
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (M a') Q q X))
                (FreeCoprodCompDisc.Iso.hom O
                  (FreeCoprodCompDisc.isoOfEq O
                    (congrArg
                      (fun a'' => interpObj I O (M a'')
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ X))
                      h'.symm)))) =
            FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O γ
                (precomp I O Q q (M (fun x => (e x).elim))) f).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (M (fun x => (e x).elim)) Q q X)))
        (fun _ => rfl) h

  /-- The transported-composite equation behind the `δ`-domain case of
  the `IR.deltaEmptyPush` characterization: the composite injection
  pushed through the Lemma 4 isomorphism and the bridge factors out of
  the transported composite. -/
  theorem interpHomDeltaSummand_deltaEmpty_theta (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
      (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (delta I O E M)))
      (w : Hom.{uA, uB, uI, uO} I O (c i)
        (precomp I O B i (M (precompMerge I B i (fun x => (e x).elim)
          (fun z : {z : E // (fun x => (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit} => (((e z.1).elim : PEmpty.{1}).elim : I))))))
      (v : Hom.{uA, uB, uI, uO} I O (c i)
        (precomp I O B i (M (fun x => (e x).elim))))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (hu : (interpHom I O (c i) (precomp I O B i (delta I O E M)) u).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i)
            (precomp I O B i (M (precompMerge I B i (fun x => (e x).elim)
              (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
          (FreeCoprodCompDisc.Hom.comp O
            (deltaEmptyInj I O
              {z : E // (fun x => (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
                Sum.inr PUnit.unit}
              (fun z => (e z.1).elim)
              (fun j => precomp I O B i
                (M (precompMerge I B i (fun x => (e x).elim) j)))
              X)
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp I O B i
                    (M (precompMerge I B i cl.down j)))) X)
              (ULift.up (fun x => (e x).elim)))))
      (hv : FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i)
            (precomp I O B i (M (precompMerge I B i (fun x => (e x).elim)
              (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
          (deltaEmptySummandHom I O E e M B i X) =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i)
            (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (M (fun x => (e x).elim)) B i X))) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (c i) (precomp I O B i (delta I O E M)) u).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (delta I O E M) B i X)))
          ((plusLiftBridgeNatInv I O B i (delta I O E M)).1 X) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i)
                (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (M (fun x => (e x).elim)) B i X)))
            ((plusLiftBridgeNatInv I O B i (M (fun x => (e x).elim))).1 X))
          (deltaEmptyInj I O E e M
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)) :=
    (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (delta I O E M) B i X)))
          ((plusLiftBridgeNatInv I O B i (delta I O E M)).1 X))
        hu).trans
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O t
            ((plusLiftBridgeNatInv I O B i (delta I O E M)).1 X))
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              ((interpHom I O (c i)
                (precomp I O B i (M (precompMerge I B i (fun x => (e x).elim)
                  (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
              (FreeCoprodCompDisc.Hom.comp O
                (deltaEmptyInj I O
                  {z : E // (fun x => (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
                    Sum.inr PUnit.unit}
                  (fun z => (e z.1).elim)
                  (fun j => precomp I O B i
                    (M (precompMerge I B i (fun x => (e x).elim) j)))
                  X)
                (FreeCoprodCompDisc.coprodInj O
                  (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                  (fun cl => interpObj I O
                    (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                      (fun j => precomp I O B i
                        (M (precompMerge I B i cl.down j)))) X)
                  (ULift.up (fun x => (e x).elim))))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (delta I O E M) B i X))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (c i)
                    (precomp I O B i (M (precompMerge I B i
                      (fun x => (e x).elim)
                      (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))))
                    w).1 X))
                (interpPrecompIso_deltaEmpty_inj I O E e M B i X)).trans
              ((FreeCoprodCompDisc.Hom.comp_assoc O
                  ((interpHom I O (c i)
                    (precomp I O B i (M (precompMerge I B i
                      (fun x => (e x).elim)
                      (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))))
                    w).1 X)
                  (deltaEmptySummandHom I O E e M B i X)
                  (deltaEmptyInj I O E e M
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                      ⟨B, i⟩ X))).symm.trans
                (congrArg
                  (fun t => FreeCoprodCompDisc.Hom.comp O t
                    (deltaEmptyInj I O E e M
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)))
                  hv))))).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i)
                (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (M (fun x => (e x).elim)) B i X)))
            (deltaEmptyInj I O E e M
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
            ((plusLiftBridgeNatInv I O B i (delta I O E M)).1 X)).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (c i)
                    (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (M (fun x => (e x).elim)) B i X))))
              (interpMor_deltaEmpty_inj I O E e M
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                (plusLiftBridgeInvHom I B i X))).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i)
                  (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (M (fun x => (e x).elim)) B i X)))
              ((plusLiftBridgeNatInv I O B i (M (fun x => (e x).elim))).1 X)
              (deltaEmptyInj I O E e M
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                  X))).symm)))

  /-- The per-summand transport of the empty-summand inclusion through
  the `δ`-case target transports, given the summand's own push and cast
  equations. -/
  theorem interpHomDeltaSummand_deltaEmptyInj (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (E : Type uB) (e : E → PEmpty.{1})
      (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
      (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (delta I O E M)))
      (w : Hom.{uA, uB, uI, uO} I O (c i)
        (precomp I O B i (M (precompMerge I B i (fun x => (e x).elim)
          (fun z : {z : E // (fun x => (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit} => (((e z.1).elim : PEmpty.{1}).elim : I))))))
      (v : Hom.{uA, uB, uI, uO} I O (c i)
        (precomp I O B i (M (fun x => (e x).elim))))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (hu : (interpHom I O (c i) (precomp I O B i (delta I O E M)) u).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i)
            (precomp I O B i (M (precompMerge I B i (fun x => (e x).elim)
              (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
          (FreeCoprodCompDisc.Hom.comp O
            (deltaEmptyInj I O
              {z : E // (fun x => (e x).elim : E → B ⊕ PUnit.{uB + 1}) z =
                Sum.inr PUnit.unit}
              (fun z => (e z.1).elim)
              (fun j => precomp I O B i
                (M (precompMerge I B i (fun x => (e x).elim) j)))
              X)
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp I O B i
                    (M (precompMerge I B i cl.down j)))) X)
              (ULift.up (fun x => (e x).elim)))))
      (hv : FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i)
            (precomp I O B i (M (precompMerge I B i (fun x => (e x).elim)
              (fun z => (((e z.1).elim : PEmpty.{1}).elim : I))))) w).1 X)
          (deltaEmptySummandHom I O E e M B i X) =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i)
            (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (M (fun x => (e x).elim)) B i X))) :
      (interpHomDeltaSummand I O B c (delta I O E M) i u).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHomDeltaSummand I O B c (M (fun x => (e x).elim)) i v).1 X)
          (deltaEmptyInj I O E e M X) :=
    (congrArg
        (FreeCoprodCompDisc.coprodDesc O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          (fun _ => interpObj I O (c i) X)
          (interpObj I O (delta I O E M) X))
        (funext (fun e' =>
          (congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O t
                (interpMor I O (delta I O E M)
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e'
                    (FreeCoprodCompDisc.Hom.id I X))))
              (interpHomDeltaSummand_deltaEmpty_theta I O B c E e M i u w v X
                hu hv)).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    ((interpHom I O (c i)
                      (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (M (fun x => (e x).elim)) B i X)))
                  ((plusLiftBridgeNatInv I O B i
                    (M (fun x => (e x).elim))).1 X))
                (deltaEmptyInj I O E e M
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
                (interpMor I O (delta I O E M)
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e'
                    (FreeCoprodCompDisc.Hom.id I X)))).trans
              ((congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Hom.comp O
                        ((interpHom I O (c i)
                          (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
                        (FreeCoprodCompDisc.Iso.hom O
                          (interpPrecompIso I O (M (fun x => (e x).elim))
                            B i X)))
                      ((plusLiftBridgeNatInv I O B i
                        (M (fun x => (e x).elim))).1 X)))
                  (interpMor_deltaEmpty_inj I O E e M
                    (FreeCoprodCompDisc.plus I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                    X
                    (FreeCoprodCompDisc.coprodPairDesc I e'
                      (FreeCoprodCompDisc.Hom.id I X)))).trans
                (FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      ((interpHom I O (c i)
                        (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (M (fun x => (e x).elim)) B i X)))
                    ((plusLiftBridgeNatInv I O B i
                      (M (fun x => (e x).elim))).1 X))
                  (interpMor I O (M (fun x => (e x).elim))
                    (FreeCoprodCompDisc.plus I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                    X
                    (FreeCoprodCompDisc.coprodPairDesc I e'
                      (FreeCoprodCompDisc.Hom.id I X)))
                  (deltaEmptyInj I O E e M X)).symm))))).trans
      (FreeCoprodCompDisc.coprodDesc_comp O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          (fun _ => interpObj I O (c i) X)
          (interpObj I O (M (fun x => (e x).elim)) X)
          (interpObj I O (delta I O E M) X)
          (fun e' => FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i)
                  (precomp I O B i (M (fun x => (e x).elim))) v).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (M (fun x => (e x).elim)) B i X)))
              ((plusLiftBridgeNatInv I O B i (M (fun x => (e x).elim))).1 X))
            (interpMor I O (M (fun x => (e x).elim))
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) X
              (FreeCoprodCompDisc.coprodPairDesc I e'
                (FreeCoprodCompDisc.Hom.id I X))))
          (deltaEmptyInj I O E e M X)).symm

  /-- The `δ`-domain case of the `IR.deltaEmptyPush` characterization. -/
  theorem interpHom_deltaEmptyPush_mk_delta (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomDeltaEmptyPushMotive I O (d x)) :
      InterpHomDeltaEmptyPushMotive I O (mk I O (Sum.inr (Sum.inr B)) d) :=
    fun E e M f X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inr (Sum.inr B)) d)
            (delta I O E M) t).1 X)
          (deltaEmptyPush_mk_delta I O B d E e M f)).trans
        ((interpHom_delta I O B (fun j => d (ULift.up j)) (delta I O E M)
            (fun i => sigmaPush I O (d (ULift.up i))
              (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
              (fun cl => delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                (fun j => precomp I O B i (M (precompMerge I B i cl.down j))))
              (ULift.up (fun x => (e x).elim))
              (deltaEmptyPush I O (d (ULift.up i))
                {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                (fun z => (e z.1).elim)
                (fun j => precomp I O B i
                  (M (precompMerge I B i (fun x => (e x).elim) j)))
                (cast (congrArg
                  (fun a => Hom I O (d (ULift.up i)) (precomp I O B i (M a)))
                  (funext (fun x => (e x).elim) :
                    (fun x => (e x).elim) = precompMerge I B i
                      (fun x => (e x).elim)
                      (fun z : {z : E // (fun x => (e x).elim) z =
                          Sum.inr PUnit.unit}
                        => ((e z.1).elim : PEmpty.{1}).elim)))
                  (f i)))) X).trans
          ((congrArg
              (deltaDesc I O B (fun j => d (ULift.up j)) X
                (interpObj I O (delta I O E M) X))
              (funext (fun i =>
                interpHomDeltaSummand_deltaEmptyInj I O B
                  (fun j => d (ULift.up j)) E e M i
                  (sigmaPush I O (d (ULift.up i))
                    (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                    (fun cl => delta I O
                      {z : E // cl.down z = Sum.inr PUnit.unit}
                      (fun j => precomp I O B i
                        (M (precompMerge I B i cl.down j))))
                    (ULift.up (fun x => (e x).elim))
                    (deltaEmptyPush I O (d (ULift.up i))
                      {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                      (fun z => (e z.1).elim)
                      (fun j => precomp I O B i
                        (M (precompMerge I B i (fun x => (e x).elim) j)))
                      (cast (congrArg
                        (fun a => Hom I O (d (ULift.up i))
                          (precomp I O B i (M a)))
                        (funext (fun x => (e x).elim) :
                          (fun x => (e x).elim) = precompMerge I B i
                            (fun x => (e x).elim)
                            (fun z : {z : E // (fun x => (e x).elim) z =
                                Sum.inr PUnit.unit}
                              => ((e z.1).elim : PEmpty.{1}).elim)))
                        (f i))))
                  (cast (congrArg
                    (fun a => Hom I O (d (ULift.up i))
                      (precomp I O B i (M a)))
                    (funext (fun x => (e x).elim) :
                      (fun x => (e x).elim) = precompMerge I B i
                        (fun x => (e x).elim)
                        (fun z : {z : E // (fun x => (e x).elim) z =
                            Sum.inr PUnit.unit}
                          => ((e z.1).elim : PEmpty.{1}).elim)))
                    (f i))
                  (f i) X
                  ((interpHom_sigmaPush I O (d (ULift.up i))
                      (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                      (fun cl => delta I O
                        {z : E // cl.down z = Sum.inr PUnit.unit}
                        (fun j => precomp I O B i
                          (M (precompMerge I B i cl.down j))))
                      (ULift.up (fun x => (e x).elim))
                      (deltaEmptyPush I O (d (ULift.up i))
                        {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                        (fun z => (e z.1).elim)
                        (fun j => precomp I O B i
                          (M (precompMerge I B i (fun x => (e x).elim) j)))
                        (cast (congrArg
                          (fun a => Hom I O (d (ULift.up i))
                            (precomp I O B i (M a)))
                          (funext (fun x => (e x).elim) :
                            (fun x => (e x).elim) = precompMerge I B i
                              (fun x => (e x).elim)
                              (fun z : {z : E // (fun x => (e x).elim) z =
                                  Sum.inr PUnit.unit}
                                => ((e z.1).elim : PEmpty.{1}).elim)))
                          (f i))) X).trans
                    ((congrArg
                        (fun t => FreeCoprodCompDisc.Hom.comp O t
                          (FreeCoprodCompDisc.coprodInj O
                            (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                            (fun cl => interpObj I O
                              (delta I O
                                {z : E // cl.down z = Sum.inr PUnit.unit}
                                (fun j => precomp I O B i
                                  (M (precompMerge I B i cl.down j)))) X)
                            (ULift.up (fun x => (e x).elim))))
                        (ih (ULift.up i)
                          {z : E // (fun x => (e x).elim :
                            E → B ⊕ PUnit.{uB + 1}) z = Sum.inr PUnit.unit}
                          (fun z => (e z.1).elim)
                          (fun j => precomp I O B i
                            (M (precompMerge I B i (fun x => (e x).elim) j)))
                          (cast (congrArg
                            (fun a => Hom I O (d (ULift.up i))
                              (precomp I O B i (M a)))
                            (funext (fun x => (e x).elim) :
                              (fun x => (e x).elim) = precompMerge I B i
                                (fun x => (e x).elim)
                                (fun z : {z : E // (fun x => (e x).elim) z =
                                    Sum.inr PUnit.unit}
                                  => ((e z.1).elim : PEmpty.{1}).elim)))
                            (f i))
                          X)).trans
                      (FreeCoprodCompDisc.Hom.comp_assoc O
                        ((interpHom I O (d (ULift.up i))
                          (precomp I O B i (M (precompMerge I B i
                            (fun x => (e x).elim)
                            (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))))
                          (cast (congrArg
                            (fun a => Hom I O (d (ULift.up i))
                              (precomp I O B i (M a)))
                            (funext (fun x => (e x).elim) :
                              (fun x => (e x).elim) = precompMerge I B i
                                (fun x => (e x).elim)
                                (fun z : {z : E // (fun x => (e x).elim) z =
                                    Sum.inr PUnit.unit}
                                  => ((e z.1).elim : PEmpty.{1}).elim)))
                            (f i))).1 X)
                        (deltaEmptyInj I O
                          {z : E // (fun x => (e x).elim :
                            E → B ⊕ PUnit.{uB + 1}) z = Sum.inr PUnit.unit}
                          (fun z => (e z.1).elim)
                          (fun j => precomp I O B i
                            (M (precompMerge I B i (fun x => (e x).elim) j)))
                          X)
                        (FreeCoprodCompDisc.coprodInj O
                          (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
                          (fun cl => interpObj I O
                            (delta I O
                              {z : E // cl.down z = Sum.inr PUnit.unit}
                              (fun j => precomp I O B i
                                (M (precompMerge I B i cl.down j)))) X)
                          (ULift.up (fun x => (e x).elim))))))
                  (interpHom_deltaEmptySummand_cast I O (d (ULift.up i))
                    E e M B i X
                    (precompMerge I B i (fun x => (e x).elim)
                      (fun z => (((e z.1).elim : PEmpty.{1}).elim : I)))
                    (funext (fun x => (e x).elim))
                    (f i))))).trans
            ((deltaDesc_comp I O B (fun j => d (ULift.up j)) X
                (interpObj I O (M (fun x => (e x).elim)) X)
                (interpObj I O (delta I O E M) X)
                (fun i => (interpHomDeltaSummand I O B (fun j => d (ULift.up j))
                  (M (fun x => (e x).elim)) i (f i)).1 X)
                (deltaEmptyInj I O E e M X)).symm.trans
              (congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O t
                  (deltaEmptyInj I O E e M X))
                (interpHom_delta I O B (fun j => d (ULift.up j))
                  (M (fun x => (e x).elim)) f X).symm))))

  /-- `IR.interpHom` sends `IR.deltaEmptyPush` to composition with the
  semantic empty-summand inclusion, by `IR.induction`. -/
  theorem interpHom_deltaEmptyPush (γ : IR.{max uA uB, uB, uI, uO} I O) :
      InterpHomDeltaEmptyPushMotive I O γ :=
    induction I O (InterpHomDeltaEmptyPushMotive I O)
      (fun s => match s with
        | Sum.inl o => fun d _ => interpHom_deltaEmptyPush_mk_iota I O o d
        | Sum.inr (Sum.inl A) => fun d ih =>
            interpHom_deltaEmptyPush_mk_sigma I O A d ih
        | Sum.inr (Sum.inr B) => fun d ih =>
            interpHom_deltaEmptyPush_mk_delta I O B d ih)
      γ
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `IR.deltaEmptyWeight`, `IR.deltaEmptyInj` — the canonical weight
    out of the lift of an empty-witnessed family, and the semantic
    inclusion of the empty-witnessed summand into the `δ`
    interpretation.
  * `IR.deltaEmptySummandHom` — the transported summand isomorphism
    of the Lemma 4 `δ`-square at that inclusion.
  * `IR.InterpHomDeltaEmptyPushMotive` — the statement of the
    `IR.deltaEmptyPush` characterization at one code.
  ```

  and to `## Main statements`:

  ```markdown
  * `IR.interpHom_deltaEmptyPush` — `IR.interpHom` sends
    `IR.deltaEmptyPush` to composition with the semantic
    empty-summand inclusion.
  * `IR.emptyHom_ext` — any two morphisms out of the lift of an
    empty-witnessed family are equal.
  * `IR.interpMor_deltaEmpty_inj`,
    `IR.interpPrecompIso_deltaEmpty_inj` — the naturality square of
    the empty-summand inclusion, and the Lemma 4 `δ`-square at it.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files.

- [ ] **Step 5: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent, then:

  ```bash
  jj commit -m "feat(indrec): characterize the interpretation of the empty-delta push"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 7: the navigation characterizations

The three remaining branch-2a injection helpers move a morphism up the
stack of `IR.mprecomp`: `IR.msigmaPush` is the stack-indexed
`σ`-push, `IR.deltaNavBase` the `δ`-injection at the base of the
stack, and `IR.deltaNav` the iterated form at a right-appended
superscript. Each is characterized as composition with an explicit
semantic inclusion, conjugated by the tower isomorphism
`IR.mprecompIso` of Task 3; the conjugation is read off by
`IR.eq_comp_invHom`, which turns a factorization through the forward
component into one through the inverse.

The inclusion of the iterated case is `IR.navInj`: the copower
injection at the tower navigation weight `IR.navWeight`, followed by
`IR.deltaInto`, both at the tower coproduct. `IR.navWeight` recurses
on the stack by `List.rec` and is the graph of the factorization into
the appended superscript at the base (`IR.navWeight_snoc`,
`IR.navWeight_reindex`, over the reindexing `IR.navReindex`); the
inclusion equations `IR.navInj_nil` and `IR.navInj_cons` are the base
and step of the `List.rec` that proves `IR.interpHom_deltaNav`. The two
navigation squares of the Lemma 4 isomorphism —
`IR.interpPrecompIso_deltaNav_inj` at an all-resolved classifier and
`IR.interpPrecompIso_deltaNavAll_inj` at an all-unresolved one — are
computed at the name level by `IR.deltaNav_strip`.

The tower lemmas earlier in the same development
(`IR.mplusInj_snoc`, `IR.mprecompIso_snoc_hom`,
`IR.mprecompIso_snoc_invHom`, `IR.mplusMorMap`,
`IR.mprecompIso_natural`) are Task 3's; this task consumes them. The
prototype's `coprodPairInr'` is Task 1's generalized
`FreeCoprodCompDisc.coprodPairInr` at `.{uI, uB, max uA uB}`, and
`comp_coprodPairInr'_cast` is Task 3's `comp_coprodPairInr_cast`; both
renames are applied in the code below, with the affected lines
re-wrapped to 100 columns.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean`

**Interfaces:**

- Consumes: Task 6's `IR.deltaEmptyInj`, `IR.interpObj_isoOfEq_cast`,
  `IR.interpHom_deltaEmptyPush`; Task 5's `IR.interpHom_sigmaPush`,
  `IR.interpPrecompIso_sigma_inj`; Task 3's `IR.mplus`,
  `IR.mplus_snoc`, `IR.mplusInj`, `IR.mprecompIso`; Task 1's
  `FreeCoprodCompDisc.coprodPairInr`; `IR.msigmaPush`,
  `IR.deltaNavBase`, `IR.deltaNav`, `IR.sigmaPush`,
  `IR.deltaEmptyPush`, `IR.mprecomp`, `IR.precompMerge`,
  `IR.deltaInto`, `IR.interpHom`, `IR.interpObj`, `IR.interpMor`,
  `IR.interpPrecompIso`, `IR.interpPrecompIso_mk`,
  `FreeCoprodCompDisc.lift`, `FreeCoprodCompDisc.plus`,
  `FreeCoprodCompDisc.coprodInj`, `FreeCoprodCompDisc.isoOfEq`,
  `FreeCoprodCompDisc.Iso.hom_invHom`,
  `FreeCoprodCompDisc.Iso.invHom_hom`,
  `FreeCoprodCompDisc.Hom.id_comp`,
  `FreeCoprodCompDisc.Hom.comp_id`,
  `FreeCoprodCompDisc.Hom.comp_assoc`.
- Produces (in `namespace IR`): `eq_comp_invHom`,
  `interpHom_msigmaPush`, `interpHom_deltaNavBase`, `deltaNav_strip`,
  `interpPrecompIso_deltaNav_inj`, `navWeight`, `navWeight_snoc`,
  `navReindex`, `navWeight_reindex`,
  `interpPrecompIso_deltaNavAll_inj`, `navInj`, `navInj_nil`,
  `navInj_cons`, `interpHom_deltaNav`.

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean` (after
  `sampleDeltaEmptyPushChar_apply`):

  ```lean
  /-- Cancellation through an isomorphism at the sample universes. -/
  theorem sampleEqCompInvHom (V Y Z : FreeCoprodCompDisc.{0, 0} Bool)
      (f : FreeCoprodCompDisc.Hom Bool V Y)
      (g : FreeCoprodCompDisc.Hom Bool V Z)
      (e : FreeCoprodCompDisc.Iso Bool Y Z)
      (h : FreeCoprodCompDisc.Hom.comp Bool f
        (FreeCoprodCompDisc.Iso.hom Bool e) = g) :
      f = FreeCoprodCompDisc.Hom.comp Bool g
        (FreeCoprodCompDisc.Iso.invHom Bool e) :=
    eq_comp_invHom Bool V Y Z f g e h

  /-- The tower navigation weight at the empty stack is the graph of
  the factorization into the appended superscript. -/
  theorem sampleNavWeight_nil_apply :
      (navWeight Bool Bool (fun b => b) Bool (fun b => b) sampleCategoryObj
          []).1 (ULift.up true) =
        Sum.inl true :=
    rfl

  /-- The `IR.msigmaPush` characterization at the sample code and a
  singleton stack. -/
  theorem sampleMsigmaPushChar (A' : Type) (K' : A' → IR.{0, 0, 0, 0} Bool Bool)
      (a' : A')
      (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
        (mprecomp Bool Bool [sampleCategorySup] (K' a'))) :
      (interpHom Bool Bool sampleCategoryCode
          (mprecomp Bool Bool [sampleCategorySup] (sigma Bool Bool A' K'))
          (msigmaPush Bool Bool sampleCategoryCode A' K' a' [sampleCategorySup] f)).1
          sampleCategoryObj =
        FreeCoprodCompDisc.Hom.comp Bool
          ((interpHom Bool Bool sampleCategoryCode
            (mprecomp Bool Bool [sampleCategorySup] (K' a')) f).1 sampleCategoryObj)
          (FreeCoprodCompDisc.Hom.comp Bool
            (FreeCoprodCompDisc.Hom.comp Bool
              (FreeCoprodCompDisc.Iso.hom Bool
                (mprecompIso Bool Bool [sampleCategorySup] (K' a') sampleCategoryObj))
              (FreeCoprodCompDisc.coprodInj Bool A'
                (fun a => interpObj Bool Bool (K' a)
                  (mplus Bool [sampleCategorySup] sampleCategoryObj)) a'))
            (FreeCoprodCompDisc.Iso.invHom Bool
              (mprecompIso Bool Bool [sampleCategorySup] (sigma Bool Bool A' K')
                sampleCategoryObj))) :=
    interpHom_msigmaPush Bool Bool sampleCategoryCode A' K' a' [sampleCategorySup] f
      sampleCategoryObj

  /-- The `IR.deltaNavBase` characterization at the sample code. -/
  theorem sampleDeltaNavBaseChar (Bout : Type) (iout : Bout → Bool) (Bin : Type)
      (K : (Bin → Bool) → IR.{0, 0, 0, 0} Bool Bool) (g : Bin → Bout)
      (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
        (precomp Bool Bool Bout iout (K (iout ∘ g)))) :
      (interpHom Bool Bool sampleCategoryCode
          (precomp Bool Bool Bout iout (delta Bool Bool Bin K))
          (deltaNavBase Bool Bool sampleCategoryCode Bout iout Bin K g f)).1
          sampleCategoryObj =
        FreeCoprodCompDisc.Hom.comp Bool
          ((interpHom Bool Bool sampleCategoryCode
            (precomp Bool Bool Bout iout (K (iout ∘ g))) f).1 sampleCategoryObj)
          (FreeCoprodCompDisc.Hom.comp Bool
            (deltaEmptyInj Bool Bool
              {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{1}) z =
                Sum.inr PUnit.unit}
              (fun z => nomatch z.2)
              (fun j => precomp Bool Bool Bout iout
                (K (precompMerge Bool Bout iout (fun b => Sum.inl (g b)) j)))
              sampleCategoryObj)
            (FreeCoprodCompDisc.coprodInj Bool
              (ULift.{0} (Bin → Bout ⊕ PUnit.{1}))
              (fun cl => interpObj Bool Bool
                (delta Bool Bool {z : Bin // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp Bool Bool Bout iout
                    (K (precompMerge Bool Bout iout cl.down j)))) sampleCategoryObj)
              (ULift.up (fun b => Sum.inl (g b))))) :=
    interpHom_deltaNavBase Bool Bool sampleCategoryCode Bout iout Bin K g f
      sampleCategoryObj

  /-- The `IR.deltaNav` characterization at the sample code and a
  singleton stack. -/
  theorem sampleDeltaNavChar (Bout : Type) (iout : Bout → Bool) (Bin : Type)
      (K : (Bin → Bool) → IR.{0, 0, 0, 0} Bool Bool) (g : Bin → Bout)
      (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
        (mprecomp Bool Bool
          ([sampleCategorySup] ++ [(⟨Bout, iout⟩ : SupObj.{0, 0} Bool)])
          (K (iout ∘ g)))) :
      (interpHom Bool Bool sampleCategoryCode
          (mprecomp Bool Bool
            ([sampleCategorySup] ++ [(⟨Bout, iout⟩ : SupObj.{0, 0} Bool)])
            (delta Bool Bool Bin K))
          (deltaNav Bool Bool sampleCategoryCode Bout iout Bin K g [sampleCategorySup]
            f)).1 sampleCategoryObj =
        FreeCoprodCompDisc.Hom.comp Bool
          ((interpHom Bool Bool sampleCategoryCode
            (mprecomp Bool Bool
              ([sampleCategorySup] ++ [(⟨Bout, iout⟩ : SupObj.{0, 0} Bool)])
              (K (iout ∘ g))) f).1 sampleCategoryObj)
          (navInj Bool Bool Bout iout Bin K g [sampleCategorySup] sampleCategoryObj) :=
    interpHom_deltaNav Bool Bool sampleCategoryCode Bout iout Bin K g [sampleCategorySup]
      f sampleCategoryObj
  ```

  Extend the test file's module docstring summary with one sentence:
  "Cancellation through an isomorphism, the tower navigation weight at
  the empty stack, and the three navigation characterizations are
  exercised over the Booleans."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.eq_comp_invHom`.

- [ ] **Step 3: Implement.** Append to
  `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`, above `end IR`:

  ```lean
  /-- Cancellation through an isomorphism: a factorization through the
  forward component determines the factorization through the inverse. -/
  theorem eq_comp_invHom (V Y Z : FreeCoprodCompDisc.{uA, uO} O)
      (f : FreeCoprodCompDisc.Hom O V Y) (g : FreeCoprodCompDisc.Hom O V Z)
      (e : FreeCoprodCompDisc.Iso O Y Z)
      (h : FreeCoprodCompDisc.Hom.comp O f (FreeCoprodCompDisc.Iso.hom O e) = g) :
      f = FreeCoprodCompDisc.Hom.comp O g (FreeCoprodCompDisc.Iso.invHom O e) :=
    (FreeCoprodCompDisc.Hom.comp_id O f).symm.trans
      ((congrArg (FreeCoprodCompDisc.Hom.comp O f)
          (FreeCoprodCompDisc.Iso.hom_invHom O e).symm).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O f (FreeCoprodCompDisc.Iso.hom O e)
            (FreeCoprodCompDisc.Iso.invHom O e)).symm.trans
          (congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Iso.invHom O e))
            h)))

  /-- The `IR.msigmaPush` characterization: `IR.interpHom` sends a stack
  `σ`-push to the composite with the semantic `σ`-injection conjugated
  through the iterated Lemma 4 isomorphism. -/
  theorem interpHom_msigmaPush (D : IR.{max uA uB, uB, uI, uO} I O)
      (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
      (L : List (SupObj.{uB, uI} I))
      (f : Hom.{uA, uB, uI, uO} I O D (mprecomp I O L (K' a')))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      (interpHom I O D (mprecomp I O L (sigma I O A' K'))
          (msigmaPush I O D A' K' a' L f)).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O D (mprecomp I O L (K' a')) f).1 X)
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O L (K' a') X))
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a) (mplus.{uA, uB, uI} I L X)) a'))
            (FreeCoprodCompDisc.Iso.invHom O
              (mprecompIso.{uA, uB, uI, uO} I O L (sigma I O A' K') X))) :=
    L.rec (motive := fun L' => ∀ (A'' : Type (max uA uB))
        (K'' : A'' → IR.{max uA uB, uB, uI, uO} I O) (a'' : A'')
        (f' : Hom.{uA, uB, uI, uO} I O D (mprecomp I O L' (K'' a'')))
        (X' : FreeCoprodCompDisc.{max uA uB, uI} I),
        (interpHom I O D (mprecomp I O L' (sigma I O A'' K''))
            (msigmaPush I O D A'' K'' a'' L' f')).1 X' =
          FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O D (mprecomp I O L' (K'' a'')) f').1 X')
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O L' (K'' a'') X'))
                (FreeCoprodCompDisc.coprodInj O A''
                  (fun a => interpObj I O (K'' a) (mplus.{uA, uB, uI} I L' X'))
                  a''))
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O L' (sigma I O A'' K'') X'))))
      (fun A'' K'' a'' f' X' => interpHom_sigmaPush I O D A'' K'' a'' f' X')
      (fun b _L ih A'' K'' a'' f' X' =>
        (ih (ULift.{uB} A'') (fun x => precomp I O b.1 b.2 (K'' x.down))
            (ULift.up a'') f' X').trans
          (congrArg
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O D
                (mprecomp I O _L (precomp I O b.1 b.2 (K'' a''))) f').1 X'))
            ((congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O b.1 b.2 (K'' a'')) X'))
                    t)
                  (FreeCoprodCompDisc.Iso.invHom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O b.1 b.2 (sigma I O A'' K'')) X')))
                (eq_comp_invHom O
                  (interpObj I O (precomp I O b.1 b.2 (K'' a''))
                    (mplus.{uA, uB, uI} I _L X'))
                  (interpObj I O (precomp I O b.1 b.2 (sigma I O A'' K''))
                    (mplus.{uA, uB, uI} I _L X'))
                  (interpObj I O (sigma I O A'' K'')
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                      (mplus.{uA, uB, uI} I _L X')))
                  (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A'')
                    (fun x => interpObj I O (precomp I O b.1 b.2 (K'' x.down))
                      (mplus.{uA, uB, uI} I _L X'))
                    (ULift.up a''))
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K'' a'') b.1 b.2
                        (mplus.{uA, uB, uI} I _L X')))
                    (FreeCoprodCompDisc.coprodInj O A''
                      (fun a => interpObj I O (K'' a)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                          (mplus.{uA, uB, uI} I _L X')))
                      a''))
                  (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                    (mplus.{uA, uB, uI} I _L X'))
                  (interpPrecompIso_sigma_inj I O A'' K'' a'' b.1 b.2
                    (mplus.{uA, uB, uI} I _L X')))).trans
              ((FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O b.1 b.2 (K'' a'')) X'))
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K'' a'') b.1 b.2
                          (mplus.{uA, uB, uI} I _L X')))
                      (FreeCoprodCompDisc.coprodInj O A''
                        (fun a => interpObj I O (K'' a)
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                            (mplus.{uA, uB, uI} I _L X')))
                        a''))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                        (mplus.{uA, uB, uI} I _L X'))))
                  (FreeCoprodCompDisc.Iso.invHom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O b.1 b.2 (sigma I O A'' K'')) X'))).trans
                ((congrArg
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O b.1 b.2 (K'' a'')) X')))
                    (FreeCoprodCompDisc.Hom.comp_assoc O
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.hom O
                          (interpPrecompIso I O (K'' a'') b.1 b.2
                            (mplus.{uA, uB, uI} I _L X')))
                        (FreeCoprodCompDisc.coprodInj O A''
                          (fun a => interpObj I O (K'' a)
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                              (mplus.{uA, uB, uI} I _L X')))
                          a''))
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                          (mplus.{uA, uB, uI} I _L X')))
                      (FreeCoprodCompDisc.Iso.invHom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O b.1 b.2 (sigma I O A'' K'')) X')))).trans
                  ((FreeCoprodCompDisc.Hom.comp_assoc O
                      (FreeCoprodCompDisc.Iso.hom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O b.1 b.2 (K'' a'')) X'))
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.hom O
                          (interpPrecompIso I O (K'' a'') b.1 b.2
                            (mplus.{uA, uB, uI} I _L X')))
                        (FreeCoprodCompDisc.coprodInj O A''
                          (fun a => interpObj I O (K'' a)
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                              (mplus.{uA, uB, uI} I _L X')))
                          a''))
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.invHom O
                          (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                            (mplus.{uA, uB, uI} I _L X')))
                        (FreeCoprodCompDisc.Iso.invHom O
                          (mprecompIso.{uA, uB, uI, uO} I O _L
                            (precomp I O b.1 b.2 (sigma I O A'' K'')) X')))).symm.trans
                    (congrArg
                      (fun t => FreeCoprodCompDisc.Hom.comp O t
                        (FreeCoprodCompDisc.Hom.comp O
                          (FreeCoprodCompDisc.Iso.invHom O
                            (interpPrecompIso I O (sigma I O A'' K'') b.1 b.2
                              (mplus.{uA, uB, uI} I _L X')))
                          (FreeCoprodCompDisc.Iso.invHom O
                            (mprecompIso.{uA, uB, uI, uO} I O _L
                              (precomp I O b.1 b.2 (sigma I O A'' K'')) X'))))
                      (FreeCoprodCompDisc.Hom.comp_assoc O
                        (FreeCoprodCompDisc.Iso.hom O
                          (mprecompIso.{uA, uB, uI, uO} I O _L
                            (precomp I O b.1 b.2 (K'' a'')) X'))
                        (FreeCoprodCompDisc.Iso.hom O
                          (interpPrecompIso I O (K'' a'') b.1 b.2
                            (mplus.{uA, uB, uI} I _L X')))
                        (FreeCoprodCompDisc.coprodInj O A''
                          (fun a => interpObj I O (K'' a)
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b
                              (mplus.{uA, uB, uI} I _L X')))
                          a'')).symm)))))))
      A' K' a' f X

  /-- The `IR.deltaNavBase` characterization: `IR.interpHom` sends the
  base navigation to the composite with the empty-summand inclusion at
  the all-resolved classifier's unresolved subtype, followed by the
  semantic `σ`-injection at that classifier. -/
  theorem interpHom_deltaNavBase (D : IR.{max uA uB, uB, uI, uO} I O)
      (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
      (f : Hom.{uA, uB, uI, uO} I O D (precomp I O Bout iout (K (iout ∘ g))))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      (interpHom I O D (precomp I O Bout iout (delta I O Bin K))
          (deltaNavBase I O D Bout iout Bin K g f)).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O D (precomp I O Bout iout (K (iout ∘ g))) f).1 X)
          (FreeCoprodCompDisc.Hom.comp O
            (deltaEmptyInj I O
              {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
                Sum.inr PUnit.unit}
              (fun z => nomatch z.2)
              (fun j => precomp I O Bout iout
                (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
              X)
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp I O Bout iout
                    (K (precompMerge I Bout iout cl.down j)))) X)
              (ULift.up (fun b => Sum.inl (g b))))) :=
    (interpHom_sigmaPush I O D (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
        (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
          (fun j => precomp I O Bout iout
            (K (precompMerge I Bout iout cl.down j))))
        (ULift.up (fun b => Sum.inl (g b)))
        (deltaEmptyPush I O D
          {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
            Sum.inr PUnit.unit}
          (fun z => nomatch z.2)
          (fun j => precomp I O Bout iout
            (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
          f)
        X).trans
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp I O Bout iout
                    (K (precompMerge I Bout iout cl.down j)))) X)
              (ULift.up (fun b => Sum.inl (g b)))))
          (interpHom_deltaEmptyPush I O D
            {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z => nomatch z.2)
            (fun j => precomp I O Bout iout
              (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
            f X)).trans
        (FreeCoprodCompDisc.Hom.comp_assoc O
          ((interpHom I O D (precomp I O Bout iout (K (iout ∘ g))) f).1 X)
          (deltaEmptyInj I O
            {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z => nomatch z.2)
            (fun j => precomp I O Bout iout
              (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
            X)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
            (fun cl => interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun j => precomp I O Bout iout
                  (K (precompMerge I Bout iout cl.down j)))) X)
            (ULift.up (fun b => Sum.inl (g b))))))

  /-- The name-level computation of the Lemma 4 `δ`-square at a summand
  of a classifier's unresolved subtype, with every assignment equality
  generalized: both routes transport the summand's Lemma 4 image along
  propositionally equal paths, identified by proof irrelevance at the
  base. -/
  theorem deltaNav_strip (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I)
      (cl : Bin → Q ⊕ PUnit.{uB + 1}) :
      ∀ (j₀ j₂ : {z : Bin // cl z = Sum.inr PUnit.unit} → I) (hj : j₀ = j₂)
        (w₁ : Bin → Q ⊕ k.1)
        (s₁ : precompMerge I Q q cl j₂ = Sum.elim q k.2 ∘ w₁)
        (w₂ : Bin → Q ⊕ k.1) (_hw : w₁ = w₂)
        (b₀ : Bin → I) (r₀ : precompMerge I Q q cl j₀ = b₀)
        (s₂ : b₀ = Sum.elim q k.2 ∘ w₂)
        (n : (interpObj I O
          (precomp I O Q q (K (precompMerge I Q q cl j₀))) k).1),
        (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m => interpObj I O (K m)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K (precompMerge I Q q cl j₂)) Q q k)).1
              (cast (congrArg (fun t => (interpObj I O
                (precomp I O Q q (K (precompMerge I Q q cl t))) k).1) hj) n))⟩ :
          (interpObj I O (delta I O Bin K)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
        ⟨w₂, cast (congrArg (fun m => (interpObj I O (K m)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
          ((FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (K b₀) Q q k)).1
            (cast (congrArg (fun t => (interpObj I O
              (precomp I O Q q (K t)) k).1) r₀) n))⟩ :=
    fun j₀ _ hj =>
      Eq.rec (motive := fun j₂' hj' => ∀ (w₁ : Bin → Q ⊕ k.1)
          (s₁ : precompMerge I Q q cl j₂' = Sum.elim q k.2 ∘ w₁)
          (w₂ : Bin → Q ⊕ k.1) (_hw : w₁ = w₂)
          (b₀ : Bin → I) (r₀ : precompMerge I Q q cl j₀ = b₀)
          (s₂ : b₀ = Sum.elim q k.2 ∘ w₂)
          (n : (interpObj I O
            (precomp I O Q q (K (precompMerge I Q q cl j₀))) k).1),
          (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun m => interpObj I O (K m)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) s₁)).1
              ((FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K (precompMerge I Q q cl j₂')) Q q k)).1
                (cast (congrArg (fun t => (interpObj I O
                  (precomp I O Q q (K (precompMerge I Q q cl t))) k).1) hj')
                  n))⟩ :
            (interpObj I O (delta I O Bin K)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
          ⟨w₂, cast (congrArg (fun m => (interpObj I O (K m)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) s₂)
            ((FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K b₀) Q q k)).1
              (cast (congrArg (fun t => (interpObj I O
                (precomp I O Q q (K t)) k).1) r₀) n))⟩)
        (fun w₁ s₁ _ hw =>
          Eq.rec (motive := fun w₂' _ => ∀ (b₀ : Bin → I)
              (r₀ : precompMerge I Q q cl j₀ = b₀)
              (s₂ : b₀ = Sum.elim q k.2 ∘ w₂')
              (n : (interpObj I O
                (precomp I O Q q (K (precompMerge I Q q cl j₀))) k).1),
              (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun m => interpObj I O (K m)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                    s₁)).1
                  ((FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (K (precompMerge I Q q cl j₀))
                      Q q k)).1 n)⟩ :
                (interpObj I O (delta I O Bin K)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1) =
              ⟨w₂', cast (congrArg (fun m => (interpObj I O (K m)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1)
                  s₂)
                ((FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (K b₀) Q q k)).1
                  (cast (congrArg (fun t => (interpObj I O
                    (precomp I O Q q (K t)) k).1) r₀) n))⟩)
            (fun _ r₀ =>
              Eq.rec (motive := fun b₀' r₀' => ∀
                  (s₂ : b₀' = Sum.elim q k.2 ∘ w₁)
                  (n : (interpObj I O
                    (precomp I O Q q (K (precompMerge I Q q cl j₀))) k).1),
                  (⟨w₁, (FreeCoprodCompDisc.isoOfEq O
                      (congrArg (fun m => interpObj I O (K m)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                        s₁)).1
                      ((FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K (precompMerge I Q q cl j₀))
                          Q q k)).1 n)⟩ :
                    (interpObj I O (delta I O Bin K)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                        I ⟨Q, q⟩ k)).1) =
                  ⟨w₁, cast (congrArg (fun m => (interpObj I O (K m)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                        I ⟨Q, q⟩ k)).1) s₂)
                    ((FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K b₀') Q q k)).1
                      (cast (congrArg (fun t => (interpObj I O
                        (precomp I O Q q (K t)) k).1) r₀') n))⟩)
                (fun s₂ n =>
                  congrArg
                    (fun t => (⟨w₁, t⟩ :
                      (interpObj I O (delta I O Bin K)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                          I ⟨Q, q⟩ k)).1))
                    (interpObj_isoOfEq_cast I O Bin K
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)
                      (precompMerge I Q q cl j₀) (Sum.elim q k.2 ∘ w₁) s₁ s₂
                      ((FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K (precompMerge I Q q cl j₀))
                          Q q k)).1 n)))
                r₀)
            hw)
        hj

  /-- The all-resolved navigation square: the composite inclusion of the
  `IR.deltaNavBase` characterization, pushed through the Lemma 4
  isomorphism, is the copower injection at the graph weight of the
  factorization followed by the summand inclusion, after the summand's
  Lemma 4 isomorphism. -/
  theorem interpPrecompIso_deltaNav_inj (Bout : Type uB) (iout : Bout → I)
      (Bin : Type uB) (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O)
      (g : Bin → Bout) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (deltaEmptyInj I O
              {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
                Sum.inr PUnit.unit}
              (fun z => nomatch z.2)
              (fun j => precomp I O Bout iout
                (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
              X)
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp I O Bout iout
                    (K (precompMerge I Bout iout cl.down j)))) X)
              (ULift.up (fun b => Sum.inl (g b)))))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (delta I O Bin K) Bout iout X)) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K (iout ∘ g)) Bout iout X))
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
              (fun _ => interpObj I O (K (iout ∘ g))
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
              ⟨fun z => Sum.inl (g z.down), rfl⟩))
          (deltaInto I O Bin K (iout ∘ g)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)) :=
    (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (deltaEmptyInj I O
              {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
                Sum.inr PUnit.unit}
              (fun z => nomatch z.2)
              (fun j => precomp I O Bout iout
                (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
              X)
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                  (fun j => precomp I O Bout iout
                    (K (precompMerge I Bout iout cl.down j)))) X)
              (ULift.up (fun b => Sum.inl (g b)))))
          (FreeCoprodCompDisc.Iso.hom O (t Bout iout X)))
        (interpPrecompIso_mk I O (Sum.inr (Sum.inr Bin)) (K ∘ ULift.down))).trans
      (Subtype.ext (funext (fun n =>
        ((rfl :
          (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (deltaEmptyInj I O
                  {z : Bin //
                    (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
                      Sum.inr PUnit.unit}
                  (fun z => nomatch z.2)
                  (fun j => precomp I O Bout iout
                    (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
                  X)
                (FreeCoprodCompDisc.coprodInj O
                  (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
                  (fun cl => interpObj I O
                    (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                      (fun j => precomp I O Bout iout
                        (K (precompMerge I Bout iout cl.down j)))) X)
                  (ULift.up (fun b => Sum.inl (g b)))))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIsoStep I O (Sum.inr (Sum.inr Bin)) (K ∘ ULift.down)
                  (fun x => interpPrecompIso I O ((K ∘ ULift.down) x))
                  Bout iout X))).1 n =
            (⟨arrowSumMerge (fun b => Sum.inl (g b))
              (fun z => ((nomatch z.2 : PEmpty.{1}).elim : X.1)),
            (FreeCoprodCompDisc.isoOfEq O
              (congrArg
                (fun m => interpObj I O (K m)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
                (precompMerge_elim I Bout iout X Bin (fun b => Sum.inl (g b))
                  (fun z => ((nomatch z.2 : PEmpty.{1}).elim : X.1))))).1
              ((FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O
                  (K (precompMerge I Bout iout (fun b => Sum.inl (g b))
                    (fun z => X.2 ((nomatch z.2 : PEmpty.{1}).elim))))
                  Bout iout X)).1
                (cast
                  (congrArg
                    (fun t => (interpObj I O (precomp I O Bout iout
                      (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) t)))
                      X).1)
                    (funext (fun z => nomatch z.2) :
                      (fun x : {z : Bin //
                          (fun b => Sum.inl (g b) :
                            Bin → Bout ⊕ PUnit.{uB + 1}) z =
                            Sum.inr PUnit.unit} =>
                        ((nomatch x.2 : PEmpty.{1}).elim : I)) =
                        fun z : {z : Bin //
                          (fun b => Sum.inl (g b) :
                            Bin → Bout ⊕ PUnit.{uB + 1}) z =
                            Sum.inr PUnit.unit} =>
                          X.2 ((nomatch z.2 : PEmpty.{1}).elim)))
                  n))⟩ :
            (interpObj I O (delta I O Bin K)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)).1)).trans
          ((deltaNav_strip I O Bin K Bout iout X (fun b => Sum.inl (g b))
            (fun x => ((nomatch x.2 : PEmpty.{1}).elim : I))
            (fun z => X.2 ((nomatch z.2 : PEmpty.{1}).elim))
            (funext (fun z => nomatch z.2))
            (arrowSumMerge (fun b => Sum.inl (g b))
              (fun z => ((nomatch z.2 : PEmpty.{1}).elim : X.1)))
            (precompMerge_elim I Bout iout X Bin (fun b => Sum.inl (g b))
              (fun z => ((nomatch z.2 : PEmpty.{1}).elim : X.1)))
            (fun z => (Sum.inl (g z) : Bout ⊕ X.1))
            rfl
            (iout ∘ g)
            (funext (fun _ => rfl))
            (funext (fun _ => rfl))
            n).trans
            (rfl :
              (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (K (iout ∘ g)) Bout iout X))
                (FreeCoprodCompDisc.coprodInj O
                  (FreeCoprodCompDisc.Hom I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                      ⟨Bin, iout ∘ g⟩)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                      ⟨Bout, iout⟩ X))
                  (fun _ => interpObj I O (K (iout ∘ g))
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                      ⟨Bout, iout⟩ X))
                  ⟨fun z => Sum.inl (g z.down), rfl⟩))
              (deltaInto I O Bin K (iout ∘ g)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                  ⟨Bout, iout⟩ X))).1 n =
                (⟨fun z => Sum.inl (g z),
            cast
              (congrArg
                (fun m => (interpObj I O (K m)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                    ⟨Bout, iout⟩ X)).1)
                (funext (fun _ => rfl) :
                  iout ∘ g = Sum.elim iout X.2 ∘ fun z : Bin => Sum.inl (g z)))
              ((FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K (iout ∘ g)) Bout iout X)).1
                (cast
                  (congrArg
                    (fun t => (interpObj I O
                      (precomp I O Bout iout (K t)) X).1)
                    (funext (fun _ => rfl) :
                      precompMerge I Bout iout (fun b => Sum.inl (g b))
                          (fun x : {z : Bin //
                            (fun b => Sum.inl (g b) :
                              Bin → Bout ⊕ PUnit.{uB + 1}) z =
                                Sum.inr PUnit.unit} =>
                            ((nomatch x.2 : PEmpty.{1}).elim : I)) =
                        iout ∘ g))
                  n))⟩ :
            (interpObj I O (delta I O Bin K)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)).1)).symm)))))

  /-- The tower navigation weight: the graph of the factorization into
  the appended superscript, followed by the iterated right injection up
  the tower. By `List.rec`, so the `cons` equation is definitional. -/
  def navWeight (Bout : Type uB) (iout : Bout → I) (Bin : Type uB) (g : Bin → Bout)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) (L : List (SupObj.{uB, uI} I)) :
      FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X) :=
    L.rec (motive := fun L' : List (SupObj.{uB, uI} I) =>
        FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
          (mplus.{uA, uB, uI} I (L' ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
      ⟨fun z => Sum.inl (g z.down), rfl⟩
      (fun a _L ih =>
        FreeCoprodCompDisc.Hom.comp I ih
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
            (mplus.{uA, uB, uI} I (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))

  /-- `IR.navWeight`, transported along `IR.mplus_snoc`, is the graph
  weight at the base followed by the tower injection `IR.mplusInj`. -/
  theorem navWeight_snoc (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
      (g : Bin → Bout) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (L : List (SupObj.{uB, uI} I)) :
      cast
          (congrArg
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩))
            (mplus_snoc.{uA, uB, uI} I L (⟨Bout, iout⟩ : SupObj.{uB, uI} I) X))
          (navWeight I Bout iout Bin g X L) =
        FreeCoprodCompDisc.Hom.comp I
          (⟨fun z => Sum.inl (g z.down), rfl⟩ :
            FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
          (mplusInj.{uA, uB, uI} I L
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)) :=
    L.rec (motive := fun L' =>
        cast
            (congrArg
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩))
              (mplus_snoc.{uA, uB, uI} I L' (⟨Bout, iout⟩ : SupObj.{uB, uI} I) X))
            (navWeight I Bout iout Bin g X L') =
          FreeCoprodCompDisc.Hom.comp I
            (⟨fun z => Sum.inl (g z.down), rfl⟩ :
              FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            (mplusInj.{uA, uB, uI} I L'
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)))
      (FreeCoprodCompDisc.Hom.comp_id I
        (⟨fun z => Sum.inl (g z.down), rfl⟩ :
          FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))).symm
      (fun a _L ih =>
        (comp_coprodPairInr_cast I a
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
            (mplus.{uA, uB, uI} I (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)
            (mplus.{uA, uB, uI} I _L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            (mplus_snoc.{uA, uB, uI} I _L (⟨Bout, iout⟩ : SupObj.{uB, uI} I) X)
            (navWeight I Bout iout Bin g X _L)).trans
          ((congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp I t
                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                  (mplus.{uA, uB, uI} I _L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                      ⟨Bout, iout⟩ X))))
              ih).trans
            (FreeCoprodCompDisc.Hom.comp_assoc I
              (⟨fun z => Sum.inl (g z.down), rfl⟩ :
                FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
              (mplusInj.{uA, uB, uI} I _L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                (mplus.{uA, uB, uI} I _L
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                    ⟨Bout, iout⟩ X))))))

  /-- The reindexing of a lifted direction family along the inclusion of
  the all-unresolved classifier's subtype (all of the arity). -/
  def navReindex (Bin : Type uB) (j : Bin → I) (Q : Type uB) :
      FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, j⟩)
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
          ⟨{z : Bin //
              (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z =
                Sum.inr PUnit.unit},
            fun z => j z.1⟩) :=
    ⟨fun z => ULift.up ⟨z.down, rfl⟩, rfl⟩

  /-- `IR.navWeight` at the all-unresolved classifier's subtype,
  restricted along `IR.navReindex`, is `IR.navWeight` at the base
  arity. -/
  theorem navWeight_reindex (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
      (g : Bin → Bout) (Q : Type uB) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (L : List (SupObj.{uB, uI} I)) :
      FreeCoprodCompDisc.Hom.comp I (navReindex.{uA, uB, uI} I Bin (iout ∘ g) Q)
          (navWeight I Bout iout
            {z : Bin //
              (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z =
                Sum.inr PUnit.unit}
            (fun z => g z.1) X L) =
        navWeight I Bout iout Bin g X L :=
    L.rec (motive := fun L' =>
        FreeCoprodCompDisc.Hom.comp I (navReindex.{uA, uB, uI} I Bin (iout ∘ g) Q)
            (navWeight I Bout iout
              {z : Bin //
                (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z =
                  Sum.inr PUnit.unit}
              (fun z => g z.1) X L') =
          navWeight I Bout iout Bin g X L')
      (Subtype.ext rfl)
      (fun a _L ih =>
        (FreeCoprodCompDisc.Hom.comp_assoc I
            (navReindex.{uA, uB, uI} I Bin (iout ∘ g) Q)
            (navWeight I Bout iout
              {z : Bin //
                (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z =
                  Sum.inr PUnit.unit}
              (fun z => g z.1) X _L)
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
              (mplus.{uA, uB, uI} I
                (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))).symm.trans
          (congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp I t
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                (mplus.{uA, uB, uI} I
                  (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
            ih))

  /-- The all-unresolved navigation square: the copower injection into
  the all-unresolved classifier summand, pushed through the Lemma 4
  isomorphism, is the copower injection at the reindexed weight followed
  by the summand inclusion, after the summand's Lemma 4 isomorphism. -/
  theorem interpPrecompIso_deltaNavAll_inj (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (q : Q → I) (j : Bin → I)
      (k : FreeCoprodCompDisc.{max uA uB, uI} I)
      (u : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
          ⟨{z : Bin //
            (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit},
            fun z => j z.1⟩)
        k) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.coprodInj O
                (FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                    ⟨{z : Bin //
                      (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                        z = Sum.inr PUnit.unit},
                      fun z => j z.1⟩)
                  k)
                (fun _ => interpObj I O
                  (precomp I O Q q (K (precompMerge I Q q
                    (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                    (fun z : {z : Bin //
                      (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                        z = Sum.inr PUnit.unit} =>
                      j z.1))))
                  k)
                u)
              (deltaInto I O {z : Bin //
                (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}
                (fun m => precomp I O Q q (K (precompMerge I Q q
                  (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) m)))
                (fun z => j z.1) k))
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (Bin → Q ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                  (fun m => precomp I O Q q
                    (K (precompMerge I Q q cl.down m)))) k)
              (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})))))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (delta I O Bin K) Q q k)) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (K j) Q q k))
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, j⟩)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
              (fun _ => interpObj I O (K j)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
              (FreeCoprodCompDisc.Hom.comp I (navReindex.{uA, uB, uI} I Bin j Q)
                (FreeCoprodCompDisc.Hom.comp I u
                  (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I ⟨Q, q⟩ k)))))
          (deltaInto I O Bin K j
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) :=
    (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.coprodInj O
                (FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                    ⟨{z : Bin //
                      (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                        z = Sum.inr PUnit.unit},
                      fun z => j z.1⟩)
                  k)
                (fun _ => interpObj I O
                  (precomp I O Q q (K (precompMerge I Q q
                    (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                    (fun z : {z : Bin //
                      (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                        z = Sum.inr PUnit.unit} =>
                      j z.1))))
                  k)
                u)
              (deltaInto I O {z : Bin //
                (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}
                (fun m => precomp I O Q q (K (precompMerge I Q q
                  (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) m)))
                (fun z => j z.1) k))
            (FreeCoprodCompDisc.coprodInj O
              (ULift.{max uA uB} (Bin → Q ⊕ PUnit.{uB + 1}))
              (fun cl => interpObj I O
                (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                  (fun m => precomp I O Q q
                    (K (precompMerge I Q q cl.down m)))) k)
              (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})))))
          (FreeCoprodCompDisc.Iso.hom O (t Q q k)))
        (interpPrecompIso_mk I O (Sum.inr (Sum.inr Bin)) (K ∘ ULift.down))).trans
      (Subtype.ext (funext (fun n =>
        ((rfl :
          (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.coprodInj O
                    (FreeCoprodCompDisc.Hom I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I
                        ⟨{z : Bin //
                          (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                            z = Sum.inr PUnit.unit},
                          fun z => j z.1⟩)
                      k)
                    (fun _ => interpObj I O
                      (precomp I O Q q (K (precompMerge I Q q
                        (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                        (fun z : {z : Bin //
                          (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                            z = Sum.inr PUnit.unit} =>
                          j z.1))))
                      k)
                    u)
                  (deltaInto I O {z : Bin //
                    (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}
                    (fun m => precomp I O Q q (K (precompMerge I Q q
                      (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) m)))
                    (fun z => j z.1) k))
                (FreeCoprodCompDisc.coprodInj O
                  (ULift.{max uA uB} (Bin → Q ⊕ PUnit.{uB + 1}))
                  (fun cl => interpObj I O
                    (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                      (fun m => precomp I O Q q
                        (K (precompMerge I Q q cl.down m)))) k)
                  (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})))))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIsoStep I O (Sum.inr (Sum.inr Bin))
                  (K ∘ ULift.down)
                  (fun x => interpPrecompIso I O ((K ∘ ULift.down) x))
                  Q q k))).1 n =
            (⟨arrowSumMerge
              (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) (fun z => u.1 (ULift.up z)),
              (FreeCoprodCompDisc.isoOfEq O
                (congrArg
                  (fun m => interpObj I O (K m)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                  (precompMerge_elim I Q q k Bin
                    (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                    (fun z => u.1 (ULift.up z))))).1
                ((FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O
                    (K (precompMerge I Q q (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                      (fun z => k.2 (u.1 (ULift.up z)))))
                    Q q k)).1
                  (cast
                    (congrArg
                      (fun t => (interpObj I O (precomp I O Q q
                        (K (precompMerge I Q q
                          (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) t))) k).1)
                      (funext (fun z => (congrFun u.2 (ULift.up z)).symm) :
                        (fun z : {z : Bin //
                          (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                            z = Sum.inr PUnit.unit} =>
                          j z.1) =
                          fun z : {z : Bin //
                            (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                              z = Sum.inr PUnit.unit} =>
                            k.2 (u.1 (ULift.up z))))
                    n))⟩ :
              (interpObj I O (delta I O Bin K)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)).1)).trans
          ((deltaNav_strip I O Bin K Q q k (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
            (fun z => j z.1)
            (fun z => k.2 (u.1 (ULift.up z)))
            (funext (fun z => (congrFun u.2 (ULift.up z)).symm))
            (arrowSumMerge
              (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) (fun z => u.1 (ULift.up z)))
            (precompMerge_elim I Q q k Bin
              (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1})) (fun z => u.1 (ULift.up z)))
            (fun b => (Sum.inr (u.1 (ULift.up ⟨b, rfl⟩)) : Q ⊕ k.1))
            rfl
            j
            (funext (fun _ => rfl))
            (funext (fun b => (congrFun u.2 (ULift.up ⟨b, rfl⟩)).symm))
            n).trans
            (rfl :
              (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K j) Q q k))
                    (FreeCoprodCompDisc.coprodInj O
                      (FreeCoprodCompDisc.Hom I
                        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, j⟩)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                      (fun _ => interpObj I O (K j)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k))
                      (FreeCoprodCompDisc.Hom.comp I
                        (navReindex.{uA, uB, uI} I Bin j Q)
                        (FreeCoprodCompDisc.Hom.comp I u
                          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I ⟨Q, q⟩ k)))))
                  (deltaInto I O Bin K j
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                      ⟨Q, q⟩ k))).1 n =
                (⟨fun b => (Sum.inr (u.1 (ULift.up ⟨b, rfl⟩)) : Q ⊕ k.1),
                  cast
                    (congrArg
                      (fun m => (interpObj I O (K m)
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                          ⟨Q, q⟩ k)).1)
                      (funext
                        (fun b => (congrFun u.2 (ULift.up ⟨b, rfl⟩)).symm) :
                        j = Sum.elim q k.2 ∘
                          fun b : Bin =>
                            (Sum.inr (u.1 (ULift.up ⟨b, rfl⟩)) : Q ⊕ k.1)))
                    ((FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K j) Q q k)).1
                      (cast
                        (congrArg
                          (fun t => (interpObj I O
                            (precomp I O Q q (K t)) k).1)
                          (funext (fun _ => rfl) :
                            precompMerge I Q q
                              (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                                (fun z : {z : Bin //
                                  (fun _ : Bin => (Sum.inr PUnit.unit : Q ⊕ PUnit.{uB + 1}))
                                    z = Sum.inr PUnit.unit} =>
                                  j z.1) =
                              j))
                        n))⟩ :
                  (interpObj I O (delta I O Bin K)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I
                      ⟨Q, q⟩ k)).1)).symm)))))

  /-- The tower-conjugated navigation inclusion: the copower injection
  at the `IR.navWeight` weight followed by the summand inclusion, both
  at the tower coproduct, conjugated by the iterated Lemma 4
  isomorphisms. -/
  def navInj (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom O
        (interpObj I O
          (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (K (iout ∘ g))) X)
        (interpObj I O
          (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (delta I O Bin K)) X) :=
    FreeCoprodCompDisc.Hom.comp O
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O
            (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)) X))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (fun _ => interpObj I O (K (iout ∘ g))
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
            (navWeight I Bout iout Bin g X L))
          (deltaInto I O Bin K (iout ∘ g)
            (mplus.{uA, uB, uI} I
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
      (FreeCoprodCompDisc.Iso.invHom O
        (mprecompIso.{uA, uB, uI, uO} I O
          (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O Bin K) X))

  /-- The base-inclusion equation: the composite inclusion of the
  `IR.deltaNavBase` characterization is `IR.navInj` at the empty
  stack. -/
  theorem navInj_nil (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z => nomatch z.2)
            (fun j => precomp I O Bout iout
              (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
            X)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
            (fun cl => interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun j => precomp I O Bout iout
                  (K (precompMerge I Bout iout cl.down j)))) X)
            (ULift.up (fun b => Sum.inl (g b)))) =
        navInj I O Bout iout Bin K g [] X :=
    (eq_comp_invHom O
        (interpObj I O (precomp I O Bout iout (K (iout ∘ g))) X)
        (interpObj I O (precomp I O Bout iout (delta I O Bin K)) X)
        (interpObj I O (delta I O Bin K)
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
        (FreeCoprodCompDisc.Hom.comp O
          (deltaEmptyInj I O
            {z : Bin // (fun b => Sum.inl (g b) : Bin → Bout ⊕ PUnit.{uB + 1}) z =
              Sum.inr PUnit.unit}
            (fun z => nomatch z.2)
            (fun j => precomp I O Bout iout
              (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
            X)
          (FreeCoprodCompDisc.coprodInj O
            (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
            (fun cl => interpObj I O
              (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                (fun j => precomp I O Bout iout
                  (K (precompMerge I Bout iout cl.down j)))) X)
            (ULift.up (fun b => Sum.inl (g b)))))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K (iout ∘ g)) Bout iout X))
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
              (fun _ => interpObj I O (K (iout ∘ g))
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
              ⟨fun z => Sum.inl (g z.down), rfl⟩))
          (deltaInto I O Bin K (iout ∘ g)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X)))
        (interpPrecompIso I O (delta I O Bin K) Bout iout X)
        (interpPrecompIso_deltaNav_inj I O Bout iout Bin K g X)).trans
      (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O t
          (FreeCoprodCompDisc.Iso.invHom O
            (interpPrecompIso I O (delta I O Bin K) Bout iout X)))
        (FreeCoprodCompDisc.Hom.comp_assoc O
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (K (iout ∘ g)) Bout iout X))
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            (fun _ => interpObj I O (K (iout ∘ g))
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))
            ⟨fun z => Sum.inl (g z.down), rfl⟩)
          (deltaInto I O Bin K (iout ∘ g)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Bout, iout⟩ X))))

  /-- The cons-inclusion equation: the navigation inclusion at the
  unresolved-subtype data, composed with the classifier-summand
  inclusion conjugated through the tower isomorphisms, is `IR.navInj`
  at the extended stack. -/
  theorem navInj_cons (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
      (a : SupObj.{uB, uI} I) (L : List (SupObj.{uB, uI} I))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp O
          (navInj I O Bout iout
            {z : Bin //
              (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                Sum.inr PUnit.unit}
            (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2
              (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))
            (fun z => g z.1) L X)
          (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                      (delta I O
                        {z : Bin //
                          (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
                            Sum.inr PUnit.unit}
                        (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2
                          (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))))
                      X))
                (FreeCoprodCompDisc.coprodInj O
                  (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                  (fun cl => interpObj I O
                    (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                      (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
                    (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                  (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})))))
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                    (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
                      (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
                        (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m)))))
                    X))) =
        navInj I O Bout iout Bin K g (a :: L) X :=
      Eq.trans (FreeCoprodCompDisc.Hom.comp_assoc O (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K (iout ∘ g))) X)) (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI,
        max uA uB} I ⟨{z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
        Sum.inr PUnit.unit}, fun z => (iout ∘ g) z.1⟩) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X)) (fun _ => interpObj I O (precomp I O a.1 a.2 (K (precompMerge I a.1
        a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) (fun z : {z : Bin // (fun _
        : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} => (iout ∘ g)
        z.1)))) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (navWeight I
        Bout iout {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
        Sum.inr PUnit.unit} (fun z => g z.1) X L)) (deltaInto I O {z : Bin // (fun _ : Bin =>
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I O
        a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB +
        1})) m))) (fun z => (iout ∘ g) z.1) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB,
        uI} I)]) X)))) (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (L ++
        [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O {z : Bin // (fun _ : Bin => (Sum.inr
        PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K
        (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))))
        X)) (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) (delta I O {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕
        PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I
        a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X))
        (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl
        => interpObj I O (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I
        O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout,
        iout⟩ : SupObj.{uB, uI} I)]) X)) (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕
        PUnit.{uB + 1}))))) (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (L ++
        [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕
        PUnit.{uB + 1})) (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m =>
        precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X)))) (Eq.trans (congrArg
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O
        a.1 a.2 (K (iout ∘ g))) X)) (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨{z : Bin // (fun _
        : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}, fun z =>
        (iout ∘ g) z.1⟩) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (fun
        _ => interpObj I O (precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr
        PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) (fun z : {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit
        : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} => (iout ∘ g) z.1)))) (mplus.{uA, uB, uI} I
        (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (navWeight I Bout iout {z : Bin // (fun _ :
        Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun z => g z.1)
        X L)) (deltaInto I O {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB +
        1})) z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _
        : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))) (fun z => (iout ∘ g) z.1)
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))) (Eq.trans (Eq.symm
        (FreeCoprodCompDisc.Hom.comp_assoc O (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB,
        uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O {z : Bin // (fun _ : Bin
        => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I
        O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB +
        1})) m)))) X)) (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O {z
        : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
        PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin =>
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X)) (FreeCoprodCompDisc.coprodInj O
        (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl => interpObj I O (delta I O {z
        : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I
        a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
        (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})))))
        (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl
        => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K
        (precompMerge I a.1 a.2 cl.down m))))) X)))) (congrArg (fun t => FreeCoprodCompDisc.Hom.comp
        O t (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun
        cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K
        (precompMerge I a.1 a.2 cl.down m))))) X))) (Eq.trans (Eq.symm
        (FreeCoprodCompDisc.Hom.comp_assoc O (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB,
        uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O {z : Bin // (fun _ : Bin
        => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I
        O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB +
        1})) m)))) X)) (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O (L ++
        [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O {z : Bin // (fun _ : Bin => (Sum.inr
        PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K
        (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))))
        X)) (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
        (fun cl => interpObj I O (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m =>
        precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (L ++
        [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit :
        a.1 ⊕ PUnit.{uB + 1})))))) (Eq.trans (congrArg (fun t => FreeCoprodCompDisc.Hom.comp O t
        (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl
        => interpObj I O (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I
        O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout,
        iout⟩ : SupObj.{uB, uI} I)]) X)) (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕
        PUnit.{uB + 1}))))) (FreeCoprodCompDisc.Iso.invHom_hom O (mprecompIso.{uA, uB, uI, uO} I O
        (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O {z : Bin // (fun _ : Bin => (Sum.inr
        PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K
        (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))))
        X))) (FreeCoprodCompDisc.Hom.id_comp O (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB,
        uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl => interpObj I O (delta I O {z : Bin // cl.down z
        = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (ULift.up (fun _ : Bin
        => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})))))))))) (Eq.trans
        (FreeCoprodCompDisc.Hom.comp_assoc O (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI,
        uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K (iout ∘ g))) X))
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.coprodInj O (FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨{z : Bin // (fun _ : Bin => (Sum.inr
        PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}, fun z => (iout ∘ g) z.1⟩)
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (fun _ => interpObj I
        O (precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1
        ⊕ PUnit.{uB + 1})) (fun z : {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕
        PUnit.{uB + 1})) z = Sum.inr PUnit.unit} => (iout ∘ g) z.1)))) (mplus.{uA, uB, uI} I (L ++
        [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (navWeight I Bout iout {z : Bin // (fun _ : Bin =>
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun z => g z.1) X L))
        (deltaInto I O {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
        Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin =>
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))) (fun z => (iout ∘ g) z.1) (mplus.{uA, uB,
        uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl
        => interpObj I O (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I
        O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout,
        iout⟩ : SupObj.{uB, uI} I)]) X)) (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕
        PUnit.{uB + 1})))) (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (L ++
        [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕
        PUnit.{uB + 1})) (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m =>
        precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X)))) (Eq.trans (congrArg
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I
        O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K (iout ∘ g))) X)))
        (Eq.symm (FreeCoprodCompDisc.Hom.comp_assoc O (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI,
        max uA uB} I ⟨{z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
        Sum.inr PUnit.unit}, fun z => (iout ∘ g) z.1⟩) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X)) (fun _ => interpObj I O (precomp I O a.1 a.2 (K (precompMerge I a.1
        a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) (fun z : {z : Bin // (fun _
        : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} => (iout ∘ g)
        z.1)))) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (navWeight I
        Bout iout {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
        Sum.inr PUnit.unit} (fun z => g z.1) X L)) (deltaInto I O {z : Bin // (fun _ : Bin =>
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I O
        a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB +
        1})) m))) (fun z => (iout ∘ g) z.1) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB,
        uI} I)]) X))) (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB
        + 1})) (fun cl => interpObj I O (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun
        m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (L
        ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit :
        a.1 ⊕ PUnit.{uB + 1})))) (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O
        (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕
        PUnit.{uB + 1})) (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m =>
        precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X))))) (Eq.trans (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB,
        uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K (iout ∘ g)))
        X)) (FreeCoprodCompDisc.Hom.comp O t (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB,
        uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB}
        (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl => delta I O {z : Bin // cl.down z = Sum.inr
        PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m))))) X))))
        (eq_comp_invHom O (interpObj I O (precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ :
        Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) (fun z : {z : Bin // (fun _ : Bin =>
        (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} => (iout ∘ g) z.1))))
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (interpObj I O
        (precomp I O a.1 a.2 (delta I O Bin K)) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X)) (interpObj I O (delta I O Bin K) (FreeCoprodCompDisc.plus.{uI, uB,
        max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.coprodInj
        O (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨{z : Bin // (fun
        _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit}, fun z =>
        (iout ∘ g) z.1⟩) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (fun
        _ => interpObj I O (precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _ : Bin => (Sum.inr
        PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) (fun z : {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit
        : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} => (iout ∘ g) z.1)))) (mplus.{uA, uB, uI} I
        (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)) (navWeight I Bout iout {z : Bin // (fun _ :
        Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun z => g z.1)
        X L)) (deltaInto I O {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB +
        1})) z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2 (fun _
        : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))) (fun z => (iout ∘ g) z.1)
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
        (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl
        => interpObj I O (delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I
        O a.1 a.2 (K (precompMerge I a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (L ++ [(⟨Bout,
        iout⟩ : SupObj.{uB, uI} I)]) X)) (ULift.up (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕
        PUnit.{uB + 1}))))) (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2 (mplus.{uA, uB,
        uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (fun _ => interpObj I O (K (iout ∘ g))
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Hom.comp I (navReindex.{uA, uB, uI} I Bin
        (iout ∘ g) a.1) (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout {z : Bin // (fun _ :
        Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun z => g z.1)
        X L) (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X)))))) (deltaInto I O Bin K (iout ∘ g) (FreeCoprodCompDisc.plus.{uI,
        uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
        (interpPrecompIso I O (delta I O Bin K) a.1 a.2 (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X)) (interpPrecompIso_deltaNavAll_inj I O Bin K a.1 a.2 (iout ∘ g)
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X) (navWeight I Bout iout
        {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
        PUnit.unit} (fun z => g z.1) X L)))) (Eq.trans (congrArg (fun w =>
        FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I
        O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K (iout ∘ g))) X))
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (K (iout
        ∘ g)) a.1 a.2 (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
        (FreeCoprodCompDisc.coprodInj O (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI,
        max uA uB} I ⟨Bin, iout ∘ g⟩) (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA,
        uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) (fun _ => interpObj I O (K (iout
        ∘ g)) (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout,
        iout⟩ : SupObj.{uB, uI} I)]) X))) (w))) (deltaInto I O Bin K (iout ∘ g)
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X)))) (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O (delta I
        O Bin K) a.1 a.2 (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
        (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl
        => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K
        (precompMerge I a.1 a.2 cl.down m))))) X)))) (Eq.trans (Eq.symm
        (FreeCoprodCompDisc.Hom.comp_assoc I (navReindex.{uA, uB, uI} I Bin (iout ∘ g) a.1)
        (navWeight I Bout iout {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB +
        1})) z = Sum.inr PUnit.unit} (fun z => g z.1) X L)
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))) (congrArg (fun t =>
        FreeCoprodCompDisc.Hom.comp I t
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++
        [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) (navWeight_reindex I Bout iout Bin g a.1 X L))))
        (Eq.trans (congrArg (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O
        a.1 a.2 (K (iout ∘ g))) X))) (FreeCoprodCompDisc.Hom.comp_assoc O
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2 (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.coprodInj O (FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (fun _ => interpObj I O (K (iout ∘ g))
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout Bin g X L)
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB,
        uI} I)]) X))))) (deltaInto I O Bin K (iout ∘ g) (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
        I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))
        (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O (delta I O Bin K) a.1 a.2 (mplus.{uA,
        uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Iso.invHom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (sigma I O
        (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl => delta I O {z : Bin //
        cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2
        cl.down m))))) X)))) (Eq.trans (congrArg (fun t => FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K (iout ∘ g))) X)) (FreeCoprodCompDisc.Hom.comp O
        t (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O
        (delta I O Bin K) a.1 a.2 (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
        X))) (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun
        cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K
        (precompMerge I a.1 a.2 cl.down m))))) X))))) (FreeCoprodCompDisc.Hom.comp_assoc O
        (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2 (mplus.{uA, uB,
        uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (fun _ => interpObj I O (K (iout ∘ g))
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout Bin g X L)
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB,
        uI} I)]) X)))) (deltaInto I O Bin K (iout ∘ g) (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
        I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))))) (Eq.trans
        (Eq.symm (FreeCoprodCompDisc.Hom.comp_assoc O (FreeCoprodCompDisc.Iso.hom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O
        a.1 a.2 (K (iout ∘ g))) X)) (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2 (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (fun _ => interpObj I O (K (iout ∘ g))
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout Bin g X L)
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB,
        uI} I)]) X)))) (deltaInto I O Bin K (iout ∘ g) (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
        I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))
        (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O (delta
        I O Bin K) a.1 a.2 (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))
        (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl
        => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K
        (precompMerge I a.1 a.2 cl.down m))))) X))))) (congrArg (fun t =>
        FreeCoprodCompDisc.Hom.comp O t (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O (delta I O Bin K) a.1 a.2 (mplus.{uA,
        uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Iso.invHom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (sigma I O
        (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1})) (fun cl => delta I O {z : Bin //
        cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K (precompMerge I a.1 a.2
        cl.down m))))) X)))) (Eq.symm (FreeCoprodCompDisc.Hom.comp_assoc O
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K (iout ∘ g))) X)) (FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIso I O (K (iout ∘ g)) a.1 a.2 (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ :
        SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.coprodInj O
        (FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (fun _ => interpObj I O (K (iout ∘ g))
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩
        : SupObj.{uB, uI} I)]) X))) (FreeCoprodCompDisc.Hom.comp I (navWeight I Bout iout Bin g X L)
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
        (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB,
        uI} I)]) X)))) (deltaInto I O Bin K (iout ∘ g) (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
        I a (mplus.{uA, uB, uI} I (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))))))))))))

  /-- The `IR.deltaNav` characterization: `IR.interpHom` sends the
  tower navigation to the composite with the tower-conjugated
  navigation inclusion `IR.navInj`, by `List.rec` following
  `IR.deltaNav`'s own recursion. -/
  theorem interpHom_deltaNav (D : IR.{max uA uB, uB, uI, uO} I O)
      (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
      (L : List (SupObj.{uB, uI} I))
      (f : Hom.{uA, uB, uI, uO} I O D
        (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g))))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      (interpHom I O D
          (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (delta I O Bin K))
          (deltaNav I O D Bout iout Bin K g L f)).1 X =
        FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O D
            (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
              (K (iout ∘ g))) f).1 X)
          (navInj I O Bout iout Bin K g L X) :=
    L.rec (motive := fun L' : List (SupObj.{uB, uI} I) =>
        ∀ (Bin' : Type uB) (K' : (Bin' → I) → IR.{max uA uB, uB, uI, uO} I O)
          (g' : Bin' → Bout)
          (f' : Hom.{uA, uB, uI, uO} I O D
            (mprecomp I O (L' ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
              (K' (iout ∘ g'))))
          (X' : FreeCoprodCompDisc.{max uA uB, uI} I),
        (interpHom I O D
            (mprecomp I O (L' ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
              (delta I O Bin' K'))
            (deltaNav I O D Bout iout Bin' K' g' L' f')).1 X' =
          FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O D
              (mprecomp I O (L' ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
                (K' (iout ∘ g'))) f').1 X')
            (navInj I O Bout iout Bin' K' g' L' X'))
      (fun Bin' K' g' f' X' =>
        (interpHom_deltaNavBase I O D Bout iout Bin' K' g' f' X').trans
          (congrArg
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O D (precomp I O Bout iout (K' (iout ∘ g'))) f').1 X'))
            (navInj_nil I O Bout iout Bin' K' g' X')))
      (fun a _L ih Bin' K' g' f' X' =>
        Eq.trans (interpHom_msigmaPush I O D (ULift.{max uA uB, uB} (Bin' → a.1 ⊕ PUnit.{uB + 1}))
          (fun cl => delta I O {z : Bin' // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O
          a.1 a.2 (K' (precompMerge I a.1 a.2 cl.down m)))) (ULift.up (fun _ => Sum.inr PUnit.unit))
          (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (deltaNav I O D Bout iout {z : Bin' // (fun _
          : Bin' => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m =>
          precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ : Bin' => (Sum.inr PUnit.unit : a.1
          ⊕ PUnit.{uB + 1})) m))) (fun z => g' z.1) _L f') X') (Eq.trans (congrArg (fun t =>
          FreeCoprodCompDisc.Hom.comp O t (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO}
          I O (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O {z : Bin' // (fun _ : Bin' =>
          (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr PUnit.unit} (fun m => precomp I O
          a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ : Bin' => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB
          + 1})) m)))) X')) (FreeCoprodCompDisc.coprodInj O (ULift.{max uA uB, uB} (Bin' → a.1 ⊕
          PUnit.{uB + 1})) (fun cl => interpObj I O (delta I O {z : Bin' // cl.down z = Sum.inr
          PUnit.unit} (fun m => precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 cl.down m))))
          (mplus.{uA, uB, uI} I (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X')) (ULift.up (fun _
          => Sum.inr PUnit.unit)))) (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I
          O (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin' →
          a.1 ⊕ PUnit.{uB + 1})) (fun cl => delta I O {z : Bin' // cl.down z = Sum.inr PUnit.unit}
          (fun m => precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 cl.down m))))) X')))) (ih {z :
          Bin' // (fun _ : Bin' => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
          PUnit.unit} (fun m => precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ : Bin' =>
          (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))) (fun z => g' z.1) f' X')) (Eq.trans
          (FreeCoprodCompDisc.Hom.comp_assoc O ((interpHom I O D (mprecomp I O (_L ++ [(⟨Bout, iout⟩
          : SupObj.{uB, uI} I)]) (precomp I O a.1 a.2 (K' (iout ∘ g')))) f').1 X') (navInj I O Bout
          iout {z : Bin' // (fun _ : Bin' => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z =
          Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ :
          Bin' => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m))) (fun z => g' z.1) _L X')
          (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Hom.comp O (FreeCoprodCompDisc.Iso.hom
          O (mprecompIso.{uA, uB, uI, uO} I O (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I
          O {z : Bin' // (fun _ : Bin' => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z = Sum.inr
          PUnit.unit} (fun m => precomp I O a.1 a.2 (K' (precompMerge I a.1 a.2 (fun _ : Bin' =>
          (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) m)))) X')) (FreeCoprodCompDisc.coprodInj O
          (ULift.{max uA uB, uB} (Bin' → a.1 ⊕ PUnit.{uB + 1})) (fun cl => interpObj I O (delta I O
          {z : Bin' // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2 (K'
          (precompMerge I a.1 a.2 cl.down m)))) (mplus.{uA, uB, uI} I (_L ++ [(⟨Bout, iout⟩ :
          SupObj.{uB, uI} I)]) X')) (ULift.up (fun _ => Sum.inr PUnit.unit))))
          (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O (_L ++ [(⟨Bout, iout⟩ :
          SupObj.{uB, uI} I)]) (sigma I O (ULift.{max uA uB, uB} (Bin' → a.1 ⊕ PUnit.{uB + 1})) (fun
          cl => delta I O {z : Bin' // cl.down z = Sum.inr PUnit.unit} (fun m => precomp I O a.1 a.2
          (K' (precompMerge I a.1 a.2 cl.down m))))) X')))) (congrArg (FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O D (mprecomp I O (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (precomp I O
          a.1 a.2 (K' (iout ∘ g')))) f').1 X')) (navInj_cons I O Bout iout Bin' K' g' a _L X')))))
      Bin K g f X
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `IR.navWeight`, `IR.navReindex` — the tower navigation weight,
    and the reindexing of a lifted direction family along the
    inclusion of the all-unresolved classifier's subtype.
  * `IR.navInj` — the tower-conjugated navigation inclusion.
  ```

  and to `## Main statements`:

  ```markdown
  * `IR.interpHom_msigmaPush`, `IR.interpHom_deltaNavBase`,
    `IR.interpHom_deltaNav` — `IR.interpHom` sends the stack
    `σ`-push, the base `δ`-navigation, and the tower navigation to
    composition with the corresponding semantic inclusion.
  * `IR.navWeight_snoc`, `IR.navInj_nil`, `IR.navInj_cons` — the
    tower navigation weight at a right-appended superscript, and the
    inclusion equations of `IR.navInj` at the empty and extended
    stacks.
  * `IR.eq_comp_invHom` — a factorization through the forward
    component of an isomorphism determines the factorization through
    the inverse.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files.

- [ ] **Step 5: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent, then:

  ```bash
  jj commit -m "feat(indrec): characterize the interpretation of the navigation helpers"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 8: the identity-image induction

The identity-image equation
`IR.interpHom γ γ (IR.id γ) = NatTrans.id ⟦γ⟧` is the branch's
closure gate: Task 9's identity laws consume it, and no earlier
branch delivers it. This task discharges it, in the generalized form
its induction requires. `IR.InterpHomPreUnitMotive γ` is the
component equation for `IR.preUnitStack γ L` against the semantic
pre-unit component `IR.preUnitComponent γ L X`, at every stack `L`
and object `X`; `IR.interpHom_preUnitStack` proves it by
`IR.induction` on the domain code, mirroring `IR.preUnitStack`'s own
recursion. Task 9 instantiates it at `L = []`, where Task 3's
`IR.preUnitComponent_nil` collapses the right-hand side to the
identity.

Each case unfolds `IR.preUnitStack` by Task 2's computation
equations and `IR.interpHom` by Task 4's characterizing equations,
rewrites every cotuple component into an inclusion composed with a
common factor by the Tasks 5–7 helper characterizations, and
collapses by the matching cotuple eta law:
`IR.interpHomPreUnit_mk_iota` (through the codomain-generalized
`IR.interpHomPreUnit_iotaGen`), `IR.interpHomPreUnit_mk_sigma`
(through the per-summand `IR.interpHomPreUnit_sigmaSummand` and
`FreeCoprodCompDisc.coprodDesc_eta`), and
`IR.interpHomPreUnit_mk_delta` (through the per-summand
`IR.interpHomPreUnit_deltaSummand` and
`FreeCoprodCompDisc.deltaDesc_eta`).

The `δ`-case is the one whose transports merge, per the design
spec's § The identity-image induction. Its per-weight identity
`IR.interpHomPreUnit_deltaWeight` is derived by post-composing with
the forward hom of the tower isomorphism at the extended stack
`L ++ [⟨B, i⟩]`, Task 7's `IR.eq_comp_invHom` reading the resulting
factorization back through the inverse. The post-composition
collapses `IR.preUnitComponent`'s right-hand side to a bare
`IR.interpMor` of `IR.mplusInj` (`IR.preUnitComponent_comp_hom`) and
merges the `IR.mprecomp_snoc` transport with the Lemma 4 layer into
that single isomorphism (`IR.mprecompIso_snoc_hom_comp`,
`IR.navInj_comp_hom`), leaving the reduced form
`IR.interpHomPreUnit_deltaWeightRight`. Its residue is
`IR.deltaInto`/`FreeCoprodCompDisc.coprodInj` naturality
(`IR.deltaIntoWeight_comp`) together with two identities on the
tower against the bridge morphism `IR.navBridgeMor` — for the
iterated injection (`IR.mplusInj_navBridge`) and for the navigation
weight (`IR.navWeight_navBridge`). Unfolding the tower layer by
layer and cancelling the Lemma 4 layer separately does not terminate
against the `IR.mprecomp_snoc` cast, so the merge is what makes the
case finite.

Task 2 commits the named recursor motive and steps of
`IR.preUnitStack` to `Hom.lean` — `IR.PreUnitStackMotive`,
`IR.preUnitStackStep`, `IR.preUnitStack_mk_iota`,
`IR.preUnitStack_mk_sigma`, `IR.preUnitDeltaData`, and
`IR.preUnitStack_mk_delta`. This task consumes them and does not
redeclare them.

`IR.comp_isoOfEq_hom` and `IR.isoOfEq_symm_hom_comp` each carry a
`set_option linter.checkUnivs false in` line, reproduced verbatim in
Step 3: in both, the separated `uA` and `uB` occur only under `max`,
the configuration the linter reports.
`Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` is the precedent,
carrying the same option on eight declarations.

The prototype's `coprodPairInr'_mor` is `IR.coprodPairInr_mor` here,
and every `coprodPairInr'` call is Task 1's generalized
`FreeCoprodCompDisc.coprodPairInr` at `.{uI, uB, max uA uB}`; both
renames are applied in the code below, with the three lines the
rename pushes past 100 columns re-wrapped.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean`

**Interfaces:**

- Consumes: Task 7's `IR.eq_comp_invHom`, `IR.navInj`,
  `IR.navWeight`, `IR.navWeight_snoc`, `IR.interpHom_deltaNav`,
  `IR.interpHom_msigmaPush`; Task 6's `IR.interpHom_deltaEmptyPush`;
  Task 5's `IR.interpHom_sigmaPush`; Task 4's `IR.interpHom_sigma`,
  `IR.interpHom_delta`, `IR.interpHomDeltaSummand`,
  `IR.interpMor_sigma_inj`; Task 3's `IR.mplus`, `IR.mplus_snoc`,
  `IR.mplusInj`, `IR.mplusInj_snoc`, `IR.mplusMorMap`,
  `IR.mprecompIso`, `IR.mprecompIso_snoc_hom`,
  `IR.mprecompIso_natural`, `IR.preUnitComponent`; Task 2's
  `IR.preUnitStack_mk_iota`, `IR.preUnitStack_mk_sigma`,
  `IR.preUnitDeltaData`, `IR.preUnitStack_mk_delta`; Task 1's
  `FreeCoprodCompDisc.coprodPairInr`; `IR.induction`,
  `IR.preUnitStack`, `IR.msigmaPush`, `IR.deltaNav`, `IR.deltaInto`,
  `IR.deltaDesc`, `IR.deltaInto_natural`, `IR.deltaDesc_eta`,
  `IR.interpMor_comp`, `IR.plusLiftBridgeInvHom`,
  `IR.plusLiftBridgeNatInv`, `IR.mprecomp`, `IR.mprecomp_snoc`,
  `IR.mprecomp_iota_mk`, `FreeCoprodCompDisc.coprodDesc`,
  `FreeCoprodCompDisc.coprodDesc_eta`,
  `FreeCoprodCompDisc.coprodInj`,
  `FreeCoprodCompDisc.coprodInj_mor`,
  `FreeCoprodCompDisc.coprodPairDesc`,
  `FreeCoprodCompDisc.coprodPairMor`,
  `FreeCoprodCompDisc.copowerHomMapMor`,
  `FreeCoprodCompDisc.isoOfEq`, `FreeCoprodCompDisc.Iso.invHom_hom`,
  and the `FreeCoprodCompDisc.Hom` category laws.
- Produces (in `namespace IR`): `InterpHomPreUnitMotive`,
  `interpHom_cast_cod`, `comp_isoOfEq_hom`, `isoOfEq_symm_hom_comp`,
  `interpMor_isoOfEq_dom`, `coprodPairInr_mor`, `mplusInj_natural`,
  `deltaIntoWeight_comp`, `mprecompIso_snoc_hom_comp`,
  `navBridgeMor`, `mplusInj_navBridge`, `navWeight_navBridge`,
  `navInj_comp_hom`, `preUnitComponent_comp_hom`,
  `interpHomPreUnit_deltaWeightRight`,
  `interpHomPreUnit_deltaWeight`, `interpHomPreUnit_deltaSummand`,
  `interpHomPreUnit_mk_delta`, `interpHomPreUnit_iotaGen`,
  `interpHomPreUnit_mk_iota`, `interpHomPreUnit_sigmaSummand`,
  `interpHomPreUnit_mk_sigma`, `interpHom_preUnitStack`.

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean` (after
  `sampleDeltaNavChar`):

  ```lean
  /-- The identity-image equation at the sample code and the empty
  stack. -/
  theorem sampleInterpHomPreUnitStack_nil
      (X : FreeCoprodCompDisc.{0, 0} Bool) :
      (interpHom Bool Bool sampleCategoryCode
          (mprecomp Bool Bool [] sampleCategoryCode)
          (preUnitStack Bool Bool sampleCategoryCode [])).1 X =
        preUnitComponent Bool Bool sampleCategoryCode [] X :=
    interpHom_preUnitStack Bool Bool sampleCategoryCode [] X

  /-- The semantic pre-unit component followed by the tower
  isomorphism, at the sample code and the empty stack. -/
  theorem samplePreUnitComponentCompHom :
      FreeCoprodCompDisc.Hom.comp Bool
          (preUnitComponent Bool Bool sampleCategoryCode []
            sampleCategoryObj)
          (FreeCoprodCompDisc.Iso.hom Bool
            (mprecompIso Bool Bool [] sampleCategoryCode
              sampleCategoryObj)) =
        interpMor Bool Bool sampleCategoryCode sampleCategoryObj
          (mplus Bool [] sampleCategoryObj)
          (mplusInj Bool [] sampleCategoryObj) :=
    preUnitComponent_comp_hom Bool Bool sampleCategoryCode []
      sampleCategoryObj
  ```

  Extend the test file's module docstring summary with one sentence:
  "The identity-image equation and the tower factorization of the
  semantic pre-unit component are exercised at the empty stack."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.interpHom_preUnitStack`.

- [ ] **Step 3: Implement.** Append to
  `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`, above `end IR`:

  ```lean
  /-- The statement of the identity-image equation at one code: the
  component of `IR.interpHom` at the pre-unit is the semantic pre-unit
  component. -/
  def InterpHomPreUnitMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
    ∀ (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I),
      (interpHom I O γ (mprecomp I O L γ) (preUnitStack I O γ L)).1 X =
        preUnitComponent I O γ L X

  /-- Elimination of a codomain-code transport inside `IR.interpHom`, by
  elimination of the generalized equality: the transport passes to an
  object-equality transport on the component. -/
  theorem interpHom_cast_cod (D : IR.{max uA uB, uB, uI, uO} I O)
      (γ₀ : IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      ∀ (γ'' : IR.{max uA uB, uB, uI, uO} I O) (h : γ₀ = γ'')
        (f : Hom.{uA, uB, uI, uO} I O D γ₀),
        (interpHom I O D γ'' (cast (congrArg (Hom I O D) h) f)).1 X =
          FreeCoprodCompDisc.Hom.comp O ((interpHom I O D γ₀ f).1 X)
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun cc => interpObj I O cc X) h))) :=
    fun _ h =>
      Eq.rec (motive := fun γ'' h' =>
          ∀ f : Hom.{uA, uB, uI, uO} I O D γ₀,
            (interpHom I O D γ'' (cast (congrArg (Hom I O D) h') f)).1 X =
              FreeCoprodCompDisc.Hom.comp O ((interpHom I O D γ₀ f).1 X)
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun cc => interpObj I O cc X) h'))))
        (fun f => (FreeCoprodCompDisc.Hom.comp_id O
          ((interpHom I O D γ₀ f).1 X)).symm)
        h

  set_option linter.checkUnivs false in
  /-- Postcomposition with an object-equality transport is the transport
  of the morphism's codomain, by elimination of the generalized
  equality. -/
  theorem comp_isoOfEq_hom (Z W : FreeCoprodCompDisc.{max uA uB, uI} I) :
      ∀ (V : FreeCoprodCompDisc.{max uA uB, uI} I) (q : W = V)
        (f : FreeCoprodCompDisc.Hom I Z W),
        FreeCoprodCompDisc.Hom.comp I f
            (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I q)) =
          cast (congrArg (FreeCoprodCompDisc.Hom I Z) q) f :=
    fun _ q =>
      Eq.rec (motive := fun _V' q' =>
          ∀ f : FreeCoprodCompDisc.Hom I Z W,
            FreeCoprodCompDisc.Hom.comp I f
                (FreeCoprodCompDisc.Iso.hom I
                  (FreeCoprodCompDisc.isoOfEq I q')) =
              cast (congrArg (FreeCoprodCompDisc.Hom I Z) q') f)
        (fun f => FreeCoprodCompDisc.Hom.comp_id I f) q

  set_option linter.checkUnivs false in
  /-- An object-equality transport followed by its inverse is the
  identity, by elimination of the generalized equality. -/
  theorem isoOfEq_symm_hom_comp (Z : FreeCoprodCompDisc.{max uA uB, uO} O) :
      ∀ (W : FreeCoprodCompDisc.{max uA uB, uO} O) (q : Z = W),
        FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O q.symm))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O q)) =
          FreeCoprodCompDisc.Hom.id O W :=
    fun _ q =>
      Eq.rec (motive := fun W' q' =>
          FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (FreeCoprodCompDisc.isoOfEq O q'.symm))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O q')) =
            FreeCoprodCompDisc.Hom.id O W')
        (Subtype.ext rfl) q

  /-- An object-equality transport of the interpreted argument passes
  through `IR.interpMor`, by elimination of the generalized equality. -/
  theorem interpMor_isoOfEq_dom (γ' : IR.{max uA uB, uB, uI, uO} I O)
      (W Y : FreeCoprodCompDisc.{max uA uB, uI} I) :
      ∀ (V : FreeCoprodCompDisc.{max uA uB, uI} I) (q : W = V)
        (h : FreeCoprodCompDisc.Hom I V Y),
        FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ') q)))
            (interpMor I O γ' V Y h) =
          interpMor I O γ' W Y
            (FreeCoprodCompDisc.Hom.comp I
              (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I q)) h) :=
    fun _ q =>
      Eq.rec (motive := fun V' q' =>
          ∀ h : FreeCoprodCompDisc.Hom I V' Y,
            FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (interpObj I O γ') q')))
                (interpMor I O γ' V' Y h) =
              interpMor I O γ' W Y
                (FreeCoprodCompDisc.Hom.comp I
                  (FreeCoprodCompDisc.Iso.hom I
                    (FreeCoprodCompDisc.isoOfEq I q')) h))
        (fun _ => rfl) q

  /-- The fresh right injection commutes past a coproduct-pair morphism
  with identity left component. -/
  theorem coprodPairInr_mor (a : SupObj.{uB, uI} I)
      (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I Z W) :
      FreeCoprodCompDisc.Hom.comp I (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a Z)
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I a) h) =
        FreeCoprodCompDisc.Hom.comp I h
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W) :=
    Subtype.ext rfl

  /-- Naturality of the iterated right injection `IR.mplusInj` in the
  base object. -/
  theorem mplusInj_natural (L : List (SupObj.{uB, uI} I))
      (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I Z W) :
      FreeCoprodCompDisc.Hom.comp I (mplusInj.{uA, uB, uI} I L Z)
          (mplusMorMap.{uA, uB, uI} I L Z W h) =
        FreeCoprodCompDisc.Hom.comp I h (mplusInj.{uA, uB, uI} I L W) :=
    L.rec (motive := fun L' =>
        FreeCoprodCompDisc.Hom.comp I (mplusInj.{uA, uB, uI} I L' Z)
            (mplusMorMap.{uA, uB, uI} I L' Z W h) =
          FreeCoprodCompDisc.Hom.comp I h (mplusInj.{uA, uB, uI} I L' W))
      ((FreeCoprodCompDisc.Hom.id_comp I h).trans
        (FreeCoprodCompDisc.Hom.comp_id I h).symm)
      (fun a _L ih =>
        (FreeCoprodCompDisc.Hom.comp_assoc I (mplusInj.{uA, uB, uI} I _L Z)
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a (mplus.{uA, uB, uI} I _L Z))
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I a)
              (mplusMorMap.{uA, uB, uI} I _L Z W h))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp I (mplusInj.{uA, uB, uI} I _L Z) :
                _ → _)
              (coprodPairInr_mor I a (mplus.{uA, uB, uI} I _L Z)
                (mplus.{uA, uB, uI} I _L W)
                (mplusMorMap.{uA, uB, uI} I _L Z W h))).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc I (mplusInj.{uA, uB, uI} I _L Z)
                (mplusMorMap.{uA, uB, uI} I _L Z W h)
                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                  (mplus.{uA, uB, uI} I _L W))).symm.trans
              ((congrArg
                  (fun t => FreeCoprodCompDisc.Hom.comp I t
                    (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                      (mplus.{uA, uB, uI} I _L W)))
                  ih).trans
                (FreeCoprodCompDisc.Hom.comp_assoc I h
                  (mplusInj.{uA, uB, uI} I _L W)
                  (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                    (mplus.{uA, uB, uI} I _L W)))))))

  /-- The weighted summand inclusion commutes with the interpreted
  morphism: reindexing the weight moves the inclusion to the codomain
  object. -/
  theorem deltaIntoWeight_comp (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
      (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I Z W)
      (u : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
              (fun _ => interpObj I O (c i) Z) u)
            (deltaInto I O B c i Z))
          (interpMor I O (delta I O B c) Z W h) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O (interpMor I O (c i) Z W h)
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) W)
              (fun _ => interpObj I O (c i) W)
              (FreeCoprodCompDisc.Hom.comp I u h)))
          (deltaInto I O B c i W) :=
    (FreeCoprodCompDisc.Hom.comp_assoc O
        (FreeCoprodCompDisc.coprodInj O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
          (fun _ => interpObj I O (c i) Z) u)
        (deltaInto I O B c i Z) (interpMor I O (delta I O B c) Z W h)).trans
      ((congrArg
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
              (fun _ => interpObj I O (c i) Z) u))
          (deltaInto_natural I O B c i Z W h).symm).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
              (fun _ => interpObj I O (c i) Z) u)
            (FreeCoprodCompDisc.copowerHomMapMor
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
              (interpMor I O (c i)) Z W h)
            (deltaInto I O B c i W)).symm.trans
          (congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t (deltaInto I O B c i W))
            (FreeCoprodCompDisc.coprodInj_mor O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) Z)
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) W)
              (fun e' => FreeCoprodCompDisc.Hom.comp I e' h)
              (fun _ => interpObj I O (c i) Z)
              (fun _ => interpObj I O (c i) W)
              (fun _ => interpMor I O (c i) Z W h) u))))

  /-- The forward component of `IR.mprecompIso` at a right-appended
  superscript, with the `IR.mplus_snoc` transport moved to the other
  side. -/
  theorem mprecompIso_snoc_hom_comp (L : List (SupObj.{uB, uI} I))
      (b : SupObj.{uB, uI} I) (γ : IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun cc => interpObj I O cc X) (mprecomp_snoc I O L b γ))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X)))
          (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O (L ++ [b]) γ X))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X)))) :=
    ((congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O t
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X)))))
        (mprecompIso_snoc_hom I O L b γ X)).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun cc => interpObj I O cc X) (mprecomp_snoc I O L b γ))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X)))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ)
                (mplus_snoc.{uA, uB, uI} I L b X).symm))))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X))))).trans
        (congrArg
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun cc => interpObj I O cc X)
                  (mprecomp_snoc I O L b γ))))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X))))
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O L γ
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O γ)
                  (mplus_snoc.{uA, uB, uI} I L b X).symm)))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O γ)
                  (mplus_snoc.{uA, uB, uI} I L b X))))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O L γ
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
                (isoOfEq_symm_hom_comp.{uA, uB, uO} O
                  (interpObj I O γ (mplus.{uA, uB, uI} I (L ++ [b]) X))
                  (interpObj I O γ (mplus.{uA, uB, uI} I L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                  (congrArg (interpObj I O γ)
                    (mplus_snoc.{uA, uB, uI} I L b X)))).trans
              (FreeCoprodCompDisc.Hom.comp_id O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O L γ
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))))))).symm

  /-- The tower morphism induced by a weight at a right-appended
  superscript: the `IR.mplus_snoc` transport followed by the tower action
  on the bridge cotuple at the base. -/
  def navBridgeMor (B : Type uB) (i : B → I) (L : List (SupObj.{uB, uI} I))
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (e : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
      FreeCoprodCompDisc.Hom I
        (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
        (mplus.{uA, uB, uI} I L X) :=
    FreeCoprodCompDisc.Hom.comp I
      (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I
        (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)))
      (mplusMorMap.{uA, uB, uI} I L
        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
        (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
          (FreeCoprodCompDisc.coprodPairDesc I e (FreeCoprodCompDisc.Hom.id I X))))

  /-- The tower injection at a right-appended superscript, followed by the
  weight's tower morphism, is the tower injection at the base stack. -/
  theorem mplusInj_navBridge (B : Type uB) (i : B → I)
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (e : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
      FreeCoprodCompDisc.Hom.comp I
          (mplusInj.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
          (navBridgeMor.{uA, uB, uI} I B i L X e) =
        mplusInj.{uA, uB, uI} I L X :=
    (FreeCoprodCompDisc.Hom.comp_assoc I
        (mplusInj.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
        (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I
          (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)))
        (mplusMorMap.{uA, uB, uI} I L
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
          (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
            (FreeCoprodCompDisc.coprodPairDesc I e
              (FreeCoprodCompDisc.Hom.id I X))))).symm.trans
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp I t
            (mplusMorMap.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X)))))
          ((comp_isoOfEq_hom.{uA, uB, uI} I X
              (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
              (mplus.{uA, uB, uI} I L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
              (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)
              (mplusInj.{uA, uB, uI} I
                (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)).trans
            (mplusInj_snoc.{uA, uB, uI} I L
              (⟨B, i⟩ : SupObj.{uB, uI} I) X))).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc I
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I (⟨B, i⟩ : SupObj.{uB, uI} I) X)
            (mplusInj.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
            (mplusMorMap.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X))))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp I
                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I
                  (⟨B, i⟩ : SupObj.{uB, uI} I) X))
              (mplusInj_natural.{uA, uB, uI} I L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
                (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X))))).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc I
                (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I
                  (⟨B, i⟩ : SupObj.{uB, uI} I) X)
                (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X)))
                (mplusInj.{uA, uB, uI} I L X)).symm.trans
              ((congrArg
                  (fun t => FreeCoprodCompDisc.Hom.comp I t
                    (mplusInj.{uA, uB, uI} I L X))
                  (Subtype.ext rfl :
                    FreeCoprodCompDisc.Hom.comp I
                        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I
                          (⟨B, i⟩ : SupObj.{uB, uI} I) X)
                        (FreeCoprodCompDisc.Hom.comp I
                          (plusLiftBridgeInvHom I B i X)
                          (FreeCoprodCompDisc.coprodPairDesc I e
                            (FreeCoprodCompDisc.Hom.id I X))) =
                      FreeCoprodCompDisc.Hom.id I X)).trans
                (FreeCoprodCompDisc.Hom.id_comp I
                  (mplusInj.{uA, uB, uI} I L X)))))))

  /-- The tower navigation weight, followed by the weight's tower
  morphism, is the weight followed by the tower injection at the base
  stack. -/
  theorem navWeight_navBridge (B : Type uB) (i : B → I)
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (e : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
      FreeCoprodCompDisc.Hom.comp I
          (navWeight I B i B _root_.id X L)
          (navBridgeMor.{uA, uB, uI} I B i L X e) =
        FreeCoprodCompDisc.Hom.comp I e (mplusInj.{uA, uB, uI} I L X) :=
    (FreeCoprodCompDisc.Hom.comp_assoc I
        (navWeight I B i B _root_.id X L)
        (FreeCoprodCompDisc.Iso.hom I (FreeCoprodCompDisc.isoOfEq I
          (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)))
        (mplusMorMap.{uA, uB, uI} I L
          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
          (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
            (FreeCoprodCompDisc.coprodPairDesc I e
              (FreeCoprodCompDisc.Hom.id I X))))).symm.trans
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp I t
            (mplusMorMap.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X)))))
          ((comp_isoOfEq_hom.{uA, uB, uI} I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
              (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
              (mplus.{uA, uB, uI} I L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
              (mplus_snoc.{uA, uB, uI} I L (⟨B, i⟩ : SupObj.{uB, uI} I) X)
              (navWeight I B i B _root_.id X L)).trans
            (navWeight_snoc I B i B _root_.id X L))).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc I
            (⟨fun z => Sum.inl (_root_.id z.down), rfl⟩ :
              FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
            (mplusInj.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
            (mplusMorMap.{uA, uB, uI} I L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X))))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp I
                (⟨fun z => Sum.inl (_root_.id z.down), rfl⟩ :
                  FreeCoprodCompDisc.Hom I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)))
              (mplusInj_natural.{uA, uB, uI} I L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
                (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X))))).trans
            ((FreeCoprodCompDisc.Hom.comp_assoc I
                (⟨fun z => Sum.inl (_root_.id z.down), rfl⟩ :
                  FreeCoprodCompDisc.Hom I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X)))
                (mplusInj.{uA, uB, uI} I L X)).symm.trans
              (congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp I t
                  (mplusInj.{uA, uB, uI} I L X))
                (Subtype.ext rfl :
                  FreeCoprodCompDisc.Hom.comp I
                      (⟨fun z => Sum.inl (_root_.id z.down), rfl⟩ :
                        FreeCoprodCompDisc.Hom I
                          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                            I ⟨B, i⟩ X))
                      (FreeCoprodCompDisc.Hom.comp I
                        (plusLiftBridgeInvHom I B i X)
                        (FreeCoprodCompDisc.coprodPairDesc I e
                          (FreeCoprodCompDisc.Hom.id I X))) =
                    e))))))

  /-- The tower-conjugated navigation inclusion, followed by the tower
  isomorphism at the extended stack, is the weighted copower injection
  and the summand inclusion at the tower coproduct. -/
  theorem navInj_comp_hom (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp O (navInj I O Bout iout Bin K g L X)
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O Bin K) X)) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)) X))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                (mplus.{uA, uB, uI} I
                  (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (fun _ => interpObj I O (K (iout ∘ g))
                (mplus.{uA, uB, uI} I
                  (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (navWeight I Bout iout Bin g X L))
            (deltaInto I O Bin K (iout ∘ g)
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))) :=
    (congrArg
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)) X))
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.coprodInj O
                (FreeCoprodCompDisc.Hom I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                  (mplus.{uA, uB, uI} I
                    (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                (fun _ => interpObj I O (K (iout ∘ g))
                  (mplus.{uA, uB, uI} I
                    (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
                (navWeight I Bout iout Bin g X L))
              (deltaInto I O Bin K (iout ∘ g)
                (mplus.{uA, uB, uI} I
                  (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))
        (FreeCoprodCompDisc.Iso.invHom_hom O
          (mprecompIso.{uA, uB, uI, uO} I O
            (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
            (delta I O Bin K) X))).trans
      (FreeCoprodCompDisc.Hom.comp_id O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O
              (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)) X))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.coprodInj O
              (FreeCoprodCompDisc.Hom I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Bin, iout ∘ g⟩)
                (mplus.{uA, uB, uI} I
                  (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (fun _ => interpObj I O (K (iout ∘ g))
                (mplus.{uA, uB, uI} I
                  (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X))
              (navWeight I Bout iout Bin g X L))
            (deltaInto I O Bin K (iout ∘ g)
              (mplus.{uA, uB, uI} I
                (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) X)))))

  /-- The semantic pre-unit component, followed by the tower
  isomorphism, is the interpreted tower injection. -/
  theorem preUnitComponent_comp_hom (γ : IR.{max uA uB, uB, uI, uO} I O)
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp O (preUnitComponent I O γ L X)
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O L γ X)) =
        interpMor I O γ X (mplus.{uA, uB, uI} I L X)
          (mplusInj.{uA, uB, uI} I L X) :=
    (congrArg
        (FreeCoprodCompDisc.Hom.comp O
          (interpMor I O γ X (mplus.{uA, uB, uI} I L X)
            (mplusInj.{uA, uB, uI} I L X)))
        (FreeCoprodCompDisc.Iso.invHom_hom O
          (mprecompIso.{uA, uB, uI, uO} I O L γ X))).trans
      (FreeCoprodCompDisc.Hom.comp_id O
        (interpMor I O γ X (mplus.{uA, uB, uI} I L X)
          (mplusInj.{uA, uB, uI} I L X)))

  /-- The reduced form of the per-weight identity-image equation: after
  the tower isomorphisms cancel, both routes are the interpreted tower
  injection followed by the reindexed weighted summand inclusion. -/
  theorem interpHomPreUnit_deltaWeightRight (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomPreUnitMotive I O (d x))
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (i : B → I)
      (e : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
      FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (d (ULift.up i))
            (mprecomp I O (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
              (mk I O (Sum.inr (Sum.inr B)) d))
            (deltaNav I O (d (ULift.up i)) B i B (fun i' => d (ULift.up i'))
              _root_.id L
              (preUnitStack I O (d (ULift.up i))
                (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])))).1 X)
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O
                (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                (mk I O (Sum.inr (Sum.inr B)) d) X))
            (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
              (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
              (mplus.{uA, uB, uI} I L X)
              (navBridgeMor.{uA, uB, uI} I B i L X e))) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
            (fun _ => interpObj I O (d (ULift.up i)) X) e)
          (FreeCoprodCompDisc.Hom.comp O
            (deltaInto I O B (fun j => d (ULift.up j)) i X)
            (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d) X
              (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X))) :=
    (congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O t
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (mprecompIso.{uA, uB, uI, uO} I O
                (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                (mk I O (Sum.inr (Sum.inr B)) d) X))
            (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
              (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
              (mplus.{uA, uB, uI} I L X)
              (navBridgeMor.{uA, uB, uI} I B i L X e))))
        ((interpHom_deltaNav I O (d (ULift.up i)) B i B
            (fun i' => d (ULift.up i')) _root_.id L
            (preUnitStack I O (d (ULift.up i))
              (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])) X).trans
          (congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (navInj I O B i B (fun i' => d (ULift.up i')) _root_.id L X))
            (ih (ULift.up i) (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)))).trans
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O
            (preUnitComponent I O (d (ULift.up i))
              (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
            (FreeCoprodCompDisc.Hom.comp O t
              (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
                (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                (mplus.{uA, uB, uI} I L X)
                (navBridgeMor.{uA, uB, uI} I B i L X e))))
          (navInj_comp_hom I O B i B (fun i' => d (ULift.up i')) _root_.id
            L X)).trans
        ((congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.coprodInj O
                    (FreeCoprodCompDisc.Hom I
                      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                      (mplus.{uA, uB, uI} I
                        (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X))
                    (fun _ => interpObj I O (d (ULift.up i))
                      (mplus.{uA, uB, uI} I
                        (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X))
                    (navWeight I B i B _root_.id X L))
                  (deltaInto I O B (fun j => d (ULift.up j)) i
                    (mplus.{uA, uB, uI} I
                      (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)))
                (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
                  (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                  (mplus.{uA, uB, uI} I L X)
                  (navBridgeMor.{uA, uB, uI} I B i L X e))))
            (preUnitComponent_comp_hom I O (d (ULift.up i))
              (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                (interpMor I O (d (ULift.up i)) X
                  (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                  (mplusInj.{uA, uB, uI} I
                    (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)))
              (deltaIntoWeight_comp I O B (fun j => d (ULift.up j)) i
                (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                (mplus.{uA, uB, uI} I L X)
                (navBridgeMor.{uA, uB, uI} I B i L X e)
                (navWeight I B i B _root_.id X L))).trans
            ((congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O t
                    (FreeCoprodCompDisc.coprodInj O
                      (FreeCoprodCompDisc.Hom I
                        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                        (mplus.{uA, uB, uI} I L X))
                      (fun _ => interpObj I O (d (ULift.up i))
                        (mplus.{uA, uB, uI} I L X))
                      (FreeCoprodCompDisc.Hom.comp I
                        (navWeight I B i B _root_.id X L)
                        (navBridgeMor.{uA, uB, uI} I B i L X e))))
                  (deltaInto I O B (fun j => d (ULift.up j)) i
                    (mplus.{uA, uB, uI} I L X)))
                (interpMor_comp I O (d (ULift.up i)) X
                  (mplus.{uA, uB, uI} I (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                  (mplus.{uA, uB, uI} I L X)
                  (mplusInj.{uA, uB, uI} I
                    (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                  (navBridgeMor.{uA, uB, uI} I B i L X e)).symm).trans
              ((congrArg
                  (fun t => FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      (interpMor I O (d (ULift.up i)) X
                        (mplus.{uA, uB, uI} I L X) t)
                      (FreeCoprodCompDisc.coprodInj O
                        (FreeCoprodCompDisc.Hom I
                          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                          (mplus.{uA, uB, uI} I L X))
                        (fun _ => interpObj I O (d (ULift.up i))
                          (mplus.{uA, uB, uI} I L X))
                        (FreeCoprodCompDisc.Hom.comp I
                          (navWeight I B i B _root_.id X L)
                          (navBridgeMor.{uA, uB, uI} I B i L X e))))
                    (deltaInto I O B (fun j => d (ULift.up j)) i
                      (mplus.{uA, uB, uI} I L X)))
                  (mplusInj_navBridge.{uA, uB, uI} I B i L X e)).trans
                ((congrArg
                    (fun t => FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Hom.comp O
                        (interpMor I O (d (ULift.up i)) X
                          (mplus.{uA, uB, uI} I L X)
                          (mplusInj.{uA, uB, uI} I L X))
                        (FreeCoprodCompDisc.coprodInj O
                          (FreeCoprodCompDisc.Hom I
                            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
                            (mplus.{uA, uB, uI} I L X))
                          (fun _ => interpObj I O (d (ULift.up i))
                            (mplus.{uA, uB, uI} I L X))
                          t))
                      (deltaInto I O B (fun j => d (ULift.up j)) i
                        (mplus.{uA, uB, uI} I L X)))
                    (navWeight_navBridge.{uA, uB, uI} I B i L X e)).trans
                  (deltaIntoWeight_comp I O B (fun j => d (ULift.up j)) i X
                    (mplus.{uA, uB, uI} I L X)
                    (mplusInj.{uA, uB, uI} I L X) e).symm))))))

  /-- The per-weight identity-image equation at a `δ`-domain: at each
  weight out of the lifted arity, the copower-adjunction transport of the
  navigated subcode pre-unit is the weight's injection followed by the
  summand inclusion and the semantic pre-unit component. -/
  theorem interpHomPreUnit_deltaWeight (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomPreUnitMotive I O (d x))
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (i : B → I)
      (e : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) :
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (d (ULift.up i))
                (precomp I O B i (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
                (preUnitDeltaData I O B d L i)).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O
                  (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X)))
            ((plusLiftBridgeNatInv I O B i
              (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))).1 X))
          (interpMor I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
            X
            (FreeCoprodCompDisc.coprodPairDesc I e
              (FreeCoprodCompDisc.Hom.id I X))) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
            (fun _ => interpObj I O (d (ULift.up i)) X) e)
          (FreeCoprodCompDisc.Hom.comp O
            (deltaInto I O B (fun j => d (ULift.up j)) i X)
            (preUnitComponent I O (mk I O (Sum.inr (Sum.inr B)) d) L X)) :=
    eq_comp_invHom O (interpObj I O (d (ULift.up i)) X)
      (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X)
      (interpObj I O (mk I O (Sum.inr (Sum.inr B)) d) (mplus.{uA, uB, uI} I L X))
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (d (ULift.up i))
              (precomp I O B i (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
              (preUnitDeltaData I O B d L i)).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O
                (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X)))
          ((plusLiftBridgeNatInv I O B i
            (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))).1 X))
        (interpMor I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          X
          (FreeCoprodCompDisc.coprodPairDesc I e (FreeCoprodCompDisc.Hom.id I X))))
      (FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          (fun _ => interpObj I O (d (ULift.up i)) X) e)
        (FreeCoprodCompDisc.Hom.comp O
          (deltaInto I O B (fun j => d (ULift.up j)) i X)
          (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d) X
            (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X))))
      (mprecompIso.{uA, uB, uI, uO} I O L (mk I O (Sum.inr (Sum.inr B)) d) X)
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (d (ULift.up i))
                (precomp I O B i
                  (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
                (preUnitDeltaData I O B d L i)).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O
                  (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X)))
            (FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O L
                  (mk I O (Sum.inr (Sum.inr B)) d) X))))
          (interpMor_comp I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
              X (plusLiftBridgeInvHom I B i X)
              (FreeCoprodCompDisc.coprodPairDesc I e
                (FreeCoprodCompDisc.Hom.id I X))).symm).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (d (ULift.up i))
                  (precomp I O B i
                    (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
                  (preUnitDeltaData I O B d L i)).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O
                    (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X))))
            (mprecompIso_natural.{uA, uB, uI, uO} I O L
              (mk I O (Sum.inr (Sum.inr B)) d)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
              (FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I B i X)
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X))))).trans
          ((congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O t
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O
                      (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) B i X)))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O L
                      (mk I O (Sum.inr (Sum.inr B)) d)
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)))
                  (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
                    (mplus.{uA, uB, uI} I L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                    (mplus.{uA, uB, uI} I L X)
                    (mplusMorMap.{uA, uB, uI} I L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
                      (FreeCoprodCompDisc.Hom.comp I
                        (plusLiftBridgeInvHom I B i X)
                        (FreeCoprodCompDisc.coprodPairDesc I e
                          (FreeCoprodCompDisc.Hom.id I X)))))))
              (interpHom_cast_cod I O (d (ULift.up i))
                (mprecomp I O (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                  (mk I O (Sum.inr (Sum.inr B)) d))
                X
                (precomp I O B i
                  (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)))
                (mprecomp_snoc I O L (⟨B, i⟩ : SupObj.{uB, uI} I)
                  (mk I O (Sum.inr (Sum.inr B)) d))
                (deltaNav I O (d (ULift.up i)) B i B (fun i' => d (ULift.up i'))
                  _root_.id L
                  (preUnitStack I O (d (ULift.up i))
                    (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]))))).trans
            ((congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (d (ULift.up i))
                    (mprecomp I O (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                      (mk I O (Sum.inr (Sum.inr B)) d))
                    (deltaNav I O (d (ULift.up i)) B i B
                      (fun i' => d (ULift.up i')) _root_.id L
                      (preUnitStack I O (d (ULift.up i))
                        (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])))).1 X)
                  (FreeCoprodCompDisc.Hom.comp O t
                    (interpMor I O (mk I O (Sum.inr (Sum.inr B)) d)
                      (mplus.{uA, uB, uI} I L
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                      (mplus.{uA, uB, uI} I L X)
                      (mplusMorMap.{uA, uB, uI} I L
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
                        (FreeCoprodCompDisc.Hom.comp I
                          (plusLiftBridgeInvHom I B i X)
                          (FreeCoprodCompDisc.coprodPairDesc I e
                            (FreeCoprodCompDisc.Hom.id I X)))))))
                (mprecompIso_snoc_hom_comp I O L (⟨B, i⟩ : SupObj.{uB, uI} I)
                  (mk I O (Sum.inr (Sum.inr B)) d) X)).trans
              ((congrArg
                  (fun t => FreeCoprodCompDisc.Hom.comp O
                    ((interpHom I O (d (ULift.up i))
                      (mprecomp I O (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                        (mk I O (Sum.inr (Sum.inr B)) d))
                      (deltaNav I O (d (ULift.up i)) B i B
                        (fun i' => d (ULift.up i')) _root_.id L
                        (preUnitStack I O (d (ULift.up i))
                          (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])))).1 X)
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (mprecompIso.{uA, uB, uI, uO} I O
                          (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)])
                          (mk I O (Sum.inr (Sum.inr B)) d) X))
                      t))
                  (interpMor_isoOfEq_dom I O (mk I O (Sum.inr (Sum.inr B)) d)
                    (mplus.{uA, uB, uI} I
                      (L ++ [(⟨B, i⟩ : SupObj.{uB, uI} I)]) X)
                    (mplus.{uA, uB, uI} I L X)
                    (mplus.{uA, uB, uI} I L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                    (mplus_snoc.{uA, uB, uI} I L
                      (⟨B, i⟩ : SupObj.{uB, uI} I) X)
                    (mplusMorMap.{uA, uB, uI} I L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X) X
                      (FreeCoprodCompDisc.Hom.comp I
                        (plusLiftBridgeInvHom I B i X)
                        (FreeCoprodCompDisc.coprodPairDesc I e
                          (FreeCoprodCompDisc.Hom.id I X)))))).trans
                (interpHomPreUnit_deltaWeightRight I O B d ih L X i e))))))

  /-- The per-summand identity-image equation at a `δ`-domain: the
  navigated subcode pre-unit's transported interpretation is the summand
  inclusion followed by the semantic pre-unit component. -/
  theorem interpHomPreUnit_deltaSummand (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomPreUnitMotive I O (d x))
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (i : B → I) :
      (interpHomDeltaSummand I O B (fun j => d (ULift.up j))
          (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) i
          (preUnitDeltaData I O B d L i)).1 X =
        FreeCoprodCompDisc.Hom.comp O
          (deltaInto I O B (fun j => d (ULift.up j)) i X)
          (preUnitComponent I O (mk I O (Sum.inr (Sum.inr B)) d) L X) :=
    (congrArg
        (FreeCoprodCompDisc.coprodDesc O
          (FreeCoprodCompDisc.Hom I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
          (fun _ => interpObj I O (d (ULift.up i)) X)
          (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X))
        (funext (fun e =>
          interpHomPreUnit_deltaWeight I O B d ih L X i e))).trans
      (FreeCoprodCompDisc.coprodDesc_eta O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ => interpObj I O (d (ULift.up i)) X)
        (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X)
        (FreeCoprodCompDisc.Hom.comp O
          (deltaInto I O B (fun j => d (ULift.up j)) i X)
          (preUnitComponent I O (mk I O (Sum.inr (Sum.inr B)) d) L X)))

  /-- The `δ`-domain case of the identity-image equation. -/
  theorem interpHomPreUnit_mk_delta (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomPreUnitMotive I O (d x)) :
      InterpHomPreUnitMotive I O (mk I O (Sum.inr (Sum.inr B)) d) :=
    fun L X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inr (Sum.inr B)) d)
            (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) t).1 X)
          (funext (fun i => preUnitStack_mk_delta I O B d L i))).trans
        ((interpHom_delta I O B (fun j => d (ULift.up j))
            (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))
            (preUnitDeltaData I O B d L) X).trans
          ((congrArg
              (deltaDesc I O B (fun j => d (ULift.up j)) X
                (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X))
              (funext (fun i =>
                interpHomPreUnit_deltaSummand I O B d ih L X i))).trans
            (deltaDesc_eta I O B (fun j => d (ULift.up j)) X
              (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d)) X)
              (preUnitComponent I O (mk I O (Sum.inr (Sum.inr B)) d) L X))))

  /-- The identity-image equation at an `ι`-domain, with the codomain
  code and the target morphism generalized: at the reflexive instance the
  codomain interpretation is the singleton object, so any two morphisms
  into it agree. -/
  theorem interpHomPreUnit_iotaGen (o : O)
      (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      ∀ (γ'' : IR.{max uA uB, uB, uI, uO} I O)
        (hh : iota.{max uA uB, uB, uI, uO} I O o = γ'')
        (t : FreeCoprodCompDisc.Hom O
          (interpObj I O (mk I O (Sum.inl o) d) X) (interpObj I O γ'' X)),
        (interpHom I O (mk I O (Sum.inl o) d) γ''
          (cast (congrArg (Hom I O (mk I O (Sum.inl o) d)) hh)
            (ULift.up (PLift.up rfl) :
              Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inl o) d)
                (iota.{max uA uB, uB, uI, uO} I O o)))).1 X = t :=
    fun _ hh =>
      Eq.rec (motive := fun (γ'' : IR.{max uA uB, uB, uI, uO} I O)
          (hh' : iota.{max uA uB, uB, uI, uO} I O o = γ'') =>
          ∀ t : FreeCoprodCompDisc.Hom O
            (interpObj I O (mk I O (Sum.inl o) d) X) (interpObj I O γ'' X),
            (interpHom I O (mk I O (Sum.inl o) d) γ''
              (cast (congrArg (Hom I O (mk I O (Sum.inl o) d)) hh')
                (ULift.up (PLift.up rfl) :
                  Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inl o) d)
                    (iota.{max uA uB, uB, uI, uO} I O o)))).1 X = t)
        (fun _ => Subtype.ext (funext (fun _ => congrArg ULift.up rfl))) hh

  /-- The `ι`-domain case of the identity-image equation. -/
  theorem interpHomPreUnit_mk_iota (o : O)
      (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O) :
      InterpHomPreUnitMotive I O (mk I O (Sum.inl o) d) :=
    fun L X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inl o) d)
            (mprecomp I O L (mk I O (Sum.inl o) d)) t).1 X)
          (preUnitStack_mk_iota I O o d L)).trans
        (interpHomPreUnit_iotaGen I O o d X
          (mprecomp I O L (mk I O (Sum.inl o) d))
          (mprecomp_iota_mk I O L o d).symm
          (preUnitComponent I O (mk I O (Sum.inl o) d) L X))

  /-- The per-summand identity-image equation at a `σ`-domain: the stack
  `σ`-push of the subcode's pre-unit is the semantic `σ`-injection
  followed by the pre-unit component. -/
  theorem interpHomPreUnit_sigmaSummand (A : Type (max uA uB))
      (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomPreUnitMotive I O (d x))
      (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (a : A) :
      (interpHom I O (d (ULift.up a))
          (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d))
          (msigmaPush I O (d (ULift.up a)) A (fun a' => d (ULift.up a')) a L
            (preUnitStack I O (d (ULift.up a)) L))).1 X =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O A
            (fun a' => interpObj I O (d (ULift.up a')) X) a)
          (preUnitComponent I O (mk I O (Sum.inr (Sum.inl A)) d) L X) :=
    (interpHom_msigmaPush I O (d (ULift.up a)) A (fun a' => d (ULift.up a')) a L
        (preUnitStack I O (d (ULift.up a)) L) X).trans
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O L (d (ULift.up a)) X))
                (FreeCoprodCompDisc.coprodInj O A
                  (fun a' => interpObj I O (d (ULift.up a'))
                    (mplus.{uA, uB, uI} I L X)) a))
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O L
                  (mk I O (Sum.inr (Sum.inl A)) d) X))))
          (ih (ULift.up a) L X)).trans
        ((congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O
              (interpMor I O (d (ULift.up a)) X (mplus.{uA, uB, uI} I L X)
                (mplusInj.{uA, uB, uI} I L X))
              (FreeCoprodCompDisc.Hom.comp O t
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.coprodInj O A
                    (fun a' => interpObj I O (d (ULift.up a'))
                      (mplus.{uA, uB, uI} I L X)) a)
                  (FreeCoprodCompDisc.Iso.invHom O
                    (mprecompIso.{uA, uB, uI, uO} I O L
                      (mk I O (Sum.inr (Sum.inl A)) d) X)))))
            (FreeCoprodCompDisc.Iso.invHom_hom O
              (mprecompIso.{uA, uB, uI, uO} I O L (d (ULift.up a)) X))).trans
          (congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O L
                  (mk I O (Sum.inr (Sum.inl A)) d) X)))
            (interpMor_sigma_inj I O A (fun a' => d (ULift.up a')) a X
              (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X)).symm)))

  /-- The `σ`-domain case of the identity-image equation. -/
  theorem interpHomPreUnit_mk_sigma (A : Type (max uA uB))
      (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
        InterpHomPreUnitMotive I O (d x)) :
      InterpHomPreUnitMotive I O (mk I O (Sum.inr (Sum.inl A)) d) :=
    fun L X =>
      (congrArg
          (fun t => (interpHom I O (mk I O (Sum.inr (Sum.inl A)) d)
            (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d)) t).1 X)
          (funext (fun a => preUnitStack_mk_sigma I O A d L a))).trans
        ((interpHom_sigma I O A (fun a => d (ULift.up a))
            (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d))
            (fun a => msigmaPush I O (d (ULift.up a)) A
              (fun a' => d (ULift.up a')) a L
              (preUnitStack I O (d (ULift.up a)) L)) X).trans
          ((congrArg
              (FreeCoprodCompDisc.coprodDesc O A
                (fun a => interpObj I O (d (ULift.up a)) X)
                (interpObj I O
                  (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d)) X))
              (funext (fun a =>
                interpHomPreUnit_sigmaSummand I O A d ih L X a))).trans
            (FreeCoprodCompDisc.coprodDesc_eta O A
              (fun a => interpObj I O (d (ULift.up a)) X)
              (interpObj I O (mprecomp I O L (mk I O (Sum.inr (Sum.inl A)) d)) X)
              (preUnitComponent I O (mk I O (Sum.inr (Sum.inl A)) d) L X))))

  /-- `IR.interpHom` sends `IR.preUnitStack` to the semantic pre-unit
  component, by `IR.induction`. -/
  theorem interpHom_preUnitStack (γ : IR.{max uA uB, uB, uI, uO} I O) :
      InterpHomPreUnitMotive I O γ :=
    induction I O (InterpHomPreUnitMotive I O)
      (fun s => match s with
        | Sum.inl o => fun d _ => interpHomPreUnit_mk_iota I O o d
        | Sum.inr (Sum.inl A) => fun d ih => interpHomPreUnit_mk_sigma I O A d ih
        | Sum.inr (Sum.inr B) => fun d ih => interpHomPreUnit_mk_delta I O B d ih)
      γ
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `IR.InterpHomPreUnitMotive` — the identity-image equation at one
    code, generalized over the stack.
  * `IR.navBridgeMor` — the tower morphism induced by a weight at a
    right-appended superscript.
  ```

  and to `## Main statements`:

  ```markdown
  * `IR.interpHom_preUnitStack` — `IR.interpHom` sends
    `IR.preUnitStack` to the semantic pre-unit component, by
    `IR.induction` on the domain code.
  * `IR.interpHomPreUnit_mk_iota`, `IR.interpHomPreUnit_mk_sigma`,
    `IR.interpHomPreUnit_mk_delta` — the three cases of that
    induction.
  * `IR.preUnitComponent_comp_hom`, `IR.navInj_comp_hom`,
    `IR.mprecompIso_snoc_hom_comp` — the factorizations through the
    forward hom of the tower isomorphism that merge the
    `IR.mprecomp_snoc` transport with the Lemma 4 layer.
  * `IR.mplusInj_navBridge`, `IR.navWeight_navBridge` — the iterated
    injection and the navigation weight against `IR.navBridgeMor`.
  * `IR.mplusInj_natural`, `IR.coprodPairInr_mor`,
    `IR.deltaIntoWeight_comp` — naturality of the iterated
    injection, of the fresh right injection, and of the weighted
    summand inclusion.
  * `IR.interpHom_cast_cod`, `IR.comp_isoOfEq_hom`,
    `IR.isoOfEq_symm_hom_comp`, `IR.interpMor_isoOfEq_dom` — the
    transport eliminations the induction consumes.
  ```

  and to `## Implementation notes`:

  ```markdown
  The `linter.checkUnivs false` option on `IR.comp_isoOfEq_hom` and
  `IR.isoOfEq_symm_hom_comp` suppresses the `checkUnivs` warning on
  the separated arity universes `uA`/`uB`: in those two declarations'
  types the pair appears only together under `max`, so the linter
  reports it as unifiable; keeping the two distinct is the point of
  the separation. `IndRec.Basic` carries the same suppression, for
  the same reason.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files; the two
  `set_option linter.checkUnivs false in` lines suppress the only
  warnings that would otherwise arise.

- [ ] **Step 5: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent, then:

  ```bash
  jj commit -m "feat(indrec): prove the identity-image equation of the interpretation"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 9: composition and the category laws

The branch's client-facing API, and the paper's Corollary 2:
`IR.comp` is `IR.natToHom` of the vertical composite of the
interpreted transformations, `IR.interpHom_comp` is
`IR.interpHom_natToHom` applied to that composite, and the three
laws are the corresponding laws for natural transformations
conjugated by the Theorem 3 equivalence —
`FreeCoprodCompDisc.NatTrans.vcomp_assoc` for `IR.comp_assoc`, and
`NatTrans.id_vcomp`/`NatTrans.vcomp_id` with `IR.natToHom_interpHom`
for `IR.id_comp`/`IR.comp_id`. The identity laws first rewrite by
`IR.interpHom_id`, which is Task 8's induction at the empty stack.
No new recursion arises.

The [HancockMcBrideGhaniMalatestaAltenkirch2013] citation appears in
the docstring of `IR.comp` and in the `Category` module docstring —
its `## Main statements` entry for the three laws and its
`## References` section — which is what carries it for
`IR.comp_assoc`, `IR.id_comp`, and `IR.comp_id`, per
§ Global Constraints. The docstrings below are transcribed as they
stand.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean`

**Interfaces:**

- Consumes: Task 8's `IR.interpHom_preUnitStack`; Task 3's
  `IR.preUnitComponent_nil`; `IR.Hom`, `IR.id`, `IR.interpHom`,
  `IR.natToHom`, `IR.interpHom_natToHom`, `IR.natToHom_interpHom`,
  `IR.interpObj`, `IR.interpMor`,
  `FreeCoprodCompDisc.NatTrans.id`,
  `FreeCoprodCompDisc.NatTrans.vcomp`,
  `FreeCoprodCompDisc.NatTrans.vcomp_assoc`,
  `FreeCoprodCompDisc.NatTrans.id_vcomp`,
  `FreeCoprodCompDisc.NatTrans.vcomp_id`.
- Produces (in `namespace IR`): `comp`, `interpHom_comp`,
  `comp_assoc`, `interpHom_id`, `id_comp`, `comp_id`.

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Category.lean` (after
  `samplePreUnitComponentCompHom`):

  ```lean
  /-- The composite of the sample identity morphism with itself. -/
  def sampleCompHom :
      Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode sampleCategoryCode :=
    comp Bool Bool sampleCategoryCode sampleCategoryCode
      sampleCategoryCode (IR.id Bool Bool sampleCategoryCode)
      (IR.id Bool Bool sampleCategoryCode)

  /-- The composite of the sample identity with itself is that
  identity. -/
  theorem sampleCompHom_eq_id :
      sampleCompHom = IR.id Bool Bool sampleCategoryCode :=
    id_comp Bool Bool sampleCategoryCode sampleCategoryCode
      (IR.id Bool Bool sampleCategoryCode)

  /-- `IR.interpHom` sends the sample identity to the identity
  transformation. -/
  theorem sampleInterpHomId :
      interpHom Bool Bool sampleCategoryCode sampleCategoryCode
          (IR.id Bool Bool sampleCategoryCode) =
        FreeCoprodCompDisc.NatTrans.id
          (interpObj Bool Bool sampleCategoryCode)
          (interpMor Bool Bool sampleCategoryCode) :=
    interpHom_id Bool Bool sampleCategoryCode

  /-- `IR.interpHom` sends a composite at the sample code to the
  vertical composite. -/
  theorem sampleInterpHomComp
      (f g : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
        sampleCategoryCode) :
      interpHom Bool Bool sampleCategoryCode sampleCategoryCode
          (comp Bool Bool sampleCategoryCode sampleCategoryCode
            sampleCategoryCode f g) =
        FreeCoprodCompDisc.NatTrans.vcomp
          (interpHom Bool Bool sampleCategoryCode sampleCategoryCode f)
          (interpHom Bool Bool sampleCategoryCode sampleCategoryCode g) :=
    interpHom_comp Bool Bool sampleCategoryCode sampleCategoryCode
      sampleCategoryCode f g

  /-- The right identity law at the sample code. -/
  theorem sampleCompIdHom
      (f : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
        sampleCategoryCode) :
      comp Bool Bool sampleCategoryCode sampleCategoryCode
          sampleCategoryCode f (IR.id Bool Bool sampleCategoryCode) =
        f :=
    comp_id Bool Bool sampleCategoryCode sampleCategoryCode f

  /-- Associativity at the sample code. -/
  theorem sampleCompAssocHom
      (f g h : Hom.{0, 0, 0, 0} Bool Bool sampleCategoryCode
        sampleCategoryCode) :
      comp Bool Bool sampleCategoryCode sampleCategoryCode
          sampleCategoryCode
          (comp Bool Bool sampleCategoryCode sampleCategoryCode
            sampleCategoryCode f g) h =
        comp Bool Bool sampleCategoryCode sampleCategoryCode
          sampleCategoryCode f
          (comp Bool Bool sampleCategoryCode sampleCategoryCode
            sampleCategoryCode g h) :=
    comp_assoc Bool Bool sampleCategoryCode sampleCategoryCode
      sampleCategoryCode sampleCategoryCode f g h
  ```

  Extend the test file's module docstring summary with one sentence:
  "Composition of code morphisms, its image under `IR.interpHom`,
  and the three category laws are exercised at the sample code."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.comp`.

- [ ] **Step 3: Implement.** Append to
  `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`, above `end IR`:

  ```lean
  /-- Composition of IR-code morphisms (Corollary 2 of
  [HancockMcBrideGhaniMalatestaAltenkirch2013]): the image under
  fullness of the vertical composite of the interpreted
  transformations. -/
  def comp (γ γ' γ'' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O γ γ')
      (g : Hom.{uA, uB, uI, uO} I O γ' γ'') :
      Hom.{uA, uB, uI, uO} I O γ γ'' :=
    natToHom I O γ γ''
      (FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f)
        (interpHom I O γ' γ'' g))

  /-- `IR.interpHom` sends `IR.comp` to the vertical composite: the
  interpretation is functorial on morphisms. -/
  theorem interpHom_comp (γ γ' γ'' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O γ γ')
      (g : Hom.{uA, uB, uI, uO} I O γ' γ'') :
      interpHom I O γ γ'' (comp I O γ γ' γ'' f g) =
        FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f)
          (interpHom I O γ' γ'' g) :=
    interpHom_natToHom I O γ γ''
      (FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f)
        (interpHom I O γ' γ'' g))

  /-- Associativity of `IR.comp`, by conjugation through the Theorem 3
  equivalence and associativity of vertical composition. -/
  theorem comp_assoc (γ γ' γ'' γ''' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O γ γ')
      (g : Hom.{uA, uB, uI, uO} I O γ' γ'')
      (h : Hom.{uA, uB, uI, uO} I O γ'' γ''') :
      comp I O γ γ'' γ''' (comp I O γ γ' γ'' f g) h =
        comp I O γ γ' γ''' f (comp I O γ' γ'' γ''' g h) :=
    (congrArg (fun t => natToHom I O γ γ'''
        (FreeCoprodCompDisc.NatTrans.vcomp t (interpHom I O γ'' γ''' h)))
      (interpHom_comp I O γ γ' γ'' f g)).trans
      ((congrArg (natToHom I O γ γ''')
          (FreeCoprodCompDisc.NatTrans.vcomp_assoc (interpHom I O γ γ' f)
            (interpHom I O γ' γ'' g) (interpHom I O γ'' γ''' h))).trans
        (congrArg (fun t => natToHom I O γ γ'''
            (FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f) t))
          (interpHom_comp I O γ' γ'' γ''' g h)).symm)

  /-- `IR.interpHom` sends `IR.id` to the identity transformation: the
  identity-image equation at the empty stack. -/
  theorem interpHom_id (γ : IR.{max uA uB, uB, uI, uO} I O) :
      interpHom I O γ γ (IR.id I O γ) =
        FreeCoprodCompDisc.NatTrans.id (interpObj I O γ) (interpMor I O γ) :=
    Subtype.ext (funext (fun X =>
      (interpHom_preUnitStack I O γ [] X).trans (preUnitComponent_nil I O γ X)))

  /-- `IR.id` is a left identity for `IR.comp`, by conjugation through the
  Theorem 3 equivalence and the left identity of vertical composition. -/
  theorem id_comp (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O γ γ') :
      comp I O γ γ γ' (IR.id I O γ) f = f :=
    (congrArg
        (fun t => natToHom I O γ γ'
          (FreeCoprodCompDisc.NatTrans.vcomp t (interpHom I O γ γ' f)))
        (interpHom_id I O γ)).trans
      ((congrArg (natToHom I O γ γ')
          (FreeCoprodCompDisc.NatTrans.id_vcomp
            (interpHom I O γ γ' f))).trans
        (natToHom_interpHom I O γ γ' f))

  /-- `IR.id` is a right identity for `IR.comp`, by conjugation through the
  Theorem 3 equivalence and the right identity of vertical composition. -/
  theorem comp_id (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O γ γ') :
      comp I O γ γ' γ' f (IR.id I O γ') = f :=
    (congrArg
        (fun t => natToHom I O γ γ'
          (FreeCoprodCompDisc.NatTrans.vcomp (interpHom I O γ γ' f) t))
        (interpHom_id I O γ')).trans
      ((congrArg (natToHom I O γ γ')
          (FreeCoprodCompDisc.NatTrans.vcomp_id
            (interpHom I O γ γ' f))).trans
        (natToHom_interpHom I O γ γ' f))
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `IR.comp` — composition of code morphisms: the code morphism
    carried by the vertical composite of the interpreted
    transformations.
  ```

  and to `## Main statements`:

  ```markdown
  * `IR.interpHom_comp`, `IR.interpHom_id` — `IR.interpHom` sends
    `IR.comp` to the vertical composite and `IR.id` to the identity
    transformation: the interpretation is functorial on morphisms.
  * `IR.id_comp`, `IR.comp_id`, `IR.comp_assoc` — the category laws
    of Corollary 2 of [HancockMcBrideGhaniMalatestaAltenkirch2013].
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files.

- [ ] **Step 5: Check the axioms.** The branch's gate lands here.

  Run: `lake lint`
  Expected: PASS — `GebMeta.detectNonstandardAxiom` reports no
  declaration of `Geb`/`GebTests` outside `{propext, Quot.sound}`.
  Confirm individually, by `lean_verify` or a scratch
  `#print axioms` snippet, the four Corollary 2 declarations
  `IndRec.IR.comp`, `IndRec.IR.id_comp`, `IndRec.IR.comp_id`, and
  `IndRec.IR.comp_assoc`, together with the identity-image equation
  `IndRec.IR.interpHom_id` that the identity laws consume: expected
  `{propext, Quot.sound}` for each.

- [ ] **Step 6: Commit.** Confirm with `jj status` that
  `proto_2d_gate.lean` is absent, then:

  ```bash
  jj commit -m "feat(indrec): add composition of code morphisms and the category laws"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 10: documentation and TODO closure

The workstream's persistent documentation. `docs/index.md` gains the
`Category` module's entry and records the two merged-module changes
of Tasks 1 and 2; `TODO.md` § Category of `IR` codes closes, its
content having moved to `docs/index.md`, and the results the
workstream leaves deferred stay listed. This task is documentation
only: its cycle is edit, gates, commit, with no red step.

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: Tasks 1–9.
- Produces: the branch's persistent documentation and a closed
  `TODO.md` entry.

- [ ] **Step 1: Add the `Category` module entry to
  `docs/index.md`.** Insert immediately after the
  `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean` entry (which
  ends "…equivalence (`IR.innerHomEquiv`). `Classical.choice`-free.")
  and before the `Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean`
  entry:

  ```markdown
  - `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean` — Corollary 2
    of Hancock–McBride–Ghani–Malatesta–Altenkirch: `IR` codes over a
    fixed input/output index pair, with the homsets of Definition 8,
    form a category. Composition (`IR.comp`) is the code morphism
    carried by the vertical composite of the interpreted
    transformations, and the category laws (`IR.id_comp`,
    `IR.comp_id`, `IR.comp_assoc`) follow from the vertical laws
    together with the round-trip laws of the Theorem 3 equivalence;
    `IR.interpHom_comp` and `IR.interpHom_id` record that the
    interpretation is functorial on morphisms. The identity laws
    consume the identity-image equation `IR.interpHom_id`, proved by
    induction on the domain code with the stack of `IR.preUnitStack`
    generalized (`IR.interpHom_preUnitStack`), against the semantic
    counterpart of that stack: the iterated coproduct tower
    (`IR.mplus`, `IR.mplusInj`, `IR.mplusMorMap`) with its iterated
    Lemma 4 isomorphism (`IR.mprecompIso`) and the semantic pre-unit
    component (`IR.preUnitComponent`). The induction consumes the
    characterizing equations of `IR.interpHom` at each code
    constructor (`IR.interpHom_iota`, `IR.interpHom_sigma`,
    `IR.interpHom_delta`) and a characterization of each injection
    helper of `Hom.lean` as composition with an explicit semantic
    inclusion (`IR.interpHom_sigmaPush`,
    `IR.interpHom_deltaEmptyPush`, `IR.interpHom_msigmaPush`,
    `IR.interpHom_deltaNavBase`, `IR.interpHom_deltaNav`).
    `Classical.choice`-free.
  ```

- [ ] **Step 2: Revise the two merged-module entries in
  `docs/index.md`.**

  In the `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` entry,
  replace

  ```markdown
  `coprodPairInl`/`coprodPairInr` and the universal cotuple
  ```

  with

  ```markdown
  `coprodPairInl`/`coprodPairInr` (whose two summands may sit at
  different index universes) and the universal cotuple
  ```

  In the `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean` entry, replace

  ```markdown
  `IR.mprecomp` (folding `IR.precomp` over a list of superscript
  objects `IR.SupObj`). `Classical.choice`-free.
  ```

  with

  ```markdown
  `IR.mprecomp` (folding `IR.precomp` over a list of superscript
  objects `IR.SupObj`). The recursions of `IR.sigmaPush`,
  `IR.deltaEmptyPush`, and `IR.preUnitStack` run over named motives
  and steps, so each carries its computation equations at the three
  code constructors (`IR.sigmaPush_mk_iota` and its siblings).
  `Classical.choice`-free.
  ```

- [ ] **Step 3: Close `TODO.md` § Category of `IR` codes.** Replace
  the whole section — its heading and both paragraphs, from
  "### Category of `IR` codes" through "The branch 2d transfer
  consumes `IR.natToHom`." — with

  ```markdown
  ### Theorems 2 and 4 for `IR` codes

  Independent of the roadmap sequence above; parallel to
  Complete Theorem 2.4 for `IndRec`, and building on the category of
  `IR` codes in `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean`
  (see `docs/index.md`). Two results of
  [HancockMcBrideGhaniMalatestaAltenkirch2013] remain: Theorem 2,
  the left-Kan-extension characterization of the `δ`-code
  interpretation, and Theorem 4, the equivalence with dependent
  polynomial functors.
  ```

  The mathlib `Category`/`Functor` wrapper and the constructive
  uniqueness of `IR.elim`/`IR.rec` are already listed under
  § Complete Theorem 2.4 for `IndRec` and are left as they stand.

  The numbering used throughout this workstream is that of the TLCA
  2013 paper (LNCS 7941, DOI 10.1007/978-3-642-38946-7_13), against
  which it has been checked: Definition 8 is the homsets, Theorem 2
  the left Kan extension `⟦δ P F⟧ ≅ ∐_{i : P → I} Lan_{(+i)} ⟦F i⟧`,
  Theorem 3 the full-and-faithful interpretation, Theorem 4 the
  equivalence with `Poly I O`, and Corollary 2 the category of `IR`
  codes. The extended preprint at strath.ac.uk numbers the same
  results differently (Theorem 15, Theorem 21), so a re-check reads
  the TLCA 2013 numbering, not the preprint's.

- [ ] **Step 4: Final docstring sweep.** Re-read the module
  docstrings of `FreeCoprodCompDisc.lean`, `Hom.lean`,
  `Category.lean`, and their test mirrors; confirm each describes
  the module as it now stands (all sections non-vacuous, no stale
  deferral language, citations in `[Key]` form with the keys listed
  under `## References`).

- [ ] **Step 5: Regenerate TOCs and lint.**

  Run: `doctoc --update-only . && markdownlint-cli2 '**/*.md'`
  Expected: `TODO.md`'s TOC entry for § Category of `IR` codes is
  replaced by the new heading; lint passes.

  Run: `doctoc --dryrun --update-only .`
  Expected: no file would change.

- [ ] **Step 6: Commit.**

  ```bash
  jj commit -m "doc(indrec): add the branch 2d docs and close the category entry"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Task 11: removal of the transient workstream documents

The workstream ends with branch 2d, so its spec, its plans, and its
handoffs leave the working tree in the branch's final commit, per
CONTRIBUTING § Concern shape: they record how the current state was
reached, not what it is, and remain reachable in history. This task
is documentation only: its cycle is delete, gates, commit, with no
red step.

This plan is among the files deleted. Read Steps 1–4 into context
before running Step 2; after it, the plan's text is no longer on
disk.

**Files:**

- Remove: `docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`
- Remove: `docs/superpowers/plans/2026-07-18-indrec-precomp.md`
- Remove: `docs/superpowers/plans/2026-07-19-indrec-morphisms-2a.md`
- Remove: `docs/superpowers/plans/2026-07-20-indrec-morphisms-2b.md`
- Remove: `docs/superpowers/plans/2026-07-20-indrec-relocation.md`
- Remove: `docs/superpowers/plans/2026-07-20-indrec-morphisms-2c.md`
- Remove: `docs/superpowers/plans/2026-07-21-indrec-morphisms-2d.md`
- Remove: every file under `docs/superpowers/handoffs/`

**Interfaces:**

- Consumes: Tasks 1–10.
- Produces: a working tree carrying only persistent documentation.

- [ ] **Step 1: Confirm no persisting document references any file
  being removed.** Enumerate the handoffs first, since the removal
  list names them by directory:

  ```bash
  ls docs/superpowers/handoffs/
  ```

  Expected at the time of writing:
  `2026-07-20-indrec-morphisms-2b.md`,
  `2026-07-20-indrec-morphisms-2c.md`,
  `2026-07-20-indrec-morphisms-2d.md`,
  `2026-07-20-indrec-relocation.md`. Then, for each file name in
  the removal list:

  ```bash
  grep -rn --exclude-dir=.jj --exclude-dir=.lake '<file-name>' . \
    | grep -v '^\./docs/superpowers/'
  ```

  Expected: no output for every name — every reference is from one
  transient document to another, and all of them go together. If a
  persisting document does reference one, fix that reference in this
  task before deleting.

- [ ] **Step 2: Remove the files.**

  ```bash
  rm docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md
  rm docs/superpowers/plans/2026-07-18-indrec-precomp.md \
     docs/superpowers/plans/2026-07-19-indrec-morphisms-2a.md \
     docs/superpowers/plans/2026-07-20-indrec-morphisms-2b.md \
     docs/superpowers/plans/2026-07-20-indrec-relocation.md \
     docs/superpowers/plans/2026-07-20-indrec-morphisms-2c.md \
     docs/superpowers/plans/2026-07-21-indrec-morphisms-2d.md
  rm docs/superpowers/handoffs/*.md
  ```

  `jj` tracks the deletions from the working copy; no `jj rm` step
  is needed. Empty directories are not tracked, so
  `docs/superpowers/` disappears from the tree.

- [ ] **Step 3: Verify the removal.**

  Run: `jj status`
  Expected: the removals listed, and no other change; in particular
  `proto_2d_gate.lean` absent.

  Run: `markdownlint-cli2 '**/*.md' && doctoc --dryrun --update-only .`
  Expected: both pass.

- [ ] **Step 4: Commit.**

  ```bash
  jj commit -m "doc(indrec): remove the IR-code morphisms spec, plans, and handoffs"
  jj bookmark set feat/indrec-morphisms-2d
  ```

---

## Final verification (whole branch)

- [ ] Run the full gate sequence on the completed branch:

  ```bash
  lake build && lake test && lake lint && scripts/lint-imports.sh
  ```

  Expected: all pass; the axiom linter reports no declaration
  outside `{propext, Quot.sound}`.

- [ ] `#print axioms` (via `lean_verify` or a scratch snippet) on
  `IR.comp`, `IR.interpHom_comp`, `IR.comp_assoc`, `IR.interpHom_id`,
  `IR.id_comp`, `IR.comp_id`, `IR.interpHom_preUnitStack`, and
  `FreeCoprodCompDisc.coprodPairInr`: expected ⊆
  `{propext, Quot.sound}`.
- [ ] Run `markdownlint-cli2 '**/*.md'` and
  `doctoc --dryrun --update-only .`; both pass.
- [ ] Run `scripts/pre-push.sh` once more on the completed branch
  (it catches umbrella-registration gaps and the TOC check).
- [ ] Confirm the committed Lean of the branch contains no `sorry`,
  no `admit`, no tactic block, no `noncomputable`, and no
  `Classical` invocation:

  ```bash
  jj diff --from main --name-only \
    | grep '\.lean$' \
    | xargs grep -nE ':=[[:space:]]*by\b|^[[:space:]]*by\b|\bsorry\b|\badmit\b|noncomputable|(^|[^`])Classical\.'
  ```

  Expected: exactly three lines, all docstring prose in
  `Category.lean` that wraps onto a line beginning with the English
  word "by" — in the docstrings of `IR.interpHomIotaCast_sigmaPush`,
  `IR.interpHomIotaCast_deltaEmptyPush`, and
  `IR.interpPrecompIso_deltaNavAll_inj`. Any other line is a defect.
  The pattern matches tactic-block openings and qualified
  `Classical` uses rather than the words themselves: a bare
  `\bby\b` matches the English word wherever a docstring line wraps
  on it (`Hom.lean` has eleven such lines,
  `FreeCoprodCompDisc.lean` five), and a bare `Classical` matches the
  prose "`Classical.choice`-free", which
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` carries in its
  module docstring; the backtick exclusion is what keeps those out of
  the result. The `^[[:space:]]*by\b` alternative is retained
  because it catches a tactic block opened on a continuation line,
  and the three docstring matches it admits are enumerated above
  rather than suppressed. `xargs` exits 123 when `grep` matches
  nothing, so this command must not sit in an `&&` chain.

- [ ] Confirm `proto_2d_gate.lean` is absent from the working tree
  (`jj status`) and from every commit of the branch
  (`jj log --stat` over the branch's commits).
- [ ] Confirm the workstream's spec, plans, and handoffs are absent
  from the working tree and that `docs/superpowers/` is empty of
  tracked files.
- [ ] Run the `lean4:review` skill and
  `pr-review-toolkit:review-pr` on the branch, per the phase table;
  fold fixes into their owning task commits with
  `jj absorb`/`jj squash`.
- [ ] **DO NOT PUSH.** The user reviews the branch line-by-line
  before any `jj git push`, per AGENTS.md § No `jj git push` without
  user line-by-line review.
