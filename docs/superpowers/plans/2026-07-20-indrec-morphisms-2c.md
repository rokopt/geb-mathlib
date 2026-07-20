# IR-code morphisms branch 2c (naturality and Theorem 3) Implementation Plan

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
- [Task 1: initial object, coproduct universal property, pair morphisms, fibers](#task-1-initial-object-coproduct-universal-property-pair-morphisms-fibers)
- [Task 2: the transformation layer: `NatTrans`, vertical structure, predicates](#task-2-the-transformation-layer-nattrans-vertical-structure-predicates)
- [Task 3: whiskering, horizontal composition, coherences, interchange](#task-3-whiskering-horizontal-composition-coherences-interchange)
- [Task 4: inverse pairs, iso families, transports, coproduct decomposition](#task-4-inverse-pairs-iso-families-transports-coproduct-decomposition)
- [Task 5: the copower–Yoneda adjunction](#task-5-the-copoweryoneda-adjunction)
- [Task 6: the `Naturality` module and the per-summand delta decomposition](#task-6-the-naturality-module-and-the-per-summand-delta-decomposition)
- [Task 7: the Lemma 4 naturality upgrade](#task-7-the-lemma-4-naturality-upgrade)
- [Task 8: the initial-object evaluation and `InnerHom` fiber equivalences](#task-8-the-initial-object-evaluation-and-innerhom-fiber-equivalences)
- [Task 9: the plus-lift bridge](#task-9-the-plus-lift-bridge)
- [Task 10: Theorem 3](#task-10-theorem-3)
- [Task 11: docs, TODO reduction, and gates](#task-11-docs-todo-reduction-and-gates)
- [Final verification (whole branch)](#final-verification-whole-branch)

<!-- END doctoc -->

**Goal:** natural transformations between interpretations of `IR`
codes and Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]
(the interpretation extended to morphisms, full and faithful), with
the horizontal-composition API of the transformation notion and the
naturality upgrades of Lemmas 3 and 4.

**Architecture:** per the design spec
(`docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`,
§ Naturality and Theorem 3 (branch 2c)). The transformation notion is
generic over `FreeCoprodCompDisc.Map`/`MapMor` pairs; Theorem 3 goes
by `IR.rec` on the domain code with motive
`∀ γ', Hom γ γ' ≃ NatTrans ⟦γ⟧ ⟦γ'⟧`: the `ι`-case by evaluation at a
new initial object, the `σ`-case by the indexed-coproduct
decomposition, and the `δ`-case through the per-summand Lemma 3
decomposition, the copower–Yoneda adjunction, the plus-lift bridge,
and the Lemma 4 naturality upgrade, landing definitionally on the
homset's clause 3 for the inductive hypothesis.

**Verification status:** the complete committed form of every
declaration below — at the real universe scheme, term-mode — has been
compiled against the built branch-1/2a/2b/relocation code this
session, with zero diagnostics (session scratch
`proto_2c_gate.lean`; deleted before any commit). The exact
declarations are reproduced per task below. The residual work is
tests, docstrings, docs entries, and gates.

**Tech Stack:** Lean 4, mathlib, the project's `IndRec` and
`FreeCoprodCompDisc` developments (branches 1, 2a, 2b, relocation).

## Global Constraints

Copied from the design spec and the verified prototype; every task's
requirements include these.

- Constructive only: no `noncomputable`, no `Classical`; the axiom
  linter (`lake lint`) permits `{propext, Quot.sound}` only for
  `Geb`/`GebTests`. Newly reused mathlib declarations
  (`Equiv.piCongrRight`, `Equiv.sigmaCongrLeft`,
  `Equiv.symm_apply_apply`/`apply_symm_apply`) were compiled inside
  the axiom-clean prototype; re-verify with `#print axioms` on the
  first task that uses each.
- Recursor-only recursion: `IR.rec` drives the Type-valued
  recursions (`innerHomEquiv`, `interpHomEquiv`), `IR.induction` the
  `Prop`-valued ones (`interpPrecompIso_natural`); `match` only for
  non-recursive case analysis (`Shape`/`Sigma`/`Subtype`/`Sum`
  patterns) and `Eq.rec` for equality elimination. No
  `induction`/`induction'` tactic, no self-referential `def`, no
  `termination_by`.
- Explicit proof terms: committed declarations are term-mode, no
  `by` blocks. Motives are named `UpperCamelCase` `def`s; steps and
  laws are named declarations, per the factoring constraint.
- Universe discipline: full-or-absent `.{…}` lists. Verified
  instantiations: `iota.{max uA uB, uB, uI, uO}` and
  `interpMor_iota.{max uA uB, uB, uI, uO}` are REQUIRED in fresh
  statements (inference stalls on `max ?u ?v =?= max uA uB`);
  `lift.{uB, uI, max uA uB}`; `plus.{uI, uB, max uA uB}` in
  `precompRhsMap` (the section variable comes first in `plus`'s
  list); `copower.{u, w, u}`, `Hom.{u, v, u}`, `plus.{v, u, u}` in
  the generic layer. No auto-bound `u_1`; remove unused
  `universe`/`variable`.
- Elaboration-order rules (verified): (1) in the Lemma 4 naturality
  step, rewrite `interpPrecompIso` to step form FIRST (it appears on
  both sides), then eliminate the morphism's commutation equality,
  then split on the shape, and only then rewrite `interpMor` — the
  precomposed code is a stuck match until the shape is known, after
  which it is definitionally a constructor form (per-constructor
  equations apply to it; `interpMor_mk` to the `mk` side). (2)
  `congrArg` lambdas that apply a rewritten term need explicit
  binder types (`fun (t : MorMapSig I O …) ↦ …`). (3)
  Anonymous-constructor `Hom`s passed as proof arguments need type
  ascription (`(⟨h1, rfl⟩ : FreeCoprodCompDisc.Hom I ⟨X1, Y.2 ∘ h1⟩
  Y)`). (4) `Eq.rec` motives at projection-reduced types, with
  dependent `rfl`-proofs `∀`-quantified inside the motive when their
  types mention the generalized index.
- Definitional facts the proofs rely on (do not "simplify" them
  away): `Hom.comp` is definitionally associative and unital;
  definitional proof irrelevance collapses casts along proofs of
  defeq `Prop`s (and makes two such casts interchangeable);
  ULift/Unit/Sigma/Subtype structure eta; `elim`/`elimAlg` (hence
  `interpObj`, `IR.Hom`, `InnerHom`, `precomp`) compute
  definitionally at `mk`-built codes, while `IR.rec` (hence
  `interpMor`, `interpPrecompIso`, `innerHomEquiv`,
  `interpHomEquiv`) computes only propositionally via `rec_mk`;
  `sigma I O A (fun a ↦ c (ULift.up a))` and
  `delta I O B (fun i ↦ c (ULift.up i))` are defeq to the
  corresponding `mk` forms by ULift eta (the `ι` form is NOT — its
  direction family needs `mk_congr` + `funext`/`nomatch`).
- mathlib style: 2-space indent, 100-column lines, `fun x ↦ …`,
  mandatory docstrings on every `def` and every theorem of public
  interest, naming per mathlib. `unusedVariables` lint is an error:
  use `_` binders (e.g. `plusMapMor`'s `fun _ _ h ↦ …`).
- Citations: [HancockMcBrideGhaniMalatestaAltenkirch2013] appears
  only on the Theorem 3 statements and the Lemma 3/4 upgrades (the
  paper-derived content); the `NatTrans`/coproduct/adjunction
  machinery is the project's own construction, outside the citation
  rules' scope.
- VCS: `jj` only for mutations; commit messages in mathlib
  conventional form; `jj absorb`/`squash --into` folds review fixes
  into owning task commits. No pushes.
- Gates per task: `lake build` and `lake test` pass before each
  commit; red steps run `lake test`. `sorry` only transiently.
- Module system: new modules get `module` headers, `public import`,
  and registration in BOTH the source umbrella AND the test
  umbrella; `scripts/lint-imports.sh` passes.

## File structure

- Modify `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` —
  object-level additions: initial object, indexed-coproduct
  universal property and compatibilities, `coprodPairMor` and laws,
  singleton fiber description, underlying morphisms of isomorphisms
  (Task 1).
- Create `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean` —
  the transformation layer: `IsNatTrans`/`NatTrans`, vertical
  structure and laws, preservation predicates, composite maps,
  whiskering/horizontal composition/coherences/interchange, inverse
  pairs and iso-family conversion, transport equivalences,
  `NatTrans.congrSource`, `natCoprodEquiv`, the copower–Yoneda
  adjunction (Tasks 2–5).
- Create mirrored `GebTests/Mathlib/CategoryTheory/…` test modules
  and register in the test umbrella (Tasks 1–5).
- Create `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean` — the
  IR-side development: delta decomposition, Lemma 4 naturality
  upgrade, ∅-evaluation and `InnerHom` fiber equivalences, plus-lift
  bridge, Theorem 3 (Tasks 6–10), importing `Functor` and `Hom`.
- Create `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean` —
  mirrored tests, including the `TODO.md` morphism-action sample
  (Tasks 6–10).
- Modify `Geb/Mathlib/Logic/Equiv/Basic.lean` and
  `GebTests/Mathlib/Logic/Equiv/Basic.lean` — the generic `Equiv`
  combinators `sigmaSubtypeEquiv` and `arrowPEmptyEquiv` with tests
  (Task 8), per the spec's placement rule for generic combinators.
- Modify both `IndRec` umbrellas (Task 6) and both `CategoryTheory`
  umbrellas (Task 2) — check the exact umbrella files with `ls`
  before editing; in 2a the source-umbrella registration was missed.
- Modify `docs/index.md` and `TODO.md` (Task 11); the spec and this
  plan remain in the working tree until the end of branch 2d.

(Placement rationale: the object-level additions extend the existing
module's concern; the transformation layer is a new concern at
`CategoryTheory` level — a sibling module keeps
`FreeCoprodCompDisc.lean` narrow; the IR-side is the spec's
`Naturality` module. The directory file coexists with the flat
`FreeCoprodCompDisc.lean` module per mathlib practice
(`Mathlib/CategoryTheory/NatTrans.lean`); converting
`FreeCoprodCompDisc.lean` itself into a directory index is out of
this branch's concern. The plan's adversarial review checks these
decisions.)

## Task outline

Tasks below are dependency-ordered; each carries its own TDD cycle
and commit (Task 8 carries two commits, split by scope). Exact code
per task is reproduced from the verified prototype.

- Task 1: initial object, coproduct universal property, pair
  morphisms, fibers (`FreeCoprodCompDisc.lean`).
- Task 2: the transformation layer: `NatTrans`, vertical structure,
  predicates, composite maps (new `FreeCoprodCompDisc/NatTrans.lean`).
- Task 3: whiskering, horizontal composition, coherences,
  interchange, the identity object map and its whiskering laws.
- Task 4: inverse pairs, iso families, transports, coproduct
  decomposition (`NatTrans.congrSource`, `natCoprodEquiv`).
- Task 5: the copower–Yoneda adjunction.
- Task 6: the `Naturality` module and the per-summand delta
  decomposition (`interpObj_snd_cast` … `natDeltaEquiv`), umbrella
  registration.
- Task 7: the Lemma 4 naturality upgrade (`precompRhsMap` …
  `interpPrecompIso_natural`).
- Task 8: the initial-object evaluation and `InnerHom` fiber
  equivalences (`natIotaEquiv`, `innerHomEquiv`,
  `sigmaSubtypeEquiv`, `arrowPEmptyEquiv`).
- Task 9: the plus-lift bridge (`plusLiftBridgeHom` …
  `plusLiftBridgeNat_isInverse`).
- Task 10: Theorem 3 (`InterpHomEquivMotive` … `interpHomEquiv`,
  `interpHom`/`natToHom` and the round-trip laws), with the
  morphism-action test sample.
- Task 11: docs (`docs/index.md`, docstring sweep), `TODO.md`
  reduction, and gates.

---

## Prototype-file discipline

The session prototype `proto_2c_gate.lean` at the repository root is
the verified source of every declaration below, and every declaration
is reproduced verbatim in the task bodies. The prototype is session
scratch: no commit may contain it. Delete it from the working tree
when implementation starts, and check `jj status` before Task 1's
commit (and each later commit) to confirm it is absent.

---

## Task 1: initial object, coproduct universal property, pair morphisms, fibers

The object-level infrastructure the transformation layer consumes:
the initial object with its universal morphism and uniqueness; the
universal property of the indexed coproduct at one index universe
(the large-index coproduct of the `δ`-clause is handled by the
per-summand Lemma 3 upgrade instead) with its composition
compatibilities; the functorial action of `coprodPair` on morphisms,
universe-heterogeneous in the objects, mirroring `coprodPair`; the
singleton-domain fiber description consumed throughout the `ι`-case;
and the underlying morphisms of an isomorphism with their inverse
laws.

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`

**Interfaces:**

- Consumes: `Hom`, `Hom.id`, `Hom.comp`, the category laws (branches
  1 and 2b), `coprod`, `coprodMor`, `coprodPair`, `coprodPairInl`,
  `coprodPairInr`, `coprodPairDesc`, `Iso`, `Iso.symm`;
  `Equiv.symm_apply_apply`/`Equiv.apply_symm_apply` (mathlib, first
  use — axiom-check in Step 4).
- Produces (all in `namespace FreeCoprodCompDisc`,
  `variable (D : Type v)`):

  ```lean
  emptyObj : FreeCoprodCompDisc.{u, v} D
  emptyDesc (X : FreeCoprodCompDisc.{u, v} D) : Hom D (emptyObj D) X
  emptyDesc_unique (X) (f : Hom D (emptyObj D) X) : f = emptyDesc D X
  coprodInj (ι : Type w) (fi) (i : ι) :
    Hom.{u, v, max u w} D (fi i) (coprod D ι fi)
  coprodDesc.{u'} (ι : Type w) (fi) (Z) (m : (i : ι) → Hom D (fi i) Z) :
    Hom D (coprod D ι fi) Z
  coprodHomEquiv.{u'} (ι : Type w) (fi) (Z) :
    Hom D (coprod D ι fi) Z ≃ ((i : ι) → Hom D (fi i) Z)
  coprodInj_desc / coprodDesc_eta / coprodMor_desc / coprodDesc_comp /
    coprodInj_mor — the composition compatibilities at one index
    universe (statements below)
  coprodPairMor.{uX, uY, uX', uY'} (f : Hom D X X') (g : Hom D Y Y') :
    Hom D (coprodPair D X Y) (coprodPair D X' Y')
  coprodPairMor_id / coprodPairMor_comp / coprodPairMor_desc /
    coprodPairMor_id_desc / coprodPairMor_inr_desc_inl
    (statements below)
  homSingletonEquiv (d : D) (Z : FreeCoprodCompDisc.{u, v} D) :
    Hom D (⟨ULift Unit, fun _ ↦ d⟩ : FreeCoprodCompDisc.{u, v} D) Z ≃
      {z : Z.1 // Z.2 z = d}
  Iso.hom (e : Iso D X Y) : Hom D X Y
  Iso.invHom (e : Iso D X Y) : Hom D Y X
  Iso.hom_invHom / Iso.invHom_hom — the inverse laws
    (statements below)
  ```

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` (after
  the existing sample declarations; `sampleX`, `sampleHom`,
  `sampleW`, `sampleZ`, `sampleWtoX`, and `sampleXtoZ` already exist
  there):

  ```lean
  /-- Uniqueness of the morphism out of the initial object at `sampleX`. -/
  theorem sampleEmptyDesc_unique
      (f : FreeCoprodCompDisc.Hom Bool (FreeCoprodCompDisc.emptyObj Bool) sampleX) :
      f = FreeCoprodCompDisc.emptyDesc Bool sampleX :=
    FreeCoprodCompDisc.emptyDesc_unique Bool sampleX f

  /-- Restricting the cotuple along an injection recovers the component. -/
  theorem sampleCoprodInj_desc (b : Bool) :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.coprodInj Bool Bool (fun _ ↦ sampleX) b)
          (FreeCoprodCompDisc.coprodDesc Bool Bool (fun _ ↦ sampleX) sampleX
            (fun _ ↦ sampleHom)) =
        sampleHom :=
    FreeCoprodCompDisc.coprodInj_desc Bool Bool (fun _ ↦ sampleX) sampleX
      (fun _ ↦ sampleHom) b

  /-- The inverse direction of the coproduct universal property evaluates
  componentwise. -/
  theorem sampleCoprodHomEquiv_symm_apply :
      ((FreeCoprodCompDisc.coprodHomEquiv Bool Bool (fun _ ↦ sampleX)
          sampleX).symm (fun _ ↦ sampleHom)).1 ⟨true, false⟩ = false :=
    rfl

  /-- A cotuple followed by a morphism is the cotuple of the composites. -/
  theorem sampleCoprodDesc_comp :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.coprodDesc Bool Bool (fun _ ↦ sampleX) sampleX
            (fun _ ↦ sampleHom))
          sampleXtoZ =
        FreeCoprodCompDisc.coprodDesc Bool Bool (fun _ ↦ sampleX) sampleZ
          (fun _ ↦ FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleXtoZ) :=
    FreeCoprodCompDisc.coprodDesc_comp Bool Bool (fun _ ↦ sampleX) sampleX
      sampleZ (fun _ ↦ sampleHom) sampleXtoZ

  /-- `coprodPairMor` preserves identities at the sample objects. -/
  theorem sampleCoprodPairMor_id :
      FreeCoprodCompDisc.coprodPairMor Bool
          (FreeCoprodCompDisc.Hom.id Bool sampleW)
          (FreeCoprodCompDisc.Hom.id Bool sampleX) =
        FreeCoprodCompDisc.Hom.id Bool
          (FreeCoprodCompDisc.coprodPair Bool sampleW sampleX) :=
    FreeCoprodCompDisc.coprodPairMor_id Bool sampleW sampleX

  /-- `coprodPairMor` preserves composition at the sample morphisms. -/
  theorem sampleCoprodPairMor_comp :
      FreeCoprodCompDisc.coprodPairMor Bool
          (FreeCoprodCompDisc.Hom.comp Bool sampleWtoX sampleXtoZ)
          (FreeCoprodCompDisc.Hom.comp Bool sampleWtoX sampleXtoZ) =
        FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.coprodPairMor Bool sampleWtoX sampleWtoX)
          (FreeCoprodCompDisc.coprodPairMor Bool sampleXtoZ sampleXtoZ) :=
    FreeCoprodCompDisc.coprodPairMor_comp Bool sampleWtoX sampleXtoZ
      sampleWtoX sampleXtoZ

  /-- Reindexing along the right injection then cotupling the left
  injection against the identity is the identity. -/
  theorem sampleCoprodPairMor_inr_desc_inl :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.coprodPairMor Bool
            (FreeCoprodCompDisc.Hom.id Bool sampleW)
            (FreeCoprodCompDisc.coprodPairInr Bool sampleW sampleX))
          (FreeCoprodCompDisc.coprodPairDesc Bool
            (FreeCoprodCompDisc.coprodPairInl Bool sampleW sampleX)
            (FreeCoprodCompDisc.Hom.id Bool
              (FreeCoprodCompDisc.coprodPair.{0, 0, 0} Bool sampleW sampleX))) =
        FreeCoprodCompDisc.Hom.id Bool
          (FreeCoprodCompDisc.coprodPair.{0, 0, 0} Bool sampleW sampleX) :=
    FreeCoprodCompDisc.coprodPairMor_inr_desc_inl Bool

  /-- The singleton fiber description evaluates its inverse direction at a
  fiber element. -/
  theorem sampleHomSingletonEquiv_symm_apply :
      ((FreeCoprodCompDisc.homSingletonEquiv Bool true sampleX).symm
          ⟨true, rfl⟩).1 (ULift.up Unit.unit) = true :=
    rfl

  /-- A sample object with constant decoding, carrying a non-identity
  isomorphism. -/
  def sampleC : FreeCoprodCompDisc.{0, 0} Bool :=
    ⟨Bool, fun _ ↦ true⟩

  /-- A sample non-identity isomorphism: Boolean negation on `sampleC`. -/
  def sampleIsoNot : FreeCoprodCompDisc.Iso.{0, 0, 0} Bool sampleC sampleC :=
    ⟨⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩, rfl⟩

  /-- The underlying morphisms of the sample isomorphism compose to the
  identity. -/
  theorem sampleIsoNot_hom_invHom :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Iso.hom Bool sampleIsoNot)
          (FreeCoprodCompDisc.Iso.invHom Bool sampleIsoNot) =
        FreeCoprodCompDisc.Hom.id Bool sampleC :=
    FreeCoprodCompDisc.Iso.hom_invHom Bool sampleIsoNot
  ```

  Extend the test file's module docstring summary with one sentence:
  "The initial object, the indexed-coproduct universal property,
  `coprodPairMor`, the singleton fiber description, and the
  underlying morphisms of isomorphisms are exercised at the sample
  objects."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant
  `FreeCoprodCompDisc.emptyObj`.

- [ ] **Step 3: Implement.** In
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`, insert the
  groups below near their related existing declarations; the
  suggested points follow, but place sensibly against the file as it
  stands. Universe caution: the file's existing declarations bind
  `.{w}` per declaration (`coprod.{w}`, `coprodMor.{w}`,
  `copower.{w}`, `lift.{w}`, `homLiftEquiv.{w}`), so `w` must NOT be
  added to the file-level `universe u v` line (a file-level `w`
  makes those `.{w}` binders "already declared" errors). The three
  declarations below that use `w` free are wrapped in a `section`
  with a scoped `universe w`, closed before the first existing
  `.{w}` declaration that follows the insertion point.

  After `coprodMor_comp` (the coprod group), insert:

  ```lean
  /-- The initial object of the free coproduct completion: the empty
  family. -/
  def emptyObj : FreeCoprodCompDisc.{u, v} D :=
    ⟨PEmpty, PEmpty.elim⟩

  /-- The unique morphism out of the initial object (the nullary
  cotuple). -/
  def emptyDesc (X : FreeCoprodCompDisc.{u, v} D) : Hom D (emptyObj D) X :=
    ⟨PEmpty.elim, funext (fun a ↦ a.elim)⟩

  /-- Uniqueness of the morphism out of the initial object. -/
  theorem emptyDesc_unique (X : FreeCoprodCompDisc.{u, v} D)
      (f : Hom D (emptyObj D) X) : f = emptyDesc D X :=
    Subtype.ext (funext (fun a ↦ a.elim))

  section

  universe w

  /-- The injection into the `i`-th summand of an indexed coproduct. -/
  def coprodInj (ι : Type w) (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (i : ι) : Hom.{u, v, max u w} D (fi i) (coprod D ι fi) :=
    ⟨fun a ↦ ⟨i, a⟩, rfl⟩

  /-- The cotuple: the universal morphism out of an indexed
  coproduct. -/
  def coprodDesc.{u'} (ι : Type w) (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (Z : FreeCoprodCompDisc.{u', v} D)
      (m : (i : ι) → Hom D (fi i) Z) : Hom D (coprod D ι fi) Z :=
    ⟨fun p ↦ (m p.1).1 p.2, funext (fun p ↦ congrFun (m p.1).2 p.2)⟩

  /-- The universal property of the indexed coproduct: morphisms out of
  `coprod ι fi` correspond to `ι`-indexed families of morphisms out of
  the summands (`copowerEquiv` is the constant-family case). -/
  def coprodHomEquiv.{u'} (ι : Type w)
      (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (Z : FreeCoprodCompDisc.{u', v} D) :
      Hom D (coprod D ι fi) Z ≃ ((i : ι) → Hom D (fi i) Z) :=
    { toFun := fun h i ↦
        ⟨fun a ↦ h.1 ⟨i, a⟩, funext (fun a ↦ congrFun h.2 ⟨i, a⟩)⟩,
      invFun := coprodDesc D ι fi Z,
      left_inv := fun _ ↦ Subtype.ext rfl,
      right_inv := fun _ ↦ funext (fun _ ↦ Subtype.ext rfl) }

  end

  /-- Restricting a cotuple along an injection recovers the
  component (at one index universe). -/
  theorem coprodInj_desc (ι : Type u)
      (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (Z : FreeCoprodCompDisc.{u, v} D) (m : (i : ι) → Hom D (fi i) Z)
      (i : ι) :
      Hom.comp D (coprodInj D ι fi i) (coprodDesc D ι fi Z m) = m i :=
    Subtype.ext rfl

  /-- Every morphism out of an indexed coproduct is the cotuple of its
  restrictions (at one index universe). -/
  theorem coprodDesc_eta (ι : Type u)
      (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (Z : FreeCoprodCompDisc.{u, v} D)
      (h : Hom D (coprod D ι fi) Z) :
      coprodDesc D ι fi Z
          (fun i ↦ Hom.comp D (coprodInj D ι fi i) h) = h :=
    Subtype.ext rfl

  /-- A reindexed coproduct morphism followed by a cotuple is the
  cotuple of the reindexed composites. -/
  theorem coprodMor_desc (ι κ : Type u) (r : ι → κ)
      (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (gk : κ → FreeCoprodCompDisc.{u, v} D)
      (hom : (i : ι) → Hom D (fi i) (gk (r i)))
      (Z : FreeCoprodCompDisc.{u, v} D)
      (m : (k : κ) → Hom D (gk k) Z) :
      Hom.comp D (coprodMor D ι κ r fi gk hom) (coprodDesc D κ gk Z m) =
        coprodDesc D ι fi Z (fun i ↦ Hom.comp D (hom i) (m (r i))) :=
    Subtype.ext rfl

  /-- A cotuple followed by a morphism is the cotuple of the
  composites. -/
  theorem coprodDesc_comp (ι : Type u)
      (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (Z W : FreeCoprodCompDisc.{u, v} D)
      (m : (i : ι) → Hom D (fi i) Z) (g : Hom D Z W) :
      Hom.comp D (coprodDesc D ι fi Z m) g =
        coprodDesc D ι fi W (fun i ↦ Hom.comp D (m i) g) :=
    Subtype.ext rfl

  /-- An injection followed by a reindexed coproduct morphism is the
  component followed by the reindexed injection. -/
  theorem coprodInj_mor (ι κ : Type u) (r : ι → κ)
      (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (gk : κ → FreeCoprodCompDisc.{u, v} D)
      (hom : (i : ι) → Hom D (fi i) (gk (r i))) (i : ι) :
      Hom.comp D (coprodInj D ι fi i) (coprodMor D ι κ r fi gk hom) =
        Hom.comp D (hom i) (coprodInj D κ gk (r i)) :=
    Subtype.ext rfl
  ```

  After `coprodPairDesc_eta`, insert:

  ```lean
  /-- The functorial action of `coprodPair` on morphisms. The four
  objects may sit at four different index universes, mirroring
  `coprodPair`. -/
  def coprodPairMor.{uX, uY, uX', uY'} {X : FreeCoprodCompDisc.{uX, v} D}
      {X' : FreeCoprodCompDisc.{uX', v} D}
      {Y : FreeCoprodCompDisc.{uY, v} D}
      {Y' : FreeCoprodCompDisc.{uY', v} D}
      (f : Hom D X X') (g : Hom D Y Y') :
      Hom D (coprodPair D X Y) (coprodPair D X' Y') :=
    ⟨Sum.map f.1 g.1,
      funext (fun s ↦
        Sum.casesOn s (fun a ↦ congrFun f.2 a) (fun b ↦ congrFun g.2 b))⟩

  /-- `coprodPairMor` preserves identities (at one index universe per
  side). -/
  theorem coprodPairMor_id.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
      (Y : FreeCoprodCompDisc.{uY, v} D) :
      coprodPairMor D (Hom.id D X) (Hom.id D Y) =
        Hom.id D (coprodPair D X Y) :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

  /-- `coprodPairMor` preserves composition (at one index universe, where
  `Hom.comp` is available). -/
  theorem coprodPairMor_comp {X X' X'' Y Y' Y'' : FreeCoprodCompDisc.{u, v} D}
      (f : Hom D X X') (f' : Hom D X' X'') (g : Hom D Y Y')
      (g' : Hom D Y' Y'') :
      coprodPairMor D (Hom.comp D f f') (Hom.comp D g g') =
        Hom.comp D (coprodPairMor D f g) (coprodPairMor D f' g') :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

  /-- `coprodPairMor` commutes with the cotuple: reindexing then
  descending is descending the composites (left component fixed). -/
  theorem coprodPairMor_desc {X Y Y' Z : FreeCoprodCompDisc.{u, v} D}
      (g : Hom D Y Y') (l : Hom D X Z) (m : Hom D Y' Z) :
      Hom.comp D (coprodPairMor D (Hom.id D X) g) (coprodPairDesc D l m) =
        coprodPairDesc D l (Hom.comp D g m) :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

  /-- Reindexing the right summand and then cotupling against the
  identity is cotupling against the identity and then composing. -/
  theorem coprodPairMor_id_desc {Z X Y : FreeCoprodCompDisc.{u, v} D}
      (h : Hom D X Y) (e : Hom D Z X) :
      Hom.comp D (coprodPairMor D (Hom.id D Z) h)
          (coprodPairDesc D (Hom.comp D e h) (Hom.id D Y)) =
        Hom.comp D (coprodPairDesc D e (Hom.id D X)) h :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

  /-- Reindexing the right summand along the right injection and then
  cotupling the left injection against the identity is the identity. -/
  theorem coprodPairMor_inr_desc_inl {Z X : FreeCoprodCompDisc.{u, v} D} :
      Hom.comp D (coprodPairMor D (Hom.id D Z) (coprodPairInr D Z X))
          (coprodPairDesc D (coprodPairInl D Z X)
            (Hom.id D (coprodPair.{v, u, u} D Z X))) =
        Hom.id D (coprodPair.{v, u, u} D Z X) :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))
  ```

  After `isoOfEq` (following `Iso.refl`/`Iso.symm`/`Iso.trans`),
  insert:

  ```lean
  /-- The underlying morphism of an isomorphism. -/
  def Iso.hom {X Y : FreeCoprodCompDisc.{u, v} D} (e : Iso D X Y) :
      Hom D X Y :=
    ⟨fun a ↦ e.1 a, e.2⟩

  /-- The underlying morphism of the inverse of an isomorphism. -/
  def Iso.invHom {X Y : FreeCoprodCompDisc.{u, v} D} (e : Iso D X Y) :
      Hom D Y X :=
    ⟨fun b ↦ e.1.symm b, (Iso.symm D e).2⟩

  /-- The underlying morphisms of an isomorphism compose to the
  identity, forward-then-backward. -/
  theorem Iso.hom_invHom {X Y : FreeCoprodCompDisc.{u, v} D}
      (e : Iso D X Y) :
      Hom.comp D (Iso.hom D e) (Iso.invHom D e) = Hom.id D X :=
    Subtype.ext (funext (fun a ↦ e.1.symm_apply_apply a))

  /-- The underlying morphisms of an isomorphism compose to the
  identity, backward-then-forward. -/
  theorem Iso.invHom_hom {X Y : FreeCoprodCompDisc.{u, v} D}
      (e : Iso D X Y) :
      Hom.comp D (Iso.invHom D e) (Iso.hom D e) = Hom.id D Y :=
    Subtype.ext (funext (fun b ↦ e.1.apply_symm_apply b))
  ```

  After `homLiftEquiv` (before `end FreeCoprodCompDisc`), insert:

  ```lean
  /-- Morphisms out of a singleton object are the fiber of the decoding
  over its value. -/
  def homSingletonEquiv (d : D) (Z : FreeCoprodCompDisc.{u, v} D) :
      Hom D (⟨ULift Unit, fun _ ↦ d⟩ : FreeCoprodCompDisc.{u, v} D) Z ≃
        {z : Z.1 // Z.2 z = d} :=
    { toFun := fun f ↦ ⟨f.1 (ULift.up Unit.unit),
        congrFun f.2 (ULift.up Unit.unit)⟩,
      invFun := fun z ↦ ⟨fun _ ↦ z.1, funext (fun _ ↦ z.2)⟩,
      left_inv := fun _ ↦ Subtype.ext rfl,
      right_inv := fun _ ↦ rfl }
  ```

  Update the module docstring. Append to `## Main definitions`:

  ```markdown
  * `FreeCoprodCompDisc.emptyObj`, `FreeCoprodCompDisc.emptyDesc` —
    the initial object and its universal morphism.
  * `FreeCoprodCompDisc.coprodInj`, `FreeCoprodCompDisc.coprodDesc`,
    `FreeCoprodCompDisc.coprodHomEquiv` — the injections, the
    cotuple, and the universal property of the indexed coproduct.
  * `FreeCoprodCompDisc.coprodPairMor` — the functorial action of
    `FreeCoprodCompDisc.coprodPair` on morphisms.
  * `FreeCoprodCompDisc.homSingletonEquiv` — morphisms out of a
    singleton object as the fiber of the decoding over its value.
  * `FreeCoprodCompDisc.Iso.hom`, `FreeCoprodCompDisc.Iso.invHom` —
    the underlying morphisms of an isomorphism.
  ```

  and to `## Main statements`:

  ```markdown
  * `FreeCoprodCompDisc.emptyDesc_unique` — initiality.
  * `FreeCoprodCompDisc.coprodInj_desc`,
    `FreeCoprodCompDisc.coprodDesc_eta` — the computation and
    uniqueness laws of the cotuple, with the composition
    compatibilities `FreeCoprodCompDisc.coprodMor_desc`,
    `FreeCoprodCompDisc.coprodDesc_comp`,
    `FreeCoprodCompDisc.coprodInj_mor`.
  * `FreeCoprodCompDisc.coprodPairMor_id`,
    `FreeCoprodCompDisc.coprodPairMor_comp` — the functoriality of
    `FreeCoprodCompDisc.coprodPairMor`, with the cotuple
    compatibilities `FreeCoprodCompDisc.coprodPairMor_desc`,
    `FreeCoprodCompDisc.coprodPairMor_id_desc`,
    `FreeCoprodCompDisc.coprodPairMor_inr_desc_inl`.
  * `FreeCoprodCompDisc.Iso.hom_invHom`,
    `FreeCoprodCompDisc.Iso.invHom_hom` — the inverse laws of the
    underlying morphisms.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files. Also
  `#print axioms` (via `lean_verify` or a scratch snippet) on
  `FreeCoprodCompDisc.Iso.hom_invHom` and
  `FreeCoprodCompDisc.Iso.invHom_hom` (the first uses of
  `Equiv.symm_apply_apply`/`Equiv.apply_symm_apply`):
  expected ⊆ `{propext, Quot.sound}`.

- [ ] **Step 5: Commit.** Confirm with `jj status` that
  `proto_2c_gate.lean` is absent from the working tree (see
  § Prototype-file discipline), then:

  ```bash
  jj commit -m "feat(cat): add coproduct universal properties and pair morphisms"
  ```

---

## Task 2: the transformation layer: `NatTrans`, vertical structure, predicates

The natural-transformation notion, generic to `FreeCoprodCompDisc`
and not specific to interpretations of codes: for object maps with
morphism maps, a transformation is a componentwise family of
morphisms satisfying the naturality condition — a subtype with a
`Prop`-valued condition, so equality of transformations is
`Subtype.ext` plus `funext`. Identity, vertical composition, and the
laws branch 2d consumes are componentwise, from the
`FreeCoprodCompDisc.Hom` category laws. Morphism maps carry no
functor laws; the predicates `PreservesId`/`PreservesComp` state
them, to be taken as explicit hypotheses by the operations that need
them.

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`
- Create: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`
- Modify: the `CategoryTheory` source umbrella (add
  `public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc.NatTrans`)
- Modify: the `CategoryTheory` test umbrella (add
  `import GebTests.Mathlib.CategoryTheory.FreeCoprodCompDisc.NatTrans`)

  Locate the umbrella files with
  `ls Geb/Mathlib/CategoryTheory* GebTests/Mathlib/CategoryTheory*`
  and mirror how `FreeCoprodCompDisc` is registered in each.
  Register in BOTH umbrellas — in branch 2a the source-umbrella
  registration was missed and only `pre-push.sh` caught it.

**Interfaces:**

- Consumes: `Map`, `MapMor`, `Hom`, `Hom.id`, `Hom.comp`,
  `Hom.id_comp`, `Hom.comp_id`, `Hom.comp_assoc` (branches 1, 2b).
- Produces (in `namespace FreeCoprodCompDisc`; `I : Type v`,
  `O : Type w`, `P : Type x`):

  ```lean
  IsNatTrans.{w'} (I O) (F G : Map.{u, v, w'} I O) (mF mG)
    (η : (X : FreeCoprodCompDisc.{u, v} I) →
      Hom.{u, w', u} O (F X) (G X)) : Prop
  NatTrans.{w'} (I O) (F G : Map.{u, v, w'} I O) (mF mG) :
    Type (max (u + 1) v)
  NatTrans.id (F) (mF) : NatTrans I O F F mF mF
  NatTrans.vcomp (η : NatTrans I O F G mF mG)
    (θ : NatTrans I O G H mG mH) : NatTrans I O F H mF mH
  NatTrans.id_vcomp / NatTrans.vcomp_id / NatTrans.vcomp_assoc —
    the vertical category laws (statements below)
  PreservesId (F) (mF) : Prop
  PreservesComp (F) (mF) : Prop
  mapComp (F : Map.{u, v, w} I O) (F' : Map.{u, w, x} O P) :
    Map.{u, v, x} I P
  mapMorComp (mF : MapMor I O F) (mF' : MapMor O P F') :
    MapMor I P (mapComp F F')
  ```

- [ ] **Step 1: Create the test file (failing).**
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc.NatTrans

  /-!
  # Tests for natural transformations between completion maps

  The identity and doubling object maps over `Bool`, with their
  morphism maps and functor-law witnesses, exercise the
  transformation space: the identity transformation, a non-identity
  left-injection transformation, and the vertical category laws at
  both. Named theorems give the `GebMeta` axiom linter declarations
  to inspect.

  ## Tags

  free coproduct completion, natural transformation
  -/

  @[expose] public section

  open CategoryTheory

  /-- The identity object map on the completion over `Bool`. -/
  def sampleMap : FreeCoprodCompDisc.Map.{0, 0, 0} Bool Bool :=
    fun X ↦ X

  /-- The identity morphism map over `sampleMap`. -/
  def sampleMapMor : FreeCoprodCompDisc.MapMor Bool Bool sampleMap :=
    fun _ _ h ↦ h

  /-- `sampleMapMor` preserves identities. -/
  theorem sampleMapMor_preservesId :
      FreeCoprodCompDisc.PreservesId sampleMap sampleMapMor :=
    fun _ ↦ rfl

  /-- `sampleMapMor` preserves composition. -/
  theorem sampleMapMor_preservesComp :
      FreeCoprodCompDisc.PreservesComp sampleMap sampleMapMor :=
    fun _ _ _ _ _ ↦ rfl

  /-- A non-identity object map: the binary coproduct of the argument
  with itself. -/
  def sampleMapDouble : FreeCoprodCompDisc.Map.{0, 0, 0} Bool Bool :=
    fun X ↦ FreeCoprodCompDisc.coprodPair Bool X X

  /-- The morphism map of `sampleMapDouble`, from `coprodPairMor`. -/
  def sampleMapDoubleMor :
      FreeCoprodCompDisc.MapMor Bool Bool sampleMapDouble :=
    fun _ _ h ↦ FreeCoprodCompDisc.coprodPairMor Bool h h

  /-- `sampleMapDoubleMor` preserves identities. -/
  theorem sampleMapDoubleMor_preservesId :
      FreeCoprodCompDisc.PreservesId sampleMapDouble sampleMapDoubleMor :=
    fun X ↦ FreeCoprodCompDisc.coprodPairMor_id Bool X X

  /-- `sampleMapDoubleMor` preserves composition. -/
  theorem sampleMapDoubleMor_preservesComp :
      FreeCoprodCompDisc.PreservesComp sampleMapDouble sampleMapDoubleMor :=
    fun _ _ _ f g ↦ FreeCoprodCompDisc.coprodPairMor_comp Bool f g f g

  /-- The identity natural transformation on the identity map. -/
  def sampleNatId :
      FreeCoprodCompDisc.NatTrans Bool Bool sampleMap sampleMap
        sampleMapMor sampleMapMor :=
    FreeCoprodCompDisc.NatTrans.id sampleMap sampleMapMor

  /-- A non-identity natural transformation: the left injection into the
  doubled map. -/
  def sampleNatInl :
      FreeCoprodCompDisc.NatTrans Bool Bool sampleMap sampleMapDouble
        sampleMapMor sampleMapDoubleMor :=
    ⟨fun X ↦ FreeCoprodCompDisc.coprodPairInl Bool X X,
      fun _ _ _ ↦ Subtype.ext rfl⟩

  /-- Vertical left identity at the sample transformation. -/
  theorem sampleNatInl_id_vcomp :
      FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatInl =
        sampleNatInl :=
    FreeCoprodCompDisc.NatTrans.id_vcomp sampleNatInl

  /-- Vertical right identity at the sample transformation. -/
  theorem sampleNatInl_vcomp_id :
      FreeCoprodCompDisc.NatTrans.vcomp sampleNatInl
          (FreeCoprodCompDisc.NatTrans.id sampleMapDouble sampleMapDoubleMor) =
        sampleNatInl :=
    FreeCoprodCompDisc.NatTrans.vcomp_id sampleNatInl

  /-- Vertical associativity at the sample transformations. -/
  theorem sampleNat_vcomp_assoc :
      FreeCoprodCompDisc.NatTrans.vcomp
          (FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatId)
          sampleNatInl =
        FreeCoprodCompDisc.NatTrans.vcomp sampleNatId
          (FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatInl) :=
    FreeCoprodCompDisc.NatTrans.vcomp_assoc sampleNatId sampleNatId sampleNatInl

  /-- The composite of the identity map with itself. -/
  def sampleMapComp : FreeCoprodCompDisc.Map.{0, 0, 0} Bool Bool :=
    FreeCoprodCompDisc.mapComp sampleMap sampleMap

  /-- The composite morphism map over `sampleMapComp`. -/
  def sampleMapCompMor : FreeCoprodCompDisc.MapMor Bool Bool sampleMapComp :=
    FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapMor
  ```

  Register the module in BOTH `CategoryTheory` umbrellas as listed
  under **Files**.

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL —
  `Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc.NatTrans` does not exist
  yet.

- [ ] **Step 3: Implement.** Create
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc

  /-!
  # Natural transformations between completion maps

  Natural transformations between morphism-mapped object maps of free
  coproduct completions (`FreeCoprodCompDisc.Map` paired with
  `FreeCoprodCompDisc.MapMor`): the naturality condition, the
  transformation space as a subtype, and the vertical structure
  (identity, composition, and the category laws). Functor-law
  predicates and composite maps support the horizontal structure.

  ## Main definitions

  * `FreeCoprodCompDisc.IsNatTrans`, `FreeCoprodCompDisc.NatTrans` —
    the naturality condition and the transformation space.
  * `FreeCoprodCompDisc.NatTrans.id`,
    `FreeCoprodCompDisc.NatTrans.vcomp` — the vertical structure.
  * `FreeCoprodCompDisc.PreservesId`,
    `FreeCoprodCompDisc.PreservesComp` — functor-law predicates on a
    morphism map.
  * `FreeCoprodCompDisc.mapComp`, `FreeCoprodCompDisc.mapMorComp` —
    the composite of two object maps and of their morphism maps.

  ## Main statements

  * `FreeCoprodCompDisc.NatTrans.id_vcomp`,
    `FreeCoprodCompDisc.NatTrans.vcomp_id`,
    `FreeCoprodCompDisc.NatTrans.vcomp_assoc` — the vertical
    category laws.

  ## Implementation notes

  A transformation is a subtype over a `Prop`-valued naturality
  condition, so equality of transformations is `Subtype.ext` plus
  `funext`, and the vertical laws are componentwise consequences of
  the `FreeCoprodCompDisc.Hom` category laws. Morphism maps carry no
  functor laws; the operations that need one take the corresponding
  `FreeCoprodCompDisc.PreservesId`/`FreeCoprodCompDisc.PreservesComp`
  law as an explicit hypothesis.

  ## Tags

  free coproduct completion, natural transformation, functor category
  -/

  @[expose] public section

  universe u v w x

  namespace CategoryTheory

  namespace FreeCoprodCompDisc

  /-- The naturality condition on a family of componentwise morphisms
  between two morphism-mapped object maps. -/
  def IsNatTrans.{w'} (I : Type v) (O : Type w') (F G : Map.{u, v, w'} I O)
      (mF : MapMor I O F) (mG : MapMor I O G)
      (η : (X : FreeCoprodCompDisc.{u, v} I) → Hom.{u, w', u} O (F X) (G X)) :
      Prop :=
    ∀ (X Y : FreeCoprodCompDisc.{u, v} I) (h : Hom.{u, v, u} I X Y),
      Hom.comp O (mF X Y h) (η Y) = Hom.comp O (η X) (mG X Y h)

  /-- A natural transformation between two morphism-mapped object maps:
  a componentwise family of morphisms satisfying the naturality
  condition. -/
  def NatTrans.{w'} (I : Type v) (O : Type w') (F G : Map.{u, v, w'} I O)
      (mF : MapMor I O F) (mG : MapMor I O G) : Type (max (u + 1) v) :=
    {η : (X : FreeCoprodCompDisc.{u, v} I) → Hom.{u, w', u} O (F X) (G X) //
      IsNatTrans I O F G mF mG η}

  variable {I : Type v} {O : Type w} {P : Type x}

  /-- The identity natural transformation. -/
  def NatTrans.id (F : Map.{u, v, w} I O) (mF : MapMor I O F) :
      NatTrans I O F F mF mF :=
    ⟨fun X ↦ Hom.id O (F X),
      fun X Y h ↦
        (Hom.comp_id O (mF X Y h)).trans (Hom.id_comp O (mF X Y h)).symm⟩

  /-- Vertical composition of natural transformations. -/
  def NatTrans.vcomp {F G H : Map.{u, v, w} I O} {mF : MapMor I O F}
      {mG : MapMor I O G} {mH : MapMor I O H}
      (η : NatTrans I O F G mF mG) (θ : NatTrans I O G H mG mH) :
      NatTrans I O F H mF mH :=
    ⟨fun X ↦ Hom.comp O (η.1 X) (θ.1 X),
      fun X Y h ↦
        (Hom.comp_assoc O (mF X Y h) (η.1 Y) (θ.1 Y)).symm.trans
          ((congrArg (fun t ↦ Hom.comp O t (θ.1 Y)) (η.2 X Y h)).trans
            ((Hom.comp_assoc O (η.1 X) (mG X Y h) (θ.1 Y)).trans
              ((congrArg (Hom.comp O (η.1 X)) (θ.2 X Y h)).trans
                (Hom.comp_assoc O (η.1 X) (θ.1 X) (mH X Y h)).symm)))⟩

  /-- Vertical left identity. -/
  theorem NatTrans.id_vcomp {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
      {mG : MapMor I O G} (η : NatTrans I O F G mF mG) :
      NatTrans.vcomp (NatTrans.id F mF) η = η :=
    Subtype.ext (funext (fun X ↦ Hom.id_comp O (η.1 X)))

  /-- Vertical right identity. -/
  theorem NatTrans.vcomp_id {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
      {mG : MapMor I O G} (η : NatTrans I O F G mF mG) :
      NatTrans.vcomp η (NatTrans.id G mG) = η :=
    Subtype.ext (funext (fun X ↦ Hom.comp_id O (η.1 X)))

  /-- Vertical associativity. -/
  theorem NatTrans.vcomp_assoc {F G H K : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G} {mH : MapMor I O H}
      {mK : MapMor I O K} (η : NatTrans I O F G mF mG)
      (θ : NatTrans I O G H mG mH) (ρ : NatTrans I O H K mH mK) :
      NatTrans.vcomp (NatTrans.vcomp η θ) ρ =
        NatTrans.vcomp η (NatTrans.vcomp θ ρ) :=
    Subtype.ext (funext (fun X ↦ Hom.comp_assoc O (η.1 X) (θ.1 X) (ρ.1 X)))

  /-- Preservation of identities by a morphism map. -/
  def PreservesId (F : Map.{u, v, w} I O) (mF : MapMor I O F) : Prop :=
    ∀ X : FreeCoprodCompDisc.{u, v} I,
      mF X X (Hom.id I X) = Hom.id O (F X)

  /-- Preservation of composition by a morphism map. -/
  def PreservesComp (F : Map.{u, v, w} I O) (mF : MapMor I O F) : Prop :=
    ∀ (X Y Z : FreeCoprodCompDisc.{u, v} I) (f : Hom I X Y) (g : Hom I Y Z),
      mF X Z (Hom.comp I f g) = Hom.comp O (mF X Y f) (mF Y Z g)

  /-- The composite of two object maps. -/
  def mapComp (F : Map.{u, v, w} I O) (F' : Map.{u, w, x} O P) :
      Map.{u, v, x} I P :=
    fun X ↦ F' (F X)

  /-- The composite of two morphism maps, over the composite object
  map. -/
  def mapMorComp {F : Map.{u, v, w} I O} {F' : Map.{u, w, x} O P}
      (mF : MapMor I O F) (mF' : MapMor O P F') :
      MapMor I P (mapComp F F') :=
    fun X Y h ↦ mF' (F X) (F Y) (mF X Y h)

  end FreeCoprodCompDisc

  end CategoryTheory
  ```

  (The module docstring at this commit describes only this task's
  declarations; Tasks 3–5 extend it as their content lands, keeping
  every intermediate commit's docstring accurate for doc
  generation.)

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS. Also run `scripts/lint-imports.sh` (new module and
  umbrella registrations).

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(cat): add natural transformations between completion maps"
  ```

---

## Task 3: whiskering, horizontal composition, coherences, interchange

The composition API of the transformation notion — the client-facing
surface of the functor-category structure; none of it is consumed by
Theorem 3 or the branch 2d transfer. Right whiskering needs no
functor-law hypotheses; left whiskering and horizontal composition
consume the outer morphism map's composition-preservation law as a
hypothesis; the coherences cover the agreement of the two
orientations of the horizontal composite, the identity laws,
whiskering by the identity object map, and the interchange law with
vertical composition.

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`

**Interfaces:**

- Consumes: `NatTrans`, `NatTrans.id`, `NatTrans.vcomp`,
  `PreservesId`, `PreservesComp`, `mapComp`, `mapMorComp` (Task 2),
  the `Hom` category laws (branch 2b).
- Produces:

  ```lean
  NatTrans.whiskerRight (F) (mF) (θ : NatTrans O P F' G' mF' mG') :
    NatTrans I P (mapComp F F') (mapComp F G')
      (mapMorComp mF mF') (mapMorComp mF mG')
  NatTrans.whiskerLeft (η : NatTrans I O F G mF mG) (F') (mF')
    (hF' : PreservesComp F' mF') :
    NatTrans I P (mapComp F F') (mapComp G F')
      (mapMorComp mF mF') (mapMorComp mG mF')
  NatTrans.hcomp (η) (θ) (hF' : PreservesComp F' mF') :
    NatTrans I P (mapComp F F') (mapComp G G')
      (mapMorComp mF mF') (mapMorComp mG mG')
  NatTrans.hcomp_eq_vcomp_whisker / NatTrans.hcomp_id /
    NatTrans.hcomp_id_right / NatTrans.hcomp_id_left /
    NatTrans.hcomp_vcomp — the coherence and interchange laws
    (statements below)
  idMap : Map.{u, v, v} I I
  idMapMor : MapMor I I (idMap : Map.{u, v, v} I I)
  idMapMor_preservesId :
    PreservesId (idMap : Map.{u, v, v} I I) idMapMor
  idMapMor_preservesComp :
    PreservesComp (idMap : Map.{u, v, v} I I) idMapMor
  NatTrans.whiskerRight_idMap (θ : NatTrans I O F' G' mF' mG') :
    NatTrans.whiskerRight (idMap : Map.{u, v, v} I I) idMapMor θ = θ
  NatTrans.whiskerLeft_idMap (η : NatTrans I O F G mF mG) :
    NatTrans.whiskerLeft η (idMap : Map.{u, w, w} O O) idMapMor
      idMapMor_preservesComp = η
  ```

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`:

  ```lean
  /-- Right whiskering of the sample transformation by the identity
  map. -/
  def sampleWhiskerRight :
      FreeCoprodCompDisc.NatTrans Bool Bool
        (FreeCoprodCompDisc.mapComp sampleMap sampleMap)
        (FreeCoprodCompDisc.mapComp sampleMap sampleMapDouble)
        (FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapMor)
        (FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapDoubleMor) :=
    FreeCoprodCompDisc.NatTrans.whiskerRight sampleMap sampleMapMor sampleNatInl

  /-- Left whiskering of the sample transformation by the identity map. -/
  def sampleWhiskerLeft :
      FreeCoprodCompDisc.NatTrans Bool Bool
        (FreeCoprodCompDisc.mapComp sampleMap sampleMap)
        (FreeCoprodCompDisc.mapComp sampleMapDouble sampleMap)
        (FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapMor)
        (FreeCoprodCompDisc.mapMorComp sampleMapDoubleMor sampleMapMor) :=
    FreeCoprodCompDisc.NatTrans.whiskerLeft sampleNatInl sampleMap sampleMapMor
      sampleMapMor_preservesComp

  /-- The two orientations of the horizontal composite agree at the
  sample transformations. -/
  theorem sampleHcomp_eq_vcomp_whisker :
      FreeCoprodCompDisc.NatTrans.hcomp sampleNatInl sampleNatInl
          sampleMapMor_preservesComp =
        FreeCoprodCompDisc.NatTrans.vcomp
          (FreeCoprodCompDisc.NatTrans.whiskerRight sampleMap sampleMapMor
            sampleNatInl)
          (FreeCoprodCompDisc.NatTrans.whiskerLeft sampleNatInl sampleMapDouble
            sampleMapDoubleMor sampleMapDoubleMor_preservesComp) :=
    FreeCoprodCompDisc.NatTrans.hcomp_eq_vcomp_whisker sampleNatInl sampleNatInl
      sampleMapMor_preservesComp sampleMapDoubleMor_preservesComp

  /-- The horizontal composite of identity transformations is the
  identity. -/
  theorem sampleHcomp_id :
      FreeCoprodCompDisc.NatTrans.hcomp sampleNatId sampleNatId
          sampleMapMor_preservesComp =
        FreeCoprodCompDisc.NatTrans.id
          (FreeCoprodCompDisc.mapComp sampleMap sampleMap)
          (FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapMor) :=
    FreeCoprodCompDisc.NatTrans.hcomp_id sampleMapMor_preservesComp
      sampleMapMor_preservesId

  /-- The interchange law at the sample transformations. -/
  theorem sampleHcomp_vcomp :
      FreeCoprodCompDisc.NatTrans.hcomp
          (FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatInl)
          (FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatInl)
          sampleMapMor_preservesComp =
        FreeCoprodCompDisc.NatTrans.vcomp
          (FreeCoprodCompDisc.NatTrans.hcomp sampleNatId sampleNatId
            sampleMapMor_preservesComp)
          (FreeCoprodCompDisc.NatTrans.hcomp sampleNatInl sampleNatInl
            sampleMapMor_preservesComp) :=
    FreeCoprodCompDisc.NatTrans.hcomp_vcomp sampleNatId sampleNatInl
      sampleNatId sampleNatInl sampleMapMor_preservesComp
      sampleMapMor_preservesComp

  /-- Right whiskering by the identity object map is the identity
  operation at the sample transformation. -/
  theorem sampleWhiskerRight_idMap :
      FreeCoprodCompDisc.NatTrans.whiskerRight FreeCoprodCompDisc.idMap
          FreeCoprodCompDisc.idMapMor sampleNatInl =
        sampleNatInl :=
    FreeCoprodCompDisc.NatTrans.whiskerRight_idMap sampleNatInl

  /-- Left whiskering by the identity object map is the identity
  operation at the sample transformation. -/
  theorem sampleWhiskerLeft_idMap :
      FreeCoprodCompDisc.NatTrans.whiskerLeft sampleNatInl
          FreeCoprodCompDisc.idMap FreeCoprodCompDisc.idMapMor
          FreeCoprodCompDisc.idMapMor_preservesComp =
        sampleNatInl :=
    FreeCoprodCompDisc.NatTrans.whiskerLeft_idMap sampleNatInl
  ```

  Extend the test file's module docstring summary with one sentence:
  "Whiskering, horizontal composition, and the coherence and
  interchange laws are exercised at the sample transformations."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant
  `FreeCoprodCompDisc.NatTrans.whiskerRight`.

- [ ] **Step 3: Implement.** Append to the `FreeCoprodCompDisc`
  namespace of `FreeCoprodCompDisc/NatTrans.lean` (before
  `end FreeCoprodCompDisc`). The identity object map and its
  whiskering laws (`idMap` … `NatTrans.whiskerLeft_idMap`) follow
  `NatTrans.hcomp_id_left` in the file:

  ```lean
  /-- Right whiskering: precomposition of a transformation with an
  object map (no functor-law hypotheses). -/
  def NatTrans.whiskerRight {F' G' : Map.{u, w, x} O P}
      {mF' : MapMor O P F'} {mG' : MapMor O P G'} (F : Map.{u, v, w} I O)
      (mF : MapMor I O F) (θ : NatTrans O P F' G' mF' mG') :
      NatTrans I P (mapComp F F') (mapComp F G')
        (mapMorComp mF mF') (mapMorComp mF mG') :=
    ⟨fun X ↦ θ.1 (F X), fun X Y h ↦ θ.2 (F X) (F Y) (mF X Y h)⟩

  /-- Left whiskering: postcomposition of a transformation with an
  object map, whose naturality consumes the outer morphism map's
  composition-preservation law. -/
  def NatTrans.whiskerLeft {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
      {mG : MapMor I O G} (η : NatTrans I O F G mF mG)
      (F' : Map.{u, w, x} O P) (mF' : MapMor O P F')
      (hF' : PreservesComp F' mF') :
      NatTrans I P (mapComp F F') (mapComp G F')
        (mapMorComp mF mF') (mapMorComp mG mF') :=
    ⟨fun X ↦ mF' (F X) (G X) (η.1 X),
      fun X Y h ↦
        (hF' (F X) (F Y) (G Y) (mF X Y h) (η.1 Y)).symm.trans
          ((congrArg (mF' (F X) (G Y)) (η.2 X Y h)).trans
            (hF' (F X) (G X) (G Y) (η.1 X) (mG X Y h)))⟩

  /-- Horizontal composition of natural transformations, in the
  `whiskerLeft`-then-`whiskerRight` orientation. -/
  def NatTrans.hcomp {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
      {mG : MapMor I O G} {F' G' : Map.{u, w, x} O P}
      {mF' : MapMor O P F'} {mG' : MapMor O P G'}
      (η : NatTrans I O F G mF mG) (θ : NatTrans O P F' G' mF' mG')
      (hF' : PreservesComp F' mF') :
      NatTrans I P (mapComp F F') (mapComp G G')
        (mapMorComp mF mF') (mapMorComp mG mG') :=
    NatTrans.vcomp (NatTrans.whiskerLeft η F' mF' hF')
      (NatTrans.whiskerRight G mG θ)

  /-- The two orientations of the horizontal composite agree, by the
  second transformation's naturality. -/
  theorem NatTrans.hcomp_eq_vcomp_whisker {F G : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G} {F' G' : Map.{u, w, x} O P}
      {mF' : MapMor O P F'} {mG' : MapMor O P G'}
      (η : NatTrans I O F G mF mG) (θ : NatTrans O P F' G' mF' mG')
      (hF' : PreservesComp F' mF') (hG' : PreservesComp G' mG') :
      NatTrans.hcomp η θ hF' =
        NatTrans.vcomp (NatTrans.whiskerRight F mF θ)
          (NatTrans.whiskerLeft η G' mG' hG') :=
    Subtype.ext (funext (fun X ↦ θ.2 (F X) (G X) (η.1 X)))

  /-- The horizontal composite of identity transformations is the
  identity (consuming the outer morphism map's identity-preservation
  law). -/
  theorem NatTrans.hcomp_id {F : Map.{u, v, w} I O} {mF : MapMor I O F}
      {F' : Map.{u, w, x} O P} {mF' : MapMor O P F'}
      (hF'comp : PreservesComp F' mF') (hF'id : PreservesId F' mF') :
      NatTrans.hcomp (NatTrans.id F mF) (NatTrans.id F' mF') hF'comp =
        NatTrans.id (mapComp F F') (mapMorComp mF mF') :=
    Subtype.ext (funext (fun X ↦
      (congrArg (fun t ↦ Hom.comp P t (Hom.id P (F' (F X))))
          (hF'id (F X))).trans
        (Hom.comp_id P (Hom.id P (F' (F X))))))

  /-- Whiskering by an identity-transformation on the right is left
  whiskering. -/
  theorem NatTrans.hcomp_id_right {F G : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G} {F' : Map.{u, w, x} O P}
      {mF' : MapMor O P F'} (η : NatTrans I O F G mF mG)
      (hF' : PreservesComp F' mF') :
      NatTrans.hcomp η (NatTrans.id F' mF') hF' =
        NatTrans.whiskerLeft η F' mF' hF' :=
    Subtype.ext (funext (fun X ↦ Hom.comp_id P (mF' (F X) (G X) (η.1 X))))

  /-- Whiskering by an identity-transformation on the left is right
  whiskering. -/
  theorem NatTrans.hcomp_id_left {F : Map.{u, v, w} I O}
      {mF : MapMor I O F} {F' G' : Map.{u, w, x} O P}
      {mF' : MapMor O P F'} {mG' : MapMor O P G'}
      (θ : NatTrans O P F' G' mF' mG') (hF'comp : PreservesComp F' mF')
      (hF'id : PreservesId F' mF') :
      NatTrans.hcomp (NatTrans.id F mF) θ hF'comp =
        NatTrans.whiskerRight F mF θ :=
    Subtype.ext (funext (fun X ↦
      (congrArg (fun t ↦ Hom.comp P t (θ.1 (F X))) (hF'id (F X))).trans
        (Hom.id_comp P (θ.1 (F X)))))

  /-- The identity object map. -/
  def idMap : Map.{u, v, v} I I :=
    fun X ↦ X

  /-- The morphism-map component of the identity object map. -/
  def idMapMor : MapMor I I (idMap : Map.{u, v, v} I I) :=
    fun _ _ h ↦ h

  /-- The identity object map preserves identities. -/
  theorem idMapMor_preservesId :
      PreservesId (idMap : Map.{u, v, v} I I) idMapMor :=
    fun _ ↦ rfl

  /-- The identity object map preserves composition. -/
  theorem idMapMor_preservesComp :
      PreservesComp (idMap : Map.{u, v, v} I I) idMapMor :=
    fun _ _ _ _ _ ↦ rfl

  /-- Whiskering a transformation with the identity object map on the
  precomposition side is the identity operation. -/
  theorem NatTrans.whiskerRight_idMap {F' G' : Map.{u, v, w} I O}
      {mF' : MapMor I O F'} {mG' : MapMor I O G'}
      (θ : NatTrans I O F' G' mF' mG') :
      NatTrans.whiskerRight (idMap : Map.{u, v, v} I I) idMapMor θ = θ :=
    Subtype.ext rfl

  /-- Whiskering a transformation with the identity object map on the
  postcomposition side is the identity operation. -/
  theorem NatTrans.whiskerLeft_idMap {F G : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G}
      (η : NatTrans I O F G mF mG) :
      NatTrans.whiskerLeft η (idMap : Map.{u, w, w} O O) idMapMor
        idMapMor_preservesComp = η :=
    Subtype.ext rfl

  /-- The interchange law between horizontal and vertical composition. -/
  theorem NatTrans.hcomp_vcomp {F G H : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G} {mH : MapMor I O H}
      {F' G' H' : Map.{u, w, x} O P} {mF' : MapMor O P F'}
      {mG' : MapMor O P G'} {mH' : MapMor O P H'}
      (η : NatTrans I O F G mF mG) (η' : NatTrans I O G H mG mH)
      (θ : NatTrans O P F' G' mF' mG') (θ' : NatTrans O P G' H' mG' mH')
      (hF' : PreservesComp F' mF') (hG' : PreservesComp G' mG') :
      NatTrans.hcomp (NatTrans.vcomp η η') (NatTrans.vcomp θ θ') hF' =
        NatTrans.vcomp (NatTrans.hcomp η θ hF')
          (NatTrans.hcomp η' θ' hG') :=
    Subtype.ext (funext (fun X ↦
      (congrArg (fun t ↦ Hom.comp P t
          (Hom.comp P (θ.1 (H X)) (θ'.1 (H X))))
        (hF' (F X) (G X) (H X) (η.1 X) (η'.1 X))).trans
      (congrArg (fun t ↦
          Hom.comp P (Hom.comp P (mF' (F X) (G X) (η.1 X)) t)
            (θ'.1 (H X)))
        (θ.2 (G X) (H X) (η'.1 X)))))
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `FreeCoprodCompDisc.NatTrans.whiskerRight`,
    `FreeCoprodCompDisc.NatTrans.whiskerLeft`,
    `FreeCoprodCompDisc.NatTrans.hcomp` — whiskering and horizontal
    composition.
  * `FreeCoprodCompDisc.idMap`, `FreeCoprodCompDisc.idMapMor` — the
    identity object map and its morphism-map component.
  ```

  and to `## Main statements`:

  ```markdown
  * `FreeCoprodCompDisc.NatTrans.hcomp_eq_vcomp_whisker`,
    `FreeCoprodCompDisc.NatTrans.hcomp_id`,
    `FreeCoprodCompDisc.NatTrans.hcomp_id_right`,
    `FreeCoprodCompDisc.NatTrans.hcomp_id_left`,
    `FreeCoprodCompDisc.NatTrans.hcomp_vcomp` — the coherence and
    interchange laws of horizontal composition.
  * `FreeCoprodCompDisc.NatTrans.whiskerRight_idMap`,
    `FreeCoprodCompDisc.NatTrans.whiskerLeft_idMap` — whiskering by
    the identity object map is the identity operation (with the
    functor-law witnesses `FreeCoprodCompDisc.idMapMor_preservesId`
    and `FreeCoprodCompDisc.idMapMor_preservesComp`).
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(cat): add whiskering and horizontal composition"
  ```

---

## Task 4: inverse pairs, iso families, transports, coproduct decomposition

The conversion and transport layer the Theorem 3 induction composes
with: a natural family of isomorphisms (the form of the Lemma 4
upgrade) converts to a mutually inverse pair of natural
transformations — naturality of the inverse family follows by
conjugating the square by the inverses; either half of an inverse
pair transports a transformation space by pre- or postcomposition;
`NatTrans.congrSource` rewrites the source morphism map along an
equality (the form in which the characterizing equations
`interpMor_sigma`/`interpMor_delta` enter the induction); and
`natCoprodEquiv` decomposes transformations out of a pointwise
indexed coproduct into families (the `σ`-case).

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`

**Interfaces:**

- Consumes: `NatTrans`, `IsNatTrans`, `NatTrans.id`,
  `NatTrans.vcomp`, the vertical laws (Task 2); `Iso.hom`,
  `Iso.invHom`, `Iso.hom_invHom`, `Iso.invHom_hom`, `coprodInj`,
  `coprodDesc`, `coprodMor` (Task 1 and branch 1).
- Produces:

  ```lean
  NatTrans.IsInverse (α : NatTrans I O F G mF mG)
    (β : NatTrans I O G F mG mF) : Prop
  isNatTrans_invHom (iso : (X) → Iso O (F X) (G X))
    (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
    IsNatTrans I O G F mG mF (fun X ↦ Iso.invHom O (iso X))
  NatTrans.ofIsoFamily (iso) (hnat) : NatTrans I O F G mF mG
  NatTrans.invOfIsoFamily (iso) (hnat) : NatTrans I O G F mG mF
  NatTrans.ofIsoFamily_isInverse (iso) (hnat) :
    NatTrans.IsInverse (NatTrans.ofIsoFamily iso hnat)
      (NatTrans.invOfIsoFamily iso hnat)
  NatTrans.equivOfInverseTarget (α) (β) (h : NatTrans.IsInverse α β) :
    NatTrans I O F G mF mG ≃ NatTrans I O F G' mF mG'
  NatTrans.equivOfInverseSource (α) (β) (h : NatTrans.IsInverse α β) :
    NatTrans I O F G mF mG ≃ NatTrans I O F' G mF' mG
  NatTrans.congrSource (e : mF = mF') (mG : MapMor I O G) :
    NatTrans I O F G mF mG ≃ NatTrans I O F G mF' mG
  natCoprodEquiv (A : Type u) (Fa : A → Map.{u, v, w} I O) (mFa) (G)
    (mG) :
    NatTrans I O (fun X ↦ coprod O A (fun a ↦ Fa a X)) G … mG ≃
      ((a : A) → NatTrans I O (Fa a) G (mFa a) mG)
  ```

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`:

  ```lean
  /-- The identity isomorphism family on the identity map is natural. -/
  theorem sampleIsoFamily_isNatTrans :
      FreeCoprodCompDisc.IsNatTrans Bool Bool sampleMap sampleMap
        sampleMapMor sampleMapMor
        (fun X ↦ FreeCoprodCompDisc.Iso.hom Bool
          (FreeCoprodCompDisc.Iso.refl Bool X)) :=
    fun _ _ _ ↦ Subtype.ext rfl

  /-- The transformation packaged from the identity isomorphism family. -/
  def sampleOfIsoFamily :
      FreeCoprodCompDisc.NatTrans Bool Bool sampleMap sampleMap
        sampleMapMor sampleMapMor :=
    FreeCoprodCompDisc.NatTrans.ofIsoFamily
      (fun X ↦ FreeCoprodCompDisc.Iso.refl Bool X) sampleIsoFamily_isNatTrans

  /-- The inverse transformation packaged from the identity isomorphism
  family. -/
  def sampleInvOfIsoFamily :
      FreeCoprodCompDisc.NatTrans Bool Bool sampleMap sampleMap
        sampleMapMor sampleMapMor :=
    FreeCoprodCompDisc.NatTrans.invOfIsoFamily
      (fun X ↦ FreeCoprodCompDisc.Iso.refl Bool X) sampleIsoFamily_isNatTrans

  /-- The two packaged transformations are inverse. -/
  theorem sampleOfIsoFamily_isInverse :
      FreeCoprodCompDisc.NatTrans.IsInverse sampleOfIsoFamily
        sampleInvOfIsoFamily :=
    FreeCoprodCompDisc.NatTrans.ofIsoFamily_isInverse
      (fun X ↦ FreeCoprodCompDisc.Iso.refl Bool X) sampleIsoFamily_isNatTrans

  /-- Postcomposition with the sample inverse pair round-trips a
  transformation. -/
  theorem sampleEquivOfInverseTarget_roundtrip :
      (FreeCoprodCompDisc.NatTrans.equivOfInverseTarget sampleOfIsoFamily
            sampleInvOfIsoFamily sampleOfIsoFamily_isInverse).symm
          ((FreeCoprodCompDisc.NatTrans.equivOfInverseTarget sampleOfIsoFamily
            sampleInvOfIsoFamily sampleOfIsoFamily_isInverse) sampleNatId) =
        sampleNatId :=
    (FreeCoprodCompDisc.NatTrans.equivOfInverseTarget sampleOfIsoFamily
      sampleInvOfIsoFamily sampleOfIsoFamily_isInverse).symm_apply_apply
      sampleNatId

  /-- Rewriting the source morphism map along reflexivity is the
  identity. -/
  theorem sampleCongrSource_apply :
      FreeCoprodCompDisc.NatTrans.congrSource
          (rfl : sampleMapMor = sampleMapMor) sampleMapDoubleMor sampleNatInl =
        sampleNatInl :=
    rfl

  /-- The coproduct decomposition round-trips a family of
  transformations. -/
  theorem sampleNatCoprodEquiv_roundtrip :
      (FreeCoprodCompDisc.natCoprodEquiv Bool (fun _ ↦ sampleMap)
          (fun _ ↦ sampleMapMor) sampleMapDouble sampleMapDoubleMor)
          ((FreeCoprodCompDisc.natCoprodEquiv Bool (fun _ ↦ sampleMap)
            (fun _ ↦ sampleMapMor) sampleMapDouble sampleMapDoubleMor).symm
            (fun _ ↦ sampleNatInl)) =
        fun _ ↦ sampleNatInl :=
    (FreeCoprodCompDisc.natCoprodEquiv Bool (fun _ ↦ sampleMap)
      (fun _ ↦ sampleMapMor) sampleMapDouble
      sampleMapDoubleMor).apply_symm_apply (fun _ ↦ sampleNatInl)
  ```

  Extend the test file's module docstring summary with one sentence:
  "The identity isomorphism family packages into an inverse pair of
  transformations; the transport equivalences, the source-map
  rewrite, and the coproduct decomposition round-trip sample
  transformations."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant
  `FreeCoprodCompDisc.NatTrans.ofIsoFamily` (the first appended
  test, `sampleIsoFamily_isNatTrans`, uses only Task 1/2 content and
  compiles).

- [ ] **Step 3: Implement.** Append to the `FreeCoprodCompDisc`
  namespace of `FreeCoprodCompDisc/NatTrans.lean` (before
  `end FreeCoprodCompDisc`):

  ```lean
  /-- Two natural transformations are inverse when their vertical
  composites in both orders are identities. -/
  def NatTrans.IsInverse {F G : Map.{u, v, w} I O} {mF : MapMor I O F}
      {mG : MapMor I O G} (α : NatTrans I O F G mF mG)
      (β : NatTrans I O G F mG mF) : Prop :=
    NatTrans.vcomp α β = NatTrans.id F mF ∧
      NatTrans.vcomp β α = NatTrans.id G mG

  /-- The componentwise inverses of a natural family of isomorphisms
  form a natural family. -/
  theorem isNatTrans_invHom {F G : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G}
      (iso : (X : FreeCoprodCompDisc.{u, v} I) → Iso O (F X) (G X))
      (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
      IsNatTrans I O G F mG mF (fun X ↦ Iso.invHom O (iso X)) :=
    fun X Y h ↦
      Subtype.ext (funext (fun b ↦
        (congrArg (fun t ↦ (iso Y).1.symm ((mG X Y h).1 t))
            ((iso X).1.apply_symm_apply b).symm).trans
          ((congrArg (fun t ↦ (iso Y).1.symm t)
              (congrFun (congrArg Subtype.val (hnat X Y h))
                ((iso X).1.symm b)).symm).trans
            ((iso Y).1.symm_apply_apply
              ((mF X Y h).1 ((iso X).1.symm b))))))

  /-- Package a natural family of isomorphisms as a natural
  transformation. -/
  def NatTrans.ofIsoFamily {F G : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G}
      (iso : (X : FreeCoprodCompDisc.{u, v} I) → Iso O (F X) (G X))
      (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
      NatTrans I O F G mF mG :=
    ⟨fun X ↦ Iso.hom O (iso X), hnat⟩

  /-- Package the inverses of a natural family of isomorphisms as a
  natural transformation. -/
  def NatTrans.invOfIsoFamily {F G : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G}
      (iso : (X : FreeCoprodCompDisc.{u, v} I) → Iso O (F X) (G X))
      (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
      NatTrans I O G F mG mF :=
    ⟨fun X ↦ Iso.invHom O (iso X), isNatTrans_invHom iso hnat⟩

  /-- The two transformations packaged from a natural family of
  isomorphisms are inverse. -/
  theorem NatTrans.ofIsoFamily_isInverse {F G : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G}
      (iso : (X : FreeCoprodCompDisc.{u, v} I) → Iso O (F X) (G X))
      (hnat : IsNatTrans I O F G mF mG (fun X ↦ Iso.hom O (iso X))) :
      NatTrans.IsInverse (NatTrans.ofIsoFamily iso hnat)
        (NatTrans.invOfIsoFamily iso hnat) :=
    ⟨Subtype.ext (funext (fun X ↦ Iso.hom_invHom O (iso X))),
      Subtype.ext (funext (fun X ↦ Iso.invHom_hom O (iso X)))⟩

  /-- Postcomposition with one half of an inverse pair is an
  equivalence on transformation spaces (target side). -/
  def NatTrans.equivOfInverseTarget {F G G' : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mG : MapMor I O G} {mG' : MapMor I O G'}
      (α : NatTrans I O G G' mG mG') (β : NatTrans I O G' G mG' mG)
      (h : NatTrans.IsInverse α β) :
      NatTrans I O F G mF mG ≃ NatTrans I O F G' mF mG' :=
    { toFun := fun η ↦ NatTrans.vcomp η α,
      invFun := fun θ ↦ NatTrans.vcomp θ β,
      left_inv := fun η ↦
        (NatTrans.vcomp_assoc η α β).trans
          ((congrArg (fun t ↦ NatTrans.vcomp η t) h.1).trans
            (NatTrans.vcomp_id η)),
      right_inv := fun θ ↦
        (NatTrans.vcomp_assoc θ β α).trans
          ((congrArg (fun t ↦ NatTrans.vcomp θ t) h.2).trans
            (NatTrans.vcomp_id θ)) }

  /-- Precomposition with one half of an inverse pair is an
  equivalence on transformation spaces (source side). -/
  def NatTrans.equivOfInverseSource {F F' G : Map.{u, v, w} I O}
      {mF : MapMor I O F} {mF' : MapMor I O F'} {mG : MapMor I O G}
      (α : NatTrans I O F' F mF' mF) (β : NatTrans I O F F' mF mF')
      (h : NatTrans.IsInverse α β) :
      NatTrans I O F G mF mG ≃ NatTrans I O F' G mF' mG :=
    { toFun := fun η ↦ NatTrans.vcomp α η,
      invFun := fun θ ↦ NatTrans.vcomp β θ,
      left_inv := fun η ↦
        (NatTrans.vcomp_assoc β α η).symm.trans
          ((congrArg (fun t ↦ NatTrans.vcomp t η) h.2).trans
            (NatTrans.id_vcomp η)),
      right_inv := fun θ ↦
        (NatTrans.vcomp_assoc α β θ).symm.trans
          ((congrArg (fun t ↦ NatTrans.vcomp t θ) h.1).trans
            (NatTrans.id_vcomp θ)) }

  /-- Rewrite the source morphism map of a transformation space along an
  equality of morphism maps. -/
  def NatTrans.congrSource {F G : Map.{u, v, w} I O} {mF mF' : MapMor I O F}
      (e : mF = mF') (mG : MapMor I O G) :
      NatTrans I O F G mF mG ≃ NatTrans I O F G mF' mG :=
    Eq.rec (motive := fun mF'' _ ↦
        NatTrans I O F G mF mG ≃ NatTrans I O F G mF'' mG)
      (Equiv.refl (NatTrans I O F G mF mG)) e

  /-- The generic coproduct decomposition of transformation spaces:
  transformations out of a pointwise indexed coproduct of object maps
  correspond to families of transformations out of the summands. -/
  def natCoprodEquiv (A : Type u) (Fa : A → Map.{u, v, w} I O)
      (mFa : (a : A) → MapMor I O (Fa a)) (G : Map.{u, v, w} I O)
      (mG : MapMor I O G) :
      NatTrans I O (fun X ↦ coprod O A (fun a ↦ Fa a X)) G
          (fun X Y h ↦ coprodMor O A A _root_.id (fun a ↦ Fa a X)
            (fun a ↦ Fa a Y) (fun a ↦ mFa a X Y h)) mG ≃
        ((a : A) → NatTrans I O (Fa a) G (mFa a) mG) :=
    { toFun := fun η a ↦
        ⟨fun X ↦ Hom.comp O (coprodInj O A (fun a' ↦ Fa a' X) a) (η.1 X),
          fun X Y h ↦
            congrArg (Hom.comp O (coprodInj O A (fun a' ↦ Fa a' X) a))
              (η.2 X Y h)⟩,
      invFun := fun θ ↦
        ⟨fun X ↦ coprodDesc O A (fun a ↦ Fa a X) (G X) (fun a ↦ (θ a).1 X),
          fun X Y h ↦
            congrArg (coprodDesc O A (fun a ↦ Fa a X) (G Y))
              (funext (fun a ↦ (θ a).2 X Y h))⟩,
      left_inv := fun _ ↦ Subtype.ext (funext (fun _ ↦ Subtype.ext rfl)),
      right_inv := fun _ ↦
        funext (fun _ ↦ Subtype.ext (funext (fun _ ↦ Subtype.ext rfl))) }
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `FreeCoprodCompDisc.NatTrans.IsInverse`,
    `FreeCoprodCompDisc.NatTrans.ofIsoFamily`,
    `FreeCoprodCompDisc.NatTrans.invOfIsoFamily` — inverse pairs and
    the conversion of a natural family of isomorphisms.
  * `FreeCoprodCompDisc.NatTrans.equivOfInverseTarget`,
    `FreeCoprodCompDisc.NatTrans.equivOfInverseSource`,
    `FreeCoprodCompDisc.NatTrans.congrSource` — transport
    equivalences of transformation spaces.
  * `FreeCoprodCompDisc.natCoprodEquiv` — the coproduct
    decomposition of transformation spaces.
  ```

  and to `## Main statements`:

  ```markdown
  * `FreeCoprodCompDisc.isNatTrans_invHom`,
    `FreeCoprodCompDisc.NatTrans.ofIsoFamily_isInverse` — naturality
    of the inverse family and the inverse laws of the packaged pair.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(cat): add inverse pairs and the coproduct decomposition"
  ```

---

## Task 5: the copower–Yoneda adjunction

The equivalence the `δ`-case of Theorem 3 composes with per summand:
transformations out of the copowered map
`X ↦ Hom(c, X) ⊗ F X` correspond to transformations from `F` into
the `plus`-precomposed map `X ↦ G (c + X)`. The functor-law
hypotheses enter exactly as the spec prescribes: the forward
direction consumes `F`'s composition preservation, the backward
direction `G`'s, and each round trip the corresponding identity
preservation.

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`

**Interfaces:**

- Consumes: `copower`, `plus`, `coprodPair`, `coprodPairInl`,
  `coprodPairInr`, `coprodPairDesc`, `coprodMor` (branch 1);
  `coprodInj`, `coprodDesc`, `coprodPairMor`,
  `coprodPairMor_id_desc`,
  `coprodPairMor_inr_desc_inl` (Task 1); `NatTrans`, `PreservesId`,
  `PreservesComp`, `mapComp`, `mapMorComp` (Task 2); the `Hom`
  category laws (branch 2b).
- Produces:

  ```lean
  copowerHomMap (c : FreeCoprodCompDisc.{u, v} I)
    (F : Map.{u, v, w} I O) : Map.{u, v, w} I O
  copowerHomMapMor (c) (mF : MapMor I O F) :
    MapMor I O (copowerHomMap c F)
  plusMap (c : FreeCoprodCompDisc.{u, v} I) : Map.{u, v, v} I I
  plusMapMor (c) : MapMor I I (plusMap c)
  natCopowerPlusToFun (c) (hFcomp) (η) :
    NatTrans I O F (mapComp (plusMap c) G) mF
      (mapMorComp (plusMapMor c) mG)
  natCopowerPlusInvFun (c) (hGcomp) (θ) :
    NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG
  natCopowerPlus_invFun_toFun / natCopowerPlus_toFun_invFun — the
    round-trip laws (statements below)
  natCopowerPlusEquiv (c) (mF) (mG) (hFid hFcomp hGid hGcomp) :
    NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG ≃
      NatTrans I O F (mapComp (plusMap c) G) mF
        (mapMorComp (plusMapMor c) mG)
  ```

  (Verified universe instantiations, already encoded in the code
  below: `copower.{u, w, u}`, `Hom.{u, v, u}` in `copowerHomMap`;
  `plus.{v, u, u}` in `plusMap`.)

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean`:

  ```lean
  /-- A sample completion object for the copower–Yoneda adjunction. -/
  def sampleNatObj : FreeCoprodCompDisc.{0, 0} Bool :=
    ⟨Bool, fun b ↦ b⟩

  /-- A sample endomorphism of `sampleNatObj`. -/
  def sampleNatObjHom : FreeCoprodCompDisc.Hom Bool sampleNatObj sampleNatObj :=
    ⟨fun b ↦ b, rfl⟩

  /-- The morphism map of the copowered map evaluates componentwise. -/
  theorem sampleCopowerHomMapMor_apply :
      (FreeCoprodCompDisc.copowerHomMapMor sampleNatObj sampleMapMor
          sampleNatObj sampleNatObj sampleNatObjHom).1
          ⟨sampleNatObjHom, true⟩ =
        ⟨FreeCoprodCompDisc.Hom.comp Bool sampleNatObjHom sampleNatObjHom,
          true⟩ :=
    rfl

  /-- The right-injection transformation into the `plus`-precomposed
  identity map. -/
  def sampleNatInr :
      FreeCoprodCompDisc.NatTrans Bool Bool sampleMap
        (FreeCoprodCompDisc.mapComp
          (FreeCoprodCompDisc.plusMap sampleNatObj) sampleMap)
        sampleMapMor
        (FreeCoprodCompDisc.mapMorComp
          (FreeCoprodCompDisc.plusMapMor sampleNatObj) sampleMapMor) :=
    ⟨fun X ↦ FreeCoprodCompDisc.coprodPairInr Bool sampleNatObj X,
      fun _ _ _ ↦ Subtype.ext rfl⟩

  /-- The copower–Yoneda adjunction round-trips the sample
  transformation. -/
  theorem sampleNatCopowerPlus_roundtrip :
      (FreeCoprodCompDisc.natCopowerPlusEquiv sampleNatObj sampleMapMor
          sampleMapMor sampleMapMor_preservesId sampleMapMor_preservesComp
          sampleMapMor_preservesId sampleMapMor_preservesComp)
          ((FreeCoprodCompDisc.natCopowerPlusEquiv sampleNatObj sampleMapMor
            sampleMapMor sampleMapMor_preservesId sampleMapMor_preservesComp
            sampleMapMor_preservesId sampleMapMor_preservesComp).symm
            sampleNatInr) =
        sampleNatInr :=
    (FreeCoprodCompDisc.natCopowerPlusEquiv sampleNatObj sampleMapMor
      sampleMapMor sampleMapMor_preservesId sampleMapMor_preservesComp
      sampleMapMor_preservesId sampleMapMor_preservesComp).apply_symm_apply
      sampleNatInr
  ```

  Extend the test file's module docstring summary with one sentence:
  "The copower–Yoneda adjunction round-trips the right-injection
  transformation."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant
  `FreeCoprodCompDisc.copowerHomMapMor`.

- [ ] **Step 3: Implement.** Append to the `FreeCoprodCompDisc`
  namespace of `FreeCoprodCompDisc/NatTrans.lean` (before
  `end FreeCoprodCompDisc`):

  ```lean
  /-- The object map `X ↦ Hom(c, X) ⊗ F X`: the copower of the value of
  `F` by the hom-set out of `c`. -/
  def copowerHomMap (c : FreeCoprodCompDisc.{u, v} I)
      (F : Map.{u, v, w} I O) : Map.{u, v, w} I O :=
    fun X ↦ copower.{u, w, u} O (Hom.{u, v, u} I c X) (F X)

  /-- The morphism-map component of `copowerHomMap`. -/
  def copowerHomMapMor (c : FreeCoprodCompDisc.{u, v} I)
      {F : Map.{u, v, w} I O} (mF : MapMor I O F) :
      MapMor I O (copowerHomMap c F) :=
    fun X Y h ↦
      coprodMor O (Hom I c X) (Hom I c Y) (fun e ↦ Hom.comp I e h)
        (fun _ ↦ F X) (fun _ ↦ F Y) (fun _ ↦ mF X Y h)

  /-- The object map `(c +)`: the binary coproduct with fixed left
  object `c`. -/
  def plusMap (c : FreeCoprodCompDisc.{u, v} I) : Map.{u, v, v} I I :=
    fun X ↦ plus.{v, u, u} I c X

  /-- The morphism-map component of `plusMap`. -/
  def plusMapMor (c : FreeCoprodCompDisc.{u, v} I) :
      MapMor I I (plusMap c) :=
    fun _ _ h ↦ coprodPairMor I (Hom.id I c) h

  /-- The forward direction of the copower–plus correspondence: from a
  transformation out of the copowered map to one into the
  `plus`-precomposed map. -/
  def natCopowerPlusToFun (c : FreeCoprodCompDisc.{u, v} I)
      {F G : Map.{u, v, w} I O} {mF : MapMor I O F} {mG : MapMor I O G}
      (hFcomp : PreservesComp F mF)
      (η : NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG) :
      NatTrans I O F (mapComp (plusMap c) G) mF
        (mapMorComp (plusMapMor c) mG) :=
    ⟨fun X ↦
      Hom.comp O (mF X (plus I c X) (coprodPairInr I c X))
        (Hom.comp O
          (coprodInj O (Hom I c (plus I c X)) (fun _ ↦ F (plus I c X))
            (coprodPairInl I c X))
          (η.1 (plus I c X))),
      fun X Y h ↦
        Subtype.ext (funext (fun a ↦
          (congrArg
              (fun t ↦ (η.1 (plus I c Y)).1 ⟨coprodPairInl I c Y, t⟩)
              ((congrFun (congrArg Subtype.val
                    (hFcomp X Y (plus I c Y) h (coprodPairInr I c Y)))
                  a).symm.trans
                (congrFun (congrArg Subtype.val
                    (hFcomp X (plus I c X) (plus I c Y)
                      (coprodPairInr I c X)
                      (coprodPairMor I (Hom.id I c) h)))
                  a))).trans
            (congrFun (congrArg Subtype.val
                (η.2 (plus I c X) (plus I c Y)
                  (coprodPairMor I (Hom.id I c) h)))
              ⟨coprodPairInl I c X,
                (mF X (plus I c X) (coprodPairInr I c X)).1 a⟩)))⟩

  /-- The backward direction of the copower–plus correspondence: from a
  transformation into the `plus`-precomposed map to one out of the
  copowered map. -/
  def natCopowerPlusInvFun (c : FreeCoprodCompDisc.{u, v} I)
      {F G : Map.{u, v, w} I O} {mF : MapMor I O F} {mG : MapMor I O G}
      (hGcomp : PreservesComp G mG)
      (θ : NatTrans I O F (mapComp (plusMap c) G) mF
        (mapMorComp (plusMapMor c) mG)) :
      NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG :=
    ⟨fun X ↦
      coprodDesc O (Hom I c X) (fun _ ↦ F X) (G X)
        (fun e ↦
          Hom.comp O (θ.1 X)
            (mG (plus I c X) X (coprodPairDesc I e (Hom.id I X)))),
      fun X Y h ↦
        Subtype.ext (funext (fun p ↦
          (congrArg
              (fun t ↦ (mG (plus I c Y) Y
                  (coprodPairDesc I (Hom.comp I p.1 h) (Hom.id I Y))).1 t)
              (congrFun (congrArg Subtype.val (θ.2 X Y h)) p.2)).trans
            ((congrFun (congrArg Subtype.val
                  (hGcomp (plus I c X) (plus I c Y) Y
                    (coprodPairMor I (Hom.id I c) h)
                    (coprodPairDesc I (Hom.comp I p.1 h) (Hom.id I Y))))
                ((θ.1 X).1 p.2)).symm.trans
              ((congrArg
                  (fun k ↦ (mG (plus I c X) Y k).1 ((θ.1 X).1 p.2))
                  (coprodPairMor_id_desc I h p.1)).trans
                (congrFun (congrArg Subtype.val
                    (hGcomp (plus I c X) X Y
                      (coprodPairDesc I p.1 (Hom.id I X)) h))
                  ((θ.1 X).1 p.2))))))⟩

  /-- The backward direction inverts the forward direction of the
  copower–plus correspondence. -/
  theorem natCopowerPlus_invFun_toFun (c : FreeCoprodCompDisc.{u, v} I)
      {F G : Map.{u, v, w} I O} {mF : MapMor I O F} {mG : MapMor I O G}
      (hFid : PreservesId F mF) (hFcomp : PreservesComp F mF)
      (hGcomp : PreservesComp G mG)
      (η : NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG) :
      natCopowerPlusInvFun c hGcomp (natCopowerPlusToFun c hFcomp η) = η :=
    Subtype.ext (funext (fun X ↦ Subtype.ext (funext (fun p ↦
      (congrFun (congrArg Subtype.val
            (η.2 (plus I c X) X (coprodPairDesc I p.1 (Hom.id I X))))
          ⟨coprodPairInl I c X,
            (mF X (plus I c X) (coprodPairInr I c X)).1 p.2⟩).symm.trans
        (congrArg (fun t ↦ (η.1 X).1 ⟨p.1, t⟩)
          ((congrFun (congrArg Subtype.val
                (hFcomp X (plus I c X) X (coprodPairInr I c X)
                  (coprodPairDesc I p.1 (Hom.id I X)))) p.2).symm.trans
            (congrFun (congrArg Subtype.val (hFid X)) p.2)))))))

  /-- The forward direction inverts the backward direction of the
  copower–plus correspondence. -/
  theorem natCopowerPlus_toFun_invFun (c : FreeCoprodCompDisc.{u, v} I)
      {F G : Map.{u, v, w} I O} {mF : MapMor I O F} {mG : MapMor I O G}
      (hGid : PreservesId G mG) (hGcomp : PreservesComp G mG)
      (hFcomp : PreservesComp F mF)
      (θ : NatTrans I O F (mapComp (plusMap c) G) mF
        (mapMorComp (plusMapMor c) mG)) :
      natCopowerPlusToFun c hFcomp (natCopowerPlusInvFun c hGcomp θ) = θ :=
    Subtype.ext (funext (fun X ↦ Subtype.ext (funext (fun a ↦
      (congrArg
          (fun t ↦ (mG (plus I c (plus I c X)) (plus I c X)
              (coprodPairDesc I (coprodPairInl I c X)
                (Hom.id I (plus I c X)))).1 t)
          (congrFun (congrArg Subtype.val
              (θ.2 X (plus I c X) (coprodPairInr I c X))) a)).trans
        ((congrFun (congrArg Subtype.val
              (hGcomp (plus I c X) (plus I c (plus I c X)) (plus I c X)
                (coprodPairMor I (Hom.id I c) (coprodPairInr I c X))
                (coprodPairDesc I (coprodPairInl I c X)
                  (Hom.id I (plus I c X)))))
            ((θ.1 X).1 a)).symm.trans
          ((congrArg
              (fun k ↦ (mG (plus I c X) (plus I c X) k).1 ((θ.1 X).1 a))
              (coprodPairMor_inr_desc_inl I (Z := c) (X := X))).trans
            (congrFun (congrArg Subtype.val (hGid (plus I c X)))
              ((θ.1 X).1 a))))))))

  /-- The copower–Yoneda adjunction: transformations out of the
  copowered map correspond to transformations into the
  `plus`-precomposed map. -/
  def natCopowerPlusEquiv (c : FreeCoprodCompDisc.{u, v} I)
      {F G : Map.{u, v, w} I O} (mF : MapMor I O F) (mG : MapMor I O G)
      (hFid : PreservesId F mF) (hFcomp : PreservesComp F mF)
      (hGid : PreservesId G mG) (hGcomp : PreservesComp G mG) :
      NatTrans I O (copowerHomMap c F) G (copowerHomMapMor c mF) mG ≃
        NatTrans I O F (mapComp (plusMap c) G) mF
          (mapMorComp (plusMapMor c) mG) :=
    { toFun := natCopowerPlusToFun c hFcomp,
      invFun := natCopowerPlusInvFun c hGcomp,
      left_inv := natCopowerPlus_invFun_toFun c hFid hFcomp hGcomp,
      right_inv := natCopowerPlus_toFun_invFun c hGid hGcomp hFcomp }
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `FreeCoprodCompDisc.copowerHomMap`,
    `FreeCoprodCompDisc.plusMap` (with their morphism maps) and
    `FreeCoprodCompDisc.natCopowerPlusEquiv` — the copower–Yoneda
    adjunction: transformations out of the copowered map correspond
    to transformations into the `plus`-precomposed map.
  ```

  and to `## Main statements`:

  ```markdown
  * `FreeCoprodCompDisc.natCopowerPlus_invFun_toFun`,
    `FreeCoprodCompDisc.natCopowerPlus_toFun_invFun` — the
    round-trip laws of the adjunction.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(cat): add the copower-yoneda adjunction"
  ```

---

## Task 6: the `Naturality` module and the per-summand delta decomposition

The naturality upgrade of Lemma 3 of
[HancockMcBrideGhaniMalatestaAltenkirch2013], in per-summand form:
the lemma's right-hand side is a coproduct over `i : B → I` whose
index type exceeds the uniform index universe, so the total
coproduct never appears as a functor. Each summand
`W i := X ↦ Hom(lift ⟨B, i⟩, X) ⊗ ⟦c i⟧ X` is a `Map` at the
uniform index universe; the upgrade delivers the natural inclusion
family `deltaInto`, the cotuple `deltaDesc` with its computation and
uniqueness laws (jointly, the inclusions are jointly epic), and the
decomposition `natDeltaEquiv` of transformations out of the `delta`
interpretation into families over the direction assignments. Since
`IR.interpDeltaIso` is a single non-recursive composite of
equivalences, these are direct calculations (after rewriting the
`⟦δ B c⟧`-side morphism map by `interpMor_delta`, with the
established transport eliminations for the weight equalities), not
inductions.

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec.lean` (add
  `public import Geb.Mathlib.Data.PFunctor.IndRec.Naturality` after
  the `Functor` import)
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec.lean` (add
  `import GebTests.Mathlib.Data.PFunctor.IndRec.Naturality` after
  the `Functor` import)

  Register in BOTH umbrellas — in branch 2a the source-umbrella
  registration was missed and only `pre-push.sh` caught it.

**Interfaces:**

- Consumes: `interpObj`, `interpMor`, `interpMor_delta` (branches 1,
  2b); `interpMorDelta` (branch 1, `Basic.lean`); `copowerHomMap`,
  `copowerHomMapMor` (Task 5); `lift`
  (branch 1); `IsNatTrans`, `NatTrans`, `NatTrans.id` (Task 2); the
  `Hom` category laws (branch 2b).
- Produces (in `namespace IndRec`, `namespace IR`;
  `variable (I : Type uI) (O : Type uO)`):

  ```lean
  interpObj_snd_cast (B) (c) (X) (e : i = j) (n) :
    (interpObj I O (c j) X).2 (cast … n) = (interpObj I O (c i) X).2 n
  deltaInto (B) (c) (i : B → I) (X) :
    FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)) X)
      (interpObj I O (delta I O B c) X)
  deltaDesc (B) (c) (X) (Z) (m) :
    FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z
  deltaInto_desc_aux — the transport-elimination step (statement
    below)
  deltaInto_desc (B) (c) (i) (X) (Z) (m) :
    FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X)
      (deltaDesc I O B c X Z m) = m i
  deltaDesc_eta (B) (c) (X) (Z) (h) :
    deltaDesc I O B c X Z
      (fun i ↦ FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) h)
      = h
  deltaHom_ext — joint epicness (statement below)
  interpMor_cast — transport commutation for the morphism map
    (statement below)
  DeltaIntoNaturalMotive / deltaInto_natural_base /
    deltaInto_natural — naturality of `deltaInto` in the object
    (statements below)
  natDeltaEquiv (B) (c) (mG) :
    FreeCoprodCompDisc.NatTrans I O (interpObj I O (delta I O B c)) G
        (interpMor I O (delta I O B c)) mG ≃
      ((i : B → I) → FreeCoprodCompDisc.NatTrans I O … mG)
  ```

- [ ] **Step 1: Create the test file (failing).**
  `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Naturality

  /-!
  # Tests for the naturality of the IR interpretation

  A `delta` code over Boolean indices whose subcode depends on its
  direction assignment exercises the per-summand decomposition: the
  injections, the cotuple, their computation law, naturality, and
  the transformation-space equivalence. Named theorems give the
  `GebMeta` axiom linter declarations to inspect.

  ## Tags

  inductive-recursive, interpretation, natural transformation
  -/

  @[expose] public section

  open CategoryTheory
  open IndRec IndRec.IR

  /-- A sample object over the Boolean index type. -/
  def sampleIObj : FreeCoprodCompDisc.{0, 0} Bool :=
    ⟨Bool, fun b ↦ b⟩

  /-- The direction-dependent subcode family of `sampleDeltaCode`. -/
  def sampleDeltaSub : (PUnit → Bool) → IR.{0, 0, 0, 0} Bool Bool :=
    fun j ↦ iota Bool Bool (j PUnit.unit)

  /-- A sample `delta` code whose subcode depends on the direction
  assignment. -/
  def sampleDeltaCode : IR.{0, 0, 0, 0} Bool Bool :=
    delta Bool Bool PUnit sampleDeltaSub

  /-- The sample delta injection evaluates a copower name to a delta
  name. -/
  theorem sampleDeltaInto_apply :
      (IR.deltaInto.{0, 0, 0, 0} Bool Bool PUnit sampleDeltaSub
          (fun _ ↦ true) sampleIObj).1
          ⟨⟨fun _ ↦ true, rfl⟩, ULift.up Unit.unit⟩ =
        ⟨fun _ ↦ true, ULift.up Unit.unit⟩ :=
    rfl

  /-- Restricting the sample delta cotuple along the sample injection
  recovers the component. -/
  theorem sampleDeltaInto_desc :
      FreeCoprodCompDisc.Hom.comp Bool
          (IR.deltaInto.{0, 0, 0, 0} Bool Bool PUnit sampleDeltaSub
            (fun _ ↦ true) sampleIObj)
          (IR.deltaDesc Bool Bool PUnit sampleDeltaSub sampleIObj
            (IR.interpObj Bool Bool sampleDeltaCode sampleIObj)
            (fun i ↦ IR.deltaInto Bool Bool PUnit sampleDeltaSub i sampleIObj)) =
        IR.deltaInto Bool Bool PUnit sampleDeltaSub (fun _ ↦ true) sampleIObj :=
    IR.deltaInto_desc Bool Bool PUnit sampleDeltaSub (fun _ ↦ true) sampleIObj
      (IR.interpObj Bool Bool sampleDeltaCode sampleIObj)
      (fun i ↦ IR.deltaInto Bool Bool PUnit sampleDeltaSub i sampleIObj)

  /-- Naturality of the sample delta injection. -/
  theorem sampleDeltaInto_natural :
      FreeCoprodCompDisc.IsNatTrans Bool Bool
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{0, 0, 0} Bool ⟨PUnit, fun _ ↦ true⟩)
          (IR.interpObj Bool Bool (sampleDeltaSub (fun _ ↦ true))))
        (IR.interpObj Bool Bool sampleDeltaCode)
        (FreeCoprodCompDisc.copowerHomMapMor
          (FreeCoprodCompDisc.lift.{0, 0, 0} Bool ⟨PUnit, fun _ ↦ true⟩)
          (IR.interpMor Bool Bool (sampleDeltaSub (fun _ ↦ true))))
        (IR.interpMor Bool Bool sampleDeltaCode)
        (IR.deltaInto Bool Bool PUnit sampleDeltaSub (fun _ ↦ true)) :=
    IR.deltaInto_natural Bool Bool PUnit sampleDeltaSub (fun _ ↦ true)

  /-- The per-summand delta decomposition round-trips the identity
  transformation. -/
  theorem sampleNatDeltaEquiv_roundtrip :
      (IR.natDeltaEquiv.{0, 0, 0, 0} Bool Bool PUnit sampleDeltaSub
            (IR.interpMor Bool Bool sampleDeltaCode)).symm
          ((IR.natDeltaEquiv Bool Bool PUnit sampleDeltaSub
            (IR.interpMor Bool Bool sampleDeltaCode))
            (FreeCoprodCompDisc.NatTrans.id
              (IR.interpObj Bool Bool sampleDeltaCode)
              (IR.interpMor Bool Bool sampleDeltaCode))) =
        FreeCoprodCompDisc.NatTrans.id (IR.interpObj Bool Bool sampleDeltaCode)
          (IR.interpMor Bool Bool sampleDeltaCode) :=
    (IR.natDeltaEquiv Bool Bool PUnit sampleDeltaSub
      (IR.interpMor Bool Bool sampleDeltaCode)).symm_apply_apply
      (FreeCoprodCompDisc.NatTrans.id (IR.interpObj Bool Bool sampleDeltaCode)
        (IR.interpMor Bool Bool sampleDeltaCode))
  ```

  Register the module in BOTH `IndRec` umbrellas as listed under
  **Files**.

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL —
  `Geb.Mathlib.Data.PFunctor.IndRec.Naturality` does not exist yet.

- [ ] **Step 3: Implement.** Create
  `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc.NatTrans
  public import Geb.Mathlib.Data.PFunctor.IndRec.Functor
  public import Geb.Mathlib.Data.PFunctor.IndRec.Hom

  /-!
  # Naturality of the IR interpretation and Theorem 3

  Toward Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]:
  the per-summand decomposition of transformation spaces at a `delta`
  code (the naturality upgrade of the paper's Lemma 3). Each copower
  summand — the value of `IR.interpObj` at a subcode, copowered by
  the morphisms out of the lifted direction assignment — includes
  into the `delta` interpretation naturally (`IR.deltaInto`); the
  inclusions admit a cotuple (`IR.deltaDesc`) and are jointly epic;
  and transformations out of the `delta` interpretation decompose
  into families of transformations out of the summands
  (`IR.natDeltaEquiv`).

  ## Main definitions

  * `IR.deltaInto`, `IR.deltaDesc` — the natural inclusions of the
    copower summands into the `delta` interpretation and their
    cotuple ([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 3,
    upgraded to per-summand natural form).
  * `IR.natDeltaEquiv` — the per-summand decomposition of
    transformation spaces at a `delta` code.

  ## Main statements

  * `IR.deltaInto_desc`, `IR.deltaDesc_eta`, `IR.deltaHom_ext` — the
    computation and uniqueness laws of the cotuple, and joint
    epicness of the inclusions.
  * `IR.deltaInto_natural` — naturality of the inclusions in the
    interpreted object.

  ## Implementation notes

  The total coproduct of Lemma 3 has an index type exceeding the
  uniform index universe, so it never appears as a
  `FreeCoprodCompDisc.Map`; the decomposition is per summand. The
  `delta`-side morphism map is rewritten by `IR.interpMor_delta`,
  and transports of names along equalities of direction assignments
  are eliminated by the cast lemmas `IR.interpObj_snd_cast` and
  `IR.interpMor_cast`, with `Eq.rec` motives at projection-reduced
  types and dependent `rfl`-proofs quantified inside the motive.

  ## References

  * [HancockMcBrideGhaniMalatestaAltenkirch2013]

  ## Tags

  inductive-recursive, interpretation, natural transformation
  -/

  @[expose] public section

  universe uA uB uI uO

  namespace IndRec

  open CategoryTheory

  variable (I : Type uI) (O : Type uO)

  namespace IR

  /-- Decoding of interpretation names commutes with transport along an
  equality of direction assignments. -/
  theorem interpObj_snd_cast (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) {i j : B → I}
      (e : i = j) (n : (interpObj I O (c i) X).1) :
      (interpObj I O (c j) X).2
          (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e) n) =
        (interpObj I O (c i) X).2 n :=
    Eq.rec (motive := fun j' e' ↦
        (interpObj I O (c j') X).2
            (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e') n) =
          (interpObj I O (c i) X).2 n)
      rfl e

  /-- The injection of the `i`-th copower summand into the `delta`
  interpretation: a copower name `⟨e, n⟩` maps to the delta name whose
  direction is `e.1` restricted along `ULift.up`, with `n` transported
  along the induced equality of direction assignments. -/
  def deltaInto (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (i : B → I) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpObj I O (c i)) X)
        (interpObj I O (delta I O B c) X) :=
    ⟨fun p ↦ ⟨p.1.1 ∘ ULift.up,
        cast (congrArg (fun t ↦ (interpObj I O (c t) X).1)
          (congrArg (· ∘ ULift.up) p.1.2).symm) p.2⟩,
      funext (fun p ↦
        interpObj_snd_cast I O B c X
          (congrArg (· ∘ ULift.up) p.1.2).symm p.2)⟩

  /-- The cotuple out of the `delta` interpretation: a delta name
  `⟨g, n⟩` is dispatched to the component of `m` at the direction
  assignment `X.2 ∘ g`, at the copower name pairing the lifted
  direction with `n`. -/
  def deltaDesc (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
      (m : (i : B → I) → FreeCoprodCompDisc.Hom O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpObj I O (c i)) X) Z) :
      FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z :=
    ⟨fun q ↦ (m (X.2 ∘ q.1)).1 ⟨⟨q.1 ∘ ULift.down, rfl⟩, q.2⟩,
      funext (fun q ↦
        congrFun (m (X.2 ∘ q.1)).2 ⟨⟨q.1 ∘ ULift.down, rfl⟩, q.2⟩)⟩

  /-- The transport-elimination step of `IR.deltaInto_desc`: the target
  direction assignment is generalized together with the transport
  equality and the inner commutation proof, so the base case is
  definitional. -/
  theorem deltaInto_desc_aux (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
      (m : (i' : B → I) → FreeCoprodCompDisc.Hom O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i'⟩)
          (interpObj I O (c i')) X) Z)
      (e : FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
      (n : (interpObj I O (c i) X).1) (j : B → I) (h : i = j)
      (pf : X.2 ∘ ((e.1 ∘ ULift.up) ∘ ULift.down) =
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, j⟩).2) :
      (m j).1 ⟨⟨(e.1 ∘ ULift.up) ∘ ULift.down, pf⟩,
          cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) h) n⟩ =
        (m i).1 ⟨e, n⟩ :=
    Eq.rec (motive := fun j' h' ↦
        ∀ pf' : X.2 ∘ ((e.1 ∘ ULift.up) ∘ ULift.down) =
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, j'⟩).2,
        (m j').1 ⟨⟨(e.1 ∘ ULift.up) ∘ ULift.down, pf'⟩,
            cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) h') n⟩ =
          (m i).1 ⟨e, n⟩)
      (fun _ ↦ rfl) h pf

  /-- Restricting the delta cotuple along the `i`-th injection recovers
  the component. -/
  theorem deltaInto_desc (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
      (m : (i' : B → I) → FreeCoprodCompDisc.Hom O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i'⟩)
          (interpObj I O (c i')) X) Z) :
      FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X)
        (deltaDesc I O B c X Z m) = m i :=
    Subtype.ext (funext (fun p ↦
      deltaInto_desc_aux I O B c i X Z m p.1 p.2
        (X.2 ∘ (p.1.1 ∘ ULift.up))
        ((congrArg (· ∘ ULift.up) p.1.2).symm) rfl))

  /-- Every morphism out of the delta interpretation is the cotuple of
  its restrictions along the injections. -/
  theorem deltaDesc_eta (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
      (h : FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z) :
      deltaDesc I O B c X Z
          (fun i ↦ FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) h) =
        h :=
    Subtype.ext (funext (fun _ ↦ rfl))

  /-- The `IR.deltaInto` family is jointly epic: two morphisms out of
  the delta interpretation agree when their restrictions along every
  injection agree. -/
  theorem deltaHom_ext (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I)
      (Z : FreeCoprodCompDisc.{max uA uB, uO} O)
      (f g : FreeCoprodCompDisc.Hom O (interpObj I O (delta I O B c) X) Z)
      (hfg : ∀ i : B → I,
        FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) f =
          FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) g) :
      f = g :=
    (deltaDesc_eta I O B c X Z f).symm.trans
      ((congrArg (deltaDesc I O B c X Z) (funext hfg)).trans
        (deltaDesc_eta I O B c X Z g))

  /-- `IR.interpMor` commutes with transport of names along an equality
  of direction assignments. -/
  theorem interpMor_cast (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I X Y) {i j : B → I} (e : i = j)
      (n : (interpObj I O (c i) X).1) :
      cast (congrArg (fun t ↦ (interpObj I O (c t) Y).1) e)
          ((interpMor I O (c i) X Y h).1 n) =
        (interpMor I O (c j) X Y h).1
          (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e) n) :=
    Eq.rec (motive := fun j' e' ↦
        cast (congrArg (fun t ↦ (interpObj I O (c t) Y).1) e')
            ((interpMor I O (c i) X Y h).1 n) =
          (interpMor I O (c j') X Y h).1
            (cast (congrArg (fun t ↦ (interpObj I O (c t) X).1) e') n))
      rfl e

  /-- The motive of the commutation-equality elimination in
  `IR.deltaInto_natural`: the domain decoding is generalized together
  with the morphism's commutation proof, and the delta-side morphism
  map appears in its `IR.interpMorDelta` form. -/
  def DeltaIntoNaturalMotive (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
      (X1 : Type (max uA uB)) (Y : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h1 : X1 → Y.1) (x2 : X1 → I) (hcomm : Y.2 ∘ h1 = x2) : Prop :=
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.copowerHomMapMor
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpMor I O (c i)) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩)
        (deltaInto I O B c i Y) =
      FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i ⟨X1, x2⟩)
        (interpMorDelta I O B (fun f ↦ interpObj I O (c f))
          (fun f ↦ interpMor I O (c f)) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩)

  /-- The base case of `IR.deltaInto_natural`: at a factored domain
  decoding with reflexive commutation proof, the `homOfEq` transport in
  `IR.interpMorDelta` reduces definitionally and the square reduces to
  `IR.interpMor_cast` componentwise. -/
  theorem deltaInto_natural_base (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
      (X1 : Type (max uA uB)) (Y : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h1 : X1 → Y.1) :
      DeltaIntoNaturalMotive I O B c i X1 Y h1 (Y.2 ∘ h1) rfl :=
    Subtype.ext (funext (fun p ↦
      congrArg
        (fun t ↦ (⟨h1 ∘ (p.1.1 ∘ ULift.up), t⟩ :
          Σ g : B → Y.1, (interpObj I O (c (Y.2 ∘ g)) Y).1))
        (interpMor_cast I O B c ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩
          ((congrArg (· ∘ ULift.up) p.1.2).symm) p.2)))

  /-- Naturality of `IR.deltaInto` in the object. -/
  theorem deltaInto_natural (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (i : B → I) :
      FreeCoprodCompDisc.IsNatTrans I O
        (FreeCoprodCompDisc.copowerHomMap
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpObj I O (c i)))
        (interpObj I O (delta I O B c))
        (FreeCoprodCompDisc.copowerHomMapMor
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
          (interpMor I O (c i)))
        (interpMor I O (delta I O B c))
        (deltaInto I O B c i) :=
    fun X Y h ↦
      match X, h with
      | ⟨X1, x2⟩, ⟨h1, hcomm⟩ =>
        (Eq.rec (motive := fun x2' hcomm' ↦
            DeltaIntoNaturalMotive I O B c i X1 Y h1 x2' hcomm')
          (deltaInto_natural_base I O B c i X1 Y h1) hcomm).trans
          (congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O
              (deltaInto I O B c i ⟨X1, x2⟩) (t ⟨X1, x2⟩ Y ⟨h1, hcomm⟩))
            (interpMor_delta I O B c).symm)

  /-- The per-summand decomposition of transformation spaces at a
  `delta` code: transformations out of the `delta` interpretation
  correspond to families, over the direction assignments, of
  transformations out of the copower summands. -/
  def natDeltaEquiv (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      {G : FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O}
      (mG : FreeCoprodCompDisc.MapMor I O G) :
      FreeCoprodCompDisc.NatTrans I O (interpObj I O (delta I O B c)) G
          (interpMor I O (delta I O B c)) mG ≃
        ((i : B → I) → FreeCoprodCompDisc.NatTrans I O
          (FreeCoprodCompDisc.copowerHomMap
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
            (interpObj I O (c i))) G
          (FreeCoprodCompDisc.copowerHomMapMor
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
            (interpMor I O (c i))) mG) :=
    { toFun := fun η i ↦
        ⟨fun X ↦
          FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X) (η.1 X),
          fun X Y h ↦
            (congrArg
                (fun t ↦ FreeCoprodCompDisc.Hom.comp O t (η.1 Y))
                (deltaInto_natural I O B c i X Y h)).trans
              (congrArg
                (FreeCoprodCompDisc.Hom.comp O (deltaInto I O B c i X))
                (η.2 X Y h))⟩,
      invFun := fun θ ↦
        ⟨fun X ↦ deltaDesc I O B c X (G X) (fun i ↦ (θ i).1 X),
          fun X Y h ↦
            deltaHom_ext I O B c X (G Y) _ _ (fun i ↦
              (((congrArg
                    (fun t ↦ FreeCoprodCompDisc.Hom.comp O t
                      (deltaDesc I O B c Y (G Y) (fun i' ↦ (θ i').1 Y)))
                    (deltaInto_natural I O B c i X Y h)).symm.trans
                ((congrArg
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.copowerHomMapMor
                        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB}
                          I ⟨B, i⟩)
                        (interpMor I O (c i)) X Y h))
                    (deltaInto_desc I O B c i Y (G Y)
                      (fun i' ↦ (θ i').1 Y))).trans
                  ((θ i).2 X Y h))).trans
              (congrArg
                (fun t ↦ FreeCoprodCompDisc.Hom.comp O t (mG X Y h))
                (deltaInto_desc I O B c i X (G X)
                  (fun i' ↦ (θ i').1 X)).symm)))⟩,
      left_inv := fun η ↦ Subtype.ext (funext (fun X ↦
        deltaDesc_eta I O B c X (G X) (η.1 X))),
      right_inv := fun θ ↦ funext (fun i ↦ Subtype.ext (funext (fun X ↦
        deltaInto_desc I O B c i X (G X) (fun i' ↦ (θ i').1 X)))) }

  end IR

  end IndRec
  ```

  (The module docstring at this commit describes only this task's
  declarations; Tasks 7–10 extend it as their content lands, and
  Task 10 rewrites the first paragraph to the delivered-Theorem-3
  form.)

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS. Also run `scripts/lint-imports.sh` (new module and
  umbrella registrations).

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add the naturality module and the delta decomposition"
  ```

---

## Task 7: the Lemma 4 naturality upgrade

The naturality upgrade of Lemma 4 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]: for fixed `Q`, `i`,
`γ`, the existing pointwise isomorphism family `IR.interpPrecompIso`
is natural between the precomposed interpretation and the direct
interpretation at the coproduct object, whose right-hand side
`k ↦ ⟦γ⟧ (plus ⟨Q, i⟩ k)` carries the composite morphism map
`h ↦ interpMor γ _ _ (coprodPairMor (Hom.id ⟨Q, i⟩) h)` (the
heterogeneous `coprodPairMor` instantiation). The square is
`Prop`-valued, so the proof goes by `IR.induction` on `γ`, using
branch 2b's characterizing equations, with the transport
eliminations in the manner of `InterpMorCompHgMotive`.

Elaboration-order rule (verified; from Global Constraints): in the
inductive step, rewrite `interpPrecompIso` to step form FIRST (it
appears on both sides), then eliminate the morphism's commutation
equality, then split on the shape, and only then rewrite `interpMor`
— the precomposed code is a stuck match until the shape is known,
after which it is definitionally a constructor form
(per-constructor equations apply to it; `interpMor_mk` to the `mk`
side). `congrArg` lambdas that apply a rewritten term need explicit
binder types (`fun (t : MorMapSig I O …) ↦ …`), and
anonymous-constructor `Hom`s passed as proof arguments need type
ascription. The verified forms below already encode all of this.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`

**Interfaces:**

- Consumes: `precomp`, `precompMerge`, `precompMerge_elim`,
  `interpPrecompIso`, `interpPrecompIsoStep`, `arrowSumMerge`,
  `arrowSumMerge_eq`, `ArrowSumClassifier`, `ArrowSumUnresolved`
  (branch 1); `rec_mk`, `interpMor_mk`, `interpMor_iota`,
  `interpMor_sigma`, `interpMor_delta`, `MorMapSig`, `induction`,
  `InductionStep` (branches 1, 2b); `isoOfEq`, `homOfEq`, `plus`,
  `Hom.id` (branch 1); `Iso.hom` (Task 1); `coprodPairMor`
  (Task 1); `IsNatTrans` (Task 2).
- Produces:

  ```lean
  precompRhsMap (Q : Type uB) (i : Q → I)
    (γ : IR.{max uA uB, uB, uI, uO} I O) :
    FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O
  precompRhsMapMor (Q) (i) (γ) :
    FreeCoprodCompDisc.MapMor I O (precompRhsMap I O Q i γ)
  interpPrecompIso_mk (s) (d) :
    interpPrecompIso I O (mk I O s d) =
      interpPrecompIsoStep I O s d (fun x ↦ interpPrecompIso I O (d x))
  arrowSumMerge_map — merge-map commutation (statement below)
  interpMor_isoOfEq — the `IR.interpMor_cast` companion at
    object-equality transports (statement below)
  PrecompNatDeltaPairMotive / PrecompNatDeltaPairInnerMotive /
    precompNatDeltaPair_inner / precompNatDeltaPair — the `δ`-case
    transport-commutation square and its eliminations
  PrecompNatMotive / PrecompNatMkMotive / precompNat_mk_iota /
    precompNat_mk_sigma / precompNat_mk_delta / precompNat_mk_base /
    interpPrecompIso_natural_step — the induction motives and steps
  interpPrecompIso_natural (γ) (Q) (i) :
    FreeCoprodCompDisc.IsNatTrans I O
      (interpObj I O (precomp I O Q i γ)) (precompRhsMap I O Q i γ)
      (interpMor I O (precomp I O Q i γ)) (precompRhsMapMor I O Q i γ)
      (fun k ↦ FreeCoprodCompDisc.Iso.hom O
        (interpPrecompIso I O γ Q i k))
  ```

  (Verified universe instantiation, already encoded below:
  `plus.{uI, uB, max uA uB}` in `precompRhsMap` — the section
  variable comes first in `plus`'s list.)

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`:

  ```lean
  /-- The characterizing equation of `IR.interpPrecompIso` at a concrete
  `ι`-shaped code. -/
  theorem sampleInterpPrecompIso_mk :
      IR.interpPrecompIso.{0, 0, 0, 0} Bool Bool
          (IR.mk Bool Bool (Sum.inl true) PEmpty.elim) =
        IR.interpPrecompIsoStep Bool Bool (Sum.inl true) PEmpty.elim
          (fun x ↦ IR.interpPrecompIso Bool Bool (PEmpty.elim x)) :=
    IR.interpPrecompIso_mk Bool Bool (Sum.inl true) PEmpty.elim

  /-- Postcomposing merged-assignment values commutes with the merge at
  the sample types. -/
  theorem sampleArrowSumMerge_map (c : ArrowSumClassifier.{0, 0, 0} Bool Bool)
      (j : ArrowSumUnresolved c → Bool) (b : Bool) :
      Sum.map _root_.id Bool.not (arrowSumMerge c j b) =
        arrowSumMerge c (Bool.not ∘ j) b :=
    IR.arrowSumMerge_map c j Bool.not b

  /-- Naturality of the Lemma 4 isomorphism family at the sample delta
  code. -/
  theorem samplePrecompNat :
      FreeCoprodCompDisc.IsNatTrans Bool Bool
        (IR.interpObj Bool Bool
          (IR.precomp Bool Bool PUnit (fun _ ↦ false) sampleDeltaCode))
        (IR.precompRhsMap Bool Bool PUnit (fun _ ↦ false) sampleDeltaCode)
        (IR.interpMor Bool Bool
          (IR.precomp Bool Bool PUnit (fun _ ↦ false) sampleDeltaCode))
        (IR.precompRhsMapMor Bool Bool PUnit (fun _ ↦ false) sampleDeltaCode)
        (fun k ↦ FreeCoprodCompDisc.Iso.hom Bool
          (IR.interpPrecompIso Bool Bool sampleDeltaCode PUnit
            (fun _ ↦ false) k)) :=
    IR.interpPrecompIso_natural Bool Bool sampleDeltaCode PUnit (fun _ ↦ false)
  ```

  Extend the test file's module docstring summary with one sentence:
  "The Lemma 4 naturality upgrade and its characterizing equation
  are exercised at the sample code."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.interpPrecompIso_mk`.

- [ ] **Step 3: Implement.** Append to the `IR` namespace of
  `Naturality.lean` (before `end IR`):

  ```lean
  /-- The right-hand object map of the Lemma 4 naturality square: the
  direct interpretation of `γ` at the coproduct of `⟨Q, i⟩` with the
  argument object. -/
  def precompRhsMap (Q : Type uB) (i : Q → I)
      (γ : IR.{max uA uB, uB, uI, uO} I O) :
      FreeCoprodCompDisc.Map.{max uA uB, uI, uO} I O :=
    fun k ↦ interpObj I O γ (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, i⟩ k)

  /-- The morphism-map component of `IR.precompRhsMap`: the direct
  interpretation's morphism map at the coproduct of the identity on
  `⟨Q, i⟩` with the argument morphism. -/
  def precompRhsMapMor (Q : Type uB) (i : Q → I)
      (γ : IR.{max uA uB, uB, uI, uO} I O) :
      FreeCoprodCompDisc.MapMor I O (precompRhsMap I O Q i γ) :=
    fun X Y h ↦ interpMor I O γ
      (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X) (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
      (FreeCoprodCompDisc.coprodPairMor I (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h)

  /-- The characterizing equation of `IR.interpPrecompIso` at `IR.mk`:
  the isomorphism family computes by one step of
  `IR.interpPrecompIsoStep`. -/
  theorem interpPrecompIso_mk (s : Shape.{max uA uB, uB, uO} O)
      (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O) :
      interpPrecompIso I O (mk I O s d) =
        interpPrecompIsoStep I O s d (fun x ↦ interpPrecompIso I O (d x)) :=
    rec_mk I O (interpPrecompIsoStep I O) s d

  /-- Postcomposing the values of a merged assignment commutes with the
  merge, pointwise: case analysis on the classifier at each element. -/
  theorem arrowSumMerge_map {B : Type uB} {X : Type uB}
      {Y Z : Type (max uA uB)} (c : ArrowSumClassifier.{uB, uB, uB} B X)
      (j : ArrowSumUnresolved c → Y) (h : Y → Z) (b : B) :
      Sum.map _root_.id h (arrowSumMerge c j b) = arrowSumMerge c (h ∘ j) b :=
    Sum.casesOn (motive := fun t ↦ c b = t →
        Sum.map _root_.id h (arrowSumMerge c j b) = arrowSumMerge c (h ∘ j) b)
      (c b)
      (fun x hx ↦
        (congrArg (Sum.map _root_.id h) (arrowSumMerge_eq c j b (Sum.inl x) hx)).trans
          (arrowSumMerge_eq c (h ∘ j) b (Sum.inl x) hx).symm)
      (fun u hu ↦
        (congrArg (Sum.map _root_.id h) (arrowSumMerge_eq c j b (Sum.inr u) hu)).trans
          (arrowSumMerge_eq c (h ∘ j) b (Sum.inr u) hu).symm)
      rfl

  /-- `IR.interpMor` commutes with `FreeCoprodCompDisc.isoOfEq`
  transport of names along an equality of direction assignments (the
  `IR.interpMor_cast` companion at object-equality transports). -/
  theorem interpMor_isoOfEq (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (V W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (pm : FreeCoprodCompDisc.Hom I V W) {m₀ m₁ : B → I} (e : m₀ = m₁)
      (u : (interpObj I O (c m₀) V).1) :
      (FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (c m) W) e)).1
          ((interpMor I O (c m₀) V W pm).1 u) =
        (interpMor I O (c m₁) V W pm).1
          ((FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m ↦ interpObj I O (c m) V) e)).1 u) :=
    Eq.rec (motive := fun m' e' ↦
        (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m ↦ interpObj I O (c m) W) e')).1
            ((interpMor I O (c m₀) V W pm).1 u) =
          (interpMor I O (c m') V W pm).1
            ((FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun m ↦ interpObj I O (c m) V) e')).1 u))
      rfl e

  /-- The motive of the commutation-proof elimination in
  `IR.precompNatDeltaPair`: the domain decoding of the coproduct
  morphism is generalized together with its commutation proof, and the
  assignment equalities (whose types depend on it) are quantified
  inside. -/
  def PrecompNatDeltaPairMotive (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (V1 : Type (max uA uB)) (W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (p1 : V1 → W.1) (gx : B → V1) (m₀ : B → I)
      (v2 : V1 → I) (p2 : W.2 ∘ p1 = v2) : Prop :=
    ∀ (gy : B → W.1), p1 ∘ gx = gy →
      ∀ (eX : m₀ = v2 ∘ gx) (eY : m₀ = W.2 ∘ gy)
        (u : (interpObj I O (c m₀) ⟨V1, v2⟩).1),
      (⟨gy, (FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (c m) W) eY)).1
          ((interpMor I O (c m₀) ⟨V1, v2⟩ W ⟨p1, p2⟩).1 u)⟩ :
        (interpObj I O (delta I O B c) W).1) =
      ⟨p1 ∘ gx,
        (FreeCoprodCompDisc.homOfEq O
            (congrArg (fun t ↦ interpObj I O (c (t ∘ gx)) W) p2.symm)
            (interpMor I O (c (v2 ∘ gx)) ⟨V1, v2⟩ W ⟨p1, p2⟩)).1
          ((FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun m ↦ interpObj I O (c m) ⟨V1, v2⟩) eX)).1 u)⟩

  /-- The motive of the reassembled-assignment elimination inside the
  base case of `IR.precompNatDeltaPair`: the codomain-side assignment is
  generalized together with its factoring through the coproduct
  morphism, at the already-factored domain decoding (where the
  `homOfEq` transport has reduced definitionally). -/
  def PrecompNatDeltaPairInnerMotive (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (V1 : Type (max uA uB)) (W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (p1 : V1 → W.1) (gx : B → V1) (m₀ : B → I) (gy : B → W.1) : Prop :=
    ∀ (eX : m₀ = (W.2 ∘ p1) ∘ gx) (eY : m₀ = W.2 ∘ gy)
      (u : (interpObj I O (c m₀) ⟨V1, W.2 ∘ p1⟩).1),
    (⟨gy, (FreeCoprodCompDisc.isoOfEq O
        (congrArg (fun m ↦ interpObj I O (c m) W) eY)).1
        ((interpMor I O (c m₀) ⟨V1, W.2 ∘ p1⟩ W ⟨p1, rfl⟩).1 u)⟩ :
      (interpObj I O (delta I O B c) W).1) =
    ⟨p1 ∘ gx,
      (interpMor I O (c ((W.2 ∘ p1) ∘ gx)) ⟨V1, W.2 ∘ p1⟩ W ⟨p1, rfl⟩).1
        ((FreeCoprodCompDisc.isoOfEq O
          (congrArg (fun m ↦ interpObj I O (c m) ⟨V1, W.2 ∘ p1⟩) eX)).1 u)⟩

  /-- The base case of both eliminations in `IR.precompNatDeltaPair`:
  at the factored assignment `p1 ∘ gx`, the two assignment-equality
  transports commute with the morphism map by `IR.interpMor_isoOfEq`
  under the common first component. -/
  theorem precompNatDeltaPair_inner (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (V1 : Type (max uA uB)) (W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (p1 : V1 → W.1) (gx : B → V1) (m₀ : B → I) :
      PrecompNatDeltaPairInnerMotive I O B c V1 W p1 gx m₀ (p1 ∘ gx) :=
    fun eX _ u ↦
      congrArg (fun t ↦ (⟨p1 ∘ gx, t⟩ : (interpObj I O (delta I O B c) W).1))
        (interpMor_isoOfEq I O B c ⟨V1, W.2 ∘ p1⟩ W ⟨p1, rfl⟩ eX u)

  /-- The transport-commutation square of the `delta` case of the
  naturality upgrade: relabeling a merged assignment on both sides of
  the morphism map (by `FreeCoprodCompDisc.isoOfEq` at the domain and
  codomain objects) agrees with the `homOfEq`-transported component of
  `IR.interpMorDelta`, as elements of the direct `delta` interpretation
  at the codomain. -/
  theorem precompNatDeltaPair (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (V1 : Type (max uA uB)) (W : FreeCoprodCompDisc.{max uA uB, uI} I)
      (p1 : V1 → W.1) (gx : B → V1) (m₀ : B → I)
      (v2 : V1 → I) (p2 : W.2 ∘ p1 = v2) :
      PrecompNatDeltaPairMotive I O B c V1 W p1 gx m₀ v2 p2 :=
    Eq.rec (motive := fun v2' p2' ↦
        PrecompNatDeltaPairMotive I O B c V1 W p1 gx m₀ v2' p2')
      (fun _gy e1 ↦
        Eq.rec (motive := fun gy' _ ↦
            PrecompNatDeltaPairInnerMotive I O B c V1 W p1 gx m₀ gy')
          (precompNatDeltaPair_inner I O B c V1 W p1 gx m₀) e1)
      p2

  /-- The motive of the naturality upgrade of Lemma 4
  ([HancockMcBrideGhaniMalatestaAltenkirch2013]): for each code, at
  every precomposition datum, the `IR.interpPrecompIso` family is
  natural between the precomposed interpretation and the direct
  interpretation at the coproduct object. -/
  def PrecompNatMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
    ∀ (Q : Type uB) (i : Q → I),
      FreeCoprodCompDisc.IsNatTrans I O
        (interpObj I O (precomp I O Q i γ)) (precompRhsMap I O Q i γ)
        (interpMor I O (precomp I O Q i γ)) (precompRhsMapMor I O Q i γ)
        (fun k ↦ FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q i k))

  /-- The motive of the commutation-equality elimination in the
  inductive step of the naturality upgrade: the domain decoding is
  generalized together with the morphism's commutation proof, at the
  `IR.interpPrecompIsoStep` form of the isomorphism family. -/
  def PrecompNatMkMotive (s : Shape.{max uA uB, uB, uO} O)
      (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
      (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1)
      (x2 : X1 → I) (hcomm : Y.2 ∘ h1 = x2) : Prop :=
    FreeCoprodCompDisc.Hom.comp O
        (interpMor I O (precomp I O Q i (mk I O s d)) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩)
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIsoStep I O s d
            (fun x ↦ interpPrecompIso I O (d x)) Q i Y)) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIsoStep I O s d
            (fun x ↦ interpPrecompIso I O (d x)) Q i ⟨X1, x2⟩))
        (interpMor I O (mk I O s d)
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ ⟨X1, x2⟩)
          (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) ⟨h1, hcomm⟩))

  /-- The `iota` case of the naturality upgrade: after the
  characterizing equations, both legs of the square are identities on
  the constant singleton interpretation. -/
  theorem precompNat_mk_iota (o : O)
      (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
      (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1) :
      PrecompNatMkMotive I O (Sum.inl o) d Q i X1 Y h1 (Y.2 ∘ h1) rfl :=
    (congrArg
        (fun (t : MorMapSig I O (iota I O o)) ↦
          FreeCoprodCompDisc.Hom.comp O (t ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIsoStep I O (Sum.inl o) d
                (fun x ↦ interpPrecompIso I O (d x)) Q i Y)))
        (interpMor_iota I O o)).trans
      (congrArg
        (fun (t : MorMapSig I O (mk I O (Sum.inl o) d)) ↦
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIsoStep I O (Sum.inl o) d
                (fun x ↦ interpPrecompIso I O (d x)) Q i ⟨X1, Y.2 ∘ h1⟩))
            (t (FreeCoprodCompDisc.plus I ⟨Q, i⟩ ⟨X1, Y.2 ∘ h1⟩)
              (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
              (FreeCoprodCompDisc.coprodPairMor I
                (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) ⟨h1, rfl⟩)))
        (interpMor_mk I O (Sum.inl o) d).symm)

  /-- The `sigma` case of the naturality upgrade: after the
  characterizing equations, both paths around the square compute
  componentwise, and each summand's square is the inductive hypothesis
  at the summand's subcode. -/
  theorem precompNat_mk_sigma (A : Type (max uA uB))
      (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
        PrecompNatMotive I O (d x))
      (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
      (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1) :
      PrecompNatMkMotive I O (Sum.inr (Sum.inl A)) d Q i X1 Y h1 (Y.2 ∘ h1) rfl :=
    Subtype.ext (funext (fun p ↦
      ((congrArg
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIsoStep I O (Sum.inr (Sum.inl A)) d
              (fun x ↦ interpPrecompIso I O (d x)) Q i Y)).1
          (congrFun (congrArg Subtype.val
              (congrFun (congrFun (congrFun
                (interpMor_sigma I O (ULift.{uB} A)
                  (fun a ↦ precomp I O Q i (d (ULift.up a.down))))
                ⟨X1, Y.2 ∘ h1⟩) Y) ⟨h1, rfl⟩))
            p)).trans
        (congrArg
          (fun t ↦ (⟨p.1.down, t⟩ :
            (interpObj I O (mk I O (Sum.inr (Sum.inl A)) d)
              (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)).1))
          (congrFun (congrArg Subtype.val
              (ih (ULift.up p.1.down) Q i ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩))
            p.2))).trans
      (congrFun (congrArg Subtype.val
          (congrFun (congrFun (congrFun
            (interpMor_mk I O (Sum.inr (Sum.inl A)) d)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ ⟨X1, Y.2 ∘ h1⟩))
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y))
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) ⟨h1, rfl⟩)))
        ((FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIsoStep I O (Sum.inr (Sum.inl A)) d
            (fun x ↦ interpPrecompIso I O (d x)) Q i ⟨X1, Y.2 ∘ h1⟩)).1 p)).symm))

  /-- The `delta` case of the naturality upgrade: after the
  characterizing equations, a name of the precomposed `delta`
  interpretation is chased componentwise through both paths of the
  square — the classifier component is preserved, the summand's square
  is the inductive hypothesis at the merged assignment, and the
  remaining transports commute by `IR.precompNatDeltaPair`. -/
  theorem precompNat_mk_delta (B : Type uB)
      (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
        IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
        PrecompNatMotive I O (d x))
      (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
      (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1) :
      PrecompNatMkMotive I O (Sum.inr (Sum.inr B)) d Q i X1 Y h1 (Y.2 ∘ h1) rfl :=
    Subtype.ext (funext (fun p ↦
      ((congrArg
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIsoStep I O (Sum.inr (Sum.inr B)) d
              (fun x ↦ interpPrecompIso I O (d x)) Q i Y)).1
          (congrFun (congrArg Subtype.val
              (congrFun (congrFun (congrFun
                (interpMor_sigma I O
                  (ULift.{max uA uB} (ArrowSumClassifier.{uB, uB, uB} B Q))
                  (fun cl ↦ delta I O (ArrowSumUnresolved cl.down)
                    (fun j ↦ precomp I O Q i
                      (d (ULift.up (precompMerge I Q i cl.down j))))))
                ⟨X1, Y.2 ∘ h1⟩) Y) ⟨h1, rfl⟩))
            p)).trans
        ((congrArg
            (fun t ↦ (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIsoStep I O (Sum.inr (Sum.inr B)) d
                (fun x ↦ interpPrecompIso I O (d x)) Q i Y)).1
              (⟨p.1, t⟩ :
                (interpObj I O
                  (precomp I O Q i (mk I O (Sum.inr (Sum.inr B)) d)) Y).1))
            (congrFun (congrArg Subtype.val
                (congrFun (congrFun (congrFun
                  (interpMor_delta I O (ArrowSumUnresolved p.1.down)
                    (fun j ↦ precomp I O Q i
                      (d (ULift.up (precompMerge I Q i p.1.down j)))))
                  ⟨X1, Y.2 ∘ h1⟩) Y) ⟨h1, rfl⟩))
              p.2)).trans
          ((congrArg
              (fun t ↦ (⟨arrowSumMerge p.1.down (h1 ∘ p.2.1),
                (FreeCoprodCompDisc.isoOfEq O
                  (congrArg
                    (fun m ↦ interpObj I O (d (ULift.up m))
                      (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y))
                    (precompMerge_elim I Q i Y B p.1.down (h1 ∘ p.2.1)))).1 t⟩ :
                (interpObj I O (mk I O (Sum.inr (Sum.inr B)) d)
                  (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)).1))
              (congrFun (congrArg Subtype.val
                  (ih (ULift.up
                      (precompMerge I Q i p.1.down ((Y.2 ∘ h1) ∘ p.2.1))) Q i
                    ⟨X1, Y.2 ∘ h1⟩ Y ⟨h1, rfl⟩))
                p.2.2)).trans
            (precompNatDeltaPair I O B (fun m ↦ d (ULift.up m)) (Q ⊕ X1)
              (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y) (Sum.map _root_.id h1)
              (arrowSumMerge p.1.down p.2.1)
              (precompMerge I Q i p.1.down ((Y.2 ∘ h1) ∘ p.2.1))
              (Sum.elim i (Y.2 ∘ h1))
              (FreeCoprodCompDisc.coprodPairMor I
                (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩)
                (⟨h1, rfl⟩ :
                  FreeCoprodCompDisc.Hom I ⟨X1, Y.2 ∘ h1⟩ Y)).2
              (arrowSumMerge p.1.down (h1 ∘ p.2.1))
              (funext (fun b ↦ arrowSumMerge_map p.1.down p.2.1 h1 b))
              (precompMerge_elim I Q i ⟨X1, Y.2 ∘ h1⟩ B p.1.down p.2.1)
              (precompMerge_elim I Q i Y B p.1.down (h1 ∘ p.2.1))
              ((FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O
                  (d (ULift.up
                    (precompMerge I Q i p.1.down ((Y.2 ∘ h1) ∘ p.2.1)))) Q i
                  ⟨X1, Y.2 ∘ h1⟩)).1 p.2.2))))).trans
      (congrFun (congrArg Subtype.val
          (congrFun (congrFun (congrFun
            (interpMor_mk I O (Sum.inr (Sum.inr B)) d)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ ⟨X1, Y.2 ∘ h1⟩))
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y))
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) ⟨h1, rfl⟩)))
        ((FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIsoStep I O (Sum.inr (Sum.inr B)) d
            (fun x ↦ interpPrecompIso I O (d x)) Q i ⟨X1, Y.2 ∘ h1⟩)).1 p)).symm))

  /-- The per-shape dispatch of the naturality upgrade's base case. -/
  theorem precompNat_mk_base (s : Shape.{max uA uB, uB, uO} O)
      (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O)
      (ih : (x : Direction I O s) → PrecompNatMotive I O (d x))
      (Q : Type uB) (i : Q → I) (X1 : Type (max uA uB))
      (Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h1 : X1 → Y.1) :
      PrecompNatMkMotive I O s d Q i X1 Y h1 (Y.2 ∘ h1) rfl :=
    match s, d, ih with
    | Sum.inl o, d, _ => precompNat_mk_iota I O o d Q i X1 Y h1
    | Sum.inr (Sum.inl A), d, ih => precompNat_mk_sigma I O A d ih Q i X1 Y h1
    | Sum.inr (Sum.inr B), d, ih => precompNat_mk_delta I O B d ih Q i X1 Y h1

  /-- The inductive step of the naturality upgrade: rewrite the
  isomorphism family by its characterizing equation
  `IR.interpPrecompIso_mk`, eliminate the morphism's commutation
  equality, and dispatch on the shape. -/
  theorem interpPrecompIso_natural_step :
      InductionStep.{max uA uB, uB, uI, uO} I O (PrecompNatMotive I O) :=
    fun s d ih Q i X Y h ↦
      match X, h with
      | ⟨X1, x2⟩, ⟨h1, hcomm⟩ =>
        Eq.mpr
          (congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O
                (interpMor I O (precomp I O Q i (mk I O s d)) ⟨X1, x2⟩ Y
                  ⟨h1, hcomm⟩)
                (FreeCoprodCompDisc.Iso.hom O (t Q i Y)) =
              FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O (t Q i ⟨X1, x2⟩))
                (precompRhsMapMor I O Q i (mk I O s d) ⟨X1, x2⟩ Y ⟨h1, hcomm⟩))
            (interpPrecompIso_mk I O s d))
          (Eq.rec (motive := fun x2' hcomm' ↦
              PrecompNatMkMotive I O s d Q i X1 Y h1 x2' hcomm')
            (precompNat_mk_base I O s d ih Q i X1 Y h1) hcomm)

  /-- Naturality of the Lemma 4 isomorphism family
  ([HancockMcBrideGhaniMalatestaAltenkirch2013]): at every code and
  every precomposition datum, `IR.interpPrecompIso` is natural in the
  interpreted object, between the precomposed interpretation and the
  direct interpretation at the coproduct object. -/
  theorem interpPrecompIso_natural (γ : IR.{max uA uB, uB, uI, uO} I O)
      (Q : Type uB) (i : Q → I) :
      FreeCoprodCompDisc.IsNatTrans I O
        (interpObj I O (precomp I O Q i γ)) (precompRhsMap I O Q i γ)
        (interpMor I O (precomp I O Q i γ)) (precompRhsMapMor I O Q i γ)
        (fun k ↦ FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q i k)) :=
    induction I O (PrecompNatMotive I O) (interpPrecompIso_natural_step I O)
      γ Q i
  ```

  Extend the module docstring. Append to `## Main statements`:

  ```markdown
  * `IR.interpPrecompIso_natural` — naturality of the Lemma 4
    isomorphism family
    ([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 4, upgraded
    from the pointwise statement), with the characterizing equation
    `IR.interpPrecompIso_mk`.
  ```

  and to `## Implementation notes`: "The Lemma 4 upgrade rewrites
  the isomorphism family to step form before eliminating the
  morphism's commutation equality and splitting on the shape; the
  precomposed code is a stuck match until the shape is known, after
  which the per-constructor `IR.interpMor` equations apply to it."

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add the lemma 4 naturality upgrade"
  ```

---

## Task 8: the initial-object evaluation and `InnerHom` fiber equivalences

The `ι`-case machinery of Theorem 3: transformations out of `⟦ι o⟧`
correspond to their components at the initial object (the
∅-evaluation equivalence, whose inverse extends a morphism by
composing with the images of the unique morphisms out of `∅`), and
the homset from an `ι`-code is the fiber, over the index, of the
decoding of the codomain's interpretation at the initial object (by
`IR.rec` on the codomain code, matching the homset clause against
the ∅-fiber per shape). Two generic `Equiv` combinators — the
sigma–subtype commutation and the empty-valued function-type
equivalence — live in `Geb/Mathlib/Logic/Equiv/Basic.lean` per the
spec's placement rule for generic `Equiv` combinators; the fiber
content cites [HancockMcBrideGhaniMalatestaAltenkirch2013] (the
`ι`-clauses of Definition 8 under Theorem 3).

**Files:**

- Modify: `Geb/Mathlib/Logic/Equiv/Basic.lean` (the two generic
  combinators)
- Modify: `GebTests/Mathlib/Logic/Equiv/Basic.lean` (their tests;
  the file exists — extend it)
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`

**Interfaces:**

- Consumes: `emptyObj`, `emptyDesc`, `emptyDesc_unique` (Task 1);
  `interpMor_id`, `interpMor_comp`, `interpMor_iota`, `MorMapSig`
  (branch 2b); `InnerHom` (branch 2a); `sigmaCongrRight'`
  (`Geb/Mathlib/Logic/Equiv/Basic.lean`); `Equiv.sigmaCongrLeft`
  (mathlib, first use — axiom-check in Step 4); `RecStep`, `rec`
  (branch 1); `NatTrans` (Task 2).
- Produces:

  ```lean
  sigmaSubtypeEquiv.{p, q} {A : Type p} (N : A → Type q)
    (P : (a : A) → N a → Prop) :
    (Σ a, {n : N a // P a n}) ≃ {z : Σ a, N a // P z.1 z.2}
  arrowPEmptyEquiv.{p, q, r} (B : Type r) :
    (B → PEmpty.{p + 1}) ≃ (B → PEmpty.{q + 1})
  interpMor_emptyDesc_comp — the interpretation's cocone over the
    initial object (statement below)
  natIotaInvFun (o) (γ') (f) :
    FreeCoprodCompDisc.NatTrans I O
      (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o))
      (interpObj I O γ') (interpMor I O …) (interpMor I O γ')
  natIotaEquiv (o) (γ') :
    FreeCoprodCompDisc.NatTrans I O … ≃
      FreeCoprodCompDisc.Hom O
        (interpObj I O (iota … I O o) (FreeCoprodCompDisc.emptyObj I))
        (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))
  InnerHomEquivMotive / innerHomEquivCast / innerHomEquivStep — the
    `IR.rec` motive, the `δ`-subcode transport, and the per-shape
    step
  innerHomEquiv (o) (γ') :
    InnerHom.{uA, uB, uI, uO} I O o γ' ≃
      {z : (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).1 //
        (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).2 z = o}
  ```

  (Verified universe discipline, already encoded below:
  `iota.{max uA uB, uB, uI, uO}` and
  `interpMor_iota.{max uA uB, uB, uI, uO}` are REQUIRED in these
  statements — inference stalls on `max ?u ?v =?= max uA uB`.)

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Logic/Equiv/Basic.lean`:

  ```lean
  /-- Commuting a sigma with a fiberwise subtype round-trips. -/
  theorem sampleSigmaSubtypeEquiv_roundtrip :
      (sigmaSubtypeEquiv (fun _ : Bool ↦ Bool) (fun a n ↦ a = n)).symm
          ((sigmaSubtypeEquiv (fun _ : Bool ↦ Bool) (fun a n ↦ a = n))
            ⟨true, ⟨true, rfl⟩⟩) =
        ⟨true, ⟨true, rfl⟩⟩ :=
    rfl

  /-- The empty-valued function types across universes are equivalent:
  the round trip is the identity. -/
  theorem sampleArrowPEmptyEquiv_roundtrip (e : Bool → PEmpty.{1}) :
      (arrowPEmptyEquiv.{0, 1, 0} Bool).symm
          (arrowPEmptyEquiv.{0, 1, 0} Bool e) = e :=
    (arrowPEmptyEquiv.{0, 1, 0} Bool).symm_apply_apply e
  ```

  and extend that file's module docstring summary with one
  sentence: "The sigma–subtype commutation and the empty-valued
  function-type equivalence round-trip at sample instances."

  Append to `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`:

  ```lean
  /-- The ∅-evaluation equivalence evaluates the identity transformation
  to the identity on the singleton name type. -/
  theorem sampleNatIotaEquiv_apply :
      ((IR.natIotaEquiv.{0, 0, 0, 0} Bool Bool true (iota Bool Bool true))
          (FreeCoprodCompDisc.NatTrans.id
            (IR.interpObj Bool Bool (iota Bool Bool true))
            (IR.interpMor Bool Bool (iota Bool Bool true)))).1
          (ULift.up Unit.unit) =
        ULift.up Unit.unit :=
    rfl

  /-- The `InnerHom` fiber equivalence sends the reflexivity witness to
  the singleton name. -/
  theorem sampleInnerHomEquiv_apply :
      ((IR.innerHomEquiv.{0, 0, 0, 0} Bool Bool true (iota Bool Bool true))
          (ULift.up (PLift.up rfl))).1 =
        ULift.up Unit.unit :=
    rfl
  ```

  and extend that file's module docstring summary with one
  sentence: "The ∅-evaluation and `InnerHom` fiber equivalences are
  exercised at `ι`-codes."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant — `sigmaSubtypeEquiv` or
  `IR.natIotaEquiv` first, depending on build order; either
  indicates the red state.

- [ ] **Step 3: Implement.** In
  `Geb/Mathlib/Logic/Equiv/Basic.lean`, insert after
  `sigmaCompEquivSigmaFiber` (the sigma-equivalence group), keeping
  the two additions adjacent:

  ```lean
  /-- Commute a sigma with a fiberwise subtype: a dependent pair whose
  second component is constrained is a constrained dependent pair. -/
  def sigmaSubtypeEquiv.{p, q} {A : Type p} (N : A → Type q)
      (P : (a : A) → N a → Prop) :
      (Σ a, {n : N a // P a n}) ≃ {z : Σ a, N a // P z.1 z.2} :=
    { toFun := fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
      invFun := fun z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩,
      left_inv := fun _ ↦ rfl,
      right_inv := fun _ ↦ rfl }

  /-- The equivalence of empty-valued function types across universes:
  each direction composes with the elimination out of `PEmpty`. -/
  def arrowPEmptyEquiv.{p, q, r} (B : Type r) :
      (B → PEmpty.{p + 1}) ≃ (B → PEmpty.{q + 1}) :=
    { toFun := fun e b ↦ (e b).elim,
      invFun := fun g b ↦ (g b).elim,
      left_inv := fun e ↦ funext (fun b ↦ (e b).elim),
      right_inv := fun g ↦ funext (fun g' ↦ (g g').elim) }
  ```

  Extend that module's docstring (`## Main definitions` or the
  summary, matching its present form) with entries for
  `sigmaSubtypeEquiv` and `arrowPEmptyEquiv`.

  Then append to the `IR` namespace of `Naturality.lean` (before
  `end IR`):

  ```lean
  /-- The interpretation's cocone over the initial object: the image of
  the unique morphism out of `∅` followed by the image of any morphism
  is the image of the unique morphism. -/
  theorem interpMor_emptyDesc_comp (γ' : IR.{max uA uB, uB, uI, uO} I O)
      (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I X Y) :
      FreeCoprodCompDisc.Hom.comp O
          (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
            (FreeCoprodCompDisc.emptyDesc I X))
          (interpMor I O γ' X Y h) =
        interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) Y
          (FreeCoprodCompDisc.emptyDesc I Y) :=
    (interpMor_comp I O γ' (FreeCoprodCompDisc.emptyObj I) X Y
        (FreeCoprodCompDisc.emptyDesc I X) h).symm.trans
      (congrArg (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) Y)
        (FreeCoprodCompDisc.emptyDesc_unique I Y
          (FreeCoprodCompDisc.Hom.comp I (FreeCoprodCompDisc.emptyDesc I X) h)))

  /-- The backward direction of `IR.natIotaEquiv`: extend a morphism at
  the initial object to a transformation by composing with the images of
  the unique morphisms out of `∅`. -/
  def natIotaInvFun (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O)
      (f : FreeCoprodCompDisc.Hom O
        (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o) (FreeCoprodCompDisc.emptyObj I))
        (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))) :
      FreeCoprodCompDisc.NatTrans I O (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o))
        (interpObj I O γ') (interpMor I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpMor I O γ') :=
    ⟨fun X ↦ FreeCoprodCompDisc.Hom.comp O f
        (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
          (FreeCoprodCompDisc.emptyDesc I X)),
      fun X Y h ↦
        (congrArg
            (fun (t : MorMapSig I O (iota.{max uA uB, uB, uI, uO} I O o)) ↦
              FreeCoprodCompDisc.Hom.comp O (t X Y h)
                (FreeCoprodCompDisc.Hom.comp O f
                  (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) Y
                    (FreeCoprodCompDisc.emptyDesc I Y))))
            (interpMor_iota.{max uA uB, uB, uI, uO} I O o)).trans
          ((congrArg (FreeCoprodCompDisc.Hom.comp O f)
              (interpMor_emptyDesc_comp I O γ' X Y h).symm).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O f
              (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))
              (interpMor I O γ' X Y h)).symm)⟩

  /-- The ∅-evaluation equivalence at an `iota` domain: transformations
  out of the interpretation of `iota o` correspond to their components
  at the initial object. -/
  def natIotaEquiv (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
      FreeCoprodCompDisc.NatTrans I O (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o))
          (interpObj I O γ') (interpMor I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpMor I O γ') ≃
        FreeCoprodCompDisc.Hom O
          (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o) (FreeCoprodCompDisc.emptyObj I))
          (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)) :=
    { toFun := fun η ↦ η.1 (FreeCoprodCompDisc.emptyObj I),
      invFun := natIotaInvFun I O o γ',
      left_inv := fun η ↦ Subtype.ext (funext (fun X ↦
        (η.2 (FreeCoprodCompDisc.emptyObj I) X
            (FreeCoprodCompDisc.emptyDesc I X)).symm.trans
          (congrArg
            (fun (t : MorMapSig I O (iota.{max uA uB, uB, uI, uO} I O o)) ↦
              FreeCoprodCompDisc.Hom.comp O
                (t (FreeCoprodCompDisc.emptyObj I) X
                  (FreeCoprodCompDisc.emptyDesc I X))
                (η.1 X))
            (interpMor_iota.{max uA uB, uB, uI, uO} I O o)))),
      right_inv := fun f ↦
        (congrArg
            (fun t ↦ FreeCoprodCompDisc.Hom.comp O f
              (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I)
                (FreeCoprodCompDisc.emptyObj I) t))
            (FreeCoprodCompDisc.emptyDesc_unique I
              (FreeCoprodCompDisc.emptyObj I)
              (FreeCoprodCompDisc.Hom.id I
                (FreeCoprodCompDisc.emptyObj I))).symm).trans
          ((congrArg (FreeCoprodCompDisc.Hom.comp O f)
              (interpMor_id I O γ' (FreeCoprodCompDisc.emptyObj I))).trans
            (FreeCoprodCompDisc.Hom.comp_id O f)) }

  /-- The motive of `IR.innerHomEquiv`: the homset from an `ι`-code to a
  code is the fiber, over the index, of the decoding of the code's
  interpretation at the initial object. -/
  def InnerHomEquivMotive (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
      Type (max uA uB uI) :=
    InnerHom.{uA, uB, uI, uO} I O o γ' ≃
      {z : (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).1 //
        (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).2 z = o}

  /-- Transport the fiber equivalence of a `δ`-subcode along an equality
  of direction assignments, keeping the equivalence's source at the
  original assignment. -/
  def innerHomEquivCast (o : O) (B : Type uB)
      (c : ULift.{max uA uB} (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (m : (x : ULift.{max uA uB} (B → I)) → InnerHomEquivMotive I O o (c x))
      (i j : B → I) (e : i = j) :
      InnerHom.{uA, uB, uI, uO} I O o (c (ULift.up i)) ≃
        {n : (interpObj I O (c (ULift.up j)) (FreeCoprodCompDisc.emptyObj I)).1 //
          (interpObj I O (c (ULift.up j)) (FreeCoprodCompDisc.emptyObj I)).2 n = o} :=
    Eq.rec (motive := fun j' _ ↦
        InnerHom.{uA, uB, uI, uO} I O o (c (ULift.up i)) ≃
          {n : (interpObj I O (c (ULift.up j'))
              (FreeCoprodCompDisc.emptyObj I)).1 //
            (interpObj I O (c (ULift.up j'))
              (FreeCoprodCompDisc.emptyObj I)).2 n = o})
      (m (ULift.up i)) e

  /-- The step of `IR.innerHomEquiv`: per shape, the homset clause and
  the ∅-fiber of the interpretation are matched componentwise, with the
  inductive hypotheses supplying the subcode equivalences. -/
  def innerHomEquivStep (o : O) :
      RecStep.{max uA uB, uB, uI, uO, max uA uB uI} I O
        (InnerHomEquivMotive I O o) :=
    fun s c m ↦ match s, c, m with
    | Sum.inl _, _, _ =>
        { toFun := fun h ↦ ⟨ULift.up Unit.unit, h.down.down.symm⟩,
          invFun := fun z ↦ ULift.up (PLift.up z.2.symm),
          left_inv := fun _ ↦ rfl,
          right_inv := fun _ ↦ rfl }
    | Sum.inr (Sum.inl _), c, m =>
        (sigmaCongrRight' (fun a ↦ m (ULift.up a))).trans
          (sigmaSubtypeEquiv
            (fun a ↦
              (interpObj I O (c (ULift.up a))
                (FreeCoprodCompDisc.emptyObj I)).1)
            (fun a n ↦
              (interpObj I O (c (ULift.up a))
                (FreeCoprodCompDisc.emptyObj I)).2 n = o))
    | Sum.inr (Sum.inr B), c, m =>
        (sigmaCongrRight' (fun (e : B → PEmpty.{1}) ↦
            innerHomEquivCast I O o B c m (fun b ↦ (e b).elim)
              ((FreeCoprodCompDisc.emptyObj I).2 ∘ (fun b ↦ (e b).elim))
              (funext (fun b ↦ (e b).elim)))).trans
          ((Equiv.sigmaCongrLeft
              (β := fun g ↦
                {n : (interpObj I O
                    (c (ULift.up ((FreeCoprodCompDisc.emptyObj I).2 ∘ g)))
                    (FreeCoprodCompDisc.emptyObj I)).1 //
                  (interpObj I O
                    (c (ULift.up ((FreeCoprodCompDisc.emptyObj I).2 ∘ g)))
                    (FreeCoprodCompDisc.emptyObj I)).2 n = o})
              (arrowPEmptyEquiv.{0, max uA uB, uB} B)).trans
            (sigmaSubtypeEquiv
              (fun g ↦
                (interpObj I O
                  (c (ULift.up ((FreeCoprodCompDisc.emptyObj I).2 ∘ g)))
                  (FreeCoprodCompDisc.emptyObj I)).1)
              (fun g n ↦
                (interpObj I O
                  (c (ULift.up ((FreeCoprodCompDisc.emptyObj I).2 ∘ g)))
                  (FreeCoprodCompDisc.emptyObj I)).2 n = o)))

  /-- The homset from an `ι`-code to a code is the fiber, over the
  index, of the decoding of the code's interpretation at the initial
  object, by `IR.rec` on the code. -/
  def innerHomEquiv (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
      InnerHom.{uA, uB, uI, uO} I O o γ' ≃
        {z : (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).1 //
          (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I)).2 z = o} :=
    rec I O (motive := InnerHomEquivMotive I O o) (innerHomEquivStep I O o) γ'
  ```

  Extend the `Naturality.lean` module docstring. Append to
  `## Main definitions`:

  ```markdown
  * `IR.natIotaEquiv` — the ∅-evaluation equivalence at an `ι`
    domain: transformations out of `⟦ι o⟧` correspond to their
    components at the initial object.
  * `IR.innerHomEquiv` — the homset from an `ι`-code as the fiber,
    over the index, of the decoding of the codomain's interpretation
    at the initial object
    ([HancockMcBrideGhaniMalatestaAltenkirch2013], Definition 8's
    `ι`-clauses, in the form Theorem 3's `ι`-case consumes).
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS. Also `#print axioms` on `IR.innerHomEquiv` (first
  use of `Equiv.sigmaCongrLeft`): expected ⊆
  `{propext, Quot.sound}`.

- [ ] **Step 5: Commit.** Two commits: first the generic `Equiv`
  combinators, then the `ι`-case machinery.

  ```bash
  jj commit Geb/Mathlib/Logic/Equiv/Basic.lean GebTests/Mathlib/Logic/Equiv/Basic.lean -m "feat(equiv): add sigma-subtype and empty-arrow equivalences"
  ```

  Check `jj status` between the two commits: only the `Naturality`
  files remain.

  ```bash
  jj commit -m "feat(indrec): add the initial-object and inner-hom fiber equivalences"
  ```

---

## Task 9: the plus-lift bridge

The reconciliation the `δ`-case needs between two right-hand sides:
the copower–Yoneda adjunction (Task 5) lands on the
`plus`-precomposed map at the LIFTED summand
`plus (lift ⟨Q, i⟩) X`, while the Lemma 4 upgrade (Task 7) is
stated at the direct coproduct `plus ⟨Q, i⟩ X`. The bridge morphisms
lower and raise the left names, compose to identities, and are
natural in the right summand; their images under the interpretation
form an inverse pair of natural transformations between the
`plus`-precomposed interpretation at the lifted summand and the
Lemma 4 right-hand map. Generic reconciliation infrastructure; no
citation.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`

**Interfaces:**

- Consumes: `plus`, `lift`, `Hom.id`, `Hom.comp` (branches 1, 2b);
  `coprodPairMor` (Task 1); `plusMap`, `plusMapMor`, `mapComp`,
  `mapMorComp` (Tasks 2, 5); `NatTrans`, `NatTrans.IsInverse`
  (Tasks 2, 4); `interpMor_id`, `interpMor_comp` (branch 2b);
  `precompRhsMap`, `precompRhsMapMor` (Task 7).
- Produces:

  ```lean
  plusLiftBridgeHom (Q : Type uB) (i : Q → I) (X) :
    FreeCoprodCompDisc.Hom I
      (FreeCoprodCompDisc.plus I
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
      (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
  plusLiftBridgeInvHom (Q) (i) (X) — the reverse bridge
  plusLiftBridge_hom_invHom / plusLiftBridge_invHom_hom — the
    inverse laws (statements below)
  plusLiftBridge_square / plusLiftBridge_square_inv — naturality in
    the right summand (statements below)
  plusLiftBridgeNat (Q) (i) (γ') :
    FreeCoprodCompDisc.NatTrans I O
      (FreeCoprodCompDisc.mapComp (FreeCoprodCompDisc.plusMap …)
        (interpObj I O γ'))
      (precompRhsMap I O Q i γ') … (precompRhsMapMor I O Q i γ')
  plusLiftBridgeNatInv (Q) (i) (γ') — the reverse transformation
  plusLiftBridgeNat_isInverse (Q) (i) (γ') :
    FreeCoprodCompDisc.NatTrans.IsInverse
      (plusLiftBridgeNat I O Q i γ') (plusLiftBridgeNatInv I O Q i γ')
  ```

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`:

  ```lean
  /-- The forward bridge followed by the backward bridge is the identity
  at the sample object. -/
  theorem samplePlusLiftBridge_hom_invHom :
      FreeCoprodCompDisc.Hom.comp Bool
          (IR.plusLiftBridgeHom Bool PUnit (fun _ ↦ false) sampleIObj)
          (IR.plusLiftBridgeInvHom Bool PUnit (fun _ ↦ false) sampleIObj) =
        FreeCoprodCompDisc.Hom.id Bool
          (FreeCoprodCompDisc.plus Bool
            (FreeCoprodCompDisc.lift.{0, 0, 0} Bool ⟨PUnit, fun _ ↦ false⟩)
            sampleIObj) :=
    IR.plusLiftBridge_hom_invHom Bool PUnit (fun _ ↦ false) sampleIObj

  /-- The two bridge transformations are inverse at the sample delta
  code. -/
  theorem samplePlusLiftBridgeNat_isInverse :
      FreeCoprodCompDisc.NatTrans.IsInverse
          (IR.plusLiftBridgeNat Bool Bool PUnit (fun _ ↦ false) sampleDeltaCode)
          (IR.plusLiftBridgeNatInv Bool Bool PUnit (fun _ ↦ false)
            sampleDeltaCode) :=
    IR.plusLiftBridgeNat_isInverse Bool Bool PUnit (fun _ ↦ false)
      sampleDeltaCode
  ```

  Extend the test file's module docstring summary with one sentence:
  "The plus-lift bridge morphisms and transformations are exercised
  at the sample object and code."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.plusLiftBridgeHom`.

- [ ] **Step 3: Implement.** Append to the `IR` namespace of
  `Naturality.lean` (before `end IR`):

  ```lean
  /-- The bridge from the lifted-summand binary coproduct to the direct
  one: lower the left names, keep the right names. -/
  def plusLiftBridgeHom (Q : Type uB) (i : Q → I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom I
        (FreeCoprodCompDisc.plus I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
        (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X) :=
    ⟨Sum.map ULift.down _root_.id,
      funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl))⟩

  /-- The bridge from the direct binary coproduct to the lifted-summand
  one: raise the left names, keep the right names. -/
  def plusLiftBridgeInvHom (Q : Type uB) (i : Q → I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom I (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
        (FreeCoprodCompDisc.plus I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X) :=
    ⟨Sum.map ULift.up _root_.id,
      funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl))⟩

  /-- The forward bridge followed by the backward bridge is the
  identity. -/
  theorem plusLiftBridge_hom_invHom (Q : Type uB) (i : Q → I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeHom I Q i X)
          (plusLiftBridgeInvHom I Q i X) =
        FreeCoprodCompDisc.Hom.id I
          (FreeCoprodCompDisc.plus I
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X) :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

  /-- The backward bridge followed by the forward bridge is the
  identity. -/
  theorem plusLiftBridge_invHom_hom (Q : Type uB) (i : Q → I)
      (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I Q i X)
          (plusLiftBridgeHom I Q i X) =
        FreeCoprodCompDisc.Hom.id I (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X) :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

  /-- The forward bridge is natural in the right summand. -/
  theorem plusLiftBridge_square (Q : Type uB) (i : Q → I)
      (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I X Y) :
      FreeCoprodCompDisc.Hom.comp I
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩)) h)
          (plusLiftBridgeHom I Q i Y) =
        FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeHom I Q i X)
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h) :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

  /-- The backward bridge is natural in the right summand. -/
  theorem plusLiftBridge_square_inv (Q : Type uB) (i : Q → I)
      (X Y : FreeCoprodCompDisc.{max uA uB, uI} I)
      (h : FreeCoprodCompDisc.Hom I X Y) :
      FreeCoprodCompDisc.Hom.comp I
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h)
          (plusLiftBridgeInvHom I Q i Y) =
        FreeCoprodCompDisc.Hom.comp I (plusLiftBridgeInvHom I Q i X)
          (FreeCoprodCompDisc.coprodPairMor I
            (FreeCoprodCompDisc.Hom.id I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩)) h) :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))

  /-- The interpretation's image of the forward bridge, as a natural
  transformation from the `plus`-precomposed interpretation at the
  lifted summand to the Lemma 4 right-hand map. -/
  def plusLiftBridgeNat (Q : Type uB) (i : Q → I)
      (γ' : IR.{max uA uB, uB, uI, uO} I O) :
      FreeCoprodCompDisc.NatTrans I O
        (FreeCoprodCompDisc.mapComp
          (FreeCoprodCompDisc.plusMap
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
          (interpObj I O γ'))
        (precompRhsMap I O Q i γ')
        (FreeCoprodCompDisc.mapMorComp
          (FreeCoprodCompDisc.plusMapMor
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
          (interpMor I O γ'))
        (precompRhsMapMor I O Q i γ') :=
    ⟨fun X ↦ interpMor I O γ'
        (FreeCoprodCompDisc.plus I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
        (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
        (plusLiftBridgeHom I Q i X),
      fun X Y h ↦
        (interpMor_comp I O γ'
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) Y)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩)) h)
            (plusLiftBridgeHom I Q i Y)).symm.trans
          ((congrArg
              (interpMor I O γ'
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
                (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y))
              (plusLiftBridge_square I Q i X Y h)).trans
            (interpMor_comp I O γ'
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
              (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
              (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
              (plusLiftBridgeHom I Q i X)
              (FreeCoprodCompDisc.coprodPairMor I
                (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h)))⟩

  /-- The interpretation's image of the backward bridge, as a natural
  transformation from the Lemma 4 right-hand map to the
  `plus`-precomposed interpretation at the lifted summand. -/
  def plusLiftBridgeNatInv (Q : Type uB) (i : Q → I)
      (γ' : IR.{max uA uB, uB, uI, uO} I O) :
      FreeCoprodCompDisc.NatTrans I O (precompRhsMap I O Q i γ')
        (FreeCoprodCompDisc.mapComp
          (FreeCoprodCompDisc.plusMap
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
          (interpObj I O γ'))
        (precompRhsMapMor I O Q i γ')
        (FreeCoprodCompDisc.mapMorComp
          (FreeCoprodCompDisc.plusMapMor
            (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
          (interpMor I O γ')) :=
    ⟨fun X ↦ interpMor I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
        (FreeCoprodCompDisc.plus I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
        (plusLiftBridgeInvHom I Q i X),
      fun X Y h ↦
        (interpMor_comp I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ Y)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) Y)
            (FreeCoprodCompDisc.coprodPairMor I
              (FreeCoprodCompDisc.Hom.id I ⟨Q, i⟩) h)
            (plusLiftBridgeInvHom I Q i Y)).symm.trans
          ((congrArg
              (interpMor I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) Y))
              (plusLiftBridge_square_inv I Q i X Y h)).trans
            (interpMor_comp I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) Y)
              (plusLiftBridgeInvHom I Q i X)
              (FreeCoprodCompDisc.coprodPairMor I
                (FreeCoprodCompDisc.Hom.id I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩))
                h)))⟩

  /-- The two bridge transformations are inverse. -/
  theorem plusLiftBridgeNat_isInverse (Q : Type uB) (i : Q → I)
      (γ' : IR.{max uA uB, uB, uI, uO} I O) :
      FreeCoprodCompDisc.NatTrans.IsInverse (plusLiftBridgeNat I O Q i γ')
        (plusLiftBridgeNatInv I O Q i γ') :=
    ⟨Subtype.ext (funext (fun X ↦
        (interpMor_comp I O γ'
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
            (plusLiftBridgeHom I Q i X)
            (plusLiftBridgeInvHom I Q i X)).symm.trans
          ((congrArg
              (interpMor I O γ'
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X))
              (plusLiftBridge_hom_invHom I Q i X)).trans
            (interpMor_id I O γ'
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X))))),
      Subtype.ext (funext (fun X ↦
        (interpMor_comp I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩) X)
            (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
            (plusLiftBridgeInvHom I Q i X)
            (plusLiftBridgeHom I Q i X)).symm.trans
          ((congrArg
              (interpMor I O γ' (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)
                (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X))
              (plusLiftBridge_invHom_hom I Q i X)).trans
            (interpMor_id I O γ'
              (FreeCoprodCompDisc.plus I ⟨Q, i⟩ X)))))⟩
  ```

  Extend the module docstring. Append to `## Main definitions`:

  ```markdown
  * `IR.plusLiftBridgeNat`, `IR.plusLiftBridgeNatInv` — the inverse
    pair of transformations bridging the `plus`-precomposed
    interpretation at the lifted summand and the Lemma 4 right-hand
    map.
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add the plus-lift bridge"
  ```

---

## Task 10: Theorem 3

Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: the
homset between two codes is equivalent to the space of natural
transformations between their interpretations, by `IR.rec` on the
domain code with motive `∀ γ', Hom γ γ' ≃ NatTrans ⟦γ⟧ ⟦γ'⟧`. The
`ι`-case composes the `InnerHom` fiber equivalence, the singleton
fiber description, and the ∅-evaluation equivalence (transported
along `mk_congr` to the generalized direction family — the `ι` form
is not defeq to the `mk` form); the `σ`-case composes the pointwise
inductive hypotheses, the coproduct decomposition, and the
`congrSource` rewrite along `interpMor_sigma`; the `δ`-case
composes, per summand, the inductive hypothesis at the precomposed
codomain (landing definitionally on the homset's clause 3), the
Lemma 4 upgrade converted through `ofIsoFamily`, the plus-lift
bridge, the copower–Yoneda adjunction, and the delta decomposition.
The directions `interpHom`/`natToHom` and their round-trip laws
package fullness and faithfulness.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`

**Interfaces:**

- Consumes: `Hom`, `InnerHom`, `precomp`, `IR.id` (branch 2a,
  `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`); `mk_congr`,
  `RecStep`, `rec` (branch 1); `interpPrecompIso` (branch 1,
  `Basic.lean`); `interpMor_sigma`, `interpMor_id`,
  `interpMor_comp` (branch 2b); `homSingletonEquiv` (Task 1);
  `NatTrans` (Task 2); `NatTrans.ofIsoFamily`,
  `NatTrans.invOfIsoFamily`, `NatTrans.ofIsoFamily_isInverse`,
  `NatTrans.equivOfInverseTarget`, `NatTrans.congrSource`,
  `natCoprodEquiv` (Task 4); `natCopowerPlusEquiv` (Task 5);
  `natDeltaEquiv` (Task 6); `interpPrecompIso_natural` (Task 7);
  `natIotaEquiv`, `innerHomEquiv` (Task 8); `plusLiftBridgeNat`,
  `plusLiftBridgeNatInv`, `plusLiftBridgeNat_isInverse` (Task 9);
  `Equiv.piCongrRight` (mathlib, first use — axiom-check in
  Step 4).
- Produces:

  ```lean
  InterpHomEquivMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
    Type (max (max uA uB + 1) uI uO)
  interpHomEquivStep :
    RecStep.{max uA uB, uB, uI, uO, max (max uA uB + 1) uI uO} I O
      (InterpHomEquivMotive I O)
  interpHomEquiv (γ γ' : IR.{max uA uB, uB, uI, uO} I O) :
    Hom.{uA, uB, uI, uO} I O γ γ' ≃
      FreeCoprodCompDisc.NatTrans I O (interpObj I O γ)
        (interpObj I O γ') (interpMor I O γ) (interpMor I O γ')
  interpHom (γ γ') (f : Hom.{uA, uB, uI, uO} I O γ γ') :
    FreeCoprodCompDisc.NatTrans I O (interpObj I O γ)
      (interpObj I O γ') (interpMor I O γ) (interpMor I O γ')
  natToHom (γ γ') (η) : Hom.{uA, uB, uI, uO} I O γ γ'
  interpHom_natToHom (γ γ') (η) :
    interpHom I O γ γ' (natToHom I O γ γ' η) = η
  natToHom_interpHom (γ γ') (f) :
    natToHom I O γ γ' (interpHom I O γ γ' f) = f
  ```

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Naturality.lean`. Four
  mandated groups: (a) a sample `interpHom` application at a
  concrete `Hom`; (b) the `TODO.md` morphism-action sample — a
  `delta` morphism action with a propositionally nontrivial
  commutation proof (distinct decodings on domain and codomain),
  exercising the `FreeCoprodCompDisc.homOfEq` transport in
  `IR.interpMorDelta` observably; (c) round-trip samples for
  `interpHom_natToHom`/`natToHom_interpHom` at `ι`- and `σ`-domain
  morphisms; (d) a `δ`-domain round trip at the identity morphism
  of the sample `δ`-code, specializing Theorem 3's forward map and
  its inverse at a concrete `δ`-code (the `δ`-branch computes only
  propositionally through `IR.rec`, so the specialization is
  type-level, not definitional).

  ```lean
  /-- A sample code morphism between `ι`-codes: the reflexivity
  witness. -/
  def sampleIotaHom :
      IR.Hom.{0, 0, 0, 0} Bool Bool (iota Bool Bool true)
        (iota Bool Bool true) :=
    ULift.up (PLift.up rfl)

  /-- The interpretation of `sampleIotaHom` as a natural transformation:
  its component at the sample object is the identity on the singleton
  name type. -/
  theorem sampleInterpHom_component :
      ((IR.interpHom.{0, 0, 0, 0} Bool Bool (iota Bool Bool true)
            (iota Bool Bool true) sampleIotaHom).1 sampleIObj).1
          (ULift.up Unit.unit) =
        ULift.up Unit.unit :=
    rfl

  /-- A domain object with constant decoding. -/
  def sampleActX : FreeCoprodCompDisc.{0, 0} Bool :=
    ⟨Bool, fun _ ↦ true⟩

  /-- A codomain object whose decoding agrees with the constant one only
  propositionally. -/
  def sampleActY : FreeCoprodCompDisc.{0, 0} Bool :=
    ⟨Bool, fun b ↦ b || true⟩

  /-- A morphism whose commutation proof is propositionally nontrivial:
  the identity index function, with decodings equal by `Bool.or_true`
  rather than by reflexivity. -/
  def sampleActHom : FreeCoprodCompDisc.Hom Bool sampleActX sampleActY :=
    ⟨fun b ↦ b, funext (fun b ↦ Bool.or_true b)⟩

  /-- The morphism action of the interpretation at `sampleDeltaCode` and
  `sampleActHom`: the `homOfEq` transport in `IR.interpMorDelta` is taken
  along the propositionally nontrivial commutation proof, and the image
  name is observable. -/
  theorem sampleInterpMorDelta_action :
      (IR.interpMor.{0, 0, 0, 0} Bool Bool sampleDeltaCode sampleActX
            sampleActY sampleActHom).1
          ⟨fun _ ↦ false, ULift.up Unit.unit⟩ =
        ⟨fun _ ↦ false, ULift.up Unit.unit⟩ :=
    congrFun
      (congrArg Subtype.val
        (congrFun (congrFun (congrFun
          (IR.interpMor_delta Bool Bool PUnit sampleDeltaSub) sampleActX)
          sampleActY) sampleActHom))
      ⟨fun _ ↦ false, ULift.up Unit.unit⟩

  /-- The decoding of the image agrees with the decoding of the argument:
  the interpretation's morphism action commutes with the decodings. -/
  theorem sampleInterpMorDelta_action_decode :
      (IR.interpObj Bool Bool sampleDeltaCode sampleActY).2
          ((IR.interpMor.{0, 0, 0, 0} Bool Bool sampleDeltaCode sampleActX
                sampleActY sampleActHom).1
            ⟨fun _ ↦ false, ULift.up Unit.unit⟩) =
        true :=
    congrFun
      (IR.interpMor Bool Bool sampleDeltaCode sampleActX sampleActY
          sampleActHom).2
      ⟨fun _ ↦ false, ULift.up Unit.unit⟩

  /-- A sample code morphism out of a `σ`-code: componentwise reflexivity
  witnesses. -/
  def sampleSigmaToIotaHom :
      IR.Hom.{0, 0, 0, 0} Bool Bool
        (sigma Bool Bool Bool (fun _ ↦ iota Bool Bool true))
        (iota Bool Bool true) :=
    fun _ ↦ ULift.up (PLift.up rfl)

  /-- `IR.natToHom` inverts `IR.interpHom` at the sample `ι`-morphism. -/
  theorem sampleNatToHom_interpHom :
      IR.natToHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
          (IR.interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
            sampleIotaHom) =
        sampleIotaHom :=
    IR.natToHom_interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
      sampleIotaHom

  /-- `IR.natToHom` inverts `IR.interpHom` at the sample `σ`-morphism. -/
  theorem sampleSigmaNatToHom_interpHom :
      IR.natToHom Bool Bool (sigma Bool Bool Bool (fun _ ↦ iota Bool Bool true))
          (iota Bool Bool true)
          (IR.interpHom Bool Bool
            (sigma Bool Bool Bool (fun _ ↦ iota Bool Bool true))
            (iota Bool Bool true) sampleSigmaToIotaHom) =
        sampleSigmaToIotaHom :=
    IR.natToHom_interpHom Bool Bool
      (sigma Bool Bool Bool (fun _ ↦ iota Bool Bool true))
      (iota Bool Bool true) sampleSigmaToIotaHom

  /-- `IR.interpHom` inverts `IR.natToHom` at the interpretation of the
  sample `ι`-morphism. -/
  theorem sampleInterpHom_natToHom :
      IR.interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
          (IR.natToHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
            (IR.interpHom Bool Bool (iota Bool Bool true)
              (iota Bool Bool true) sampleIotaHom)) =
        IR.interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
          sampleIotaHom :=
    IR.interpHom_natToHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
      (IR.interpHom Bool Bool (iota Bool Bool true) (iota Bool Bool true)
        sampleIotaHom)

  /-- The identity morphism of the sample `δ`-code (branch 2a's
  `IR.id`), the domain for the `δ`-branch exercise of Theorem 3. -/
  def sampleDeltaId :
      IR.Hom.{0, 0, 0, 0} Bool Bool sampleDeltaCode sampleDeltaCode :=
    IR.id Bool Bool sampleDeltaCode

  /-- Theorem 3's forward map specialized at a `δ`-domain morphism:
  the identity of the sample `δ`-code as a natural transformation
  (`IR.interpHomEquiv` computes only propositionally through
  `IR.rec`, so the specialization is type-level). -/
  def sampleDeltaIdNat :
      FreeCoprodCompDisc.NatTrans Bool Bool
        (IR.interpObj Bool Bool sampleDeltaCode)
        (IR.interpObj Bool Bool sampleDeltaCode)
        (IR.interpMor Bool Bool sampleDeltaCode)
        (IR.interpMor Bool Bool sampleDeltaCode) :=
    IR.interpHom Bool Bool sampleDeltaCode sampleDeltaCode sampleDeltaId

  /-- The `δ`-domain round trip: `IR.natToHom` recovers the identity
  morphism from its interpretation. -/
  theorem sampleDeltaId_roundTrip :
      IR.natToHom Bool Bool sampleDeltaCode sampleDeltaCode
          sampleDeltaIdNat =
        sampleDeltaId :=
    IR.natToHom_interpHom Bool Bool sampleDeltaCode sampleDeltaCode
      sampleDeltaId
  ```

  Notes on the morphism-action pair (group b): `sampleActHom`'s
  commutation proof is `funext (fun b ↦ Bool.or_true b)` — not
  `rfl`, since `b || true` is stuck on a variable — so the
  `homOfEq` transport in `IR.interpMorDelta` is taken along a
  propositionally nontrivial equality, and `sampleDeltaCode`'s
  subcode depends on the transported direction assignment. The
  action theorem's proof rewrites by `IR.interpMor_delta` (the
  morphism map computes only propositionally) and then observes the
  image name; the decode theorem observes the image through the
  morphism's commutation component. Group (a)'s component
  application closes by `rfl` (the component's codomain name type
  is a singleton).

  Extend the test file's module docstring summary with one
  sentence: "Theorem 3 is exercised at concrete morphisms: a
  component application, a `delta` morphism action with a
  propositionally nontrivial commutation proof (observing the
  `FreeCoprodCompDisc.homOfEq` transport in `IR.interpMorDelta`),
  and the round-trip laws at `ι`-, `σ`-, and `δ`-domain morphisms."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.interpHom` (the first
  appended declaration, `sampleIotaHom`, uses only branch 2a
  content and compiles).

- [ ] **Step 3: Implement.** Append to the `IR` namespace of
  `Naturality.lean` (before `end IR`):

  ```lean
  /-- The motive of `IR.interpHomEquiv`: for each code, the homset to
  every codomain code is equivalent to the space of natural
  transformations between the interpretations. -/
  def InterpHomEquivMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
      Type (max (max uA uB + 1) uI uO) :=
    (γ' : IR.{max uA uB, uB, uI, uO} I O) →
      Hom.{uA, uB, uI, uO} I O γ γ' ≃
        FreeCoprodCompDisc.NatTrans I O (interpObj I O γ) (interpObj I O γ')
          (interpMor I O γ) (interpMor I O γ')

  /-- The step of `IR.interpHomEquiv`: per shape, the homset clause and
  the transformation space are matched by the corresponding
  decomposition equivalence, with the inductive hypotheses supplying the
  subcode equivalences. -/
  def interpHomEquivStep :
      RecStep.{max uA uB, uB, uI, uO, max (max uA uB + 1) uI uO} I O
        (InterpHomEquivMotive I O) :=
    fun s c m ↦ match s, c, m with
    | Sum.inl o, c, _ => fun γ' ↦
        Eq.rec (motive := fun ir _ ↦
            InnerHom.{uA, uB, uI, uO} I O o γ' ≃
              FreeCoprodCompDisc.NatTrans I O (interpObj I O ir)
                (interpObj I O γ') (interpMor I O ir) (interpMor I O γ'))
          ((innerHomEquiv I O o γ').trans
            ((FreeCoprodCompDisc.homSingletonEquiv O o
                (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))).symm.trans
              (natIotaEquiv I O o γ').symm))
          (mk_congr I O (Sum.inl o) (funext (fun x ↦ nomatch x)) :
            mk I O (Sum.inl o) c = iota.{max uA uB, uB, uI, uO} I O o).symm
    | Sum.inr (Sum.inl A), c, m => fun γ' ↦
        (Equiv.piCongrRight (fun a ↦ m (ULift.up a) γ')).trans
          ((FreeCoprodCompDisc.natCoprodEquiv A
              (fun a ↦ interpObj I O (c (ULift.up a)))
              (fun a ↦ interpMor I O (c (ULift.up a)))
              (interpObj I O γ') (interpMor I O γ')).symm.trans
            (FreeCoprodCompDisc.NatTrans.congrSource
              (interpMor_sigma I O A (fun a ↦ c (ULift.up a)))
              (interpMor I O γ')).symm)
    | Sum.inr (Sum.inr Q), c, m => fun γ' ↦
        (Equiv.piCongrRight (fun i ↦
            (((m (ULift.up i) (precomp I O Q i γ')).trans
              (FreeCoprodCompDisc.NatTrans.equivOfInverseTarget
                (FreeCoprodCompDisc.NatTrans.ofIsoFamily
                  (fun k ↦ interpPrecompIso I O γ' Q i k)
                  (interpPrecompIso_natural I O γ' Q i))
                (FreeCoprodCompDisc.NatTrans.invOfIsoFamily
                  (fun k ↦ interpPrecompIso I O γ' Q i k)
                  (interpPrecompIso_natural I O γ' Q i))
                (FreeCoprodCompDisc.NatTrans.ofIsoFamily_isInverse
                  (fun k ↦ interpPrecompIso I O γ' Q i k)
                  (interpPrecompIso_natural I O γ' Q i)))).trans
              (FreeCoprodCompDisc.NatTrans.equivOfInverseTarget
                (plusLiftBridgeNatInv I O Q i γ')
                (plusLiftBridgeNat I O Q i γ')
                ⟨(plusLiftBridgeNat_isInverse I O Q i γ').2,
                  (plusLiftBridgeNat_isInverse I O Q i γ').1⟩)).trans
              (FreeCoprodCompDisc.natCopowerPlusEquiv
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨Q, i⟩)
                (interpMor I O (c (ULift.up i))) (interpMor I O γ')
                (interpMor_id I O (c (ULift.up i)))
                (interpMor_comp I O (c (ULift.up i)))
                (interpMor_id I O γ') (interpMor_comp I O γ')).symm)).trans
          (natDeltaEquiv I O Q (fun i ↦ c (ULift.up i)) (interpMor I O γ')).symm

  /-- Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: the
  homset between two codes is equivalent to the space of natural
  transformations between their interpretations, by `IR.rec` on the
  domain code. -/
  def interpHomEquiv (γ γ' : IR.{max uA uB, uB, uI, uO} I O) :
      Hom.{uA, uB, uI, uO} I O γ γ' ≃
        FreeCoprodCompDisc.NatTrans I O (interpObj I O γ) (interpObj I O γ')
          (interpMor I O γ) (interpMor I O γ') :=
    rec I O (interpHomEquivStep I O) γ γ'

  /-- The interpretation of a code morphism as a natural transformation
  (the forward direction of `IR.interpHomEquiv`). -/
  def interpHom (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O γ γ') :
      FreeCoprodCompDisc.NatTrans I O (interpObj I O γ) (interpObj I O γ')
        (interpMor I O γ) (interpMor I O γ') :=
    interpHomEquiv I O γ γ' f

  /-- The code morphism carried by a natural transformation between
  interpretations (the backward direction of `IR.interpHomEquiv`). -/
  def natToHom (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
      (η : FreeCoprodCompDisc.NatTrans I O (interpObj I O γ)
        (interpObj I O γ') (interpMor I O γ) (interpMor I O γ')) :
      Hom.{uA, uB, uI, uO} I O γ γ' :=
    (interpHomEquiv I O γ γ').symm η

  /-- `IR.interpHom` inverts `IR.natToHom`. -/
  theorem interpHom_natToHom (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
      (η : FreeCoprodCompDisc.NatTrans I O (interpObj I O γ)
        (interpObj I O γ') (interpMor I O γ) (interpMor I O γ')) :
      interpHom I O γ γ' (natToHom I O γ γ' η) = η :=
    Equiv.apply_symm_apply (interpHomEquiv I O γ γ') η

  /-- `IR.natToHom` inverts `IR.interpHom`. -/
  theorem natToHom_interpHom (γ γ' : IR.{max uA uB, uB, uI, uO} I O)
      (f : Hom.{uA, uB, uI, uO} I O γ γ') :
      natToHom I O γ γ' (interpHom I O γ γ' f) = f :=
    Equiv.symm_apply_apply (interpHomEquiv I O γ γ') f
  ```

  Rewrite the module docstring's first paragraph to the delivered
  form:

  "Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: the
  homset between two `IR` codes is equivalent to the space of
  natural transformations between their interpretations
  (`IR.interpHomEquiv`), by `IR.rec` on the domain code. The
  supporting development comprises the per-summand decomposition at
  a `delta` code (the naturality upgrade of the paper's Lemma 3),
  the naturality upgrade of Lemma 4, the ∅-evaluation and `InnerHom`
  fiber equivalences of the `ι`-case, and the plus-lift bridge."

  Append to `## Main definitions`:

  ```markdown
  * `IR.interpHomEquiv` — Theorem 3 of
    [HancockMcBrideGhaniMalatestaAltenkirch2013]: `Hom γ γ'` is
    equivalent to the transformation space between the
    interpretations, with the directions `IR.interpHom` and
    `IR.natToHom`.
  ```

  and to `## Main statements`:

  ```markdown
  * `IR.interpHom_natToHom`, `IR.natToHom_interpHom` — the
    round-trip laws of `IR.interpHomEquiv` (fullness and
    faithfulness of the interpretation on morphisms).
  ```

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS. Also `#print axioms` on `IR.interpHomEquiv`
  (first use of `Equiv.piCongrRight`): expected ⊆
  `{propext, Quot.sound}`.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add theorem 3"
  ```

---

## Task 11: docs, TODO reduction, and gates

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: everything above.
- Produces: the branch's persistent documentation and a passing
  pre-push gate.

- [ ] **Step 1: Update `docs/index.md`.** Read the file first and
  match its entry format (one bullet per module, topological
  order). After the entry for
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`, add:

  ```markdown
  - `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/NatTrans.lean` —
    natural transformations between morphism-mapped object maps of
    free coproduct completions: the naturality condition
    (`IsNatTrans`), the transformation space (`NatTrans`, a subtype
    over the `Prop`-valued condition), the vertical structure
    (`NatTrans.id`/`NatTrans.vcomp` with the category laws),
    whiskering and horizontal composition with the coherence and
    interchange laws (taking the outer morphism map's
    `PreservesId`/`PreservesComp` laws as hypotheses), inverse pairs
    (`NatTrans.IsInverse`) with the conversion of a natural family
    of isomorphisms (`NatTrans.ofIsoFamily`/`invOfIsoFamily`),
    transport equivalences
    (`NatTrans.equivOfInverseTarget`/`equivOfInverseSource`,
    `NatTrans.congrSource`), the coproduct decomposition
    (`natCoprodEquiv`), and the copower–Yoneda adjunction
    (`natCopowerPlusEquiv`). `Classical.choice`-free.
  ```

  After the `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean` entry,
  add:

  ```markdown
  - `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean` — Theorem 3
    of Hancock–McBride–Ghani–Malatesta–Altenkirch: the homset
    between two codes is equivalent to the space of natural
    transformations between their interpretations
    (`IR.interpHomEquiv`, with the directions
    `IR.interpHom`/`IR.natToHom` and their round-trip laws), by
    `IR.rec` on the domain code. The `δ`-case goes through the
    per-summand naturality upgrade of Lemma 3 (`IR.deltaInto`,
    `IR.deltaDesc`, `IR.natDeltaEquiv`), the copower–Yoneda
    adjunction, the plus-lift bridge (`IR.plusLiftBridgeNat`), and
    the naturality upgrade of Lemma 4
    (`IR.interpPrecompIso_natural`); the `σ`-case through the
    coproduct decomposition; the `ι`-case through the ∅-evaluation
    equivalence (`IR.natIotaEquiv`) and the `InnerHom` fiber
    equivalence (`IR.innerHomEquiv`). `Classical.choice`-free.
  ```

  Also revise the existing entries:

  - The `Geb/Mathlib/Logic/Equiv/Basic.lean` entry: record the two
    new combinators (`sigmaSubtypeEquiv`, the sigma–subtype
    commutation; `arrowPEmptyEquiv`, the empty-valued function-type
    equivalence across universes).
  - The `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` entry:
    record the initial object (`emptyObj`/`emptyDesc` with
    uniqueness), the indexed-coproduct universal property
    (`coprodInj`/`coprodDesc`/`coprodHomEquiv` with the composition
    compatibilities), `coprodPairMor` with its laws, the singleton
    fiber description (`homSingletonEquiv`), and the underlying
    morphisms of isomorphisms (`Iso.hom`/`Iso.invHom` with the
    inverse laws).
  - The `Geb/Mathlib/Data/PFunctor/IndRec/` entry: its Lemma 4
    span ("the paper states an equality, recorded here as the
    deviation to a pointwise isomorphism") gains a pointer that the
    naturality upgrade is `IR.interpPrecompIso_natural` in
    `Naturality.lean`; its Lemma 3 span's parenthetical "(natural
    transformations between interpretations are not yet defined)"
    is now false — revise it to point to the per-summand natural
    form in `Naturality.lean`.

- [ ] **Step 2: Update `TODO.md`.**

  - In § Complete Theorem 2.4 for `IndRec`: remove the "Tests:"
    paragraph (the propositionally nontrivial morphism-action
    sample it requests is delivered by Task 10's
    `sampleInterpMorDelta_action`/`_decode`).
  - In § Category of `IR` codes: the second paragraph
    ("Establishing the natural-transformation notion … must be
    budgeted for.") is now delivered — replace it with a paragraph
    recording that the natural-transformation notion and Theorem 3
    of Hancock–McBride–Ghani–Malatesta–Altenkirch
    (`IR.interpHomEquiv`), with the Lemma 3 and Lemma 4 naturality
    upgrades, are in
    `Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean`, and that
    the remaining content of the entry is the homset composition
    and the category laws (the branch 2d transfer consumes
    `IR.natToHom`). The existing `TODO.md` paragraph attributes
    Theorem 3 to [GhaniNordvallForsbergMalatesta2015]; the
    replacement corrects the attribution to
    [HancockMcBrideGhaniMalatestaAltenkirch2013], matching the
    citations verified in the design spec and `Basic.lean` (the
    theorem numbering is the TLCA 2013 paper's).

- [ ] **Step 3: Final docstring sweep.** Re-read the module
  docstrings of `FreeCoprodCompDisc.lean`,
  `FreeCoprodCompDisc/NatTrans.lean`, `Naturality.lean`,
  `Logic/Equiv/Basic.lean`, and their test mirrors; confirm each
  describes the module as it now stands (all sections non-vacuous,
  no stale deferral language, citations in `[Key]` form with the
  keys listed under `## References`).

- [ ] **Step 4: Regenerate TOCs and lint.**

  Run: `doctoc --update-only . && markdownlint-cli2 '**/*.md'`
  Expected: TOCs unchanged or updated; lint passes.

- [ ] **Step 5: Full gates.**

  Run: `lake build && lake test && lake lint && scripts/lint-imports.sh`
  Expected: all pass; the axiom linter reports no declaration
  outside `{propext, Quot.sound}` for the new modules.

  Then run `scripts/pre-push.sh` and confirm it passes (it catches
  umbrella-registration gaps).

- [ ] **Step 6: Commit.**

  ```bash
  jj commit -m "doc(indrec): add the branch 2c docs and reduce TODO"
  ```

---

## Final verification (whole branch)

- [ ] Run `scripts/pre-push.sh` once more on the completed branch.
- [ ] `#print axioms` (via `lean_verify` or a scratch snippet) on
  `IR.interpHomEquiv`, `IR.interpHom`, `IR.natToHom`,
  `IR.interpPrecompIso_natural`, `IR.innerHomEquiv`, and
  `FreeCoprodCompDisc.natCopowerPlusEquiv`:
  expected ⊆ `{propext, Quot.sound}`.
- [ ] Confirm no commit contains `proto_2c_gate.lean`: scan
  `jj log --stat` over the branch's commits.
- [ ] Run the `lean4:review` skill and `pr-review-toolkit:review-pr`
  on the branch, per the phase table; fold fixes into their owning
  task commits with `jj absorb`/`jj squash`.
- [ ] Confirm the spec and this plan remain in the working tree
  (they are removed only at the end of branch 2d, per CONTRIBUTING
  § Concern shape).
