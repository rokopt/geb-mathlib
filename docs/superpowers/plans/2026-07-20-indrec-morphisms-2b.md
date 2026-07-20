# IR-code morphisms branch 2b (Theorem 2.4 functoriality) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [File structure](#file-structure)
- [Task 1: `FreeCoprodCompDisc` identity, category laws, and `coprodMor` functoriality](#task-1-freecoprodcompdisc-identity-category-laws-and-coprodmor-functoriality)
- [Task 2: the `IR.rec` propositional computation rule](#task-2-the-irrec-propositional-computation-rule)
- [Task 3: the `Functor` module and the characterizing equations of `IR.interpMor`](#task-3-the-functor-module-and-the-characterizing-equations-of-irinterpmor)
- [Task 4: preservation of identity](#task-4-preservation-of-identity)
- [Task 5: preservation of composition](#task-5-preservation-of-composition)
- [Task 6: docs, TODO reduction, and gates](#task-6-docs-todo-reduction-and-gates)
- [Final verification (whole branch)](#final-verification-whole-branch)

<!-- END doctoc -->

**Goal:** the functoriality content of Theorem 2.4 of
[GhaniNordvallForsbergMalatesta2015] (attributed there to
[DybjerSetzer2003]), constructively: the `FreeCoprodCompDisc.Hom`
identity and category laws with the functoriality of `coprodMor`; the
propositional computation rule of `IR.rec` (with an `IR.elim`
computation-rule pin); the characterizing equations of `IR.interpMor`
at each code constructor; and preservation of identity and composition
by `IR.interpMor`.

**Architecture:** per the design spec
(`docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`,
§ Theorem 2.4 functoriality (branch 2b)). `IR.rec` is
`sigmaFstSectionElim (sigmaRec …) (sigmaRec_fst …)`, a single
`Eq.ndrec` transport along the section proof; the computation rule
follows from one transport-congruence lemma (`Eq.rec` on a generalized
direction-family equality), with definitional proof irrelevance
collapsing the transports. The functor laws go by `IR.induction` with
the objects and morphisms quantified in the motive; the composition
law first eliminates the two morphism-commutation equalities (nested
`Eq.rec`s whose motives abstract the decoding together with its proof,
in the `IR.ExtMotive` manner), after which every `homOfEq` transport
reduces definitionally and both laws reduce to the functoriality of
`coprodMor`.

**Verification status:** the complete committed form of every
declaration below — at the real universe scheme, term-mode — has been
compiled against the built `Basic.lean` this session and is
axiom-clean (`#print axioms` ⊆ `{Quot.sound}`; `IR.elim_mk` is
axiom-free). The session reference is
`proto_2b_gate.lean` (session scratch); the exact declarations are
reproduced per task below. An independent adversarial-review compile
confirmed the composition law. The residual work is tests, docstrings,
docs entries, and gates.

**Tech Stack:** Lean 4, mathlib (`WType`), the project's `IndRec` and
`FreeCoprodCompDisc` developments (branch 1).

## Global Constraints

Copied from the design spec; every task's requirements include these.

- Constructive only: no `noncomputable`, no `Classical`; the axiom
  linter (`lake lint`) permits `{propext, Quot.sound}` only for
  `Geb`/`GebTests`. Before reusing any mathlib declaration inside a
  definition, `#print axioms` it and reject any depending on
  `Classical.choice`. (`congrArg₂`, the one newly reused mathlib
  lemma, is confirmed clean: the composition law compiled with
  axioms `{Quot.sound}` only.)
- Recursor-only recursion: all recursion through recursors
  (`IR.induction` drives every law proof; `match` is used only for
  non-recursive case analysis on `Shape`/`Sigma`/`Subtype` patterns
  and `Eq.rec` for equality elimination). No `induction`/`induction'`
  tactic, no self-referential `def`, no `termination_by`.
- Explicit proof terms: committed declarations are term-mode, no `by`
  blocks. Term-level `match` (including `| rfl =>`) is permitted.
  Every step is a named declaration (motives as `def`s, steps and
  laws as `theorem`s), per the factoring constraint.
- Universe discipline: at application sites of this repository's
  declarations, a `.{…}` list is either omitted entirely or written
  in full — partial lists are banned. `interpMorIota` requires the
  full list `interpMorIota.{uA, uB, uI, uO}` at use sites whose
  arguments do not mention `uA`/`uB` (verified: inference stalls
  without it). `compBaseF`/`compBaseG` carry a single index-universe
  parameter `w` (instantiated at `max uA uB` by inference from their
  arguments); giving them separate `uA uB` parameters both trips the
  `checkUnivs` linter and leaves `max ?uA ?uB =?= max uA uB` stuck at
  use sites. No auto-bound `u_1` variables; remove unused
  `universe`/`variable`.
- Elimination order in the composition law: the two commutation
  equalities are eliminated BEFORE any rewrite by `interpMor_mk` and
  before the shape split (rewriting first breaks the elimination),
  and the `Eq.rec` motives are stated at projection-reduced types
  (`hf : Y2 ∘ f1 = x2`, not `⟨Y1, Y2⟩.snd ∘ f1 = ⟨X1, x2⟩.snd`) —
  the `rfl`/`subst`-style pattern match fails on the unreduced forms,
  and abstracting the decoding without its proof makes the motive
  ill-typed. The verified forms below already encode this.
- mathlib style: 2-space indent, 100-column lines, `fun x ↦ …`,
  mandatory docstrings on every `def` and every theorem of public
  interest, naming per mathlib (`lowerCamelCase` data, `snake_case`
  theorems, `UpperCamelCase` for `Prop`-valued `def`s such as the
  motives).
- VCS: `jj` only for mutations (raw mutating `git` is hook-blocked);
  commit messages in mathlib conventional form
  (`feat|test|doc|refactor|chore(scope): imperative subject`, no
  capital, no trailing period). No pushes.
- Gates per task: `lake build` and `lake test` pass before each
  commit. Red (verify-failure) steps run `lake test` (bare
  `lake build` does not build `GebTests`). `sorry` only transiently
  inside a task; never committed.
- Module system: `Functor.lean` gets a `module` header and
  `public import Geb.Mathlib.Data.PFunctor.IndRec.Basic`;
  `scripts/lint-imports.sh` passes. New modules are registered in
  BOTH the source umbrella (`Geb/Mathlib/Data/PFunctor/IndRec.lean`)
  AND the test umbrella (`GebTests/Mathlib/Data/PFunctor/IndRec.lean`)
  — in 2a the source-umbrella registration was missed and only
  `pre-push.sh` caught it.

## File structure

- Modify `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` —
  `Hom.id`, the three category laws, `coprodMor_id`,
  `coprodMor_comp`; module-docstring updates (Task 1).
- Modify `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` —
  tests for the above (Task 1).
- Modify `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` — `elim_mk`
  (after `elimAlg`), `RecStepCongrMotive`/`recStep_congr`/`rec_mk`/
  `rec_iota`/`rec_sigma`/`rec_delta` (after `rec`, before `end IR` at
  the end of the recursor section); module-docstring updates (Task 2).
- Modify `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean` — tests
  for the above (Task 2).
- Create `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean` —
  `interpMor_mk`, the three characterizing equations, the two functor
  laws with their motives and steps (Tasks 3–5).
- Create `GebTests/Mathlib/Data/PFunctor/IndRec/Functor.lean` —
  mirrored tests (Tasks 3–5).
- Modify `Geb/Mathlib/Data/PFunctor/IndRec.lean` AND
  `GebTests/Mathlib/Data/PFunctor/IndRec.lean` — register the new
  module in both umbrellas (Task 3).
- Modify `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean` — revise the
  two comments that cite the missing computation rule (Task 5).
- Modify `docs/index.md`, `TODO.md` — the docs entry and the TODO
  entry reduction (Task 6).

The declared universe list order is `universe uA uB uI uO` plus the
per-declaration `.{v}`/`.{w}` parameters shown below. All codes are at
the uniform instantiation only where the interpretation requires it
(`interpObj` lands in `FreeCoprodCompDisc.Map.{max uA uB, uI, uO}`);
the `rec` computation rule itself is fully general in
`IR.{uA, uB, uI, uO}` and `motive : IR I O → Type v`.

Placement notes: the `IR.rec` computation rule is a fact about
`IR.rec` and lives in `Basic.lean`, whose module docstring already
names it as missing. `IR.elim_mk` and the per-constructor `rec`
specializations are plan-level additions beyond the spec's 2b bullet
list: the former pins the definitional-unfolding chain through
mathlib's `WType.elim` that `rec_mk`'s elaboration depends on (so a
future mathlib module-system change breaks one named `rfl` rather
than `rec_mk` itself), and the latter are the forms downstream
branches apply. The `Universes`/`Container` relocation required
by the spec's placement section is assigned to a dedicated relocation
branch after 2b (spec § Branch decomposition); nothing in this branch
moves them. `IR.rec` uniqueness/initiality (TODO item 3) is deferred
out of 2b: the 2c route (recursion on the domain code via Lemmas 3/4
plus this branch's characterizing equations) does not consume it.

---

## Task 1: `FreeCoprodCompDisc` identity, category laws, and `coprodMor` functoriality

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`

**Interfaces:**

- Consumes: `Hom`, `Hom.comp`, `coprod`, `coprodMor` (branch 1).
- Produces (all in `namespace FreeCoprodCompDisc`, `variable (D : Type v)`):

  ```lean
  Hom.id (X : FreeCoprodCompDisc.{u, v} D) : Hom D X X
  Hom.id_comp : Hom.comp D (Hom.id D X) f = f
  Hom.comp_id : Hom.comp D f (Hom.id D Y) = f
  Hom.comp_assoc :
    Hom.comp D (Hom.comp D f g) h = Hom.comp D f (Hom.comp D g h)
  coprodMor_id :
    coprodMor D ι ι _root_.id fi fi (fun i ↦ Hom.id D (fi i)) =
      Hom.id D (coprod D ι fi)
  coprodMor_comp :
    Hom.comp D (coprodMor D ι κ r fi gk hom₁)
        (coprodMor D κ ρ t gk hr hom₂) =
      coprodMor D ι ρ (t ∘ r) fi hr
        (fun i ↦ Hom.comp D (hom₁ i) (hom₂ (r i)))
  ```

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` (after the
  existing sample declarations; `sampleX`/`sampleHom` already exist
  there):

  ```lean
  /-- The identity morphism of `sampleX` is the sample endomorphism. -/
  theorem sampleHom_id :
      FreeCoprodCompDisc.Hom.id Bool sampleX = sampleHom :=
    Subtype.ext rfl

  /-- Left identity at the sample endomorphism. -/
  theorem sampleHom_id_comp :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Hom.id Bool sampleX) sampleHom =
        sampleHom :=
    FreeCoprodCompDisc.Hom.id_comp Bool sampleHom

  /-- Right identity at the sample endomorphism. -/
  theorem sampleHom_comp_id :
      FreeCoprodCompDisc.Hom.comp Bool sampleHom
          (FreeCoprodCompDisc.Hom.id Bool sampleX) =
        sampleHom :=
    FreeCoprodCompDisc.Hom.comp_id Bool sampleHom

  /-- Associativity at the sample endomorphism. -/
  theorem sampleHom_comp_assoc :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom)
          sampleHom =
        FreeCoprodCompDisc.Hom.comp Bool sampleHom
          (FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom) :=
    FreeCoprodCompDisc.Hom.comp_assoc Bool sampleHom sampleHom sampleHom

  /-- The identity-family coproduct morphism over a constant family is
  the identity. -/
  theorem sampleCoprodMor_id :
      FreeCoprodCompDisc.coprodMor Bool PUnit PUnit _root_.id
          (fun _ ↦ sampleX) (fun _ ↦ sampleX)
          (fun _ ↦ FreeCoprodCompDisc.Hom.id Bool sampleX) =
        FreeCoprodCompDisc.Hom.id Bool
          (FreeCoprodCompDisc.coprod Bool PUnit (fun _ ↦ sampleX)) :=
    FreeCoprodCompDisc.coprodMor_id Bool PUnit (fun _ ↦ sampleX)

  /-- Composition of identity-reindexed coproduct morphisms composes
  componentwise. -/
  theorem sampleCoprodMor_comp :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.coprodMor Bool PUnit PUnit _root_.id
            (fun _ ↦ sampleX) (fun _ ↦ sampleX) (fun _ ↦ sampleHom))
          (FreeCoprodCompDisc.coprodMor Bool PUnit PUnit _root_.id
            (fun _ ↦ sampleX) (fun _ ↦ sampleX) (fun _ ↦ sampleHom)) =
        FreeCoprodCompDisc.coprodMor Bool PUnit PUnit
          (_root_.id ∘ _root_.id) (fun _ ↦ sampleX) (fun _ ↦ sampleX)
          (fun _ ↦ FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom) :=
    FreeCoprodCompDisc.coprodMor_comp Bool PUnit PUnit PUnit
      _root_.id _root_.id (fun _ ↦ sampleX) (fun _ ↦ sampleX)
      (fun _ ↦ sampleX) (fun _ ↦ sampleHom) (fun _ ↦ sampleHom)
  ```

  Also extend the test file's module docstring summary with one
  sentence: "The identity morphism, the category laws, and the
  functoriality of `coprodMor` are exercised at the sample
  endomorphism."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `FreeCoprodCompDisc.Hom.id`.

- [ ] **Step 3: Implement.** In
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`, insert after
  `Hom.comp` (order: `Hom.id` and laws next to `Hom.comp`;
  `coprodMor_id`/`coprodMor_comp` directly after `coprodMor`):

  ```lean
  /-- The identity morphism of the free coproduct completion. -/
  def Hom.id (X : FreeCoprodCompDisc.{u, v} D) : Hom D X X :=
    ⟨_root_.id, rfl⟩

  /-- Composition with the identity on the left is the identity of
  composition. -/
  theorem Hom.id_comp {X Y : FreeCoprodCompDisc.{u, v} D} (f : Hom D X Y) :
      Hom.comp D (Hom.id D X) f = f :=
    Subtype.ext rfl

  /-- Composition with the identity on the right is the identity of
  composition. -/
  theorem Hom.comp_id {X Y : FreeCoprodCompDisc.{u, v} D} (f : Hom D X Y) :
      Hom.comp D f (Hom.id D Y) = f :=
    Subtype.ext rfl

  /-- Composition is associative. -/
  theorem Hom.comp_assoc {X Y Z W : FreeCoprodCompDisc.{u, v} D}
      (f : Hom D X Y) (g : Hom D Y Z) (h : Hom D Z W) :
      Hom.comp D (Hom.comp D f g) h = Hom.comp D f (Hom.comp D g h) :=
    Subtype.ext rfl
  ```

  and after `coprodMor`:

  ```lean
  /-- The functorial action of `coprod` preserves identities. -/
  theorem coprodMor_id.{w} (ι : Type w)
      (fi : ι → FreeCoprodCompDisc.{u, v} D) :
      coprodMor D ι ι _root_.id fi fi (fun i ↦ Hom.id D (fi i)) =
        Hom.id D (coprod D ι fi) :=
    Subtype.ext rfl

  /-- The functorial action of `coprod` preserves composition. -/
  theorem coprodMor_comp.{w} (ι κ ρ : Type w) (r : ι → κ) (t : κ → ρ)
      (fi : ι → FreeCoprodCompDisc.{u, v} D)
      (gk : κ → FreeCoprodCompDisc.{u, v} D)
      (hr : ρ → FreeCoprodCompDisc.{u, v} D)
      (hom₁ : (i : ι) → Hom D (fi i) (gk (r i)))
      (hom₂ : (k : κ) → Hom D (gk k) (hr (t k))) :
      Hom.comp D (coprodMor D ι κ r fi gk hom₁)
          (coprodMor D κ ρ t gk hr hom₂) =
        coprodMor D ι ρ (t ∘ r) fi hr
          (fun i ↦ Hom.comp D (hom₁ i) (hom₂ (r i))) :=
    Subtype.ext rfl
  ```

  (If the file's `coprod` section already binds universe `w` under
  another name, match the file's convention.) Update the module
  docstring: in `## Main definitions`, extend the `Hom.comp` bullet to
  "`FreeCoprodCompDisc.Hom.id`, `FreeCoprodCompDisc.Hom.comp` — the
  identity and composition of morphisms, composition in diagrammatic
  order." Add a `## Main statements` section (before
  `## Implementation notes`) with:

  ```markdown
  ## Main statements

  * `FreeCoprodCompDisc.Hom.id_comp`, `FreeCoprodCompDisc.Hom.comp_id`,
    `FreeCoprodCompDisc.Hom.comp_assoc` — the category laws.
  * `FreeCoprodCompDisc.coprodMor_id`,
    `FreeCoprodCompDisc.coprodMor_comp` — the functoriality of
    `FreeCoprodCompDisc.coprodMor`.
  ```

  (If a `## Main statements` section already exists, append the two
  bullets to it instead.)

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS, no warnings in the touched files.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add the hom identity, category laws, and coprodMor functoriality"
  ```

---

## Task 2: the `IR.rec` propositional computation rule

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`

**Interfaces:**

- Consumes: `IR.elim`, `IR.elimAlg`, `IR.mk`, `IR.iota`/`sigma`/
  `delta`, `IR.RecStep`, `IR.sigmaRec`, `IR.sigmaRec_fst`, `IR.rec`.
- Produces (in `namespace IR`, `variable (I : Type uI) (O : Type uO)`):

  ```lean
  IR.elim_mk.{v} (V : Type v) (alg : Obj I O V → V) (s : Shape O)
    (d : Direction I O s → IR I O) :
    elim I O V alg (mk I O s d) = alg ⟨s, fun x ↦ elim I O V alg (d x)⟩
  IR.RecStepCongrMotive.{v} {motive} (mk' : RecStep I O motive)
    (s f m g e) : Prop
  IR.recStep_congr.{v} … : RecStepCongrMotive I O mk' s f m g e
  IR.rec_mk.{v} {motive} (mk' : RecStep I O motive) (s d) :
    rec I O mk' (mk I O s d) = mk' s d (fun x ↦ rec I O mk' (d x))
  IR.rec_iota.{v} / IR.rec_sigma.{v} / IR.rec_delta.{v} —
    the constructor specializations (statements below)
  ```

- [ ] **Step 1: Write the failing tests.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`. The file has
  `open CategoryTheory IndRec` (so `IR.`-qualified names resolve) and
  declares only `universe uK uT`; start the appended block with
  `universe uA uB uI uO`:

  ```lean
  universe uA uB uI uO

  -- `IR.elim` computes definitionally at `IR.mk`.

  example (I : Type uI) (O : Type uO) (V : Type) (alg : IR.Obj I O V → V)
      (s : IR.Shape O) (d : IR.Direction I O s → IR.{uA, uB, uI, uO} I O) :
      IR.elim I O V alg (IR.mk I O s d) =
        alg ⟨s, fun x ↦ IR.elim I O V alg (d x)⟩ :=
    IR.elim_mk I O V alg s d

  -- The propositional computation rule of `IR.rec` at a concrete
  -- constant motive and code: `IR.rec` at `iota` returns the step's
  -- value.

  /-- A sample `IR.rec` computation: at the constant motive `Bool` with
  a step returning `true`, the recursor returns `true` on `iota`. -/
  theorem sampleRec_iota :
      IR.rec.{0, 0, 0, 0, 0} PUnit PUnit
          (motive := fun _ ↦ Bool) (fun _ _ _ ↦ true)
          (IR.iota PUnit PUnit PUnit.unit) =
        true :=
    IR.rec_iota PUnit PUnit (motive := fun _ ↦ Bool)
      (fun _ _ _ ↦ true) PUnit.unit

  /-- A sample `IR.rec` computation at a `sigma` code. -/
  theorem sampleRec_sigma :
      IR.rec.{0, 0, 0, 0, 0} PUnit PUnit
          (motive := fun _ ↦ Bool) (fun _ _ _ ↦ true)
          (IR.sigma PUnit PUnit Bool
            (fun _ ↦ IR.iota PUnit PUnit PUnit.unit)) =
        true :=
    IR.rec_sigma PUnit PUnit (motive := fun _ ↦ Bool)
      (fun _ _ _ ↦ true) Bool (fun _ ↦ IR.iota PUnit PUnit PUnit.unit)

  /-- A sample `IR.rec` computation at a `delta` code. -/
  theorem sampleRec_delta :
      IR.rec.{0, 0, 0, 0, 0} PUnit PUnit
          (motive := fun _ ↦ Bool) (fun _ _ _ ↦ true)
          (IR.delta PUnit PUnit PUnit
            (fun _ ↦ IR.iota PUnit PUnit PUnit.unit)) =
        true :=
    IR.rec_delta PUnit PUnit (motive := fun _ ↦ Bool)
      (fun _ _ _ ↦ true) PUnit (fun _ ↦ IR.iota PUnit PUnit PUnit.unit)
  ```

  Extend the test file's module docstring with one summary sentence:
  "The computation rules `IR.elim_mk` and `IR.rec_mk` (via the
  per-constructor forms) are exercised at concrete codes and a
  constant motive."

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.elim_mk`.

- [ ] **Step 3: Implement.** In
  `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`, insert after
  `elimAlg`:

  ```lean
  /-- The computation rule of `IR.elim` at `IR.mk`. It holds
  definitionally; the named statement pins the definitional-unfolding
  chain through `WType.elim` at one site, so that any change to that
  chain localizes here. -/
  theorem elim_mk.{v} (V : Type v) (alg : Obj.{uA, uB, uI, uO, v} I O V → V)
      (s : Shape O) (d : Direction I O s → IR I O) :
      elim I O V alg (mk I O s d) = alg ⟨s, fun x ↦ elim I O V alg (d x)⟩ :=
    rfl
  ```

  and after `rec` (before the closing `end IR` of the recursor
  section):

  ```lean
  /-- The motive of the proof of `IR.recStep_congr`: transporting a
  recursor-step application along an equality of constructed codes
  agrees with applying the step to the pointwise-transported
  results. -/
  def RecStepCongrMotive.{v} {motive : IR.{uA, uB, uI, uO} I O → Type v}
      (mk' : RecStep I O motive) (s : Shape O)
      (f : Direction I O s → IR I O) (m : (x : Direction I O s) → motive (f x))
      (g : Direction I O s → IR I O) (e : f = g) : Prop :=
    ∀ h : mk I O s f = mk I O s g,
      Eq.ndrec (motive := motive) (mk' s f m) h =
        mk' s g (fun x ↦ Eq.ndrec (motive := motive) (m x) (congrFun e x))

  /-- Transporting a recursor-step application along an equality of
  constructed codes agrees with applying the step to the
  pointwise-transported results. The base case is definitional:
  proof irrelevance identifies the transport proof with `rfl`. -/
  theorem recStep_congr.{v} {motive : IR.{uA, uB, uI, uO} I O → Type v}
      (mk' : RecStep I O motive) (s : Shape O)
      (f : Direction I O s → IR I O) (m : (x : Direction I O s) → motive (f x))
      (g : Direction I O s → IR I O) (e : f = g) :
      RecStepCongrMotive I O mk' s f m g e :=
    Eq.rec (motive := fun g' e' ↦ RecStepCongrMotive I O mk' s f m g' e')
      (fun _ ↦ rfl) e

  /-- The propositional computation rule of `IR.rec` at `IR.mk`.
  `IR.rec` does not satisfy a definitional computation rule (it is
  built from `IR.elim` through a propositional first-projection
  section), so the rule holds propositionally, by `IR.recStep_congr`
  along the pointwise section proofs. -/
  theorem rec_mk.{v} {motive : IR.{uA, uB, uI, uO} I O → Type v}
      (mk' : RecStep I O motive) (s : Shape O)
      (d : Direction I O s → IR I O) :
      rec I O mk' (mk I O s d) = mk' s d (fun x ↦ rec I O mk' (d x)) :=
    recStep_congr I O mk' s
      (fun x ↦ (sigmaRec I O motive mk' (d x)).1)
      (fun x ↦ (sigmaRec I O motive mk' (d x)).2)
      d
      (funext (fun x ↦ sigmaRec_fst I O motive mk' (d x)))
      (sigmaRec_fst I O motive mk' (mk I O s d))

  /-- The computation rule of `IR.rec` at `IR.iota`. -/
  theorem rec_iota.{v} {motive : IR.{uA, uB, uI, uO} I O → Type v}
      (mk' : RecStep I O motive) (o : O) :
      rec I O mk' (iota I O o) =
        mk' (Sum.inl o) PEmpty.elim (fun x ↦ rec I O mk' (PEmpty.elim x)) :=
    rec_mk I O mk' (Sum.inl o) PEmpty.elim

  /-- The computation rule of `IR.rec` at `IR.sigma`. -/
  theorem rec_sigma.{v} {motive : IR.{uA, uB, uI, uO} I O → Type v}
      (mk' : RecStep I O motive) (A : Type uA) (c : A → IR I O) :
      rec I O mk' (sigma I O A c) =
        mk' (Sum.inr (Sum.inl A)) (c ∘ ULift.down)
          (fun x ↦ rec I O mk' (c x.down)) :=
    rec_mk I O mk' (Sum.inr (Sum.inl A)) (c ∘ ULift.down)

  /-- The computation rule of `IR.rec` at `IR.delta`. -/
  theorem rec_delta.{v} {motive : IR.{uA, uB, uI, uO} I O → Type v}
      (mk' : RecStep I O motive) (B : Type uB) (c : (B → I) → IR I O) :
      rec I O mk' (delta I O B c) =
        mk' (Sum.inr (Sum.inr B)) (c ∘ ULift.down)
          (fun x ↦ rec I O mk' (c x.down)) :=
    rec_mk I O mk' (Sum.inr (Sum.inr B)) (c ∘ ULift.down)
  ```

  Update the module docstring: add to `## Main statements`

  ```markdown
  * `IR.elim_mk`, `IR.rec_mk` (with `IR.rec_iota`, `IR.rec_sigma`,
    `IR.rec_delta`) — the computation rules of `IR.elim`
    (definitional, pinned) and `IR.rec` (propositional), the latter
    from the transport congruence `IR.recStep_congr`.
  ```

  and revise the Implementation-notes sentence "Neither is the
  propositional computation rule of `IR.rec`, which would characterize
  `IR.interpMor` at each code constructor." — for this commit, write:
  "The propositional computation rule of `IR.rec` is `IR.rec_mk`. The
  functor laws (preservation of identities and composition, completing
  Theorem 2.4 of [GhaniNordvallForsbergMalatesta2015]) are not yet
  stated." (Task 5 finishes the functor-laws half of the paragraph.)

  Also revise the three comments in
  `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean` that cite the
  missing computation rule, which becomes stale at this commit:

  - Lines 59–66 (the `sigmaPush` sample comment): replace the clause
    "`sigmaPush` is defined through `IndRec.IR.rec`, whose
    propositional computation rule is not yet stated (see the `IR`
    `Basic` module docstring, Implementation notes), so the result
    does not reduce definitionally against an independently-built
    witness" with "`sigmaPush` is defined through `IndRec.IR.rec`,
    whose computation rule (`IR.rec_mk`) is propositional rather than
    definitional, so the result does not reduce definitionally against
    an independently-built witness".
  - Lines 73–75 (the `deltaEmptyPush` sample comment): unchanged text
    "for the same reason as the `sigmaPush` sample above" remains
    correct once the `sigmaPush` comment is revised; verify only.
  - Lines 140–143 (the comment saying a check "does not witness that
    the `rec`-driven `id` reduces (that needs `IR.rec`'s computation
    rule)"): replace the parenthetical with "(`IR.rec`'s computation
    rule `IR.rec_mk` is propositional, so the reduction is not
    definitional)".

  The exact current wording may drift; locate each comment by its
  quoted phrase, not the line number, and keep the replacements to the
  clauses shown.

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add the propositional computation rule of IR.rec"
  ```

---

## Task 3: the `Functor` module and the characterizing equations of `IR.interpMor`

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/IndRec/Functor.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec.lean` (add
  `public import Geb.Mathlib.Data.PFunctor.IndRec.Functor`)
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec.lean` (add
  `import GebTests.Mathlib.Data.PFunctor.IndRec.Functor`)

**Interfaces:**

- Consumes: `IR.rec_mk` (Task 2), `IR.interpMor`, `IR.interpMorStep`,
  `IR.interpMorIota`/`Sigma`/`Delta`, `IR.interpObj`.
- Produces (in `namespace IndRec`, `namespace IR`):

  ```lean
  IR.interpMor_mk (s : Shape O) (d : Direction I O s → IR I O) :
    interpMor I O (mk I O s d) =
      interpMorStep I O s d (fun x ↦ interpMor I O (d x))
  IR.interpMor_iota (o : O) :
    interpMor.{uA, uB, uI, uO} I O (iota I O o) =
      interpMorIota.{uA, uB, uI, uO} I O o
  IR.interpMor_sigma (A : Type uA) (c : A → IR I O) :
    interpMor I O (sigma I O A c) =
      interpMorSigma I O A (fun a ↦ interpObj I O (c a))
        (fun a ↦ interpMor I O (c a))
  IR.interpMor_delta (B : Type uB) (c : (B → I) → IR I O) :
    interpMor I O (delta I O B c) =
      interpMorDelta I O B (fun f ↦ interpObj I O (c f))
        (fun f ↦ interpMor I O (c f))
  ```

- [ ] **Step 1: Create the test file (failing).**
  `GebTests/Mathlib/Data/PFunctor/IndRec/Functor.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Functor

  /-!
  # Tests for the functoriality of the IR interpretation

  The characterizing equations of `IR.interpMor` are exercised at
  concrete codes over the unit index types; the functor laws
  (preservation of identity and composition) are exercised at a
  sample object and endomorphism. Named theorems give the `GebMeta`
  axiom linter declarations to inspect.

  ## Tags

  inductive-recursive, interpretation, functor
  -/

  @[expose] public section

  open CategoryTheory
  open IndRec IndRec.IR

  /-- The characterizing equation of `interpMor` at a concrete `iota`
  code. -/
  theorem sampleInterpMor_iota :
      IR.interpMor.{0, 0, 0, 0} PUnit PUnit (iota PUnit PUnit PUnit.unit) =
        IR.interpMorIota.{0, 0, 0, 0} PUnit PUnit PUnit.unit :=
    IR.interpMor_iota PUnit PUnit PUnit.unit

  /-- The characterizing equation of `interpMor` at a concrete `sigma`
  code. -/
  theorem sampleInterpMor_sigma :
      IR.interpMor.{0, 0, 0, 0} PUnit PUnit
          (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit)) =
        IR.interpMorSigma PUnit PUnit Bool
          (fun _ ↦ IR.interpObj PUnit PUnit (iota PUnit PUnit PUnit.unit))
          (fun _ ↦ IR.interpMor PUnit PUnit (iota PUnit PUnit PUnit.unit)) :=
    IR.interpMor_sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit)

  /-- The characterizing equation of `interpMor` at a concrete `delta`
  code. -/
  theorem sampleInterpMor_delta :
      IR.interpMor.{0, 0, 0, 0} PUnit PUnit
          (delta PUnit PUnit PUnit (fun _ ↦ iota PUnit PUnit PUnit.unit)) =
        IR.interpMorDelta PUnit PUnit PUnit
          (fun _ ↦ IR.interpObj PUnit PUnit (iota PUnit PUnit PUnit.unit))
          (fun _ ↦ IR.interpMor PUnit PUnit (iota PUnit PUnit PUnit.unit)) :=
    IR.interpMor_delta PUnit PUnit PUnit (fun _ ↦ iota PUnit PUnit PUnit.unit)
  ```

  Register the module in BOTH umbrellas:
  `Geb/Mathlib/Data/PFunctor/IndRec.lean` gains
  `public import Geb.Mathlib.Data.PFunctor.IndRec.Functor` (after the
  `Hom` import) and `GebTests/Mathlib/Data/PFunctor/IndRec.lean` gains
  `import GebTests.Mathlib.Data.PFunctor.IndRec.Functor`.

- [ ] **Step 2: Run the tests to verify failure.**

  Run: `lake test`
  Expected: FAIL — `Geb.Mathlib.Data.PFunctor.IndRec.Functor` does not
  exist yet.

- [ ] **Step 3: Implement.** Create
  `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean`:

  ```lean
  /-
  Copyright (c) 2026 Terence Rokop. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Terence Rokop
  -/
  module

  public import Geb.Mathlib.Data.PFunctor.IndRec.Basic

  /-!
  # Functoriality of the IR interpretation

  The functoriality content of Theorem 2.4 of
  [GhaniNordvallForsbergMalatesta2015] (which attributes the theorem
  to [DybjerSetzer2003]): the interpretation of an `IR` code, given by
  the object map `IR.interpObj` and the morphism map `IR.interpMor`,
  preserves identities and composition, so `⟦γ⟧` is a functor between
  the free coproduct completions. The characterizing equations of
  `IR.interpMor` at each code constructor follow from the
  propositional computation rule `IR.rec_mk`.

  ## Main statements

  * `IR.interpMor_mk` — the characterizing equation of `IR.interpMor`
    at `IR.mk`, with the per-constructor forms `IR.interpMor_iota`,
    `IR.interpMor_sigma`, and `IR.interpMor_delta`.

  ## Implementation notes

  The characterizing equations follow from the propositional
  computation rule `IR.rec_mk`. The mathlib `Category`/`Functor`
  packaging is deferred to a `Classical.choice`-enabled wrapper (see
  `TODO.md`).

  ## References

  * [DybjerSetzer2003]
  * [GhaniNordvallForsbergMalatesta2015]

  ## Tags

  inductive-recursive, interpretation, functor, free coproduct
  completion
  -/

  @[expose] public section

  universe uA uB uI uO w

  namespace IndRec

  open CategoryTheory

  variable (I : Type uI) (O : Type uO)

  namespace IR

  /-- The characterizing equation of `IR.interpMor` at `IR.mk`: the
  morphism map computes by one step of `IR.interpMorStep`
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
  theorem interpMor_mk (s : Shape O)
      (d : Direction I O s → IR.{uA, uB, uI, uO} I O) :
      interpMor I O (mk I O s d) =
        interpMorStep I O s d (fun x ↦ interpMor I O (d x)) :=
    rec_mk I O (interpMorStep I O) s d

  /-- The characterizing equation of `IR.interpMor` at `IR.iota`
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
  theorem interpMor_iota (o : O) :
      interpMor.{uA, uB, uI, uO} I O (iota I O o) =
        interpMorIota.{uA, uB, uI, uO} I O o :=
    rec_mk I O (interpMorStep I O) (Sum.inl o) PEmpty.elim

  /-- The characterizing equation of `IR.interpMor` at `IR.sigma`
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
  theorem interpMor_sigma (A : Type uA)
      (c : A → IR.{uA, uB, uI, uO} I O) :
      interpMor I O (sigma I O A c) =
        interpMorSigma I O A (fun a ↦ interpObj I O (c a))
          (fun a ↦ interpMor I O (c a)) :=
    rec_mk I O (interpMorStep I O) (Sum.inr (Sum.inl A)) (c ∘ ULift.down)

  /-- The characterizing equation of `IR.interpMor` at `IR.delta`
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
  theorem interpMor_delta (B : Type uB)
      (c : (B → I) → IR.{uA, uB, uI, uO} I O) :
      interpMor I O (delta I O B c) =
        interpMorDelta I O B (fun f ↦ interpObj I O (c f))
          (fun f ↦ interpMor I O (c f)) :=
    rec_mk I O (interpMorStep I O) (Sum.inr (Sum.inr B)) (c ∘ ULift.down)

  end IR

  end IndRec
  ```

  (The module docstring at this commit describes only this task's
  declarations; Tasks 4 and 5 extend it as their laws land, keeping
  every intermediate commit's docstring accurate for doc generation.)

  The module docstring's title paragraph refers to functor laws that
  land in Tasks 4–5 of this same branch; phrase the first paragraph at
  this commit as: "Toward the functoriality content of Theorem 2.4 of
  [GhaniNordvallForsbergMalatesta2015] (which attributes the theorem
  to [DybjerSetzer2003]): the characterizing equations of
  `IR.interpMor` at each code constructor, from the propositional
  computation rule `IR.rec_mk`." Task 5 rewrites it to the final form
  shown above once both laws exist.

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add the characterizing equations of IR.interpMor"
  ```

---

## Task 4: preservation of identity

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Functor.lean`

**Interfaces:**

- Consumes: `interpMor_mk` (Task 3), `FreeCoprodCompDisc.Hom.id` and
  `coprodMor_id` (Task 1), `IR.induction`, `IR.InductionStep`.
- Produces:

  ```lean
  IR.InterpMorIdMotive (γ : IR.{uA, uB, uI, uO} I O) : Prop
  IR.interpMor_id_step :
    InductionStep.{uA, uB, uI, uO} I O (InterpMorIdMotive I O)
  IR.interpMor_id (γ : IR.{uA, uB, uI, uO} I O) : InterpMorIdMotive I O γ
  ```

- [ ] **Step 1: Write the failing test.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Functor.lean`:

  ```lean
  /-- A sample object of the completion over the unit type. -/
  def sampleObj : FreeCoprodCompDisc.{0, 0} PUnit :=
    ⟨Bool, fun _ ↦ PUnit.unit⟩

  /-- Preservation of identity at a concrete `sigma` code and the
  sample object. -/
  theorem sampleInterpMor_id :
      IR.interpMor.{0, 0, 0, 0} PUnit PUnit
          (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
          sampleObj sampleObj
          (FreeCoprodCompDisc.Hom.id PUnit sampleObj) =
        FreeCoprodCompDisc.Hom.id PUnit
          (IR.interpObj PUnit PUnit
            (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
            sampleObj) :=
    IR.interpMor_id PUnit PUnit
      (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
      sampleObj
  ```

- [ ] **Step 2: Run the test to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.interpMor_id`.

- [ ] **Step 3: Implement.** Append to the `IR` namespace of
  `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean` (before `end IR`):

  ```lean
  /-- The motive of the identity functor law: at every object, the
  morphism map sends the identity to the identity. -/
  def InterpMorIdMotive (γ : IR.{uA, uB, uI, uO} I O) : Prop :=
    ∀ X : FreeCoprodCompDisc.{max uA uB, uI} I,
      interpMor I O γ X X (FreeCoprodCompDisc.Hom.id I X) =
        FreeCoprodCompDisc.Hom.id O (interpObj I O γ X)

  /-- The inductive step of the identity functor law: after the
  characterizing equation `IR.interpMor_mk`, the `ι` case is
  definitional and the `σ`/`δ` cases are the inductive hypotheses
  followed by `FreeCoprodCompDisc.coprodMor_id` (the `δ`-case
  `homOfEq` transport reduces definitionally at the identity, whose
  commutation proof is reflexivity). -/
  theorem interpMor_id_step :
      InductionStep.{uA, uB, uI, uO} I O (InterpMorIdMotive I O) :=
    fun s d ih X ↦
      (congrFun (congrFun (congrFun (interpMor_mk I O s d) X) X)
        (FreeCoprodCompDisc.Hom.id I X)).trans
        (match s, d, ih with
          | Sum.inl _, _, _ => rfl
          | Sum.inr (Sum.inl A), d, ih =>
              (congrArg
                (FreeCoprodCompDisc.coprodMor O A A _root_.id
                  (fun a ↦ interpObj I O (d (ULift.up a)) X)
                  (fun a ↦ interpObj I O (d (ULift.up a)) X))
                (funext (fun a ↦ ih (ULift.up a) X))).trans
                (FreeCoprodCompDisc.coprodMor_id O A
                  (fun a ↦ interpObj I O (d (ULift.up a)) X))
          | Sum.inr (Sum.inr B), d, ih =>
              (congrArg
                (FreeCoprodCompDisc.coprodMor O (B → X.1) (B → X.1) _root_.id
                  (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X)
                  (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X))
                (funext (fun g ↦ ih (ULift.up (X.2 ∘ g)) X))).trans
                (FreeCoprodCompDisc.coprodMor_id O (B → X.1)
                  (fun g ↦ interpObj I O (d (ULift.up (X.2 ∘ g))) X)))

  /-- Preservation of identities by the interpretation
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
  theorem interpMor_id (γ : IR.{uA, uB, uI, uO} I O) :
      InterpMorIdMotive I O γ :=
    induction I O (InterpMorIdMotive I O) (interpMor_id_step I O) γ
  ```

  Extend the module docstring: append to `## Main statements`

  ```markdown
  * `IR.interpMor_id` — preservation of identities
    ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4).
  ```

  and append to `## Implementation notes`: "The functor laws are
  `Prop`-valued and go through `IR.induction` with the objects and
  morphisms quantified in the motive."

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add preservation of identity by IR.interpMor"
  ```

---

## Task 5: preservation of composition

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Functor.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`
  (Implementation-notes sentence only)

**Interfaces:**

- Consumes: `interpMor_mk` (Task 3), `coprodMor_comp` (Task 1),
  `Hom.comp` (branch 1), `congrArg₂` (mathlib, clean).
- Produces:

  ```lean
  IR.compBaseF (X1 Y1 Z1 : Type w) (Z2 : Z1 → I)
    (f1 : X1 → Y1) (g1 : Y1 → Z1) :
    FreeCoprodCompDisc.Hom I
      (⟨X1, Z2 ∘ g1 ∘ f1⟩ : FreeCoprodCompDisc.{w, uI} I) ⟨Y1, Z2 ∘ g1⟩
  IR.compBaseG (Y1 Z1 : Type w) (Z2 : Z1 → I) (g1 : Y1 → Z1) :
    FreeCoprodCompDisc.Hom I
      (⟨Y1, Z2 ∘ g1⟩ : FreeCoprodCompDisc.{w, uI} I) ⟨Z1, Z2⟩
  -- (Their universe parameters include `uI` via `I`; at use sites the
  -- `.{…}` list is omitted entirely — never a partial `.{w}`.)
  IR.InterpMorCompMotive (γ : IR.{uA, uB, uI, uO} I O) : Prop
  IR.InterpMorCompHgMotive / IR.InterpMorCompHfMotive — the two
    elimination motives (signatures below)
  IR.interpMorStep_comp — the shape dispatch at `interpMorStep` level
  IR.interpMor_comp_base — the base case (`InterpMorCompHgMotive` at
    `(Z2 ∘ g1)` and `rfl`)
  IR.interpMor_comp_step :
    InductionStep.{uA, uB, uI, uO} I O (InterpMorCompMotive I O)
  IR.interpMor_comp (γ) : InterpMorCompMotive I O γ
  ```

- [ ] **Step 1: Write the failing test.** Append to
  `GebTests/Mathlib/Data/PFunctor/IndRec/Functor.lean`:

  ```lean
  /-- A sample endomorphism of `sampleObj`. -/
  def sampleObjHom : FreeCoprodCompDisc.Hom PUnit sampleObj sampleObj :=
    ⟨_root_.id, rfl⟩

  /-- Preservation of composition at a concrete `sigma` code and the
  sample endomorphism. -/
  theorem sampleInterpMor_comp :
      IR.interpMor.{0, 0, 0, 0} PUnit PUnit
          (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
          sampleObj sampleObj
          (FreeCoprodCompDisc.Hom.comp PUnit sampleObjHom sampleObjHom) =
        FreeCoprodCompDisc.Hom.comp PUnit
          (IR.interpMor PUnit PUnit
            (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
            sampleObj sampleObj sampleObjHom)
          (IR.interpMor PUnit PUnit
            (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
            sampleObj sampleObj sampleObjHom) :=
    IR.interpMor_comp PUnit PUnit
      (sigma PUnit PUnit Bool (fun _ ↦ iota PUnit PUnit PUnit.unit))
      sampleObj sampleObj sampleObj sampleObjHom sampleObjHom
  ```

- [ ] **Step 2: Run the test to verify failure.**

  Run: `lake test`
  Expected: FAIL with unknown constant `IR.interpMor_comp`.

- [ ] **Step 3: Implement.** Append to the `IR` namespace of
  `Functor.lean` (before `end IR`), exactly:

  ```lean
  /-- The motive of the composition functor law: at all objects and
  morphisms, the morphism map sends a composite to the composite of
  the images. -/
  def InterpMorCompMotive (γ : IR.{uA, uB, uI, uO} I O) : Prop :=
    ∀ X Y Z : FreeCoprodCompDisc.{max uA uB, uI} I,
      ∀ f : FreeCoprodCompDisc.Hom I X Y,
        ∀ g : FreeCoprodCompDisc.Hom I Y Z,
          interpMor I O γ X Z (FreeCoprodCompDisc.Hom.comp I f g) =
            FreeCoprodCompDisc.Hom.comp O
              (interpMor I O γ X Y f) (interpMor I O γ Y Z g)

  /-- The first morphism of the composition law's base case: every
  decoding factors through the codomain decoding, and the commutation
  proof is reflexivity. -/
  def compBaseF (X1 Y1 Z1 : Type w) (Z2 : Z1 → I)
      (f1 : X1 → Y1) (g1 : Y1 → Z1) :
      FreeCoprodCompDisc.Hom I
        (⟨X1, Z2 ∘ g1 ∘ f1⟩ : FreeCoprodCompDisc.{w, uI} I)
        ⟨Y1, Z2 ∘ g1⟩ :=
    ⟨f1, rfl⟩

  /-- The second morphism of the composition law's base case. -/
  def compBaseG (Y1 Z1 : Type w) (Z2 : Z1 → I) (g1 : Y1 → Z1) :
      FreeCoprodCompDisc.Hom I
        (⟨Y1, Z2 ∘ g1⟩ : FreeCoprodCompDisc.{w, uI} I)
        ⟨Z1, Z2⟩ :=
    ⟨g1, rfl⟩

  /-- The motive of the second (inner) equality elimination of the
  composition law: the middle decoding is generalized together with
  its commutation proof. -/
  def InterpMorCompHgMotive (s : Shape O)
      (d : Direction I O s → IR.{uA, uB, uI, uO} I O)
      (X1 Y1 Z1 : Type (max uA uB)) (Z2 : Z1 → I)
      (f1 : X1 → Y1) (g1 : Y1 → Z1)
      (y2 : Y1 → I) (hg : Z2 ∘ g1 = y2) : Prop :=
    interpMor I O (mk I O s d) ⟨X1, y2 ∘ f1⟩ ⟨Z1, Z2⟩
        (FreeCoprodCompDisc.Hom.comp I (X := ⟨X1, y2 ∘ f1⟩)
          (Y := ⟨Y1, y2⟩) (Z := ⟨Z1, Z2⟩) ⟨f1, rfl⟩ ⟨g1, hg⟩) =
      FreeCoprodCompDisc.Hom.comp O
        (interpMor I O (mk I O s d) ⟨X1, y2 ∘ f1⟩ ⟨Y1, y2⟩ ⟨f1, rfl⟩)
        (interpMor I O (mk I O s d) ⟨Y1, y2⟩ ⟨Z1, Z2⟩ ⟨g1, hg⟩)

  /-- The motive of the first (outer) equality elimination of the
  composition law: the domain decoding is generalized together with
  its commutation proof. -/
  def InterpMorCompHfMotive (s : Shape O)
      (d : Direction I O s → IR.{uA, uB, uI, uO} I O)
      (X1 Y1 Z1 : Type (max uA uB)) (Y2 : Y1 → I) (Z2 : Z1 → I)
      (f1 : X1 → Y1) (g1 : Y1 → Z1) (hg : Z2 ∘ g1 = Y2)
      (x2 : X1 → I) (hf : Y2 ∘ f1 = x2) : Prop :=
    interpMor I O (mk I O s d) ⟨X1, x2⟩ ⟨Z1, Z2⟩
        (FreeCoprodCompDisc.Hom.comp I (X := ⟨X1, x2⟩)
          (Y := ⟨Y1, Y2⟩) (Z := ⟨Z1, Z2⟩) ⟨f1, hf⟩ ⟨g1, hg⟩) =
      FreeCoprodCompDisc.Hom.comp O
        (interpMor I O (mk I O s d) ⟨X1, x2⟩ ⟨Y1, Y2⟩ ⟨f1, hf⟩)
        (interpMor I O (mk I O s d) ⟨Y1, Y2⟩ ⟨Z1, Z2⟩ ⟨g1, hg⟩)

  /-- The shape dispatch of the composition law's base case, at the
  level of `IR.interpMorStep`: the `ι` case is definitional, and the
  `σ`/`δ` cases are the inductive hypotheses followed by
  `FreeCoprodCompDisc.coprodMor_comp` (at the base objects every
  `homOfEq` transport reduces definitionally). -/
  theorem interpMorStep_comp (s : Shape O)
      (d : Direction I O s → IR.{uA, uB, uI, uO} I O)
      (X1 Y1 Z1 : Type (max uA uB)) (Z2 : Z1 → I)
      (f1 : X1 → Y1) (g1 : Y1 → Z1)
      (ih : (x : Direction I O s) → InterpMorCompMotive I O (d x)) :
      interpMorStep I O s d (fun x ↦ interpMor I O (d x))
          ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Z1, Z2⟩
          (FreeCoprodCompDisc.Hom.comp I
            (compBaseF I X1 Y1 Z1 Z2 f1 g1) (compBaseG I Y1 Z1 Z2 g1)) =
        FreeCoprodCompDisc.Hom.comp O
          (interpMorStep I O s d (fun x ↦ interpMor I O (d x))
            ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩
            (compBaseF I X1 Y1 Z1 Z2 f1 g1))
          (interpMorStep I O s d (fun x ↦ interpMor I O (d x))
            ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
            (compBaseG I Y1 Z1 Z2 g1)) :=
    match s, d, ih with
    | Sum.inl _, _, _ => rfl
    | Sum.inr (Sum.inl A), d, ih =>
        Eq.trans
          (congrArg
            (FreeCoprodCompDisc.coprodMor O A A _root_.id
              (fun a ↦ interpObj I O (d (ULift.up a)) ⟨X1, Z2 ∘ g1 ∘ f1⟩)
              (fun a ↦ interpObj I O (d (ULift.up a)) ⟨Z1, Z2⟩))
            (funext (fun a ↦
              ih (ULift.up a) ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
                (compBaseF I X1 Y1 Z1 Z2 f1 g1)
                (compBaseG I Y1 Z1 Z2 g1))))
          (Eq.symm
            (FreeCoprodCompDisc.coprodMor_comp O A A A _root_.id _root_.id
              (fun a ↦ interpObj I O (d (ULift.up a)) ⟨X1, Z2 ∘ g1 ∘ f1⟩)
              (fun a ↦ interpObj I O (d (ULift.up a)) ⟨Y1, Z2 ∘ g1⟩)
              (fun a ↦ interpObj I O (d (ULift.up a)) ⟨Z1, Z2⟩)
              (fun a ↦ interpMor I O (d (ULift.up a))
                ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩
                (compBaseF I X1 Y1 Z1 Z2 f1 g1))
              (fun a ↦ interpMor I O (d (ULift.up a))
                ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
                (compBaseG I Y1 Z1 Z2 g1))))
    | Sum.inr (Sum.inr B), d, ih =>
        Eq.trans
          (congrArg
            (FreeCoprodCompDisc.coprodMor O (B → X1) (B → Z1)
              (fun q ↦ g1 ∘ f1 ∘ q)
              (fun q ↦ interpObj I O
                (d (ULift.up (Z2 ∘ g1 ∘ f1 ∘ q))) ⟨X1, Z2 ∘ g1 ∘ f1⟩)
              (fun q ↦ interpObj I O
                (d (ULift.up (Z2 ∘ q))) ⟨Z1, Z2⟩))
            (funext (fun q ↦
              ih (ULift.up (Z2 ∘ g1 ∘ f1 ∘ q))
                ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
                (compBaseF I X1 Y1 Z1 Z2 f1 g1)
                (compBaseG I Y1 Z1 Z2 g1))))
          (Eq.symm
            (FreeCoprodCompDisc.coprodMor_comp O
              (B → X1) (B → Y1) (B → Z1)
              (fun q ↦ f1 ∘ q) (fun q ↦ g1 ∘ q)
              (fun q ↦ interpObj I O
                (d (ULift.up (Z2 ∘ g1 ∘ f1 ∘ q))) ⟨X1, Z2 ∘ g1 ∘ f1⟩)
              (fun q ↦ interpObj I O
                (d (ULift.up (Z2 ∘ g1 ∘ q))) ⟨Y1, Z2 ∘ g1⟩)
              (fun q ↦ interpObj I O
                (d (ULift.up (Z2 ∘ q))) ⟨Z1, Z2⟩)
              (fun q ↦ interpMor I O (d (ULift.up (Z2 ∘ g1 ∘ f1 ∘ q)))
                ⟨X1, Z2 ∘ g1 ∘ f1⟩ ⟨Y1, Z2 ∘ g1⟩
                (compBaseF I X1 Y1 Z1 Z2 f1 g1))
              (fun q ↦ interpMor I O (d (ULift.up (Z2 ∘ g1 ∘ q)))
                ⟨Y1, Z2 ∘ g1⟩ ⟨Z1, Z2⟩
                (compBaseG I Y1 Z1 Z2 g1))))

  /-- The composition law's base case: `InterpMorCompHgMotive` at the
  factored middle decoding and reflexivity, by the characterizing
  equation `IR.interpMor_mk` on both sides of `interpMorStep_comp`. -/
  theorem interpMor_comp_base (s : Shape O)
      (d : Direction I O s → IR.{uA, uB, uI, uO} I O)
      (X1 Y1 Z1 : Type (max uA uB)) (Z2 : Z1 → I)
      (f1 : X1 → Y1) (g1 : Y1 → Z1)
      (ih : (x : Direction I O s) → InterpMorCompMotive I O (d x)) :
      InterpMorCompHgMotive I O s d X1 Y1 Z1 Z2 f1 g1 (Z2 ∘ g1) rfl :=
    Eq.trans
      (congrFun (congrFun (congrFun (interpMor_mk I O s d)
        ⟨X1, Z2 ∘ g1 ∘ f1⟩) ⟨Z1, Z2⟩)
        (FreeCoprodCompDisc.Hom.comp I
          (compBaseF I X1 Y1 Z1 Z2 f1 g1) (compBaseG I Y1 Z1 Z2 g1)))
      (Eq.trans
        (interpMorStep_comp I O s d X1 Y1 Z1 Z2 f1 g1 ih)
        (Eq.symm
          (congrArg₂ (FreeCoprodCompDisc.Hom.comp O)
            (congrFun (congrFun (congrFun (interpMor_mk I O s d)
              ⟨X1, Z2 ∘ g1 ∘ f1⟩) ⟨Y1, Z2 ∘ g1⟩)
              (compBaseF I X1 Y1 Z1 Z2 f1 g1))
            (congrFun (congrFun (congrFun (interpMor_mk I O s d)
              ⟨Y1, Z2 ∘ g1⟩) ⟨Z1, Z2⟩)
              (compBaseG I Y1 Z1 Z2 g1)))))

  /-- The inductive step of the composition functor law: destructure
  the objects and morphisms, then eliminate the two commutation
  equalities into the base case `IR.interpMor_comp_base`. -/
  theorem interpMor_comp_step :
      InductionStep.{uA, uB, uI, uO} I O (InterpMorCompMotive I O) :=
    fun s d ih X Y Z f g ↦
      match X, Y, Z, f, g with
      | ⟨X1, _X2⟩, ⟨Y1, Y2⟩, ⟨Z1, Z2⟩, ⟨f1, hf⟩, ⟨g1, hg⟩ =>
        Eq.rec
          (motive := fun x2 hf' ↦
            InterpMorCompHfMotive I O s d X1 Y1 Z1 Y2 Z2 f1 g1 hg x2 hf')
          (Eq.rec
            (motive := fun y2 hg' ↦
              InterpMorCompHgMotive I O s d X1 Y1 Z1 Z2 f1 g1 y2 hg')
            (interpMor_comp_base I O s d X1 Y1 Z1 Z2 f1 g1 ih)
            hg)
          hf

  /-- Preservation of composition by the interpretation
  ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4). -/
  theorem interpMor_comp (γ : IR.{uA, uB, uI, uO} I O) :
      InterpMorCompMotive I O γ :=
    induction I O (InterpMorCompMotive I O) (interpMor_comp_step I O) γ
  ```

  Then finish the doc reconciliations this law completes:

  - In `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`, replace the
    Task-2 Implementation-notes sentence "The functor laws … are not
    yet stated." with "The functor laws (preservation of identities
    and composition, completing Theorem 2.4 of
    [GhaniNordvallForsbergMalatesta2015]) are
    `IR.interpMor_id` and `IR.interpMor_comp` in
    `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean`."
  - In `Functor.lean`, rewrite the module docstring's first paragraph
    to the final form (the one given in Task 3's Step 3 under
    "# Functoriality of the IR interpretation"), append to
    `## Main statements`

    ```markdown
    * `IR.interpMor_comp` — preservation of composition
      ([GhaniNordvallForsbergMalatesta2015], Theorem 2.4).
    ```

    and append to `## Implementation notes`: "The composition law
    first eliminates the two morphism-commutation equalities (nested
    `Eq.rec`s whose motives — `InterpMorCompHgMotive` and
    `InterpMorCompHfMotive` — abstract a decoding together with its
    commutation proof), so that at the base case every decoding
    factors through the codomain decoding and the `homOfEq`
    transports in `IR.interpMorDelta` reduce definitionally; both
    laws then reduce to the functoriality of
    `FreeCoprodCompDisc.coprodMor`."

- [ ] **Step 4: Run the tests to verify success.**

  Run: `lake build && lake test`
  Expected: PASS.

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "feat(indrec): add preservation of composition by IR.interpMor"
  ```

---

## Task 6: docs, TODO reduction, and gates

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: everything above.
- Produces: the branch's persistent documentation and a passing
  pre-push gate.

- [ ] **Step 1: Update `docs/index.md`.** After the
  `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean` entry, add:

  ```markdown
  - `Geb/Mathlib/Data/PFunctor/IndRec/Functor.lean` — the
    functoriality content of Theorem 2.4 of
    Ghani–Nordvall Forsberg–Malatesta (attributed there to
    Dybjer–Setzer): the characterizing equations of `IR.interpMor`
    at each code constructor (from the propositional computation
    rule `IR.rec_mk` of `Basic.lean`), and preservation of identity
    (`IR.interpMor_id`) and composition (`IR.interpMor_comp`), so
    the interpretation of a code is a functor between free coproduct
    completions. The composition proof eliminates the
    morphism-commutation equalities before the shape split, reducing
    both laws to the functoriality of `FreeCoprodCompDisc.coprodMor`
    (`coprodMor_id`/`coprodMor_comp`, with the identity `Hom.id` and
    category laws, in `FreeCoprodCompDisc.lean`).
    `Classical.choice`-free.
  ```

  Also revise the existing entries as follows:

  - The `Geb/Mathlib/CategoryTheory/` (FreeCoprodCompDisc) entry:
    extend the `Hom.comp` clause to record `Hom.id`, the category
    laws (`Hom.id_comp`/`Hom.comp_id`/`Hom.comp_assoc`), and the
    functoriality of `coprodMor`
    (`coprodMor_id`/`coprodMor_comp`). Its "(see `TODO.md` § Complete
    Theorem 2.4 for `IndRec`)" span concerns the deferred
    `Classical.choice`-enabled `Category` wrapper, which remains
    deferred — leave that span as is.
  - The `Geb/Mathlib/Data/PFunctor/IndRec/` entry: its span saying
    the propositional computation rule of `IR.rec` (and the functor
    laws) are deferred is now false — revise it to point to
    `IR.rec_mk` in `Basic.lean` and the `Functor.lean` entry; the
    initial algebras remain deferred and keep their TODO pointer.

- [ ] **Step 2: Update `TODO.md`.** In "Complete Theorem 2.4 for
  `IndRec`", remove the delivered constructive items (the `IR.rec`
  computation rule, the characterizing equations, the functor laws),
  leaving the `Classical.choice`-enabled categorical wrapper, the
  `IR.elim`/`IR.rec` uniqueness/initiality item (note: 2c's route
  does not need it), and anything else the entry lists as
  undelivered. The entry's "Tests:" paragraph is triggered by the
  computation rule existing; this branch does not deliver the
  morphism-action test it describes (a `delta`-interpretation sample
  whose commutation proof is propositionally nontrivial, so the
  `homOfEq` transport is exercised observably — all of this branch's
  samples have reflexive commutation proofs), so retain the
  paragraph with its trigger rephrased: the rule (`IR.rec_mk`) now
  exists; the test remains to be added. In the "Category of `IR`
  codes" entry, note that the functor laws it depends on are now
  available. Add to the 2c-facing notes (wherever the entry tracks
  the remaining branches) that Theorem 3 will additionally need the
  Lemma-3/Lemma-4 isomorphisms upgraded from pointwise to natural —
  a deliverable currently in no branch's list; 2c's plan must budget
  for it.

- [ ] **Step 3: Regenerate TOCs and lint.**

  Run: `doctoc --update-only . && markdownlint-cli2 '**/*.md'`
  Expected: TOCs unchanged or updated; lint passes.

- [ ] **Step 4: Full gates.**

  Run: `lake build && lake test && lake lint && scripts/lint-imports.sh`
  Expected: all pass; axiom linter reports no declaration outside
  `{propext, Quot.sound}`.

  Then run `scripts/pre-push.sh` and confirm it passes (it catches
  umbrella-registration gaps).

- [ ] **Step 5: Commit.**

  ```bash
  jj commit -m "doc(indrec): record the Theorem 2.4 functoriality in docs and TODO"
  ```

---

## Final verification (whole branch)

- [ ] Run `scripts/pre-push.sh` once more on the completed branch.
- [ ] `#print axioms` (via `lean_verify` or a scratch snippet) on
  `IR.rec_mk`, `IR.interpMor_id`, `IR.interpMor_comp`:
  expected ⊆ `{propext, Quot.sound}`.
- [ ] Run the `lean4:review` skill and `pr-review-toolkit:review-pr`
  on the branch, per the phase table; fold fixes into their owning
  task commits with `jj absorb`/`jj squash`.
- [ ] Confirm the spec and this plan remain in the working tree (they
  are removed only at the end of branch 2d, per CONTRIBUTING
  § Concern shape), and that the handoff notes for 2c (the
  Lemma-3/Lemma-4 naturality flag) landed in `TODO.md`.
