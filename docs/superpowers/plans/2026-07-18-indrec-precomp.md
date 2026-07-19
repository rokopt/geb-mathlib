# IR precomposition and semantic lemmas — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Task 1: `FreeCoprodCompDisc` hom composition](#task-1-freecoprodcompdisc-hom-composition)
- [Task 2: binary coproducts and `plus`](#task-2-binary-coproducts-and-plus)
- [Task 3: object isomorphisms and congruence](#task-3-object-isomorphisms-and-congruence)
- [Task 4: copower and its universal property](#task-4-copower-and-its-universal-property)
- [Task 5: object lifting](#task-5-object-lifting)
- [Task 6: `Equiv` combinators — fiber grouping and sum classification](#task-6-equiv-combinators--fiber-grouping-and-sum-classification)
- [Task 7: `IR.precomp` with computation rules](#task-7-irprecomp-with-computation-rules)
- [Task 8: Lemma 4 — correctness of `precomp` (iota and sigma cases)](#task-8-lemma-4--correctness-of-precomp-iota-and-sigma-cases)
- [Task 9: Lemma 4 — delta case and assembly](#task-9-lemma-4--delta-case-and-assembly)
- [Task 10: Lemma 3 — the delta interpretation as a coproduct of copowers](#task-10-lemma-3--the-delta-interpretation-as-a-coproduct-of-copowers)
- [Task 11: documentation and gates](#task-11-documentation-and-gates)
- [Task 12: pre-review pass](#task-12-pre-review-pass)
- [Deviations and stop conditions](#deviations-and-stop-conditions)

<!-- END doctoc generated TOC -->

**Goal:** Branch 1 of the IR-code-morphisms workstream (spec:
`docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`):
`FreeCoprodCompDisc` coproduct/copower/isomorphism operations, the
code-precomposition operation `γ^i` (`IR.precomp`), and the pointwise
isomorphisms of Lemma 3 and Lemma 4 of
[HancockMcBrideGhaniMalatestaAltenkirch2013].

**Architecture:** Three files gain content. `FreeCoprodCompDisc.lean`
gains hom composition, binary coproducts, copowers, object
lifting, and an `Iso` notion with congruence operations.
`Geb/Mathlib/Logic/Equiv/Basic.lean` gains two `Equiv` combinators
(fiber grouping; classification of functions into a sum).
`IndRec/Basic.lean` gains `IR.precomp` with computation rules and the
two semantic isomorphisms, in a new section between the
interpretation block and `section Universes`.

**Tech Stack:** Lean 4 (v4.33.0-rc1 toolchain), mathlib, `lake`,
`jj` (colocated), `lean-lsp` MCP tools.

## Global constraints

Copied from the spec; every task's requirements include these.

- Constructive only: no `noncomputable`, no `Classical`; the axiom
  linter (`lake lint`) permits `{propext, Quot.sound}` only.
- Recursor-only recursion: definitions by `IR.elim`/`IR.rec`; no
  `induction` tactic; no self-referential `def`.
- Explicit proof terms: committed declarations are term-mode with no
  `by` blocks. Tactics may be used transiently to discover a proof
  (e.g. via `lean_multi_attempt` or a scratch `by` block); before
  commit, the discovered proof is rewritten as an explicit term
  factored into small named declarations (motives, step functions,
  auxiliary lemmas), in the manner of `IR.ExtMotive`/`IR.ext`.
  Term-level `match` (including `match h : e with` and `| rfl =>`
  patterns) is permitted; it is how the existing file eliminates
  equalities.
- Universe discipline: at application sites of this repository's
  declarations, a `.{...}` list is either omitted entirely
  (levels inferred) or written in full — partial lists elaborate
  but are banned. Where this plan's snippets write a list, it is
  full; where they omit one, inference is intended. For `ULift`,
  the committed house form `ULift.{r}` with the second level
  inferred from the argument (as in `IR.Direction`) is the
  standard. Ascribe structure result sorts; no
  auto-bound `u_1`-style variables; check for unused
  `universe`/`variable` declarations.
- mathlib style: 2-space indent, 100-column lines, mandatory
  docstrings on every `def` and every theorem of public interest,
  naming per mathlib conventions (`lowerCamelCase` data,
  `snake_case` theorems, `UpperCamelCase` types).
- Search before defining: check mathlib (`lean_local_search`, then
  `lean_loogle`/`lean_leansearch`) for an existing equivalent before
  adding any generic `Equiv` combinator; reuse if found. On
  reuse, re-target the task's tests and every downstream
  reference (Tasks 7, 9, 10) to the mathlib name in place, and
  record the substitution in the commit message.
- Axiom check on reuse: these three modules are held to the
  strict `{propext, Quot.sound}` set (none is on
  `GebMeta.classicalAllowedModules`), so before reusing any
  mathlib declaration in a definition, run `#print axioms` on it
  and reject any that depend on `Classical.choice`. Known traps:
  `Equiv.sigmaCongr` and `Equiv.sigmaCongrRight` are
  `Classical.choice`-tainted, so this plan supplies a choice-free
  `sigmaCongrRight'` (Task 3) in their place;
  `Equiv.sigmaCongrLeft`, `Equiv.sigmaCongrLeft'`,
  `Equiv.sigmaAssoc`, and `Equiv.ulift` are choice-free and may
  be used directly.
- VCS: `jj` only for mutations; commit messages in mathlib
  conventional form (`feat|test|doc|...(scope): imperative subject`,
  no capital, no period). No pushes.
- Gates per task: `lake build` and `lake test` pass before each
  commit. Red (verify-failure) steps run `lake test`: bare
  `lake build` builds only the `Geb` default target and cannot
  fail on a `GebTests/` reference. `sorry` only transiently inside
  a task; never committed.
- Module system: every file keeps its `module` header; new imports
  are `public import` only if re-exported to downstream users;
  `scripts/lint-imports.sh` must pass (subtree rules: `Geb/Mathlib/`
  imports only `Mathlib.*`/`Geb.Mathlib.*`; no self-prefix outside
  import lines).

---

## Task 1: `FreeCoprodCompDisc` hom composition

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
  (after `homOfEq`, before `MapMor`)
- Create: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
- Modify: `GebTests/Mathlib/CategoryTheory.lean` (add the import)

**Interfaces:**

- Consumes: `FreeCoprodCompDisc.Hom` (existing).
- Produces:
  `Hom.comp {X Y Z : FreeCoprodCompDisc.{u, v} D} (f : Hom D X Y)
  (g : Hom D Y Z) : Hom D X Z` (diagrammatic order, as mathlib's
  `CategoryStruct.comp`). Identity morphisms and category laws for
  `FreeCoprodCompDisc.Hom` are not branch-1 content; branch 2 adds
  them if its derivations require them.

- [ ] **Step 1: Write the failing test.** Create
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` with the
  house header (copyright block, `module`,
  `public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc`,
  module docstring with `# Tests for the free coproduct completion`,
  a summary sentence per test section, and `## Tags`), then
  `@[expose] public section`, `open CategoryTheory`, and a first
  section with a sample object and hom:

  ```lean
  /-- A sample object: two names decoding into `Bool` by the
  identity assignment. -/
  def sampleX : FreeCoprodCompDisc.{0, 0} Bool :=
    ⟨Bool, id⟩

  /-- A sample endomorphism of `sampleX`: the identity index
  function, a hom because the decodings agree definitionally. -/
  def sampleHom : FreeCoprodCompDisc.Hom Bool sampleX sampleX :=
    ⟨id, rfl⟩

  /-- Composition of the sample endomorphism with itself is
  itself. -/
  theorem sampleHom_comp :
      FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom = sampleHom :=
    Subtype.ext rfl
  ```

  Register the file: add
  `import GebTests.Mathlib.CategoryTheory.FreeCoprodCompDisc` to
  `GebTests/Mathlib/CategoryTheory.lean`.

- [ ] **Step 2: Run to verify failure.** `lake test` — expected:
  unknown constant `FreeCoprodCompDisc.Hom.comp`.

- [ ] **Step 3: Implement.** In the source file, after `homOfEq`:

  ```lean
  /-- Composition of morphisms of the free coproduct completion, in
  diagrammatic order. -/
  def Hom.comp {X Y Z : FreeCoprodCompDisc.{u, v} D} (f : Hom D X Y)
      (g : Hom D Y Z) : Hom D X Z :=
    ⟨g.1 ∘ f.1, (congrArg (· ∘ f.1) g.2).trans f.2⟩
  ```

  Adjust explicit/implicit argument and `D`-variable form to match
  the file's existing style (declarations take `D` from the
  section `variable`, so uses read `Hom.comp D f g` — verify the
  elaborated form with `lean_hover_info` and align the test
  file). If any `rfl` fails,
  inspect with `lean_diagnostic_messages` and repair with an
  explicit `funext`-based term; do not use `by`.

- [ ] **Step 4: Verify.** `lake build` then `lake test` — expected:
  both succeed.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add hom composition to FreeCoprodCompDisc"`

## Task 2: binary coproducts and `plus`

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
  (after `coprodMor`)
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`

**Interfaces:**

- Consumes: `Hom`, `Hom.comp` (Task 1).
- Produces:

  ```lean
  coprodPair.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
    (Y : FreeCoprodCompDisc.{uY, v} D) :
    FreeCoprodCompDisc.{max uX uY, v} D
  plus.{uJ, uK} (i : FreeCoprodCompDisc.{uJ, v} D)
    (k : FreeCoprodCompDisc.{uK, v} D) :
    FreeCoprodCompDisc.{max uJ uK, v} D
  -- homogeneous-universe hom interface:
  coprodPairInl (X Y : FreeCoprodCompDisc.{u, v} D) :
    Hom D X (coprodPair D X Y)
  coprodPairInr (X Y : FreeCoprodCompDisc.{u, v} D) :
    Hom D Y (coprodPair D X Y)
  coprodPairDesc {X Y Z : FreeCoprodCompDisc.{u, v} D}
    (f : Hom D X Z) (g : Hom D Y Z) : Hom D (coprodPair D X Y) Z
  -- theorems: coprodPair_inl_desc, coprodPair_inr_desc,
  --           coprodPairDesc_eta
  ```

- [ ] **Step 1: Write the failing tests.** In the test file, a
  section exercising a heterogeneous-universe pair and the
  universal property:

  ```lean
  /-- A binary coproduct across index universes. -/
  def samplePair : FreeCoprodCompDisc.{1, 0} Bool :=
    FreeCoprodCompDisc.coprodPair Bool ⟨PUnit.{2}, fun _ ↦ true⟩ sampleX

  /-- The left name of `samplePair` decodes through the left
  component. -/
  theorem samplePair_inl_decode :
      samplePair.2 (Sum.inl PUnit.unit) = true :=
    rfl

  /-- The cotuple restricted along the left injection is the left
  component. -/
  theorem sample_inl_desc :
      FreeCoprodCompDisc.Hom.comp Bool
          (FreeCoprodCompDisc.coprodPairInl Bool sampleX sampleX)
          (FreeCoprodCompDisc.coprodPairDesc Bool sampleHom sampleHom) =
        sampleHom :=
    FreeCoprodCompDisc.coprodPair_inl_desc Bool sampleX sampleX sampleX sampleHom sampleHom
  ```

- [ ] **Step 2: Run to verify failure.** `lake test` — expected:
  unknown constant `FreeCoprodCompDisc.coprodPair`.

- [ ] **Step 3: Implement.**

  ```lean
  /-- The binary coproduct of two objects of the free coproduct
  completion: the sum of the name types, the cotuple of the
  decodings — the cotuple object `[i, k]` of
  [HancockMcBrideGhaniMalatestaAltenkirch2013] (the discussion
  preceding Theorem 2). The two objects may live at different
  index universes. -/
  def coprodPair.{uX, uY} (X : FreeCoprodCompDisc.{uX, v} D)
      (Y : FreeCoprodCompDisc.{uY, v} D) :
      FreeCoprodCompDisc.{max uX uY, v} D :=
    ⟨X.1 ⊕ Y.1, Sum.elim X.2 Y.2⟩

  /-- The object map `(+i)` of [HancockMcBrideGhaniMalatestaAltenkirch2013]
  (the discussion preceding Theorem 2): the binary coproduct with a
  fixed left object. -/
  def plus.{uJ, uK} (i : FreeCoprodCompDisc.{uJ, v} D)
      (k : FreeCoprodCompDisc.{uK, v} D) :
      FreeCoprodCompDisc.{max uJ uK, v} D :=
    coprodPair.{v, uJ, uK} D i k

  /-- The left injection into a binary coproduct (at one index
  universe, where the coproduct is in-category). -/
  def coprodPairInl (X Y : FreeCoprodCompDisc.{u, v} D) :
      Hom D X (coprodPair.{v, u, u} D X Y) :=
    ⟨Sum.inl, rfl⟩

  /-- The right injection into a binary coproduct. -/
  def coprodPairInr (X Y : FreeCoprodCompDisc.{u, v} D) :
      Hom D Y (coprodPair.{v, u, u} D X Y) :=
    ⟨Sum.inr, rfl⟩

  /-- The cotuple: the universal morphism out of a binary
  coproduct. -/
  def coprodPairDesc {X Y Z : FreeCoprodCompDisc.{u, v} D}
      (f : Hom D X Z) (g : Hom D Y Z) :
      Hom D (coprodPair.{v, u, u} D X Y) Z :=
    ⟨Sum.elim f.1 g.1,
      funext (fun s ↦
        Sum.casesOn s (fun a ↦ congrFun f.2 a) (fun b ↦ congrFun g.2 b))⟩

  /-- The cotuple restricted along the left injection is the left
  component. -/
  theorem coprodPair_inl_desc (X Y Z : FreeCoprodCompDisc.{u, v} D)
      (f : Hom D X Z) (g : Hom D Y Z) :
      Hom.comp D (coprodPairInl D X Y) (coprodPairDesc D f g) = f :=
    Subtype.ext rfl

  /-- The cotuple restricted along the right injection is the right
  component. -/
  theorem coprodPair_inr_desc (X Y Z : FreeCoprodCompDisc.{u, v} D)
      (f : Hom D X Z) (g : Hom D Y Z) :
      Hom.comp D (coprodPairInr D X Y) (coprodPairDesc D f g) = g :=
    Subtype.ext rfl

  /-- Every morphism out of a binary coproduct is the cotuple of its
  restrictions along the injections (uniqueness half of the
  universal property). -/
  theorem coprodPairDesc_eta (X Y Z : FreeCoprodCompDisc.{u, v} D)
      (h : Hom D (coprodPair.{v, u, u} D X Y) Z) :
      coprodPairDesc D (Hom.comp D (coprodPairInl D X Y) h)
        (Hom.comp D (coprodPairInr D X Y) h) = h :=
    Subtype.ext (funext (fun s ↦ Sum.casesOn s (fun _ ↦ rfl) (fun _ ↦ rfl)))
  ```

  The cotuple proof uses only core `Sum.casesOn`/`congrFun`, so no
  import change is needed in this task. Universe lists at
  application sites are written in full (three levels for
  `coprodPair`, including the file-level `v`); the order shown
  follows the `coprod.{max uA uB, uO, uA}` precedent (file-level
  levels first) — confirm the elaborated parameter order with
  `lean_hover_info` on first use and correct every site in place
  if it differs.

- [ ] **Step 4: Verify.** `lake build && lake test` — expected: pass.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add binary coproducts to FreeCoprodCompDisc"`

## Task 3: object isomorphisms and congruence

**Files:**

- Modify: `Geb/Mathlib/Logic/Equiv/Basic.lean` (add the choice-free
  `sigmaCongrRight'`, needed by `coprodIso` below and by Task 10;
  `Equiv.sigmaCongrRight` is `Classical.choice`-tainted and these
  modules are on the strict axiom allowlist)
- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
  (import `Mathlib.Logic.Equiv.Basic` and
  `Geb.Mathlib.Logic.Equiv.Basic`; new section after the binary
  coproducts)
- Create: `GebTests/Mathlib/Logic/Equiv/Basic.lean` (mirror;
  house header; register the import chain — check whether
  `GebTests/Mathlib/Logic.lean` / `GebTests/Mathlib/Logic/Equiv.lean`
  index files exist and create them following
  `GebTests/Mathlib/CategoryTheory.lean` if not, adding the chain
  to `GebTests/Mathlib.lean`)
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`

**Interfaces:**

- Consumes: `coprod`, `coprodPair` (Task 2).
- Produces:

  ```lean
  -- α's universe `u` is file-level (bind only t₁, t₂); elaborates
  -- to `sigmaCongrRight'.{u, t₁, t₂}`.
  sigmaCongrRight'.{t₁, t₂} {α : Type u} {β₁ : α → Type t₁}
    {β₂ : α → Type t₂} (F : (a : α) → β₁ a ≃ β₂ a) :
    (Σ a, β₁ a) ≃ Σ a, β₂ a
  Iso.{u₁, u₂} (X : FreeCoprodCompDisc.{u₁, v} D)
    (Y : FreeCoprodCompDisc.{u₂, v} D) : Type (max u₁ u₂)
  -- := {e : X.1 ≃ Y.1 // Y.2 ∘ e = X.2}
  Iso.refl, Iso.symm, Iso.trans, isoOfEq
  coprodIso  -- congruence for coprod along an index Equiv
  ```

  Exact signatures:

  ```lean
  def Iso.refl (X : FreeCoprodCompDisc.{u, v} D) : Iso D X X
  def Iso.symm.{u₁, u₂} {X : FreeCoprodCompDisc.{u₁, v} D}
    {Y : FreeCoprodCompDisc.{u₂, v} D} : Iso D X Y → Iso D Y X
  def Iso.trans.{u₁, u₂, u₃} {X : FreeCoprodCompDisc.{u₁, v} D}
    {Y : FreeCoprodCompDisc.{u₂, v} D}
    {Z : FreeCoprodCompDisc.{u₃, v} D} :
    Iso D X Y → Iso D Y Z → Iso D X Z
  def isoOfEq {X Y : FreeCoprodCompDisc.{u, v} D} :
    X = Y → Iso D X Y
  def coprodIso.{u₁, u₂, w₁, w₂} (ι : Type w₁) (κ : Type w₂) (e : ι ≃ κ)
    (fi : ι → FreeCoprodCompDisc.{u₁, v} D)
    (gk : κ → FreeCoprodCompDisc.{u₂, v} D)
    (iso : (i : ι) → Iso D (fi i) (gk (e i))) :
    Iso D (coprod.{u₁, v, w₁} D ι fi) (coprod.{u₂, v, w₂} D κ gk)
  ```

- [ ] **Step 1: Write the failing tests.** (Universe lists in the
  test blocks of Tasks 3–10 follow the file-level-first order;
  confirm each with `lean_hover_info` and correct in place.)

  ```lean
  /-- A renamed copy of `sampleX`: lifted names, the same
  decodings. -/
  def sampleXLift : FreeCoprodCompDisc.{1, 0} Bool :=
    ⟨ULift.{1} Bool, id ∘ ULift.down⟩

  /-- A sample isomorphism: the `ULift` renaming commutes with the
  decodings. -/
  def sampleIso : FreeCoprodCompDisc.Iso.{0, 1, 0} Bool sampleXLift sampleX :=
    ⟨Equiv.ulift.{1, 0}, rfl⟩

  /-- Round-tripping a name through the sample isomorphism and its
  inverse is the identity. -/
  theorem sampleIso_symm_trans_apply :
      (FreeCoprodCompDisc.Iso.trans Bool sampleIso
        (FreeCoprodCompDisc.Iso.symm Bool sampleIso)).1 (ULift.up true) =
        ULift.up true :=
    rfl
  ```

- [ ] **Step 2: Run to verify failure** (`lake test`, unknown
  constant `FreeCoprodCompDisc.Iso`).
- [ ] **Step 3a: Add the choice-free `sigmaCongrRight'`.** In
  `Geb/Mathlib/Logic/Equiv/Basic.lean`, with explicit-term inverse
  proofs (verified `[Quot.sound]`-clean; mathlib's
  `Equiv.sigmaCongrRight` carries `Classical.choice`, barred here):

  ```lean
  /-- The dependent congruence of a sigma type in its second
  component, choice-free (unlike `Equiv.sigmaCongrRight`). The two
  families are at independent universes, so `coprodIso` can relate
  objects at distinct index universes. -/
  -- `u` is the file-level `universe u`; bind only `t₁ t₂` per
  -- declaration (re-listing `u` is a "already declared" error).
  def sigmaCongrRight'.{t₁, t₂} {α : Type u} {β₁ : α → Type t₁}
      {β₂ : α → Type t₂} (F : (a : α) → β₁ a ≃ β₂ a) :
      (Σ a, β₁ a) ≃ Σ a, β₂ a where
    toFun p := ⟨p.1, F p.1 p.2⟩
    invFun p := ⟨p.1, (F p.1).symm p.2⟩
    left_inv p := congrArg (Sigma.mk p.1) ((F p.1).left_inv p.2)
    right_inv p := congrArg (Sigma.mk p.1) ((F p.1).right_inv p.2)
  ```

  (Verified `[Quot.sound]`-clean, and the `coprodIso` composite
  `(sigmaCongrRight' …).trans (Equiv.sigmaCongrLeft e)` elaborates
  at distinct object universes `u₁ ≠ u₂` and stays
  `[propext, Quot.sound]`.)

  A round-trip test goes in the mirrored
  `GebTests/Mathlib/Logic/Equiv/Basic.lean` (create the file and
  its index chain per this task's Files list):

  ```lean
  /-- `sigmaCongrRight'` round-trips a sample dependent pair. -/
  theorem sampleSigmaCongrRight'_roundtrip :
      (sigmaCongrRight' (fun _ : Bool ↦ Equiv.refl Nat)).symm
        (sigmaCongrRight' (fun _ : Bool ↦ Equiv.refl Nat) ⟨true, 3⟩) =
        ⟨true, 3⟩ :=
    rfl
  ```

- [ ] **Step 3b: Implement the `Iso` interface.** `Iso` as the
  subtype above. Construction notes (verify each mathlib name with
  `lean_local_search`/`lean_hover_info` first):
  - `Iso.refl X := ⟨Equiv.refl X.1, rfl⟩` (repair with
    `funext (fun _ ↦ rfl)` if the coercion blocks `rfl`).
  - `Iso.symm e := ⟨e.1.symm, funext (fun y ↦ ...)⟩` where the
    pointwise term is
    `(congrFun e.2 (e.1.symm y)).symm.trans
    (congrArg Y.2 (e.1.apply_symm_apply y))`.
  - `Iso.trans e f := ⟨e.1.trans f.1, (congrArg (· ∘ ⇑e.1) f.2).trans e.2⟩`
    (the coercion of `Equiv.trans` is definitionally the
    composite; if elaboration blocks, insert
    `Equiv.coe_trans`-transport as an explicit `congrArg`).
  - `isoOfEq | rfl => Iso.refl D X`.
  - `coprodIso`: build the underlying name-equiv as
    `(sigmaCongrRight' (fun i ↦ (iso i).1)).trans
    (Equiv.sigmaCongrLeft (β := fun j ↦ (gk j).1) e)` — choice-free,
    since both factors are (`Equiv.sigmaCongrLeft` verified clean);
    the tainted `Equiv.sigmaCongr` is avoided. The explicit
    `(β := fun j ↦ (gk j).1)` is required: without it
    `Equiv.sigmaCongrLeft`'s fiber is an unsolved metavariable
    (the constraint is not a higher-order pattern) and the term
    picks up `sorryAx`. The commutation field is
    `funext (fun p ↦ congrFun (iso p.1).2 p.2)` (verified to close;
    use `_` binders where a name would be unused, per
    `warningAsError`). Verified `[propext, Quot.sound]` at equal
    and distinct object universes.
  Universe binders: the file declares `universe u v` only; bind the
  additional levels per declaration (`def Iso.{u₁, u₂} …`,
  `def coprodIso.{u₁, u₂, w₁, w₂} …`), following the file's
  `coprod.{w}` precedent. Import change: add the `public import`s
  for `Mathlib.Logic.Equiv.Basic` (for `Equiv`,
  `Equiv.sigmaCongrLeft`) and `Geb.Mathlib.Logic.Equiv.Basic` (for
  `sigmaCongrRight'`); locate the actual mathlib homes under the
  current pin with `lean_declaration_file` if the expected module
  differs (the deviations rule covers import-module corrections);
  run `scripts/lint-imports.sh` to confirm subtree legality.
- [ ] **Step 4: Verify.** `lake build && lake test`.
- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add object isomorphisms to FreeCoprodCompDisc"`

## Task 4: copower and its universal property

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`

**Interfaces:**

- Consumes: `coprod` (existing), `Hom`.
- Produces:

  ```lean
  def copower.{w} (X : Type w) (i : FreeCoprodCompDisc.{u, v} D) :
      FreeCoprodCompDisc.{max u w, v} D :=
    coprod.{u, v, w} D X (fun _ ↦ i)
  def copowerEquiv.{w} (X : Type w)
      (i : FreeCoprodCompDisc.{max u w, v} D)
      (Z : FreeCoprodCompDisc.{max u w, v} D) :
      Hom D (copower.{max u w, v, w} D X i) Z ≃ (X → Hom D i Z)
  ```

- [ ] **Step 1: Write the failing tests.**

  ```lean
  /-- The copower of `sampleX` by `Bool`: names are pairs
  decoding through the second component. -/
  def sampleCopower : FreeCoprodCompDisc.{0, 0} Bool :=
    FreeCoprodCompDisc.copower.{0, 0, 0} Bool Bool sampleX

  /-- A copower name decodes through its second component. -/
  theorem sampleCopower_decode : sampleCopower.2 ⟨true, false⟩ = false :=
    rfl

  /-- The copower cotuple evaluates componentwise: the inverse
  direction of `copowerEquiv` at a constant family applies the
  component morphism. -/
  theorem sampleCopower_desc_apply (b : Bool) :
      ((FreeCoprodCompDisc.copowerEquiv.{0, 0, 0} Bool Bool
        sampleX sampleX).symm (fun _ ↦ sampleHom)).1 ⟨true, b⟩ = b :=
    rfl
  ```

- [ ] **Step 2: Run to verify failure.**
- [ ] **Step 3: Implement.** Docstring cites Lemma 3's copower
  (`X ⊗ i` as the `X`-fold coproduct of `i`,
  [HancockMcBrideGhaniMalatestaAltenkirch2013] Lemma 3).
  `copowerEquiv` construction:

  ```lean
  { toFun := fun h x ↦
      ⟨fun a ↦ h.1 ⟨x, a⟩, funext (fun a ↦ congrFun h.2 ⟨x, a⟩)⟩,
    invFun := fun m ↦
      ⟨fun p ↦ (m p.1).1 p.2, funext (fun p ↦ congrFun (m p.1).2 p.2)⟩,
    left_inv := fun _ ↦ Subtype.ext rfl,
    right_inv := fun _ ↦ funext (fun _ ↦ Subtype.ext rfl) }
  ```

  (Sigma eta makes both inverse laws reduce; if not, repair with
  explicit `funext` over the sigma.)
- [ ] **Step 4: Verify.** `lake build && lake test`.
- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add copowers to FreeCoprodCompDisc"`

## Task 5: object lifting

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`

**Interfaces:**

- Consumes: `Iso` (Task 3), `Hom`.
- Produces:

  ```lean
  def lift.{w} (X : FreeCoprodCompDisc.{u, v} D) :
      FreeCoprodCompDisc.{max u w, v} D :=
    ⟨ULift.{w} X.1, X.2 ∘ ULift.down⟩
  def homLiftEquiv.{w} (X : FreeCoprodCompDisc.{u, v} D)
      (Y : FreeCoprodCompDisc.{max u w, v} D) :
      Hom D (lift.{u, v, w} D X) Y ≃ {h : X.1 → Y.1 // Y.2 ∘ h = X.2}
  ```

- [ ] **Step 1: Write the failing tests.**

  ```lean
  /-- A lifted object decodes through `ULift.down`. -/
  theorem sampleLift_decode :
      (FreeCoprodCompDisc.lift.{0, 0, 1} Bool sampleX).2 (ULift.up true) =
        true :=
    rfl

  /-- `homLiftEquiv` strips the lift from a morphism's domain:
  applying the image of the identity index function evaluates by
  `ULift.up`. -/
  theorem sampleHomLift_apply :
      ((FreeCoprodCompDisc.homLiftEquiv.{0, 0, 1} Bool sampleX
          (FreeCoprodCompDisc.lift.{0, 0, 1} Bool sampleX))
        ⟨_root_.id, rfl⟩).1 true = ULift.up true :=
    rfl
  ```

- [ ] **Step 2: Run to verify failure.**
- [ ] **Step 3: Implement.** `homLiftEquiv`:

  ```lean
  { toFun := fun f ↦
      ⟨f.1 ∘ ULift.up, funext (fun a ↦ congrFun f.2 (ULift.up a))⟩,
    invFun := fun h ↦
      ⟨h.1 ∘ ULift.down, funext (fun a ↦ congrFun h.2 a.down)⟩,
    left_inv := fun _ ↦ Subtype.ext rfl,
    right_inv := fun _ ↦ Subtype.ext rfl }
  ```

- [ ] **Step 4: Verify.** `lake build && lake test`.
- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add object lifting to FreeCoprodCompDisc"`

## Task 6: `Equiv` combinators — fiber grouping and sum classification

**Files:**

- Modify: `Geb/Mathlib/Logic/Equiv/Basic.lean`
- Modify: `GebTests/Mathlib/Logic/Equiv/Basic.lean` (created in
  Task 3, along with its index chain; add the new test sections
  here)

**Interfaces:**

- Produces:

  ```lean
  def sigmaCompEquivSigmaFiber.{w} {X : Type u} {B : Type v}
      (f : X → B) (N : B → Type w) :
      (Σ x, N (f x)) ≃ Σ b, Σ _ : {x // f x = b}, N b
  def arrowSumMerge.{w, p} {B : Type u} {X : Type v}
      {Y : Type w} (c : B → X ⊕ PUnit.{p + 1})
      (j : {b : B // c b = Sum.inr PUnit.unit} → Y) : B → X ⊕ Y
  def arrowSumEquivSigma.{w, p} (B : Type u) (X : Type v)
      (Y : Type w) :
      (B → X ⊕ Y) ≃
        Σ c : B → X ⊕ PUnit.{p + 1},
          ({b : B // c b = Sum.inr PUnit.unit} → Y)
  -- arrowSumEquivSigma.symm ⟨c, j⟩ reduces to arrowSumMerge c j
  -- definitionally (no separate theorem; Task 9 relies on it)
  ```

  The file declares `universe u v` only; `u` and `v` come from
  that declaration (re-binding them per declaration is an error),
  and `w`/`p` are bound per declaration (`def arrowSumMerge.{w,
  p} …`). Application sites still write the full four-level lists
  (`arrowSumClassify.{u, v, w, p} g`), file-level levels first.

- [ ] **Step 1: Search mathlib.** `lean_local_search` then
  `lean_loogle` for each statement (`(Σ x, ?N (?f x)) ≃ _`;
  `(?B → ?X ⊕ ?Y) ≃ _`) and `lean_leansearch` ("sigma over
  composition grouped by fibers", "function into a sum decomposed
  by classifier"). If mathlib provides either equivalence (possibly
  up to `Option`/`Sum PUnit` presentation), reuse it and skip the
  corresponding definition; record the outcome by appending a
  second `-m` paragraph to Step 8's `jj commit` command.
- [ ] **Step 2: Write the failing tests.**

  ```lean
  /-- A sample function into a sum, hitting both components. -/
  def sampleArrow : Bool → Nat ⊕ Bool :=
    fun b ↦ if b then Sum.inl 0 else Sum.inr true

  /-- The classification equivalence round-trips the sample
  function pointwise. -/
  theorem sampleArrow_roundtrip (b : Bool) :
      (arrowSumEquivSigma Bool Nat Bool).symm
        (arrowSumEquivSigma Bool Nat Bool sampleArrow) b =
        sampleArrow b :=
    Bool.casesOn b rfl rfl

  /-- The fiber-grouping equivalence round-trips a sample pair. -/
  theorem sampleSigmaFiber_roundtrip :
      (sigmaCompEquivSigmaFiber Bool.not (fun _ ↦ Nat)).symm
        (sigmaCompEquivSigmaFiber Bool.not (fun _ ↦ Nat) ⟨true, 3⟩) =
        ⟨true, 3⟩ :=
    rfl
  ```

- [ ] **Step 3: Run to verify failure.**
- [ ] **Step 4: Implement `sigmaCompEquivSigmaFiber`.**

  ```lean
  /-- Group a sigma over a composite family by the fibers of the
  inner function. -/
  def sigmaCompEquivSigmaFiber.{w} {X : Type u} {B : Type v}
      (f : X → B) (N : B → Type w) :
      (Σ x, N (f x)) ≃ Σ b, Σ _ : {x // f x = b}, N b where
    toFun p := ⟨f p.1, ⟨p.1, rfl⟩, p.2⟩
    invFun q :=
      match q with
      | ⟨_, ⟨x, rfl⟩, n⟩ => ⟨x, n⟩
    left_inv _ := rfl
    right_inv q :=
      match q with
      | ⟨_, ⟨_, rfl⟩, _⟩ => rfl
  ```

- [ ] **Step 5: Implement `arrowSumMerge` and the classification
  direction.** The `Sum.casesOn`-with-equation-motive technique
  (as `IR.ExtMotive` eliminates equalities with an explicit
  motive):

  ```lean
  /-- Reassemble a function into a sum from a classifier and an
  assignment on the unresolved subtype. -/
  def arrowSumMerge.{w, p} {B : Type u} {X : Type v}
      {Y : Type w} (c : B → X ⊕ PUnit.{p + 1})
      (j : {b : B // c b = Sum.inr PUnit.unit} → Y) : B → X ⊕ Y :=
    fun b ↦
      Sum.casesOn (motive := fun s ↦ c b = s → X ⊕ Y) (c b)
        (fun x _ ↦ Sum.inl x) (fun _ h ↦ Sum.inr (j ⟨b, h⟩)) rfl

  /-- Classify a function into a sum: keep left values, mark right
  values. -/
  def arrowSumClassify.{w, p} {B : Type u} {X : Type v}
      {Y : Type w} (g : B → X ⊕ Y) : B → X ⊕ PUnit.{p + 1} :=
    Sum.map _root_.id (fun _ ↦ PUnit.unit) ∘ g

  /-- Recover the right values of a function into a sum on the
  subtype its classifier marks. -/
  def arrowSumResolve.{w, p} {B : Type u} {X : Type v}
      {Y : Type w} (g : B → X ⊕ Y)
      (bp : {b : B // arrowSumClassify.{u, v, w, p} g b = Sum.inr PUnit.unit}) :
      Y :=
    Sum.casesOn
      (motive := fun s ↦
        Sum.map _root_.id (fun _ ↦ PUnit.unit) s = Sum.inr PUnit.unit → Y)
      (g bp.1) (fun _ h ↦ nomatch h) (fun y _ ↦ y) bp.2

  -- (`nomatch` replaces `Sum.noConfusion`, whose bare-term form does
  -- not elaborate under the v4.33 per-field noConfusion signature;
  -- the full list on `arrowSumClassify` pins the otherwise-unused
  -- level `p`.)
  ```

- [ ] **Step 6: Implement the equivalence.** The two inverse laws
  are the proofs most likely to require iteration in this
  branch. Derive each pointwise statement as its own named
  theorem. Direct `rw`/`generalize`/`simp` on the dependent
  scrutinee fails (motive-is-not-type-correct), so factor an
  equation-generalization lemma first: for arbitrary `s : X ⊕
  PUnit` and `h : c b = s`, state the value of `arrowSumMerge c j
  b` as the `Sum.casesOn` of `s` applied to `h`, proved by a
  `| rfl => rfl` match — and a second such lemma for
  `arrowSumResolve` (whose `Sum.casesOn` scrutinee `g b` is
  otherwise opaque inside `arrowSumMerge_classify`). The
  per-case residues then close by `h`-transports and proof
  irrelevance (unit eta discharges the `inr` markers); expect
  more than one auxiliary lemma, each named. The committed forms
  are explicit terms:

  ```lean
  theorem arrowSumMerge_classify.{w, p} {B : Type u}
      {X : Type v} {Y : Type w} (g : B → X ⊕ Y) (b : B) :
      arrowSumMerge (arrowSumClassify.{u, v, w, p} g)
        (arrowSumResolve g) b = g b
  theorem arrowSumClassify_merge.{w, p} {B : Type u}
      {X : Type v} {Y : Type w} (c : B → X ⊕ PUnit.{p + 1})
      (j : {b : B // c b = Sum.inr PUnit.unit} → Y) (b : B) :
      arrowSumClassify (arrowSumMerge.{u, v, w, p} c j) b = c b
  ```

  For the sigma-valued `right_inv`, the second component is a
  function whose domain depends on the first; eliminate the
  `funext`-derived first-component equality with an explicit
  motive (an `ArrowSumEta`-style motive definition analogous to
  `IR.ExtMotive`, taking the classifier equality and stating the
  transported second-component equality), rather than `Sigma.ext`
  with `HEq`. Then:

  ```lean
  /-- A function into a sum is a classifier together with an
  assignment on the unresolved subtype. -/
  def arrowSumEquivSigma.{w, p} (B : Type u) (X : Type v)
      (Y : Type w) :
      (B → X ⊕ Y) ≃
        Σ c : B → X ⊕ PUnit.{p + 1},
          ({b : B // c b = Sum.inr PUnit.unit} → Y) where
    toFun g := ⟨arrowSumClassify g, arrowSumResolve g⟩
    invFun q := arrowSumMerge q.1 q.2
    left_inv g := funext (fun b ↦ arrowSumMerge_classify g b)
    right_inv q := -- assembled from arrowSumClassify_merge via the
                   -- named motive; exact term produced in-task
  ```

  The `right_inv` field must be an explicit term at commit time; if
  after two working sessions it resists term-mode assembly, stop
  and report (stuck-and-ask template in
  `docs/rules/lean-coding.md`) rather than committing a tactic
  proof.
- [ ] **Step 7: Verify.** `lake build && lake test`.
- [ ] **Step 8: Commit.**
  `jj commit -m "feat(equiv): add fiber grouping and sum classification equivalences"`

## Task 7: `IR.precomp` with computation rules

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` (new
  section after the `interpMor` namespace block ends at
  `end IR`, before `section Universes`)
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`

**Interfaces:**

- Consumes: `IR.elimAlg`, `IR.Alg`, `IR.iota/sigma/delta`,
  `arrowSumMerge` (Task 6).
- Produces (inside `namespace IR`, with a new
  `universe uQ` declaration):

  ```lean
  def precompMerge (Q : Type uQ) (i : Q → I) {B : Type uB}
      (c : B → Q ⊕ PUnit.{uQ + 1})
      (j : {b : B // c b = Sum.inr PUnit.unit} → I) : B → I :=
    Sum.elim i _root_.id ∘ arrowSumMerge c j
  def precompAlg (Q : Type uQ) (i : Q → I) :
      Alg.{uA, uB, uI, uO, max (max uA uB uQ + 1) (uB + 1) uI uO}
        I O (IR.{max uA uB uQ, uB, uI, uO} I O)
  def precomp (Q : Type uQ) (i : Q → I) :
      IR.{uA, uB, uI, uO} I O → IR.{max uA uB uQ, uB, uI, uO} I O
  -- computation rules, all rfl:
  theorem precomp_iota (Q : Type uQ) (i : Q → I) (o : O) :
    precomp I O Q i (iota I O o) = iota I O o
  theorem precomp_sigma (Q : Type uQ) (i : Q → I) (A : Type uA)
      (c : A → IR.{uA, uB, uI, uO} I O) :
    precomp I O Q i (sigma I O A c) =
      sigma I O (ULift.{max uB uQ} A)
        (fun a ↦ precomp I O Q i (c a.down))
  theorem precomp_delta (Q : Type uQ) (i : Q → I) (B : Type uB)
      (c : (B → I) → IR.{uA, uB, uI, uO} I O) :
    precomp I O Q i (delta I O B c) =
      sigma I O (ULift.{uA} (B → Q ⊕ PUnit.{uQ + 1}))
        (fun cl ↦ delta I O {b : B // cl.down b = Sum.inr PUnit.unit}
          (fun j ↦ precomp I O Q i (c (precompMerge I Q i cl.down j))))
  ```

  Value arguments are explicit binders (the file's section
  variables are `I O` only, and `autoImplicit` is off), with the
  one exception shown: `precompMerge`'s `{B}` is implicit —
  inferable from `c`, and every stated application site relies on
  that. The
  literal universe levels above are the elaboration targets —
  confirm each with `lean_hover_info` and correct in place per
  the deviations rule if the elaborated form differs.

  Exact `.{...}` instantiations at every application site; the
  section carries a module-docstring-style comment
  (`/-! ### Precomposition on codes ... -/`) citing Lemma 4 and
  marking the concrete construction as this project's (the paper
  asserts existence only).

- [ ] **Step 1: Write the failing tests.** In the IndRec test
  file, over the index types `I := Bool`, `O := PUnit` (a
  non-unit `I`, so the merge branches are distinguishable):

  ```lean
  /-- A sample delta code: one boolean recursive arity, decoding
  to the unit. -/
  def sampleDeltaCode : IR.{0, 0, 0, 0} Bool PUnit :=
    IR.delta Bool PUnit Bool (fun _ ↦ IR.iota Bool PUnit PUnit.unit)

  /-- The merged assignment takes resolved arity elements from
  `i`. -/
  theorem samplePrecompMerge_inl (b : Bool) :
      IR.precompMerge Bool PUnit.{1} (fun _ ↦ true)
        (fun _ : Bool ↦ Sum.inl PUnit.unit)
        (fun j ↦ nomatch j.2) b = true :=
    rfl

  /-- The merged assignment takes unresolved arity elements from
  the direction assignment. -/
  theorem samplePrecompMerge_inr (b : Bool) :
      IR.precompMerge Bool PUnit.{1} (fun _ ↦ true)
        (fun _ : Bool ↦ Sum.inr PUnit.unit) (fun _ ↦ false) b =
        false :=
    rfl

  /-- The delta computation rule at the sample code. -/
  theorem samplePrecomp_delta :
      IR.precomp Bool PUnit PUnit.{1} (fun _ ↦ true) sampleDeltaCode =
        IR.sigma Bool PUnit (ULift.{0} (Bool → PUnit ⊕ PUnit.{1}))
          (fun cl ↦
            IR.delta Bool PUnit
              {b : Bool // cl.down b = Sum.inr PUnit.unit}
              (fun _ ↦ IR.iota Bool PUnit PUnit.unit)) :=
    rfl
  ```

- [ ] **Step 2: Run to verify failure.**
- [ ] **Step 3: Implement.** The algebra components:

  ```lean
  /-- The algebra computing one step of `IR.precomp`: `iota` and
  `sigma` push through (up to `ULift`); `delta` becomes a `sigma`
  over classifiers followed by a `delta` over the unresolved
  arity elements. -/
  def precompAlg (Q : Type uQ) (i : Q → I) :
      Alg.{uA, uB, uI, uO, max (max uA uB uQ + 1) (uB + 1) uI uO}
        I O (IR.{max uA uB uQ, uB, uI, uO} I O) :=
    ⟨fun o ↦ iota I O o,
      fun A f ↦ sigma I O (ULift.{max uB uQ} A) (f ∘ ULift.down),
      fun B f ↦
        sigma I O (ULift.{uA} (B → Q ⊕ PUnit.{uQ + 1})) (fun cl ↦
          delta I O {b : B // cl.down b = Sum.inr PUnit.unit} (fun j ↦
            f (precompMerge I Q i cl.down j)))⟩

  /-- Precomposition on codes (the `γ^i` of
  [HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 4, which
  asserts existence only; this construction is the project's):
  `⟦precomp Q i γ⟧ k` is isomorphic to `⟦γ⟧` at the coproduct of
  `⟨Q, i⟩` with `k` (`interpPrecompIso`). -/
  def precomp (Q : Type uQ) (i : Q → I) :
      IR.{uA, uB, uI, uO} I O → IR.{max uA uB uQ, uB, uI, uO} I O :=
    elimAlg I O (IR.{max uA uB uQ, uB, uI, uO} I O) (precompAlg I O Q i)
  ```

  The computation rules are `rfl` because
  `elimAlg` runs `WType.elim`, which reduces on `mk`; verify each
  with `lean_diagnostic_messages` before commit.
- [ ] **Step 4: Verify.** `lake build && lake test`.
- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add code precomposition along a coproduct"`

## Task 8: Lemma 4 — correctness of `precomp` (iota and sigma cases)

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`

**Interfaces:**

- Consumes: `precomp` (Task 7), `Iso`, `coprodIso`, `plus`
  (Tasks 2–3), `interpObj`, `RecStep`, `rec`.
- Produces: the motive and the first two step cases of the
  induction, at the uniform instantiation (`γ`, and every code
  argument below, at `IR.{max uA uB, uB, uI, uO} I O`;
  `Q : Type uB`; `k : FreeCoprodCompDisc.{max uA uB, uI} I`):

  ```lean
  def PrecompIsoMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
      Type (max (max uA uB + 1) uI) :=
    (Q : Type uB) → (i : Q → I) →
      (k : FreeCoprodCompDisc.{max uA uB, uI} I) →
      FreeCoprodCompDisc.Iso O
        (interpObj I O (precomp I O Q i γ) k)
        (interpObj I O γ (FreeCoprodCompDisc.plus I ⟨Q, i⟩ k))
  def precompIsoIota (o : O) : PrecompIsoMotive I O (iota I O o)
  def precompIsoSigma (A : Type (max uA uB))
      (c : A → IR.{max uA uB, uB, uI, uO} I O)
      (ih : (a : A) → PrecompIsoMotive I O (c a)) :
      PrecompIsoMotive I O (sigma I O A c)
  ```

  These blocks show signatures only; each declaration carries a
  docstring at implementation time (mandatory per the global
  constraints). The same applies to Tasks 9 and 10.

- [ ] **Step 1: Write the failing tests.** In the IndRec test
  file, at the all-zero universe instantiation:

  ```lean
  /-- A one-name sample object over the unit index type. -/
  def samplePoint : FreeCoprodCompDisc.{0, 0} PUnit :=
    ⟨PUnit, fun _ ↦ PUnit.unit⟩

  /-- The constant-case isomorphism is the identity on the single
  name. -/
  theorem samplePrecompIsoIota_apply :
      ((IR.precompIsoIota.{0, 0, 0, 0} PUnit PUnit PUnit.unit)
        PUnit (fun _ ↦ PUnit.unit) samplePoint).1 (ULift.up Unit.unit) =
        ULift.up Unit.unit :=
    rfl

  /-- The sum-case isomorphism strips the lifted index: the lifted
  left name maps to the left name. -/
  theorem samplePrecompIsoSigma_apply :
      (((IR.precompIsoSigma.{0, 0, 0, 0} PUnit PUnit Bool
            (fun _ ↦ IR.iota.{0, 0, 0, 0} PUnit PUnit PUnit.unit)
            (fun _ ↦ IR.precompIsoIota.{0, 0, 0, 0} PUnit PUnit PUnit.unit))
          PUnit (fun _ ↦ PUnit.unit) samplePoint).1
        ⟨ULift.up true, ULift.up Unit.unit⟩).1 = true :=
    rfl
  ```

- [ ] **Step 2: Run to verify failure.**
- [ ] **Step 3: Implement `precompIsoIota`.**
  `interpObj` of an `iota` code is the constant object map, so both
  sides are the same object:
  `fun _ _ k ↦ FreeCoprodCompDisc.Iso.refl O (interpObj I O (iota I O o) k)`
  (underscore binders for the unused `Q` and `i`, since the repo
  builds with `warningAsError`)
  adjusted (via `isoOfEq` on a `rfl`-checked equality) if the two
  sides are definitionally but not syntactically equal; confirm
  reduction with `lean_goal` on a scratch underscore.
- [ ] **Step 4: Implement `precompIsoSigma`.** By `precomp_sigma`,
  the left side is the `coprod` over `ULift A` of the
  interpretations of precomposed subcodes; the right side is the
  `coprod` over `A` of the subcode interpretations at the extended
  object. Assemble:

  ```lean
  fun Q i k ↦
    FreeCoprodCompDisc.coprodIso O (ULift.{uB} A) A Equiv.ulift
      (fun a ↦ interpObj I O (precomp I O Q i (c a.down)) k)
      (fun a ↦ interpObj I O (c a) (FreeCoprodCompDisc.plus I ⟨Q, i⟩ k))
      (fun a ↦ ih a.down Q i k)
  ```

  (Exact universe lists per the elaborated form; `Equiv.ulift`'s
  direction is `ULift A ≃ A`, matching `coprodIso`'s `e : ι ≃ κ`
  with `ι := ULift A`.)
- [ ] **Step 5: Verify.** `lake build && lake test`.
- [ ] **Step 6: Commit.**
  `jj commit -m "feat(indrec): prove precomp correctness for iota and sigma"`

## Task 9: Lemma 4 — delta case and assembly

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`

**Interfaces:**

- Consumes: Tasks 6–8 (`arrowSumEquivSigma`, `precompMerge`,
  `PrecompIsoMotive`, the two step cases), `Equiv.sigmaCongrLeft`
  or equivalent mathlib reshuffles (verify names by search).
- Produces:

  ```lean
  theorem precompMerge_elim (Q : Type uB) (i : Q → I)
      (k : FreeCoprodCompDisc.{max uA uB, uI} I) (B : Type uB)
      (c : B → Q ⊕ PUnit.{uB + 1})
      (j : {b : B // c b = Sum.inr PUnit.unit} → k.1) :
      precompMerge I Q i c (k.2 ∘ j) =
        Sum.elim i k.2 ∘ arrowSumMerge c j
  def precompIsoDelta (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (ih : (m : B → I) → PrecompIsoMotive I O (c m)) :
      PrecompIsoMotive I O (delta I O B c)
  def interpPrecompIso (γ : IR.{max uA uB, uB, uI, uO} I O) :
      PrecompIsoMotive I O γ
  ```

  `interpPrecompIso` is Lemma 4 (docstring cites it; the recorded
  deviation — isomorphism for the paper's equality — is stated in
  the docstring).

- [ ] **Step 1: Write the failing test.** `IR.rec`-assembled
  definitions do not reduce definitionally (the test file's module
  docstring records this for `univEndoMor`), so the test targets
  the delta case directly, following the house `interpMorStep`
  pattern; `interpPrecompIso` itself is exercised only
  propositionally (its type states Lemma 4) and gets no `rfl`
  test. (Uses `samplePoint` from Task 8's tests.)

  ```lean
  /-- The delta-case isomorphism maps an all-unresolved sample
  name to the single-classifier form: the resulting name's index
  component sends every arity element to the recursive side. -/
  theorem samplePrecompIsoDelta_apply :
      (((IR.precompIsoDelta PUnit.{1} PUnit.{1} Bool
            (fun _ ↦ IR.iota PUnit.{1} PUnit.{1} PUnit.unit)
            (fun _ ↦ IR.precompIsoIota PUnit.{1} PUnit.{1} PUnit.unit))
          PUnit.{1} (fun _ ↦ PUnit.unit) samplePoint).1
        ⟨ULift.up (fun _ ↦ Sum.inr PUnit.unit),
          fun _ ↦ PUnit.unit, ULift.up Unit.unit⟩).1 =
        fun _ ↦ Sum.inr PUnit.unit :=
    rfl
  ```

  (The sample name's exact anonymous-constructor nesting follows
  the elaborated `interpObj` shapes — adjust the `⟨…⟩` grouping to
  the goal shown by `lean_diagnostic_messages`, not the
  statement's content. If the `rfl` is blocked by an opaque
  mathlib reshuffle in the assembled equivalence, test the
  reshuffle piece — `precompIsoDeltaReshuffle` below — directly
  at the same sample instead, adjusting the test, not the
  definition. The same fallback applies to Task 10's
  `sampleInterpDeltaIso_apply`: retarget at `interpDeltaIsoGroup`
  or `interpDeltaIsoHom` if the assembled `rfl` blocks.)
- [ ] **Step 2: Run to verify failure.**
- [ ] **Step 3: Prove `precompMerge_elim`.** Pointwise by
  `funext`; per point, both sides case on `c b`
  (`Sum.casesOn` with equation motive, as in `arrowSumMerge`):
  left branch both compute `i q`; right branch both compute
  `k.2 (j ⟨b, h⟩)`. Discover with a scratch tactic block if
  needed; commit an explicit term.
- [ ] **Step 4: Implement `precompIsoDelta`.** Composition of
  isomorphisms (`Iso.trans`), built from named pieces in order:
  1. Left side, by `precomp_delta`: names are
     `Σ cl : ULift (B → Q ⊕ PUnit), Σ g : {unresolved} → k.1,
     ⟦precomp I O Q i (c (precompMerge I Q i cl.down (k.2 ∘ g)))⟧ k`.
  2. `coprodIso` over `Equiv.ulift` strips the `ULift`.
  3. For fixed `cl`, inner `coprodIso` (identity index equiv) with
     componentwise `Iso.trans` of: the inductive hypothesis
     `ih (precompMerge I Q i cl.down (k.2 ∘ g)) Q i k`, then
     `isoOfEq` applied to
     `congrArg (fun m ↦ interpObj I O (c m) (plus I ⟨Q, i⟩ k))
     (precompMerge_elim …)` — aligning the subcode argument with
     the right side's `Sum.elim i k.2 ∘ arrowSumMerge cl.down g`.
  4. The outer reshuffle to the right side's single sigma over
     `g' : B → Q ⊕ k.1`: `Equiv.sigmaCongrLeft` (or the mathlib
     equivalent found by search) along
     `(arrowSumEquivSigma B Q k.1).symm`, composed with the
     sigma-associativity equivalence; package as an `Iso` whose
     commutation field is `funext` over the sigma with pointwise
     `rfl` (repair pointwise with an explicit lemma if not `rfl`).
  Factor each numbered piece as its own named `def` (e.g.
  `precompIsoDeltaInner`, `precompIsoDeltaReshuffle`) with a
  docstring; assemble `precompIsoDelta` as their `Iso.trans`
  chain. This is the largest single proof of the branch: if the
  commutation fields resist term-mode `rfl`/`funext` assembly
  after two working sessions, stop and report per the
  stuck-and-ask template.
- [ ] **Step 5: Assemble `interpPrecompIso`.** Via `IR.rec` at the
  uniform instantiation with a `RecStep` dispatching on the shape
  (the same `match` shape as `interpMorStep`):

  ```lean
  def interpPrecompIsoStep :
      RecStep.{max uA uB, uB, uI, uO, max (max uA uB + 1) uI} I O
        (PrecompIsoMotive I O) :=
    fun s c m ↦ match s with
    | Sum.inl o => precompIsoIota I O o
    | Sum.inr (Sum.inl A) =>
        precompIsoSigma I O A (fun a ↦ c (ULift.up a))
          (fun a ↦ m (ULift.up a))
    | Sum.inr (Sum.inr B) =>
        precompIsoDelta I O B (fun f ↦ c (ULift.up f))
          (fun f ↦ m (ULift.up f))
  def interpPrecompIso (γ : IR.{max uA uB, uB, uI, uO} I O) :
      PrecompIsoMotive I O γ :=
    rec I O (interpPrecompIsoStep I O) γ
  ```

  (The step cases must produce motives at `mk`-applied codes. The
  primary path is to rely on `sigma`/`delta` being definitionally
  `mk …` — so `precompIsoSigma`/`precompIsoDelta`, stated at
  `sigma`/`delta`, already have the `mk`-form type, exactly as
  `interpMorStep` dispatches without a bridge. Only if a residual
  mismatch surfaces, transport the motive with `PrecompIsoMotive`
  applied to the code equality `sigma I O A c =
  mk I O (Sum.inr (Sum.inl A)) (c ∘ ULift.down)` — a motive
  transport along an `IR`-code equality (`Eq.mpr`/`▸`), not
  `isoOfEq`, which rewrites a `FreeCoprodCompDisc`-object equality
  inside an `Iso` rather than the code index.)
- [ ] **Step 6: Verify.** `lake build && lake test`.
- [ ] **Step 7: Commit.**
  `jj commit -m "feat(indrec): prove precomp correctness for delta"`

## Task 10: Lemma 3 — the delta interpretation as a coproduct of copowers

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean`

**Interfaces:**

- Consumes: `sigmaCompEquivSigmaFiber` (Task 6), `copower`
  (Task 4), `lift`/`homLiftEquiv` (Task 5), `coprod`, `Iso`.
- Produces:

  ```lean
  def interpDeltaIso (B : Type uB)
      (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
      (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
      FreeCoprodCompDisc.Iso O
        (interpObj I O (delta I O B c) k)
        (FreeCoprodCompDisc.coprod O (B → I) (fun i ↦
          FreeCoprodCompDisc.copower O
            (FreeCoprodCompDisc.Hom I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) k)
            (interpObj I O (c i) k)))
  ```

  Docstring cites Lemma 3 and records the pointwise-for-natural
  deviation. Exact universe lists per elaboration.

- [ ] **Step 1: Write the failing test.** (Uses `samplePoint`
  from Task 8's tests.)

  ```lean
  /-- The delta-interpretation isomorphism sends a name to the
  triple indexed by the composite of the decoding with the
  direction assignment. -/
  theorem sampleInterpDeltaIso_apply :
      ((IR.interpDeltaIso.{0, 0, 0, 0} PUnit PUnit Bool
            (fun _ ↦ IR.iota.{0, 0, 0, 0} PUnit PUnit PUnit.unit)
            samplePoint).1
          ⟨fun _ ↦ PUnit.unit, ULift.up Unit.unit⟩).1 =
        fun _ ↦ PUnit.unit :=
    rfl
  ```

- [ ] **Step 2: Run to verify failure.**
- [ ] **Step 3: Implement.** The name-type equivalence is the
  composite of:
  1. `sigmaCompEquivSigmaFiber (f := (k.2 ∘ ·))
     (N := fun i ↦ (interpObj I O (c i) k).1)` — grouping the
     left side's `Σ g : B → k.1, …` by the composite `k.2 ∘ g`;
  2. per `i` (inside `sigmaCongrRight'` from Task 3 — the
     choice-free counterpart of the tainted
     `Equiv.sigmaCongrRight`), a first-component replacement of
     `{g : B → k.1 // k.2 ∘ g = i}` by `Hom I (lift ⟨B, i⟩) k` via
     `(homLiftEquiv …).symm` — the subtype is exactly
     `homLiftEquiv`'s right-hand side at `X := ⟨B, i⟩`, `Y := k`.
     Build this replacement as a hand-rolled projection-based
     `Equiv` (`toFun := fun q ↦ ⟨(homLiftEquiv …).symm q.1, q.2⟩`,
     and likewise for `invFun`), not via `Equiv.sigmaCongrLeft'`:
     the latter's `Eq.rec` transport blocks definitional
     reduction of the commutation field, while the
     projection-based form closes it by `rfl`.
  The commutation field: `funext (fun _ ↦ rfl)` (the binder is
  unused; a named binder fails the build under `warningAsError`).
  Factor the two numbered equivalences as named defs
  (`interpDeltaIsoGroup`, `interpDeltaIsoHom`) before assembling.
  Stop condition: as in Task 6, if the assembly resists term-mode
  completion after two working sessions, stop and report per the
  stuck-and-ask template.
- [ ] **Step 4: Verify.** `lake build && lake test`.
- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): present delta interpretation as coproduct of copowers"`

## Task 11: documentation and gates

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
  (module docstring: new `## Main definitions` entries for
  `Hom.comp`, `coprodPair`/`plus`, `copower`, `lift`, `Iso` and
  congruences; `## References` gains
  `[HancockMcBrideGhaniMalatestaAltenkirch2013]`, cited by the
  `coprodPair`, `plus`, and `copower` docstrings)
- Modify: `Geb/Mathlib/Logic/Equiv/Basic.lean` (module docstring:
  the three added declarations — `sigmaCongrRight'`,
  `sigmaCompEquivSigmaFiber`, `arrowSumEquivSigma`; title/summary
  updated beyond "sections of sigma-type projections")
- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` (module
  docstring: `## Main definitions` entries for `IR.precomp` and
  the isomorphisms; `## Main statements` for the computation rules
  and `interpPrecompIso`/`interpDeltaIso`; `## Implementation
  notes` paragraph on the universe scheme and the recorded
  deviations; `## References` unchanged)
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Basic.lean` and
  `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
  (module docstrings describe the added test sections)
- Modify: `docs/index.md` (extend the `FreeCoprodCompDisc` and
  `IndRec` paragraphs with the new content, same style)
- Modify: `TODO.md` (add the branch-2 item — homset, identity,
  composition, category laws — under the IndRec workstream,
  citing the paper's Definition 8 and Corollary 2; TODO.md is
  permanent, so it must not reference the transient spec or plan
  paths)

**Interfaces:** none produced; documentation only.

- [ ] **Step 1: Update the three source module docstrings** per the
  file list above; every new declaration keeps its own docstring
  (added in Tasks 1–10); no history references. Citation scope
  (per the spec): declarations transcribed from or specified by
  the paper (`coprodPair`, `plus`, `copower`, `precomp` and its
  computation rules, `PrecompIsoMotive` — the statement schema of
  Lemma 4 — `interpPrecompIso`, `interpDeltaIso`) cite
  `[HancockMcBrideGhaniMalatestaAltenkirch2013]`; generic
  auxiliary machinery (`Hom.comp`, the injections, cotuple, and
  `coprodPairDesc_eta`, `copowerEquiv`, the `Iso` family, `lift`,
  `homLiftEquiv`, the `Equiv` combinators (`sigmaCongrRight'`,
  `sigmaCompEquivSigmaFiber`, `arrowSumEquivSigma`),
  `precompMerge`/`precompAlg`/`precompMerge_elim`, the iso step
  cases and their named factoring pieces —
  `precompIsoDeltaInner`, `precompIsoDeltaReshuffle`,
  `interpDeltaIsoGroup`, `interpDeltaIsoHom`) is not from the
  paper and carries no citation.
- [ ] **Step 2: Update `docs/index.md` and `TODO.md`.**
- [ ] **Step 3: Markdown gates.**
  `doctoc --update-only . && markdownlint-cli2 '**/*.md'`
  — expected: no TOC drift, 0 errors.
- [ ] **Step 4: Full gates.**
  `lake build && lake test && lake lint && scripts/lint-imports.sh`
  — expected: all pass; the axiom linter confirms every new
  declaration depends on `{propext, Quot.sound}` at most (this
  holds only because the tainted `Equiv.sigmaCongr`/
  `Equiv.sigmaCongrRight` were replaced by `sigmaCongrRight'`;
  spot-check `coprodIso`, `interpPrecompIso`, and `interpDeltaIso`
  with `lean_verify`, since those are the declarations whose
  earlier drafts would have carried `Classical.choice`).
- [ ] **Step 5: Shake check.** Run the pre-push shake invocation
  (`lake shake --add-public --keep-implied --keep-prefix Geb
  GebTests`, per `docs/rules/ci-and-workflow.md` — use the exact
  form in `scripts/pre-push.sh` if it differs); if a new import is
  flagged as unused because it serves only tests, follow the house
  pattern (a named `def` value in the test file exercising the
  import) rather than a suppression.
- [ ] **Step 6: Commit.**
  `jj commit -m "doc(indrec): document precomposition and semantic lemmas"`

## Task 12: pre-review pass

- [ ] **Step 1:** Run `lean4:review` on the three changed source
  files (read-only review skill; address findings or record
  disagreements).
- [ ] **Step 2:** Run `scripts/pre-push.sh`; fix anything it flags.
- [ ] **Step 3:** Final `jj status` — working copy clean; branch
  history is the Task 1–11 commit sequence on
  `feat/indrec-precomp` after the spec/plan commits. Report to the
  user for line-by-line review (no push).
- [ ] **Step 4: Transient-artifact removal (after the user's
  review approves the branch for merge, not before).** Per
  CONTRIBUTING § Concern shape, spec and plan never reach `main`'s
  working tree: whatever the merge sequencing, branch 1 is merged
  only with a final commit
  (`chore: remove transient spec and plan`) removing the spec and
  this plan from its tree. If branch 2 stacks on branch 1 before
  that removal commit exists, branch 2 is `jj`-rebased onto the
  removal commit when branch 1 is finalized; its planning phase
  reads the spec from history. The spec and this plan remain
  reachable in history in every sequencing.

## Deviations and stop conditions

- Any signature that fails to elaborate at the plan's universe
  lists, and any import whose providing module differs under the
  current pin from the plan's expectation, is corrected in place,
  with the correction recorded in the commit; if a correction
  changes an interface another task consumes, update that task
  before proceeding.
- Any statement here that turns out false (not merely hard) — in
  particular a non-`rfl` computation rule in Task 7 or a
  non-closing motive in Task 9 — stops execution; report per the
  stuck-and-ask template and return to design. Do not weaken a
  statement to make it provable.
- Tactic blocks are permitted only transiently within a task and
  never committed.
