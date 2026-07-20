# IR morphisms 2a: homset and identity — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [File structure](#file-structure)
- [Task 1: the homset `IR.Hom`](#task-1-the-homset-irhom)
- [Task 2: `σ`-injection postcomposition `IR.sigmaPush`](#task-2-%CF%83-injection-postcomposition-irsigmapush)
- [Task 3: empty-`δ` injection `IR.deltaEmptyPush`](#task-3-empty-%CE%B4-injection-irdeltaemptypush)
- [Task 4: multi-precomposition `IR.mprecomp` and its computation lemmas](#task-4-multi-precomposition-irmprecomp-and-its-computation-lemmas)
- [Task 5: stack `σ`-push `IR.msigmaPush`](#task-5-stack-%CF%83-push-irmsigmapush)
- [Task 6: navigation `IR.deltaNavBase` and `IR.deltaNav`](#task-6-navigation-irdeltanavbase-and-irdeltanav)
- [Task 7: the pre-unit `IR.preUnitStack` and the identity `IR.id`](#task-7-the-pre-unit-irpreunitstack-and-the-identity-irid)
- [Task 8: documentation and gates](#task-8-documentation-and-gates)
- [Deviations and stop conditions](#deviations-and-stop-conditions)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Add the homset of IR codes (Definition 8 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]) and the identity morphism,
constructed syntactically, at the uniform stabilized instantiation.

**Architecture:** A new module `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
(importing `IndRec/Basic.lean`) defines `IR.Hom` by `IR.elim` on the
domain code with an inner `IR.elim` on the codomain in the `ι` case, then
the identity through a list-generalized pre-unit `IR.preUnitStack`.

**Verification status:** the complete committed form of every declaration
below — at the real universe scheme, term-mode, `List.rec`-based — has been
compiled against the built `Basic.lean` and is axiom-clean
(`#print axioms IndRec.IR.id = [propext, Quot.sound]`). The reference file
is `docs/../scratchpad/proto_2a_committed.lean` (session scratch; the exact
declarations are reproduced per task below). Each task's implementation step
is transcription of verified code plus its docstring; the residual work is
the tests, docstrings, docs entry, and gates.

**Tech Stack:** Lean 4, mathlib (`WType`, `List`), the project's `IndRec`
and `FreeCoprodCompDisc` developments (branch 1).

## Global Constraints

Copied from `docs/superpowers/specs/2026-07-18-indrec-morphisms-design.md`;
every task's requirements include these.

- Constructive only: no `noncomputable`, no `Classical`; the axiom linter
  (`lake lint`) permits `{propext, Quot.sound}` only for `Geb`/`GebTests`.
  Before reusing any mathlib declaration inside a definition, `#print
  axioms` it and reject any depending on `Classical.choice`. (`id` is
  verified `{propext, Quot.sound}`; `List.foldl_concat`, the one reused
  `List` lemma, is confirmed choice-free.)
- Recursor-only recursion: definitions by recursors — `IR.elim`/`IR.rec`,
  and `List.rec` for the stack helpers (`msigmaPush`, `deltaNav`) and the
  `List` lemmas (`mprecomp_iota`). No `induction`/`induction'` tactic, no
  self-referential `def`, no `termination_by`. `List.foldl` (a standard
  verified combinator, recursion confined to its internals) is used for
  `mprecomp`; its `_snoc` lemma reuses `List.foldl_concat`.
- Explicit proof terms: committed declarations are term-mode, no `by`
  blocks. `cast` and `▸` are terms (not tactics) and are used for the
  equality transports; both satisfy the term-mode rule. Term-level `match`
  (including `| rfl =>`) is permitted.
- Universe discipline: at application sites of this repository's
  declarations, a `.{…}` list is either omitted entirely or written in
  full — partial lists are banned. The house form `ULift.{r}` (second level
  inferred) is the default, BUT it is insufficient inside `deltaNav`'s
  `List.rec` cons case, which requires the two-level `ULift.{max uA uB, uB}`
  and the full `IndRec.IR.precomp.{max uA uB, uB, uI, uO, uB}` (the
  `List.rec` motive under-determines the metavariables the equation compiler
  had inferred). `innerHom`/`Hom` result sort is `Type (max uA uB uI)`; do
  not ascribe `SupObj`'s sort (it is `Type (max (uB + 1) uI)`, inferred). No
  auto-bound `u_1` variables; remove unused `universe`/`variable`.
- Uniform stabilized instantiation: all codes are
  `IR.{max uA uB, uB, uI, uO} I O` (`I : Type uI`, `O : Type uO`). At this
  instantiation `IR.precomp Q i` (for `Q : Type uB`) is an endofunction on
  codes, so `IR.Hom`'s clause-3 recursion stays at the same instantiation.
- mathlib style: 2-space indent, 100-column lines, mandatory docstrings on
  every `def` and every theorem of public interest, naming per mathlib
  (`lowerCamelCase` data, `snake_case` theorems, `UpperCamelCase` types).
  `id`/`_root_.id`: inside `namespace IR`, once `IR.id` exists, an
  argument-position `id` must be written `_root_.id` (as in `preUnitStack`).
- VCS: `jj` only for mutations (raw mutating `git` is hook-blocked); commit
  messages in mathlib conventional form
  (`feat|test|doc|refactor|chore(scope): imperative subject`, no capital,
  no trailing period). No pushes.
- Gates per task: `lake build` and `lake test` pass before each commit.
  Red (verify-failure) steps run `lake test` (bare `lake build` does not
  build `GebTests`). `sorry` only transiently inside a task; never
  committed.
- Module system: `Hom.lean` keeps its `module` header; `public import
  Geb.Mathlib.Data.PFunctor.IndRec.Basic`. `scripts/lint-imports.sh` passes
  (`Geb/Mathlib/` imports only `Mathlib.*`/`Geb.Mathlib.*`; no
  `Geb.Mathlib.` self-prefix outside import lines).

## File structure

- Create `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean` — the homset, the
  injection/navigation helpers, the identity. Header: copyright block,
  `module`, `public import Geb.Mathlib.Data.PFunctor.IndRec.Basic`, the
  module docstring (Task 8), `@[expose] public section` (downstream tests
  rely on definitional reduction, as `Basic` does), then `namespace IndRec`,
  `open CategoryTheory`, `variable (I : Type uI) (O : Type uO)`,
  `namespace IR`. Declaration order is the task order below.
- Create `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean` — the mirrored
  tests.
- Modify `GebTests/Mathlib/Data/PFunctor/IndRec.lean` (the `IndRec` test
  index; confirmed to `import GebTests.Mathlib.Data.PFunctor.IndRec.Basic`)
  — add `import GebTests.Mathlib.Data.PFunctor.IndRec.Hom`.
- Modify `docs/index.md` — add the homset/identity entry under `IndRec`.

Placement note: `Hom.lean` is a sibling importing `Basic`. Relocating the
`Universes`/`Container` sections out of `Basic` (so they could later use
morphisms) is deferred — nothing in this branch needs it, and bundling the
relocation would violate one-concern-per-branch. `IR.Hom.homOfEq` (a
codomain transport) is NOT built here: the identity's transports use `cast`
directly and no declaration in this branch consumes `homOfEq`; it is
deferred to branch 2d (composition), which will consume it.

The declared universe list order is `universe uA uB uI uO` (or the module's
existing `Basic`-consistent order); every declaration below is at
`IR.{max uA uB, uB, uI, uO}`.

---

## Task 1: the homset `IR.Hom`

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec.lean` (add the import)

**Interfaces:**

- Consumes: `IR.iota`/`IR.sigma`/`IR.delta`, `IR.elimAlg`, `IR.precomp`.
- Produces:

  ```lean
  IR.innerHom (o : O) : IR.{max uA uB, uB, uI, uO} I O → Type (max uA uB uI)
  IR.Hom : IR.{max uA uB, uB, uI, uO} I O → IR.{max uA uB, uB, uI, uO} I O
    → Type (max uA uB uI)
  ```

  with the five Definition-8 clauses reducing definitionally.

- [ ] **Step 1: Write the failing test.** Create the test file with the
  house header (copyright block, `module`,
  `public import Geb.Mathlib.Data.PFunctor.IndRec.Hom`, module docstring
  `# Tests for the homset of IR codes` with a one-line summary and
  `## Tags`), then `@[expose] public section`, `open IndRec IndRec.IR`,
  `universe uA uB uI uO`, and the five clause-reduction checks (the
  definitional contract the later constructions depend on):

  ```lean
  example (I : Type uI) (O : Type uO) (o o' : O) :
      IR.Hom.{uA, uB, uI, uO} I O (iota I O o) (iota I O o')
        = ULift.{max uA uB uI} (PLift (o = o')) := rfl

  example (I : Type uI) (O : Type uO) (o : O) (A : Type (max uA uB))
      (K : A → IR.{max uA uB, uB, uI, uO} I O) :
      IR.Hom I O (iota I O o) (sigma I O A K)
        = Σ a, IR.Hom I O (iota I O o) (K a) := rfl

  example (I : Type uI) (O : Type uO) (o : O) (B : Type uB)
      (K : (B → I) → IR.{max uA uB, uB, uI, uO} I O) :
      IR.Hom.{uA, uB, uI, uO} I O (iota I O o) (delta I O B K)
        = Σ e : B → PEmpty.{1}, IR.Hom I O (iota I O o) (K (fun b => (e b).elim))
      := rfl

  example (I : Type uI) (O : Type uO) (A : Type (max uA uB))
      (K : A → IR.{max uA uB, uB, uI, uO} I O) (g' : IR I O) :
      IR.Hom I O (sigma I O A K) g' = ∀ a, IR.Hom I O (K a) g' := rfl

  example (I : Type uI) (O : Type uO) (B : Type uB)
      (K : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (g' : IR I O) :
      IR.Hom I O (delta I O B K) g'
        = ∀ i : B → I, IR.Hom I O (K i) (IR.precomp I O B i g') := rfl
  ```

  Register the test file: add
  `import GebTests.Mathlib.Data.PFunctor.IndRec.Hom` to
  `GebTests/Mathlib/Data/PFunctor/IndRec.lean`.

- [ ] **Step 2: Run to verify failure.** `lake test` — expected: unknown
  identifier `IR.Hom` / `IR.innerHom`.

- [ ] **Step 3: Implement.** In `Hom.lean` (verified committed form):

  ```lean
  /-- The homset from an `ι`-code (Definition 8, clauses 1A–1C of
  [HancockMcBrideGhaniMalatestaAltenkirch2013]), by `IR.elim` on the
  codomain: propositional equality of indices, a dependent sum over the
  `σ`-arity, and an empty-witness sum over the `δ`-arity. -/
  def innerHom (o : O) : IR.{max uA uB, uB, uI, uO} I O → Type (max uA uB uI) :=
    elimAlg I O (Type (max uA uB uI))
      ⟨fun o' => ULift.{max uA uB uI} (PLift (o = o')), fun _ dir => Σ a, dir a,
       fun B dir => Σ e : B → PEmpty.{1}, dir (fun b => (e b).elim)⟩

  /-- The homset of IR codes (Definition 8 of
  [HancockMcBrideGhaniMalatestaAltenkirch2013]), by `IR.elim` on the
  domain code with `IR.innerHom` in the `ι` case: a product over the
  `σ`-arity, and over `δ`-directions a product landing at the precomposed
  codomain (clause 3's `γ'^i`). -/
  def Hom : IR.{max uA uB, uB, uI, uO} I O → IR.{max uA uB, uB, uI, uO} I O
      → Type (max uA uB uI) :=
    elimAlg I O (IR.{max uA uB, uB, uI, uO} I O → Type (max uA uB uI))
      ⟨fun o => innerHom I O o, fun _ dir => fun g' => ∀ a, dir a g',
       fun B dir => fun g' => ∀ i : B → I, dir i (precomp I O B i g')⟩
  ```

- [ ] **Step 4: Verify.** `lake build` then `lake test` — expected: both
  pass; the five clause checks reduce by `rfl`.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add the homset of IR codes (Definition 8)"`

---

## Task 2: `σ`-injection postcomposition `IR.sigmaPush`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`

**Interfaces:**

- Consumes: `IR.Hom`, `IR.rec`, `IR.precomp`.
- Produces:

  ```lean
  IR.sigmaPush : (γ : IR.{max uA uB, uB, uI, uO} I O) →
    ∀ (A' : Type (max uA uB)) (K' : A' → IR I O) (a' : A'),
      Hom I O γ (K' a') → Hom I O γ (sigma I O A' K')
  ```

- [ ] **Step 1: Write the failing test.** A component-level check that the
  `ι`-domain case computes `⟨a', f⟩` (so the test fails if the injection
  targets the wrong summand):

  ```lean
  example :
      sigmaPush PUnit PUnit (iota PUnit PUnit PUnit.unit) Bool
          (fun _ => iota PUnit PUnit PUnit.unit) true
          (⟨PUnit.unit⟩ : IR.Hom PUnit PUnit (iota PUnit PUnit PUnit.unit)
            (iota PUnit PUnit PUnit.unit))
        = ⟨true, ⟨PUnit.unit⟩⟩ := rfl
  ```

  (Adjust the `ι`-hom witness to the elaborated `ULift (PLift …)` form if
  `⟨PUnit.unit⟩` does not flatten; the assertion is that the first
  component is `true`.)

- [ ] **Step 2: Run to verify failure.** `lake test` — expected: unknown
  identifier `IR.sigmaPush`.

- [ ] **Step 3: Implement.** Verified committed form:

  ```lean
  /-- Postcomposition with the `σ`-injection into the `a'`-th summand:
  identity at a `σ`-code is a product of these injections. By `IR.rec` on
  the domain with the target `(A', K', a')` generalized; the `δ`-domain
  case reuses the injection at the superscripted `σ`-code (`precomp_sigma`
  keeps `(σ A' K')^i` a `σ`-code). -/
  def sigmaPush : (γ : IR.{max uA uB, uB, uI, uO} I O) →
        ∀ (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A'),
          Hom I O γ (K' a') → Hom I O γ (sigma I O A' K') :=
    IndRec.IR.rec I O
      (motive := fun γ => ∀ (A' : Type (max uA uB))
          (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A'),
        Hom I O γ (K' a') → Hom I O γ (sigma I O A' K'))
      (fun s _c m => match s with
        | Sum.inl _ => fun _ _ a' f => ⟨a', f⟩
        | Sum.inr (Sum.inl _) => fun A' K' a' f b => m (ULift.up b) A' K' a' (f b)
        | Sum.inr (Sum.inr B) => fun A' K' a' f i =>
            m (ULift.up i) (ULift.{uB} A')
              (fun x => IndRec.IR.precomp I O B i (K' x.down)) (ULift.up a') (f i))
  ```

- [ ] **Step 4: Verify.** `lake build` then `lake test` — expected: pass.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add sigma-injection postcomposition for the homset"`

---

## Task 3: empty-`δ` injection `IR.deltaEmptyPush`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`

**Interfaces:**

- Consumes: `IR.Hom`, `IR.sigmaPush`, `IR.rec`, `IR.precomp`,
  `IR.precompMerge`.
- Produces:

  ```lean
  IR.deltaEmptyPush : (γ : IR.{max uA uB, uB, uI, uO} I O) →
    ∀ (E : Type uB) (e : E → PEmpty.{1}) (M : (E → I) → IR I O),
      Hom I O γ (M (fun x => (e x).elim)) → Hom I O γ (delta I O E M)
  ```

- [ ] **Step 1: Write the failing test.** Inject into a `delta` over
  `PEmpty` (empty witness `id : PEmpty → PEmpty`), from a `Hom` into the
  sole subcode; assert the result inhabits `IR.Hom γ (delta …)` and, where
  feasible, that its `δ`-injection component is the empty witness. Use a
  concrete `γ = iota` so the `ι`-case `⟨e, f⟩` is checkable by `rfl`.

- [ ] **Step 2: Run to verify failure.** `lake test` — expected: unknown
  identifier `IR.deltaEmptyPush`.

- [ ] **Step 3: Implement.** Verified committed form (the classifier lift is
  `ULift.{max uA uB}`, the marker `PUnit.{uB + 1}`; the `cast` is a
  term-mode transport along `precompMerge` at the empty subtype):

  ```lean
  /-- Postcomposition with the `δ`-injection at an empty direction witness
  (`e : E → PEmpty`): by `IR.rec` on the domain with `(E, e, M)`
  generalized; the `δ`-domain case injects, via `sigmaPush`, into the
  all-resolved classifier summand of the precomposed `δ`-code. -/
  def deltaEmptyPush : (γ : IR.{max uA uB, uB, uI, uO} I O) →
        ∀ (E : Type uB) (e : E → PEmpty.{1}) (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O),
          Hom I O γ (M (fun x => (e x).elim)) → Hom I O γ (delta I O E M) :=
    IndRec.IR.rec I O
      (motive := fun γ => ∀ (E : Type uB) (e : E → PEmpty.{1})
          (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O),
        Hom I O γ (M (fun x => (e x).elim)) → Hom I O γ (delta I O E M))
      (fun s c m => match s with
        | Sum.inl _ => fun _ e _ f => ⟨e, f⟩
        | Sum.inr (Sum.inl _) => fun E e M f b => m (ULift.up b) E e M (f b)
        | Sum.inr (Sum.inr B) => fun E e M f i =>
            sigmaPush I O (c (ULift.up i)) (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
              (fun cl => delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
                (fun j => IndRec.IR.precomp I O B i (M (precompMerge I B i cl.down j))))
              (ULift.up (fun x => (e x).elim))
              (m (ULift.up i) {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                (fun z => (e z.1).elim)
                (fun j => IndRec.IR.precomp I O B i
                  (M (precompMerge I B i (fun x => (e x).elim) j)))
                (cast (congrArg
                  (fun a => Hom I O (c (ULift.up i)) (IndRec.IR.precomp I O B i (M a)))
                  (funext (fun x => (e x).elim) :
                    (fun x => (e x).elim) = precompMerge I B i (fun x => (e x).elim)
                          (fun z : {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                            => ((e z.1).elim : PEmpty.{1}).elim)))
                  (f i))))
  ```

- [ ] **Step 4: Verify.** `lake build` then `lake test`; transient
  `#print axioms` confirms no `Classical.choice`.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add empty-delta injection for the homset"`

---

## Task 4: multi-precomposition `IR.mprecomp` and its computation lemmas

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`

**Interfaces:**

- Consumes: `IR.precomp`, `IR.iota`, `IR.mk`, `IR.mk_congr`, `IR.Direction`,
  `List.foldl`, `List.foldl_concat`.
- Produces:

  ```lean
  IR.SupObj (I : Type uI)               -- Σ Q : Type uB, Q → I (sort inferred)
  IR.mprecomp (L : List (SupObj I)) (γ : IR I O) : IR I O
  IR.mprecomp_snoc / IR.mprecomp_iota / IR.mprecomp_iota_mk
  ```

  `SupObj` is a `reducible abbrev`. Its sort is `Type (max (uB + 1) uI)` —
  do NOT ascribe it.

- [ ] **Step 1: Write the failing test.** `mprecomp [] γ = γ` and
  `mprecomp [⟨Q, i⟩] γ = precomp Q i γ` and `mprecomp L (iota o) = iota o`
  on concrete small data (by `rfl` / the lemmas).

- [ ] **Step 2: Run to verify failure.** `lake test` — expected: unknown
  identifier `IR.mprecomp`.

- [ ] **Step 3: Implement.** Verified committed form (the lemmas via
  `List.foldl_concat` and `List.rec`, no `induction`):

  ```lean
  /-- Superscript objects: index types with an `I`-valued assignment
  (`FreeCoprodCompDisc I` at index universe `uB`). -/
  abbrev SupObj (I : Type uI) := Σ Q : Type uB, Q → I

  /-- Iterated precomposition: fold `IR.precomp` over a list of superscript
  objects (`γ ^^ L`). -/
  def mprecomp (L : List (SupObj.{uB, uI} I)) (γ : IR.{max uA uB, uB, uI, uO} I O) :
      IR.{max uA uB, uB, uI, uO} I O :=
    L.foldl (fun g a => IndRec.IR.precomp I O a.1 a.2 g) γ

  /-- `mprecomp` at a right-appended superscript is one outer `precomp`. -/
  theorem mprecomp_snoc (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
      (γ : IR.{max uA uB, uB, uI, uO} I O) :
      mprecomp I O (L ++ [b]) γ = IndRec.IR.precomp I O b.1 b.2 (mprecomp I O L γ) :=
    (List.foldl_concat (fun g a => IndRec.IR.precomp I O a.1 a.2 g) γ b L) ▸ rfl

  /-- `mprecomp` fixes the constant (`iota`) code. -/
  theorem mprecomp_iota (L : List (SupObj.{uB, uI} I)) (o : O) :
      mprecomp I O L (iota I O o) = iota I O o :=
    L.rec (motive := fun L => ∀ o, mprecomp I O L (iota I O o) = iota I O o)
      (fun _ => rfl) (fun _a _L ih o => ih o) o

  /-- `mprecomp` fixes any `mk`-form of an `iota` code. -/
  theorem mprecomp_iota_mk (L : List (SupObj.{uB, uI} I)) (o : O)
      (c : Direction I O (Sum.inl o) → IR.{max uA uB, uB, uI, uO} I O) :
      mprecomp I O L (mk I O (Sum.inl o) c) = iota I O o :=
    (mk_congr I O (Sum.inl o) (funext (fun x => nomatch x)) :
        mk I O (Sum.inl o) c = iota I O o) ▸ mprecomp_iota I O L o
  ```

- [ ] **Step 4: Verify.** `lake build` then `lake test` — expected: pass.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add multi-precomposition and its computation lemmas"`

---

## Task 5: stack `σ`-push `IR.msigmaPush`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`

**Interfaces:**

- Consumes: `IR.Hom`, `IR.mprecomp`, `IR.sigmaPush`, `IR.precomp`.
- Produces:

  ```lean
  IR.msigmaPush (D : IR I O) (A' : Type (max uA uB)) (K' : A' → IR I O)
    (a' : A') (L : List (SupObj I)) :
      Hom I O D (mprecomp L (K' a')) → Hom I O D (mprecomp L (sigma I O A' K'))
  ```

- [ ] **Step 1: Write the failing test.** `msigmaPush … [] f = sigmaPush … f`
  on a concrete sample (by `rfl`; the `List.rec` nil case is `sigmaPush`).

- [ ] **Step 2: Run to verify failure.** `lake test` — expected: unknown
  identifier `IR.msigmaPush`.

- [ ] **Step 3: Implement.** Verified committed form (`List.rec` on `L`,
  motive generalizing `(A', K', a')`):

  ```lean
  /-- Stack `σ`-push: `sigmaPush` under an iterated precomposition. By
  `List.rec` on the stack; the `cons` step peels one `precomp` layer,
  reindexing the target family through `ULift`. -/
  def msigmaPush (D : IR.{max uA uB, uB, uI, uO} I O) (A' : Type (max uA uB))
      (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A') (L : List (SupObj.{uB, uI} I))
      (f : Hom I O D (mprecomp I O L (K' a'))) :
      Hom I O D (mprecomp I O L (sigma I O A' K')) :=
    L.rec (motive := fun L => ∀ (A' : Type (max uA uB))
        (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A'),
        Hom I O D (mprecomp I O L (K' a')) → Hom I O D (mprecomp I O L (sigma I O A' K')))
      (fun A' K' a' f => sigmaPush I O D A' K' a' f)
      (fun c _L ih A' K' a' f =>
        ih (ULift.{uB} A') (fun x => IndRec.IR.precomp I O c.1 c.2 (K' x.down))
          (ULift.up a') f)
      A' K' a' f
  ```

- [ ] **Step 4: Verify.** `lake build` then `lake test` — expected: pass.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add stack sigma-push for the homset"`

---

## Task 6: navigation `IR.deltaNavBase` and `IR.deltaNav`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`

**Interfaces:**

- Consumes: `IR.Hom`, `IR.sigmaPush`, `IR.deltaEmptyPush`, `IR.msigmaPush`,
  `IR.mprecomp`, `IR.mprecomp_snoc`, `IR.precomp`, `IR.precompMerge`.
- Produces:

  ```lean
  IR.deltaNavBase (D) (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (K : (Bin → I) → IR I O) (g : Bin → Bout) :
    Hom I O D (precomp Bout iout (K (iout ∘ g)))
      → Hom I O D (precomp Bout iout (delta I O Bin K))
  IR.deltaNav (D) (Bout : Type uB) (iout : Bout → I) (Bin : Type uB)
    (K : (Bin → I) → IR I O) (g : Bin → Bout) (L : List (SupObj I)) :
    Hom I O D (mprecomp (L ++ [⟨Bout, iout⟩]) (K (iout ∘ g)))
      → Hom I O D (mprecomp (L ++ [⟨Bout, iout⟩]) (delta I O Bin K))
  ```

  The factorization parameter `g : Bin → Bout` tracks how a peeled
  classifier subtype resolves against the outer superscript. `deltaNav`'s
  nil case transports through `mprecomp_snoc`; its cons case needs the
  two-level `ULift.{max uA uB, uB}` and full `precomp.{…}` pins (Global
  Constraints).

- [ ] **Step 1: Write the failing test.** `deltaNav … [] f = deltaNavBase …`
  transported — assert on a concrete sample that `deltaNav`'s nil case
  agrees with `deltaNavBase` (up to the `mprecomp_snoc` transport). A
  typecheck-only sample plus a `deltaNavBase` component check.

- [ ] **Step 2: Run to verify failure.** `lake test` — expected: unknown
  identifier `IR.deltaNav` / `IR.deltaNavBase`.

- [ ] **Step 3: Implement.** Verified committed form:

  ```lean
  /-- The base navigation: inject a `Hom` into `precomp Bout iout (K …)`
  up to `precomp Bout iout (delta Bin K)`, via the all-resolved classifier
  (`Sum.inl ∘ g`) whose unresolved subtype is empty. -/
  def deltaNavBase (D : IR.{max uA uB, uB, uI, uO} I O) (Bout : Type uB) (iout : Bout → I)
      (Bin : Type uB) (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
      (f : Hom I O D (IndRec.IR.precomp I O Bout iout (K (iout ∘ g)))) :
      Hom I O D (IndRec.IR.precomp I O Bout iout (delta I O Bin K)) :=
    sigmaPush I O D (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
      (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
        (fun j => IndRec.IR.precomp I O Bout iout (K (precompMerge I Bout iout cl.down j))))
      (ULift.up (fun b => Sum.inl (g b)))
      (deltaEmptyPush I O D {z : Bin // (fun b => Sum.inl (g b)) z = Sum.inr PUnit.unit}
        (fun z => nomatch z.2)
        (fun j => IndRec.IR.precomp I O Bout iout
          (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
        (cast (congrArg (fun a => Hom I O D (IndRec.IR.precomp I O Bout iout (K a)))
          (funext (fun _b => rfl) :
            (iout ∘ g) = precompMerge I Bout iout (fun b => Sum.inl (g b))
                  (fun z : {z : Bin // (fun b => Sum.inl (g b)) z = Sum.inr PUnit.unit}
                    => (nomatch z.2 : I)))) f))

  /-- The navigation up an iterated-precomposition tower: at each stack
  layer, inject through the all-unresolved classifier (`msigmaPush`),
  bottoming out at `deltaNavBase`. By `List.rec` on the stack. -/
  def deltaNav (D : IR.{max uA uB, uB, uI, uO} I O) (Bout : Type uB) (iout : Bout → I)
      (Bin : Type uB) (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
      (L : List (SupObj.{uB, uI} I))
      (f : Hom I O D
        (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)))) :
      Hom I O D (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O Bin K)) :=
    L.rec (motive := fun L => ∀ (Bin : Type uB)
        (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout),
        Hom I O D (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g))) →
        Hom I O D (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O Bin K)))
      (fun Bin K g f =>
        (mprecomp_snoc I O [] (⟨Bout, iout⟩ : SupObj.{uB, uI} I) (delta I O Bin K)).symm ▸
          deltaNavBase I O D Bout iout Bin K g
            (mprecomp_snoc I O [] (⟨Bout, iout⟩ : SupObj.{uB, uI} I) (K (iout ∘ g)) ▸ f))
      (fun a _L ih Bin K g f =>
        msigmaPush I O D (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
          (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
            (fun m => IndRec.IR.precomp.{max uA uB, uB, uI, uO, uB} I O a.1 a.2
              (K (precompMerge I a.1 a.2 cl.down m))))
          (ULift.up (fun _ => Sum.inr PUnit.unit))
          (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
          (ih {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z
                = Sum.inr PUnit.unit}
            (fun m => IndRec.IR.precomp.{max uA uB, uB, uI, uO, uB} I O a.1 a.2
              (K (precompMerge I a.1 a.2 (fun _ => Sum.inr PUnit.unit) m)))
            (fun z => g z.1) f))
      Bin K g f
  ```

- [ ] **Step 4: Verify.** `lake build` then `lake test`; transient
  `#print axioms` confirms `{propext, Quot.sound}`.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add delta-tower navigation for the identity"`

---

## Task 7: the pre-unit `IR.preUnitStack` and the identity `IR.id`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean`

**Interfaces:**

- Consumes: `IR.Hom`, `IR.innerHom`, `IR.msigmaPush`, `IR.deltaNav`,
  `IR.mprecomp`, `IR.mprecomp_snoc`, `IR.mprecomp_iota_mk`, `IR.rec`,
  `IR.mk`.
- Produces:

  ```lean
  IR.preUnitStack : (γ : IR I O) → ∀ (L : List (SupObj I)), Hom I O γ (mprecomp L γ)
  IR.id (γ : IR I O) : Hom I O γ γ
  ```

- [ ] **Step 1: Write the failing test.** `IR.id` at each constructor, plus
  a value-level check at `ι` (the identity witness is
  `ULift.up (PLift.up rfl)`):

  ```lean
  example (I : Type uI) (O : Type uO) (o : O) :
      IR.id.{uA, uB, uI, uO} I O (iota I O o)
        = (ULift.up (PLift.up rfl) : IR.Hom I O (iota I O o) (iota I O o)) := rfl
  example (I : Type uI) (O : Type uO) (A : Type (max uA uB))
      (K : A → IR.{max uA uB, uB, uI, uO} I O) :
      IR.Hom I O (sigma I O A K) (sigma I O A K) := IR.id I O (sigma I O A K)
  example (I : Type uI) (O : Type uO) (B : Type uB)
      (K : (B → I) → IR.{max uA uB, uB, uI, uO} I O) :
      IR.Hom I O (delta I O B K) (delta I O B K) := IR.id I O (delta I O B K)
  ```

- [ ] **Step 2: Run to verify failure.** `lake test` — expected: unknown
  identifier `IR.preUnitStack` / `IR.id`.

- [ ] **Step 3: Implement.** Verified committed form:

  ```lean
  /-- The list-generalized pre-unit `Hom γ (γ ^^ L)`: by `IR.rec` on `γ`
  with the stack `L` generalized. The `δ`-case appends the mapped direction
  to `L`, so the subcode induction hypothesis lands at the precomposition
  depth clause 3 demands, and `deltaNav` navigates the superscripted
  `δ`-tower. -/
  def preUnitStack : (γ : IR.{max uA uB, uB, uI, uO} I O) →
        ∀ (L : List (SupObj.{uB, uI} I)), Hom I O γ (mprecomp I O L γ) :=
    IndRec.IR.rec I O (motive := fun γ => ∀ L, Hom I O γ (mprecomp I O L γ))
      (fun s c m => match s with
        | Sum.inl o => fun L =>
            cast (congrArg (innerHom.{uA, uB, uI, uO} I O o) (mprecomp_iota_mk I O L o c).symm)
              (ULift.up (PLift.up rfl) : innerHom.{uA, uB, uI, uO} I O o (iota I O o))
        | Sum.inr (Sum.inl A) => fun L a =>
            msigmaPush I O (c (ULift.up a)) A (fun a' => c (ULift.up a')) a L (m (ULift.up a) L)
        | Sum.inr (Sum.inr B) => fun L i =>
            cast (congrArg (Hom I O (c (ULift.up i)))
                   (mprecomp_snoc I O L ⟨B, i⟩ (mk I O (Sum.inr (Sum.inr B)) c)))
              (deltaNav I O (c (ULift.up i)) B i B (fun i' => c (ULift.up i')) _root_.id L
                (m (ULift.up i) (L ++ [⟨B, i⟩]))))

  /-- The identity morphism of an IR code (the paper gives no explicit
  identity; this is a construction), as the pre-unit at the empty stack. -/
  def id (γ : IR.{max uA uB, uB, uI, uO} I O) : Hom I O γ γ := preUnitStack I O γ []
  ```

- [ ] **Step 4: Verify.** `lake build` then `lake test`. Add a permanent
  axiom-boundary check in the test file consistent with the repo pattern (a
  named `def`/`example` the `GebMeta` linter inspects — e.g. a term built
  from `IR.id`), and run `lake lint` — expected: exit 0 and `IR.id` depends
  only on `{propext, Quot.sound}`.

- [ ] **Step 5: Commit.**
  `jj commit -m "feat(indrec): add the identity morphism of IR codes"`

---

## Task 8: documentation and gates

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/IndRec/Hom.lean` (module docstring)
- Modify: `docs/index.md`
- Modify: `GebTests/Mathlib/Data/PFunctor/IndRec/Hom.lean` (test docstring)

- [ ] **Step 1: Module docstring.** Complete `Hom.lean`'s `/-! … -/`:
  `# The homset of IR codes`, a summary; `## Main definitions`
  (`IR.innerHom`, `IR.Hom`, `IR.sigmaPush`, `IR.deltaEmptyPush`,
  `IR.mprecomp`, `IR.msigmaPush`, `IR.deltaNavBase`, `IR.deltaNav`,
  `IR.preUnitStack`, `IR.id`); `## Main statements` (`IR.mprecomp_snoc`,
  `IR.mprecomp_iota`, `IR.mprecomp_iota_mk`); `## Implementation notes`
  (the uniform stabilized instantiation and why `precomp` is an endo there;
  the list-generalized pre-unit and `deltaNav`'s factorization parameter;
  `mprecomp` folds `precomp` over a list, its lemmas through `List.rec`);
  `## References` (`[HancockMcBrideGhaniMalatestaAltenkirch2013]`, citing
  Definition 8 for `IR.Hom`; note the identity is a construction — the paper
  gives no explicit identity); `## Tags`
  (`inductive-recursive, morphism, homset, category`). Docstrings
  distinguish transcription (the homset clauses) from construction (the
  identity and the injection/navigation helpers, which carry no citation).

- [ ] **Step 2: `docs/index.md` entry.** Add the homset/identity under
  `IndRec`, in topological order after the interpretation and
  precomposition entries.

- [ ] **Step 3: Full gate run.** `scripts/pre-push.sh` (or `lake build &&
  lake test && lake lint && scripts/lint-imports.sh && markdownlint-cli2
  'docs/index.md'`) — expected: exit 0, axioms clean, imports clean,
  TOC/markdown clean.

- [ ] **Step 4: Commit.**
  `jj commit -m "doc(indrec): document the homset and identity of IR codes"`

---

## Deviations and stop conditions

- The complete committed form of Tasks 1–7 is verified to compile at the
  real universe scheme (term-mode, `List.rec`-based, axioms
  `{propext, Quot.sound}`); the reference is
  `scratchpad/proto_2a_committed.lean`. Implementation is transcription plus
  docstrings; if any declaration does not compile as written, the fault is
  in transcription (an omitted universe pin, a dropped `SupObj.{uB, uI}`
  annotation, or a bare `id` for `_root_.id`) — restore the reference form
  rather than altering the construction.
- `deltaNav`'s cons case genuinely requires the two-level
  `ULift.{max uA uB, uB}` and the full
  `IndRec.IR.precomp.{max uA uB, uB, uI, uO, uB}` (the `List.rec` motive
  under-determines the metavariables that the equation compiler inferred);
  the single-level `ULift.{r}` house form fails there.
- `cast`/`▸` are terms; no committed `by` block is needed anywhere in this
  branch. If a test's `rfl` does not reduce, pin the declaration's `.{…}`
  list and the `ULift`/`PLift` witnesses fully before weakening the test.
- If `IR.id`'s axiom check shows any dependency beyond
  `{propext, Quot.sound}`, stop and locate the reused declaration that
  introduced it; replace it with a choice-free equivalent before committing.
  (`List.foldl_concat` is the only reused `List` lemma and is choice-free.)
- The identity is a self-contained deliverable; composition, the category
  laws, and `IR.Hom.homOfEq` are branch 2d and out of scope here.
