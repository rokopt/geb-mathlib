# Presheaf (PRA) W-types Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the W-types (initial algebras, existence half) of presheaf
parametric-right-adjoint functors as a subtype of the slice W-types, completing
roadmap item 2.

**Architecture:** Layer `PresheafPFunctor.W` on `SlicePFunctor.W` as
`PresheafPFunctor.obj` layers on `SlicePFunctor.Obj`: the carrier is a
hereditary-naturality subtype of the slice W-type, fibred by `windex`, lifted
to the functor's value universe `uW = max uI uA uB`; presheaf restriction is the
root-only tree image of the generalized `objRestrElt`; the recursion lives in
the hereditary-naturality predicate, defined and reasoned about through a
slice-W recursor added for the purpose.

**Tech Stack:** Lean 4, mathlib (`WType`, `PFunctor`, `CategoryTheory`
presheaves), `lake`. `jj` for version control.

## Global Constraints

Copied from the spec (`docs/superpowers/specs/2026-07-05-presheaf-w-types-design.md`);
every task's requirements include these.

- **Recursor-only.** No `induction` / `induction'` tactics, no self-calling
  `def`, no self-referential datatype. All recursion via `WType.rec` /
  `WType.elim` or the slice-W recursors added here; `cases` / `match` only for
  non-recursive case analysis.
- **Constructive.** No `noncomputable`. Core files target axioms
  `{propext, Quot.sound}`; only the categorical-wrapper surface already on
  `GebMeta.classicalAllowedModules` may use `Classical.choice`. `Presheaf/W.lean`
  is a core file (not on that list) and must stay `{propext, Quot.sound}`.
- **Universes.** The presheaf W-type value universe is `uW = max uI uA uB`; the
  carrier fibre is `ULift.{uI}` of the `Type (max uA uB)` tree subtype.
- **Naming.** Uniform with existing code: `windex*`, `objRestr*`,
  `directionRestr`, `shapeRestr`; no bare `restr`; `Is`-prefixed Prop
  predicates (`IsHereditarilyNatural`).
- **Module system.** Every `.lean` file: copyright block, `module`,
  `public import` for re-exported deps, `public section`, `@[expose]` on
  definitions the wrapper/tests unfold across the module boundary.
- **Style/docs.** mathlib style (2-space indent, ≤100-char lines, Unicode
  notation, `autoImplicit false`); mandatory module docstring (with required
  sections) and declaration docstrings; `@[ext]` on structures; universe
  pinning to avoid auto-bound `u_N`.
- **Verification per Lean task:** `lake build <module>` clean, the test mirror
  builds, `lake lint` clean (axiom + import linters), no `sorry`/`admit`/`_`
  in committed code. Use `lean4:review` before each commit; `lean4:autoprove` /
  `lean4:sorry-filler-deep` and the `lean-lsp` MCP for proving.
- **VCS.** `jj` only (never raw mutating `git`). Conventional-commit messages
  (`feat|fix|doc|style|refactor|test|chore|perf|ci`, imperative, no capital, no
  period). No `jj git push` (local commits only; user reviews before any push).

---

## File structure

- `docs/rules/lean-coding.md` — Part A policy text (Task 1, on `doc/` branch).
- `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean` — Part C: generalize
  `objRestrElt` (+ its two laws) over the projection `p` (Task 3).
- `Geb/Mathlib/Data/PFunctor/Slice/W.lean` — Part B: add the slice-W recursors
  `W.ind` and `W.recProp` (Task 4).
- `Geb/Mathlib/Data/PFunctor/Presheaf/W.lean` — Part D: the construction
  (Tasks 5–8).
- `GebTests/Mathlib/Data/PFunctor/Presheaf/W.lean` — test mirror (Tasks 5–8).
- `GebTests/Mathlib/Data/PFunctor/{Slice/W,Presheaf/Basic}.lean` — extend for
  Tasks 3–4.
- `Geb/Mathlib/Data/PFunctor/Presheaf.lean` — index: add `.W` (Task 9).
- `docs/index.md`, `TODO.md` — documentation and roadmap (Task 9).

---

## Task 1: Part A — recursor-discipline policy on its own branch

**Files:**

- Modify: `docs/rules/lean-coding.md` (new subsection under *Coding technique*)

**Interfaces:**

- Produces: the committed policy on branch `doc/recursor-discipline`, off `main`,
  which `feat/presheaf-w-types` is then stacked on.

- [ ] **Step 1: Create the doc branch off `main`.**

```bash
jj new main -m "doc(lean): require recursion through recursors

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark create doc/recursor-discipline -r @
```

- [ ] **Step 2: Add the subsection** to `docs/rules/lean-coding.md`, placed in
  the *Coding technique* section (e.g. after *Higher-order constructions*),
  with this exact text:

```markdown
### Recursion and induction through recursors

All recursion and induction is expressed through recursors — functions
taking non-recursive step functions as arguments, confining the recursion
to their own verified internals. This covers mathlib's recursors
(`WType.elim`, `WType.rec`), Lean's auto-generated ones (`casesOn`, `rec`,
`brecOn`), and recursors defined here by wrapping those (e.g. an induction
principle on a W-type subtype). Consequently:

- No `induction` / `induction'` tactics; drive a proof's recursion with an
  explicit recursor application, reserving `cases` / `casesOn` for
  non-recursive case analysis.
- No `def` that calls itself; no `termination_by` / well-founded
  self-recursion.
- No `structure` or `inductive` that contains an instance of itself.
  Self-reference is expressed as a W-type of the appropriate form
  (mathlib's `WType`, or the slice or presheaf W-types built here), so the
  recursion is carried by that type's recursor.

The purpose is to keep every datatype and every recursion expressed as a
polynomial functor and its recursor. So presented, a datatype participates
in the category of polynomial functors: it composes with the standard
combinators, it can be assembled à la carte, and every morphism between two
such datatypes takes one uniform form — a natural transformation of
polynomial functors. Explicit recursion forfeits this: a self-referential
datatype sits outside the framework, cannot reuse the shared combinators,
and forces bespoke, hand-written maps out of it. Keeping definitions
`noncomputable`-free (§ Constructive-only Lean code) is then a corollary,
since `WType.elim` folds are code-generatable.
```

- [ ] **Step 3: Update the TOC and lint.**

Run: `doctoc --update-only docs/rules/lean-coding.md && markdownlint-cli2 docs/rules/lean-coding.md`
Expected: `Summary: 0 error(s)`

- [ ] **Step 4: Commit and stack the feature branch on top.**

```bash
jj describe -m "doc(lean): require recursion through recursors

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
# Restack the existing spec commit (feat/presheaf-w-types) onto the doc branch:
jj rebase -s feat/presheaf-w-types -d doc/recursor-discipline
```

Expected: `feat/presheaf-w-types` now descends from `doc/recursor-discipline`;
`jj log` shows main ◀ doc/recursor-discipline ◀ feat/presheaf-w-types.

---

## Task 2: Commit the plan on the feature branch

**Files:**

- Create: `docs/superpowers/plans/2026-07-05-presheaf-w-types.md` (this file)

- [ ] **Step 1: Ensure the plan file is present** (it is this document).

- [ ] **Step 2: Lint.**

Run: `markdownlint-cli2 docs/superpowers/plans/2026-07-05-presheaf-w-types.md`
Expected: `Summary: 0 error(s)`

- [ ] **Step 3: Commit on the feature branch, after the spec.**

```bash
jj new feat/presheaf-w-types -m "doc(poly): add presheaf W-types implementation plan

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

---

## Task 3: Part C — generalize `objRestrElt` over the projection

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean` (`objRestrElt` :404,
  `objRestrElt_id` :474, `objRestrElt_comp` :496; add universe `uX`)
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`

**Interfaces:**

- Produces (new generalized signatures; namespace `PresheafPFunctor`):

```lean
@[expose] def objRestrElt {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {X : Type uX} {p : X → I}
    ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : F.toSliceDomPFunctor.Obj p) (hq : F.q x.1.1 = j) :
    F.toSliceDomPFunctor.Obj p
-- objRestrElt_id  : F.objRestrElt (𝟙 j) x hq = x
-- objRestrElt_comp: F.objRestrElt (h ≫ g) x hq = F.objRestrElt h (F.objRestrElt g x hq) hq'
```

- Consumes: nothing new (this is a refactor of existing decls). Existing callers
  (`objRestr` :428, `objPresheaf.map` :532) keep working because `p` is inferred
  from `x` (they pass `x : ...Obj (elemProj Z)`, so `p := elemProj Z`).

- [ ] **Step 1: Add `uX` to the file's `universe` line** (`Presheaf/Basic.lean:138`):
  append `uX` to `universe uI uJ uA uB uZ u v vI vJ`.

- [ ] **Step 2: Generalize `objRestrElt`.** Replace `{Z : Iᵒᵖ ⥤ Type uZ}` and the
  argument `(x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z))`
  with `{X : Type uX} {p : X → I}` and `(x : F.toSliceDomPFunctor.Obj p)`, and the
  return type from `...Obj (elemProj Z)` to `...Obj p`. The body is unchanged (it
  references only `x.1.1`, `x.1.2`, `F.shapeRestr`, `F.reindex`, `F.rCurried`,
  `F.compatible_iff` — never `Z`). Update its docstring to say "for a projection
  `p : X → I`" instead of naming `Z`.

- [ ] **Step 3: Build; confirm the generalization type-checks and callers
  still resolve.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.Basic`
Expected: no errors (in particular `objRestr` and `objPresheaf` still compile,
`p` inferred as `elemProj Z` at their call sites).

- [ ] **Step 4: Generalize `objRestrElt_id` and `objRestrElt_comp`** the same way
  (`{Z}` → `{X} {p}`, `elemProj Z` → `p` in the `x` argument type). Their proofs
  use only `shapeRestr_id`/`shapeRestr_comp`, `reindex_id`/`reindex_comp`,
  `cast_val_heq`, `heq_fun`, `reindex_val_heq` — none `Z`-specific — so the proof
  bodies are unchanged.

- [ ] **Step 5: Build.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.Basic`
Expected: clean.

- [ ] **Step 6: Add a test** instantiating the generalization at a non-`elemProj`
  projection, to `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`:

```lean
-- `objRestrElt` generalizes over the projection: it applies at any `p : X → I`,
-- not only `elemProj Z`. Here `p` is a constant map on `PUnit`.
example (g : (0 : Fin 2) ⟶ 1)
    (x : presheafWitness.toSliceDomPFunctor.Obj (fun _ : PUnit => (1 : Fin 2)))
    (hq : presheafWitness.q x.1.1 = 1) :
    presheafWitness.toSliceDomPFunctor.Obj (fun _ : PUnit => (1 : Fin 2)) :=
  presheafWitness.objRestrElt g x hq
```

- [ ] **Step 7: Build the test mirror.**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Presheaf.Basic`
Expected: clean.

- [ ] **Step 8: Lint, review, commit.**

Run: `lake lint` (expect clean; `Presheaf/Basic.lean` stays choice-free) and
`bash scripts/lint-imports.sh`. Then `lean4:review` the diff.

```bash
jj new -m "refactor(poly): generalize objRestrElt over its projection

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

---

## Task 4: Part B — slice-W recursors (`W.ind`, `W.recProp`)

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/W.lean` (add to `namespace SlicePFunctor.W`)
- Test: `GebTests/Mathlib/Data/PFunctor/Slice/W.lean`

**Interfaces:**

- Produces (namespace `SlicePFunctor.W`; `F : SlicePFunctor.{uA,uB,uI,uI} I I`):

```lean
-- Structural induction principle (Prop motive).
theorem ind {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    {motive : F.W → Prop}
    (mk : ∀ (x : F.toSliceDomPFunctor.Obj F.windex),
            (∀ b, motive (x.1.2 b)) → motive (W.mk x)) :
    ∀ z, motive z

-- Paramorphism into Prop: defines a predicate whose step sees the node `x`
-- (hence the child subtrees `x.1.2 b : F.W`) and the children's predicate
-- values. `@[expose]` so the presheaf layer can unfold it.
@[expose] def recProp {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (step : (x : F.toSliceDomPFunctor.Obj F.windex) → (∀ b, Prop) → Prop) :
    F.W → Prop

-- Computation rule for recProp (definitional; stated for downstream unfolding).
theorem recProp_mk {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (step : (x : F.toSliceDomPFunctor.Obj F.windex) → (∀ b, Prop) → Prop)
    (x : F.toSliceDomPFunctor.Obj F.windex) :
    W.recProp step (W.mk x) = step x (fun b => W.recProp step (x.1.2 b))
```

- Consumes: existing `W.mk`, `W.dest`, `mk_dest`, `wValid_mk`, `WValid`,
  `windexRoot`, `windexValid`.

- [ ] **Step 1: Add `W.ind`.** Strategy (mirrors the `WType.rec` usage in
  `elimData_valid` :318–325): destructure `z = ⟨w, hw⟩`, then apply `WType.rec`
  with motive `fun w => ∀ (hw : F.WValid w), motive ⟨w, hw⟩`; in the step
  `fun a f ih hw'`, rewrite `⟨WType.mk a f, hw'⟩ = W.mk (dest ⟨WType.mk a f, hw'⟩)`
  via `mk_dest`, extract each child's validity from `hw'` through `wValid_mk`, and
  apply the hypothesis `mk`. No `induction` tactic. Insert `_` for the goal first
  and build to read it.

- [ ] **Step 2: Build; iterate the proof to no goals.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Slice.W`
Expected: clean, no `sorry`/`_`. (Use `lean4:autoprove` if the recursor
plumbing stalls.)

- [ ] **Step 3: Add `W.recProp`.** Strategy (Prop-valued, so `WType.rec` in a
  `def` is admissible here — the value is erased; the round-2 review confirmed a
  `Prop`-motive `WType.rec` `def` compiles with no `noncomputable` and no extra
  axioms): define
  `fun z => WType.rec (motive := fun w => F.WValid w → Prop)
    (fun a f ih hv => step (dest ⟨WType.mk a f, hv⟩)
       (fun b => ih b (((F.wValid_mk a f).mp hv).1 b))) z.1 z.2`.
  Here `dest ⟨WType.mk a f, hv⟩ : Obj windex` supplies the node with valid
  children, and `ih b _ : Prop` is the child's predicate value.

- [ ] **Step 4: Add `recProp_mk`.** It should hold by `rfl` (or `by cases … ; rfl`
  destructing `x` to `⟨⟨a, v⟩, hc⟩`); this is the one-level computation rule the
  presheaf layer's unfolding lemma builds on. Build to confirm.

Run: `lake build Geb.Mathlib.Data.PFunctor.Slice.W`
Expected: clean.

- [ ] **Step 5: Extend the module docstring** (`## Main definitions` /
  `## Main statements`) to list `W.ind`, `W.recProp`, `recProp_mk`, describing
  `ind` as the wrapped structural induction principle and `recProp` as the
  subtree-exposing paramorphism into `Prop`.

- [ ] **Step 6: Add tests** to `GebTests/Mathlib/Data/PFunctor/Slice/W.lean`,
  reusing that file's existing slice-W fixture (call it `sliceWitness` — use the
  actual name defined there). Test that `recProp` unfolds by `recProp_mk`, and
  that `ind` proves a trivial motive:

```lean
-- recProp computes one level by recProp_mk.
example (x : sliceWitness.toSliceDomPFunctor.Obj sliceWitness.windex) :
    SlicePFunctor.W.recProp (fun _ _ => True) (SlicePFunctor.W.mk x) = True :=
  SlicePFunctor.W.recProp_mk _ x
-- ind discharges the always-true motive.
example (z : sliceWitness.W) : True :=
  SlicePFunctor.W.ind (motive := fun _ => True) (fun _ _ => trivial) z
```

- [ ] **Step 7: Build tests.**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.W`
Expected: clean.

- [ ] **Step 8: Lint (axioms!), review, commit.**

Run: `lake lint` — confirm `Slice/W.lean` still depends only on
`{propext, Quot.sound}` (verify with
`lake env lean` is forbidden; instead rely on `lake lint`'s
`GebMeta.detectNonstandardAxiom` and, if needed, `#print axioms
SlicePFunctor.W.recProp` in a scratch buffer via `lean-lsp`). Then `lean4:review`.

```bash
jj new -m "feat(poly): add structural recursors for slice W-types

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

---

## Task 5: Part D — `Presheaf/W.lean` scaffold and `IsHereditarilyNatural`

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Presheaf/W.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/Presheaf/W.lean`

**Interfaces:**

- Produces (namespace `PresheafPFunctor`;
  `F : PresheafPFunctor.{uI,uI,uA,uB,vI,vI} I I`;
  `SliceW := F.toSlicePFunctor.W`):

```lean
-- Root-only tree restriction: objRestrElt at p := windex, conjugated by dest/mk.
@[expose] def wRestrTree {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    F.toSlicePFunctor.W
-- (name: tree-level restriction; not a bare `restr`. Underlying it is the
--  generalized `objRestrElt` at `p := F.toSlicePFunctor.windex`.)

-- Tree-level IsNatural: the local naturality equation at every node.
@[expose] def IsHereditarilyNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) : F.toSlicePFunctor.W → Prop

-- One-level unfolding (from recProp_mk).
theorem isHereditarilyNatural_mk … :
    F.IsHereditarilyNatural (SlicePFunctor.W.mk x) ↔
      («local naturality of x») ∧ ∀ b, F.IsHereditarilyNatural (x.1.2 b)
```

- Consumes: Task 3's generalized `objRestrElt`; Task 4's `W.recProp` /
  `recProp_mk`; slice `W.mk`/`W.dest`/`windex`; `directionRestr`/`reindex`.

- [ ] **Step 1: Create the file header, `module`, imports, `public section`,
  module docstring.** Imports: `public import Geb.Mathlib.Data.PFunctor.Slice.W`
  and `public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic`. Copyright block
  and `Authors: The geb-mathlib contributors`. Write the module docstring with
  `# Title`, summary, `## Main definitions`, `## Main statements`,
  `## Implementation notes` (record the `I = J`/`uW` universe handling and the
  recursor discipline), `## References` ([Weber2007], [GambinoHyland2004],
  [GambinoKock2013], [AltenkirchGhaniHancockMcBrideMorris2015]), `## Tags`.
  Declare `universe uI uA uB uY vI` and `open CategoryTheory`.

- [ ] **Step 2: Define `wRestrTree`.** It is `objRestrElt` (generalized, at
  `p := F.toSlicePFunctor.windex`) conjugated by the slice `dest`/`mk`: `dest z`
  gives `x : Obj windex`; apply `F.objRestrElt g x hq'` (with `hq'` the head/`q`
  witness); `W.mk` the result. Insert `_` for the head-index witness plumbing and
  build to read the exact obligation, then discharge it (`windex`/`windexRoot`
  definitional unfolding — mirror `objRestr` :428).

- [ ] **Step 3: Build.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 4: Define `IsHereditarilyNatural`** via `SlicePFunctor.W.recProp`:

```lean
@[expose] def IsHereditarilyNatural (F) : F.toSlicePFunctor.W → Prop :=
  SlicePFunctor.W.recProp (fun x ih =>
    (∀ ⦃i i' : I⦄ (g : i' ⟶ i) (b : F.toSliceDomPFunctor.Direction x.1.1 i),
        x.1.2 (F.directionRestr x.1.1 g b).1
          = F.wRestrTree g (x.1.2 b) «index witness for the child») ∧ ∀ b, ih b)
```

The local-naturality conjunct is the tree analogue of `IsNatural` (`Basic.lean`
:194): the child at the reindexed direction equals the child restricted along
`g`. Insert `_` for the child index witness and read/discharge it from
compatibility of `x` (`compatible_iff`), mirroring how `value` :184 obtains its
index equality.

- [ ] **Step 5: Add `isHereditarilyNatural_mk`.** It follows from
  `SlicePFunctor.W.recProp_mk` (rewrite, then `Iff.rfl`). Build.

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 6: Create the test mirror scaffold** with the header/imports; import
  `Geb.Mathlib.Data.PFunctor.Presheaf.W` and reuse `presheafWitness :
  PresheafPFunctor (Fin 2) (Fin 2)` from the Presheaf/Basic test file (import it,
  or redefine the minimal fixture). Add a test that `IsHereditarilyNatural`
  unfolds:

```lean
example (x : presheafWitness.toSliceDomPFunctor.Obj presheafWitness.toSlicePFunctor.windex) :
    presheafWitness.IsHereditarilyNatural (SlicePFunctor.W.mk x) ↔
      («the unfolded conjunction») :=
  presheafWitness.isHereditarilyNatural_mk x
```

- [ ] **Step 7: Build test mirror.**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 8: Lint (axioms must be `{propext, Quot.sound}`), review, commit.**

```bash
jj new -m "feat(poly): add presheaf W-type hereditary-naturality predicate

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

---

## Task 6: Part D — the carrier presheaf `W` with restriction and functor laws

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/W.lean`
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/W.lean`

**Interfaces:**

- Produces:

```lean
-- Restriction preserves IsHereditarilyNatural and the index; on the ULifted
-- subtype it is the presheaf's map.
@[expose] def wRestr {I} [Category.{vI} I] (F : PresheafPFunctor … I I)
    ⦃j j' : I⦄ (g : j' ⟶ j) :
    ULift.{uI} { w : F.toSlicePFunctor.W //
        F.toSlicePFunctor.windex w = j ∧ F.IsHereditarilyNatural w } →
      ULift.{uI} { w : F.toSlicePFunctor.W //
        F.toSlicePFunctor.windex w = j' ∧ F.IsHereditarilyNatural w }

-- The carrier presheaf.
@[expose] def W {I} [Category.{vI} I] (F : PresheafPFunctor … I I) :
    Iᵒᵖ ⥤ Type (max uI uA uB) where
  obj j := ULift.{uI} { w : F.toSlicePFunctor.W //
    F.toSlicePFunctor.windex w = j.unop ∧ F.IsHereditarilyNatural w }
  map g := F.wRestr g.unop
  map_id := …   -- from objRestrElt_id
  map_comp := … -- from objRestrElt_comp
```

- Consumes: Task 5's `wRestrTree`, `IsHereditarilyNatural`,
  `isHereditarilyNatural_mk`; Task 3's `objRestrElt_id`/`objRestrElt_comp`.

- [ ] **Step 1: Define `wRestr`.** Unwrap `ULift`, apply `wRestrTree` to the
  underlying tree, and supply two preservation proofs: (a) the index becomes `j'`
  (`shapeRestr` sends a `Shape j` to a `Shape j'`, so the new root `q` is `j'` —
  mirror `objPresheaf.map` :532's index handling); (b) `IsHereditarilyNatural` is
  preserved by `wRestrTree` (a one-level fact: restriction rewires the root and
  leaves subtrees, so `isHereditarilyNatural_mk` reduces it to the original's
  hereditary naturality plus the rewired local condition — prove via
  `isHereditarilyNatural_mk` and `reindex_naturality`). Re-wrap in `ULift.up`.

- [ ] **Step 2: Build.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 3: Define `W`** as the `Functor` value above. `map_id` / `map_comp`
  transport from `objRestrElt_id` / `objRestrElt_comp` exactly as
  `objPresheaf.map_id` / `map_comp` (`Basic.lean` :533–539) do, threaded through
  `ULift` and `Subtype.ext`. Insert `_` for each law and discharge.

- [ ] **Step 4: Build.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 5: Test** — `W` restriction along `𝟙` is the identity, on the
  `presheafWitness` fixture:

```lean
example (w : (presheafWitness.W).obj ⟨(1 : Fin 2)⟩) :
    (presheafWitness.W).map (𝟙 ⟨(1 : Fin 2)⟩) w = w :=
  congrFun (presheafWitness.W.map_id ⟨(1 : Fin 2)⟩) w
```

- [ ] **Step 6: Build test, lint, review, commit.**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Presheaf.W && lake lint`

```bash
jj new -m "feat(poly): add presheaf W-type carrier presheaf and restriction

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

---

## Task 7: Part D — fixed-point structure `W.mk` / `W.dest`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/W.lean` (`namespace PresheafPFunctor.W`)
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/W.lean`

**Interfaces:**

- Produces:

```lean
-- `objPresheaf W` fibre → `W` fibre and back, mutually inverse, over `I`.
@[expose] def W.mk {I} [Category.{vI} I] {F : PresheafPFunctor … I I} {j : I}
    (x : (F.objPresheaf F.W).obj ⟨j⟩) : (F.W).obj ⟨j⟩
@[expose] def W.dest {I} [Category.{vI} I] {F : PresheafPFunctor … I I} {j : I}
    (z : (F.W).obj ⟨j⟩) : (F.objPresheaf F.W).obj ⟨j⟩
theorem W.dest_mk … : W.dest (W.mk x) = x
theorem W.mk_dest … : W.mk (W.dest z) = z
```

- Consumes: slice `W.mk`/`W.dest`/`dest_mk`/`mk_dest`; `isHereditarilyNatural_mk`;
  `IsNatural` (Basic :194); Task 6's `W`.

- [ ] **Step 1: Define `W.mk`.** An element of `(objPresheaf F.W).obj ⟨j⟩` is a
  natural node whose direction-assignment lands in `F.W` (the carrier presheaf).
  Convert it to a slice `Obj windex` node (`ULift.down` the child trees, forget
  to the underlying slice element), apply the slice `W.mk`, and package the
  `windex = j` and `IsHereditarilyNatural` proofs: the hereditary condition at the
  new root is `isHereditarilyNatural_mk`, whose local conjunct is exactly the
  `IsNatural` datum of `x` and whose recursive conjunct is each child's carried
  `IsHereditarilyNatural`. `ULift.up` the result.

- [ ] **Step 2: Build.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 3: Define `W.dest`.** Inverse: `ULift.down`, slice `W.dest` to a node,
  re-`ULift.up` the child subtrees into `F.W` fibres (using each child's index and
  hereditary naturality extracted via `isHereditarilyNatural_mk`), and assemble
  the `IsNatural` proof from the root local conjunct. Mirror the slice `dest`
  :232 destructuring.

- [ ] **Step 4: Build.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 5: Prove `W.dest_mk` and `W.mk_dest`.** Mirror slice
  `dest_mk` :242 / `mk_dest` :251 (`Subtype.ext` + `Sigma.ext` + `ULift` η).
  Insert `_`, read
  goals, discharge; use `lean4:sorry-filler-deep` if the `ULift`/`Subtype`
  layering stalls.

- [ ] **Step 6: Build; extend the module docstring** with `W.mk`/`W.dest`/
  `dest_mk`/`mk_dest`.

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 7: Test** `dest_mk` on the fixture:

```lean
example (x : (presheafWitness.objPresheaf presheafWitness.W).obj ⟨(1 : Fin 2)⟩) :
    PresheafPFunctor.W.dest (PresheafPFunctor.W.mk x) = x :=
  PresheafPFunctor.W.dest_mk x
```

- [ ] **Step 8: Build test, lint (axioms!), review, commit.**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Presheaf.W && lake lint`

```bash
jj new -m "feat(poly): add presheaf W-type fixed-point constructor and destructor

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

---

## Task 8: Part D — the eliminator `W.elim` and its laws

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/W.lean`
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/W.lean`

**Interfaces:**

- Produces (a presheaf algebra is
  `(Y : Iᵒᵖ ⥤ Type (max uI uA uB), α : F.functor.obj Y ⟶ Y)`):

```lean
@[expose] def W.elim {I} [Category.{vI} I] (F : PresheafPFunctor … I I)
    (Y : Iᵒᵖ ⥤ Type (max uI uA uB)) (α : F.functor.obj Y ⟶ Y) :
    NatTrans F.W Y
theorem W.comp_elim … : «elim lies over I / is a morphism of presheaves»
theorem W.elim_mk … : «W.elim (W.mk x) = α ∘ (F.functor.map (W.elim) …) x»  -- computation rule
```

- Consumes: slice `W.elim`/`elim_mk`/`comp_elim`; Task 4's `W.ind`; Tasks 6–7's
  `W`, `W.mk`.

- [ ] **Step 1: Define `W.elim`'s components.** For each `j`, the fibre map
  `F.W.obj ⟨j⟩ → Y.obj ⟨j⟩` is the slice `W.elim` into `Y`'s underlying family
  (total space `Σ j, Y.obj ⟨j⟩` with its slice-algebra structure derived from `α`;
  mirror how `objPresheaf`/`obj` relate to the slice `Obj`). `ULift.down` first.

- [ ] **Step 2: Prove the `NatTrans` naturality** (that the fibre maps commute with
  restriction) by `SlicePFunctor.W.ind`: the base case is the slice `elim_mk`
  computation rule combined with `α`'s naturality. Insert `_`, build, discharge.

- [ ] **Step 3: Build.**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 4: Prove `W.comp_elim`** (elim over `I`) mirroring slice `comp_elim`
  :340, and **`W.elim_mk`** (computation rule) mirroring slice `elim_mk` :350
  (`rfl` up to the `ULift`/`Subtype` packaging). Build after each.

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.W`
Expected: clean.

- [ ] **Step 5: Complete the module docstring** (`W.elim`, `W.comp_elim`,
  `W.elim_mk`; note only the existence half of initiality is established, per
  Scope, mirroring the slice module's closing note).

- [ ] **Step 6: Test** `elim` into the trivial/`presheafWitness`-derived algebra
  (e.g. `elim` composed with `mk` equals the algebra step, one level):

```lean
example (Y) (α) (x) :
    presheafWitness.W.elim Y α (PresheafPFunctor.W.mk x) =
      «α applied to the mapped node» :=
  presheafWitness.W.elim_mk Y α x
```

Fill `Y`/`α`/`x` with the simplest concrete presheaf algebra over `presheafWitness`
(reuse a constant presheaf as in the Basic test file's `constPUnit`/`constFin2`).

- [ ] **Step 7: Build test; lint; review; commit** (axioms
  `{propext, Quot.sound}`).

Run: `lake build GebTests.Mathlib.Data.PFunctor.Presheaf.W && lake lint`

```bash
jj new -m "feat(poly): add presheaf W-type eliminator and its laws

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

---

## Task 9: Index, documentation, roadmap

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf.lean` (index)
- Modify: `GebTests/Mathlib/Data/PFunctor/Presheaf.lean` (test index, if present)
- Modify: `docs/index.md` (add the presheaf W-type paragraph)
- Modify: `TODO.md` (remove roadmap item 2)

- [ ] **Step 1: Add `public import Geb.Mathlib.Data.PFunctor.Presheaf.W`** to the
  `Presheaf.lean` index (and the test index its mirror). Build the umbrella:

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf`
Expected: clean.

- [ ] **Step 2: Add a `docs/index.md` paragraph** under the existing
  `Geb/Mathlib/Data/PFunctor/Presheaf/` entry, describing `Presheaf/W.lean`: the
  carrier as the `IsHereditarilyNatural` subtype of the slice W-type,
  `ULift`ed to `Type (max uI uA uB)`; root-only restriction;
  `W.mk`/`W.dest`/`W.elim`;
  existence half only; `Classical.choice`-free. Match the prose register of the
  slice `W.lean` entry.

- [ ] **Step 3: Remove roadmap item 2** ("Presheaf W-types") from `TODO.md`; keep
  the surrounding numbering coherent (renumber or note removal per the file's
  convention).

- [ ] **Step 4: TOC + markdown lint.**

Run: `doctoc --update-only docs/index.md TODO.md`, then
`markdownlint-cli2 docs/index.md TODO.md`
Expected: `Summary: 0 error(s)`

- [ ] **Step 5: Full build + all lints.**

Run: `lake build && lake test && lake lint && bash scripts/lint-imports.sh`
Expected: all clean.

- [ ] **Step 6: Commit.**

```bash
jj new -m "doc(poly): index presheaf W-types and close roadmap item 2

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

---

## Task 10: Remove the transient spec and plan

**Files:**

- Delete: `docs/superpowers/specs/2026-07-05-presheaf-w-types-design.md`
- Delete: `docs/superpowers/plans/2026-07-05-presheaf-w-types.md`

Per `CONTRIBUTING.md` § Concern shape, specs and plans are transient and removed
in the branch's final commits; the code and its `docs/` entries persist.

- [ ] **Step 1: Remove both files** (via a normal file deletion; do not `git rm`).

- [ ] **Step 2: Confirm no references remain.**

Run: `grep -rn "2026-07-05-presheaf-w-types" . --include=*.md || echo clean`
Expected: `clean`.

- [ ] **Step 3: Commit.**

```bash
jj new -m "chore(poly): remove transient presheaf W-types spec and plan

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
jj bookmark set feat/presheaf-w-types -r @
```

- [ ] **Step 4: Final review gate.** Run `scripts/pre-push.sh`; have the user
  review the whole branch diff line-by-line (per the LLM-contribution bar for
  `Geb/Mathlib/`) before any push. Do not `jj git push`.
