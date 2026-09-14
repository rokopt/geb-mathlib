# Machine bound, plan 2: the compilation fold

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [Executor context](#executor-context)
- [File structure](#file-structure)
- [Commit ordering](#commit-ordering)
  - [Task 1: enumerating a sequenced family's state (`SeqFin.lean`)](#task-1-enumerating-a-sequenced-familys-state-seqfinlean)
  - [Task 2: the compilation fold (`Compile/Basic.lean`)](#task-2-the-compilation-fold-compilebasiclean)
  - [Task 3: the step-bound fold (`Compile/Bound.lean`)](#task-3-the-step-bound-fold-compileboundlean)
  - [Task 4: the correctness predicate and the base cases (`Compile/Correct.lean`)](#task-4-the-correctness-predicate-and-the-base-cases-compilecorrectlean)
  - [Task 5: valuations after a family of fresh writers (`Compile/Family.lean`)](#task-5-valuations-after-a-family-of-fresh-writers-compilefamilylean)
  - [Task 6: the substitution case (`Compile/Comp.lean`)](#task-6-the-substitution-case-compilecomplean)
  - [Task 7: the recursion body's transformer (`Compile/Body.lean`)](#task-7-the-recursion-bodys-transformer-compilebodylean)
  - [Task 8: the loop computes the recursion (`Compile/LoopEval.lean`)](#task-8-the-loop-computes-the-recursion-compileloopevallean)
  - [Task 9a: the valuation entering the loop (`Compile/SrnInit.lean`)](#task-9a-the-valuation-entering-the-loop-compilesrninitlean)
  - [Task 9b: the recursion case (`Compile/Srn.lean`)](#task-9b-the-recursion-case-compilesrnlean)
  - [Task 10: the theorem (`Compile/Theorem.lean`)](#task-10-the-theorem-compiletheoremlean)
  - [Task 11: plan exit check](#task-11-plan-exit-check)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** the spec's second plan: a fold over the algebra's syntax that
compiles every expression into a program of the calculus, a fold that reads
each expression's step bound off its syntax, and the proof that the compiled
program of every expression transforms register valuations by the
expression's meaning within that bound.

**Architecture:** `compile` is a `SlicePFunctor.W.elim` fold, as `eval`
and `evalC` are, whose carrier at arity `n` is a register need `regs` and a
function of an environment `Fin n → Fin k`, an output register, a first
free register `free` and a proof `free + regs ≤ k`, returning a program (a
state type with a choice-free `FinEnum` and a machine). Substitution
compiles the children into fresh registers, sequences them with `seqFin`,
and runs the head on those registers; recursion runs `caseLoop` on a
reversed scratch copy of the recursion argument, with a body of the steps,
the copies into the value registers, and the bounded successor extending
the processed suffix. Correctness is a predicate `Correct` on a compiled
program at an arity, relative to a meaning, a non-size-increase constant and
a step bound, proved node by node as `nsi_evalValue` and `time_evalValueC`
are, and assembled by `SlicePFunctor.W.induction`.

**Tech Stack:** Lean 4 (toolchain in `lean-toolchain`), mathlib, Cslib's
multi-tape Turing machines, Lake, `jj`.

**Spec:** `docs/superpowers/specs/2026-09-13-size-bounded-machine-design.md`

This is the second of the three plans the spec's § Plan decomposition
mandates; plan 1 built the calculus it composes. Plan 3 turns the step
bound into `IsPolyBounded`, adds the wrapper and the transport to `Fin`,
the executable test, and the documentation.

## Global constraints

Copied from the spec, plan 1, and the repository rules; every task's
requirements implicitly include this section.

- Every new module is literate: `set_option doc.verso true` after the
  imports, docstrings in Verso markup with a role on every code span:
  `{name}` for a bare constant name declared earlier in the module or
  imported, `{lit}` for applications, forward references and non-constants.
  The module docstring's sections are `# Main definitions`,
  `# Main statements`, `# Tags` (a module defining nothing omits
  `# Main definitions`), in the header form of
  `Geb/Prototypes/Computability/SizeBounded/Machine/Loop/Transforms.lean`.
  No `meta import GebMeta`.
- Every `def` is `@[expose] def`; a `def` of class type is
  `@[expose, instance_reducible] def`.
- `public import` only for what the module's public statements need
  re-exported; an import used only inside proofs or by a `{name}` docstring
  reference is a plain `import`, with `-- shake: keep` only where the use is
  elaboration-time only. Index modules (`Compile.lean`) use `public import`.
- No `induction` tactic; recursion through `Nat.rec`, `List.rec`,
  `Fin.cases`, `WType.elim`, `SlicePFunctor.W.elim` and
  `SlicePFunctor.W.induction` only. No `noncomputable`; no `sorry` in a
  commit; `_` marks a hole while working.
- `constructor <;> omega` for conjunctions; no `fin_cases`; deprecated
  names (`if_pos`, `if_neg`, `dif_pos`, `dif_neg`) are errors; a
  goal-changing tactic `show` is rejected by `linter.style.show`, use
  `change`. A theorem hypothesis its proof does not use fails
  `unusedArguments`; remove it and say so.
- `open scoped FinEnum` in every module that builds a `FinEnum` instance,
  so that the choice-free `FinEnum.unit`, `FinEnum.finFin` and
  `FinEnum.finSum` of `Geb/Mathlib/Data/FinEnum.lean` are selected;
  mathlib's `FinEnum.sum` and `FinEnum.punit` depend on `Classical.choice`.
- Every module whose statements mention `Transforms`, `RunsTo`, `Reaches`,
  `configs`, `outputString` or `spaceUsedByTape` is added to
  `GebMeta.classicalAllowedModules` in `GebMeta.lean` in the task that
  creates it (after the current last entry, before `].foldl`), and the
  task runs `lake build GebMeta` before `lake lint`. `Compile/Basic.lean`,
  `Compile/Bound.lean`, `Compile/Family.lean`, `Compile/LoopEval.lean` and
  `Compile/SrnInit.lean` are strict: they mention no such constant.
- Build with `lake build Geb.Prototypes.Computability.SizeBounded.Machine`;
  never `lake env lean`, never `lake clean`. `lake lint` must pass before
  committing.
- Line length 100; two-space indentation; multi-line `{ x with ... }`
  fields aligned at one column, continuation lines indented deeper than the
  term they continue.
- Version control is `jj`: commit with `jj commit -m "<message>"`, then
  `jj bookmark set feat/size-bounded-machine -r @-`. Commit messages follow
  `docs/rules/ci-and-workflow.md`: `feat(computability): <imperative
  subject>`, ending with the two trailer lines

  ```text
  Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
  ```

  verbatim whatever the implementer's harness suggests. Never push.
- Names: `UpperCamelCase` for Prop/Type-valued declarations,
  `lowerCamelCase` for other definitions, `snake_case` for theorems.

## Executor context

Read before starting any task:

- `docs/rules/lean-coding.md`, in full.
- `Geb/Prototypes/Computability/SizeBounded/Basic.lean`: `Shape`,
  `Direction`, `rc`, `q`, `sig`, `stepDir`, `sbsSem`, `evalSRN`,
  `srnBases`, `srnSteps`, `evalValue`, `evalStep`, `eval`, `S`, `arity`,
  `SOf`, `fst_eval`, `semAt`, `SOf.sem`, `NSI`, `stepEnv`, `finMax`,
  `le_finMax`, `nsiValue`, `nsiConst`, `nsi_evalValue`, `nsi_eval`,
  `nsi_sem`. `Sem` and `transport` are `Cobham.Sem` and
  `Cobham.transport` (`Geb/Mathlib/Computability/Cobham/Basic.lean:255-270`,
  with `transport_transport`).
- `Geb/Prototypes/Computability/SizeBounded/Cost.lean`: the model of a
  second fold with its own carrier (`SemC`, `transportC`,
  `transportC_prop`, `evalValueC`, `evalStepC`, `evalC`, `fst_evalC`,
  `accountAt`), of a per-node lemma fed by the induction
  (`nsiC_evalValueC`, `time_evalValueC`, `time_le`), and of the
  identification of two folds (`valueC_eq`, `transport_eq_of_sigma_eq`,
  `SOf.sem_eq_account`).
- Plan 1's modules under `Geb/Prototypes/Computability/SizeBounded/Machine/`:
  `Program.lean` (`Transforms`, `Transforms.mono_time`,
  `Transforms.congr`), `Seq.lean` (`Transforms.seq`), `SeqFin.lean`
  (`seqFin`, `seqFin_zero`, `seqFin_succ`, `composeFin`, `composeFin_zero`,
  `composeFin_succ`, `composeFin_bounded`, `Transforms.seqFin`),
  `Primitives/*.lean` (`copy_transforms`, `const_transforms`,
  `sbs_transforms`, `copyRev_transforms`), `Loop/Basic.lean` (`caseLoop`),
  `Loop/Transforms.lean` (`loopF`, `loopF_nil`, `loopF_cons`,
  `loopF_bounded`, `Transforms.caseLoop`), `Register.lean` (`Bounded`,
  `Bounded.mono`).
- `Geb/Mathlib/Data/PFunctor/Slice/W.lean:336-390`: `elim`, `comp_elim`,
  `elim_mk` (a `rfl`), `induction`.

The contract, verbatim from `Program.lean`:

```lean
@[expose] def Transforms {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (F : (Fin k → List Bool) → Fin k → List Bool) (T B : ℕ) : Prop :=
  ∀ {input : List Bool} (cfg : Cfg k Bool State input) (σ : Fin k → List Bool),
    cfg.state = some tm.q₀ → Parked cfg → Holds cfg σ → Bounded σ B → Bounded (F σ) B →
    ∃ t ≤ T, RunsTo tm cfg (after cfg (F σ)) t B
```

The composition lemmas, verbatim:

```lean
theorem Transforms.seq {k : ℕ} {S₁ S₂ : Type} {P : MultiTapeTM k Bool S₁}
    {Q : MultiTapeTM k Bool S₂} {F G : (Fin k → List Bool) → Fin k → List Bool} {T₁ T₂ B : ℕ}
    (hP : Transforms P F T₁ B) (hQ : Transforms Q G T₂ B)
    (hF : ∀ σ, Bounded σ B → Bounded (F σ) B) :
    Transforms (seq P Q) (fun σ ↦ G (F σ)) (T₁ + T₂) B

theorem Transforms.seqFin {k : ℕ} (B T : ℕ) : ∀ (m : ℕ) (S : Fin m → Type)
    (P : (i : Fin m) → MultiTapeTM k Bool (S i))
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ i, Transforms (P i) (F i) T B) → (∀ i σ, Bounded σ B → Bounded (F i σ) B) →
    Transforms (seqFin m S P).2 (composeFin m F) (m * T + 1) B

theorem Transforms.caseLoop {k : ℕ} {SF ST : Type} (R : Fin k)
    {bodyF : MultiTapeTM k Bool SF} {bodyT : MultiTapeTM k Bool ST}
    {FF FT : (Fin k → List Bool) → Fin k → List Bool} {T B : ℕ}
    (hF : Transforms bodyF FF T B) (hT : Transforms bodyT FT T B)
    (hFR : ∀ σ, FF σ R = σ R) (hTR : ∀ σ, FT σ R = σ R)
    (hFb : ∀ σ, Bounded σ B → Bounded (FF σ) B) (hTb : ∀ σ, Bounded σ B → Bounded (FT σ) B) :
    Transforms (caseLoop R bodyF bodyT) (fun σ ↦ loopF R FF FT (σ R) σ)
      (B * (T + 2 * B + 6) + 3) B

theorem loopF_cons {k : ℕ} (R : Fin k) (FF FT : (Fin k → List Bool) → Fin k → List Bool)
    (c : Bool) (r : List Bool) (σ : Fin k → List Bool) :
    loopF R FF FT (c :: r) σ = loopF R FF FT r ((if c then FT else FF) (Function.update σ R r))
```

The primitives' transformers: `copy i j` (`hij : i ≠ j`) is
`fun σ ↦ Function.update σ j (σ i)` in `5 * B + 12`; `const w j` is
`fun σ ↦ Function.update σ j w` in `4 * B + 9`; `sbs b x y j`
(`x ≠ y`, `x ≠ j`, `y ≠ j`) is
`fun σ ↦ Function.update σ j (sbsSem b (σ x) (σ y))` in `7 * B + 16`;
`copyRev i j` (`i ≠ j`) is `fun σ ↦ Function.update σ j (σ i).reverse` in
`5 * B + 12`; each stated for every `B`.

Idioms established in plan 1 (`.claude` memory
`reference_machine_calculus_idioms`): a `match` in a statement is its own
matcher, so generic statements are preferred; `lake lint` reads the
compiled `GebMeta`, so rebuild it after editing the allowlist; dot
notation on the `@[expose] def Transforms` does not resolve, call
`Transforms.mono_time` in prefix form.

Every definition of Tasks 1 to 4 was compiled as one transient module
before this plan was written, with exactly the text below; transcribe it.

## File structure

All under `Geb/Prototypes/Computability/SizeBounded/Machine/` unless
stated:

- `SeqFin.lean` (modified): `seqFinEnum`.
- `Compile.lean` (index) and `Compile/Basic.lean`: `Prog`, `Compiled`,
  `transportP`, `regsValue`, the `srnBody` and `srnProg` helpers,
  `compileValue`, `compileStep`, `compile`, `fst_compile`, `compileAt`,
  `SOf.compile`. Strict.
- `Compile/Bound.lean`: `stepValue`, `stepBound`, `stepBound_mk`,
  `le_nsiValue`. Strict.
- `Compile/Correct.lean`: `Correct`, `CorrectSigma`, `Correct.transport`,
  the three base-case lemmas. Allowlisted.
- `Compile/Family.lean`: the value lemmas for `composeFin` over a family
  writing fresh registers, and the step environment's injectivity. Strict.
- `Compile/Comp.lean`: `correct_comp`. Allowlisted.
- `Compile/Body.lean`: `srnBody_transforms`. Allowlisted.
- `Compile/LoopEval.lean`: `loopF_evalSRN`, `loopF_frame`. Strict.
- `Compile/SrnInit.lean`: `srnInit_valuation`. Strict.
- `Compile/Srn.lean`: `correct_srn`. Allowlisted.
- `Compile/Theorem.lean`: `correct_compileValue`, `correct_compile`,
  `SOf.correct`. Allowlisted.

## Commit ordering

One commit per task, in task order. Each commit builds
(`lake build Geb.Prototypes.Computability.SizeBounded.Machine`) and
lints with no `sorry` and no error.

---

### Task 1: enumerating a sequenced family's state (`SeqFin.lean`)

**Files:**

- Modify: `Geb/Prototypes/Computability/SizeBounded/Machine/SeqFin.lean`
  (add `open scoped FinEnum` after `open Turing MultiTapeTM`,
  `public import Geb.Mathlib.Data.FinEnum` since the exposed definition's
  body names its scoped instances, the definition below after
  `seqFin_succ`, and a `# Main definitions` entry).

**Interfaces:**

- Consumes: `seqFin`, `seqFin_succ` (a `rfl`, so
  `(seqFin (m + 1) S P).1` is definitionally the binary sum).
- Produces: `seqFinEnum`.

- [ ] **Step 1: Write**

```lean
/-- A choice-free enumeration of a sequenced family's state. -/
@[expose, instance_reducible] def seqFinEnum {k : ℕ} : (m : ℕ) → (S : Fin m → Type) →
    (P : (i : Fin m) → MultiTapeTM k Bool (S i)) → ((i : Fin m) → FinEnum (S i)) →
    FinEnum (seqFin m S P).1 :=
  Nat.rec (fun _ _ _ ↦ FinEnum.unit)
    (fun m ih S P E ↦
      @FinEnum.finSum _ _ (ih (fun i ↦ S i.castSucc) (fun i ↦ P i.castSucc) (fun i ↦ E i.castSucc))
        (E (Fin.last m)))
```

- [ ] **Step 2: Build and lint**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine && lake lint`
Expected: success; `SeqFin.lean` is already allowlisted, and `seqFinEnum`
is choice-free (its instances are the scoped ones).

- [ ] **Step 3: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): enumerate a sequenced family's states

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 2: the compilation fold (`Compile/Basic.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile.lean`
  (index, in the form of `Loop.lean`)
- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Basic.lean`
- Modify: `Machine.lean` (add `public import ...Machine.Compile` after the
  `Loop` import).

**Interfaces:**

- Consumes: Task 1; the primitives; `seqFin`; `caseLoop`; `finMax`,
  `le_finMax`, `stepDir`, `sig`, `S`, `arity` from `SizeBounded/Basic.lean`.
- Produces: `Prog` (fields `State`, `enum`, `tm`), `Compiled` (fields
  `regs`, `prog`), `transportP`, `regs_transportP`, `transportP_transportP`,
  `regsValue`, `regsValue_comp`, `regsValue_srn`, `srnBody`, `srnProg`,
  `compileValue`, `compileStep`, `compile`, `fst_compile`, `compileAt`,
  `SOf.compile`.

- [ ] **Step 1: Write the module**

Imports: `public import` of `Machine.SeqFin`, `Machine.Primitives.Copy`,
`Machine.Primitives.Const`, `Machine.Primitives.Sbs`,
`Machine.Primitives.CopyRev`, `Machine.Loop.Basic`,
`Geb.Prototypes.Computability.SizeBounded.Basic`, and
`Geb.Mathlib.Data.FinEnum` (its scoped instances appear in the exposed
definitions' bodies, so the import stays public). `open Turing
MultiTapeTM`, `open scoped FinEnum`, the `open` line

```lean
open Geb.SizeBounded (Shape Direction rc q sig finMax le_finMax stepDir sbsSem evalSRN S arity SOf)
```

then `public section`.

The definitions, verified to elaborate in this form except for the two
named helpers `srnBody` and `srnProg`, which factor the verified `srn`
case's body so that Tasks 7 to 9 can name them:

```lean
/-- A program: a state type with a choice-free enumeration and a machine on it. -/
structure Prog (k : ℕ) : Type 1 where
  /-- The state type. -/
  State : Type
  /-- Its enumeration, built from the choice-free scoped instances. -/
  enum : FinEnum State
  /-- The machine. -/
  tm : MultiTapeTM k Bool State

/-- A compiled expression of arity {lit}`n`: its register need and, for an
environment, an output register and a first free register above which its need
fits, its program. -/
structure Compiled (k n : ℕ) : Type 1 where
  /-- The number of registers the program uses above its first free one. -/
  regs : ℕ
  /-- The program, given the argument registers, the output register and the
  first free register, with the proof that the need fits below {lit}`k`. -/
  prog : (env : Fin n → Fin k) → (out : Fin k) → (free : ℕ) → free + regs ≤ k → Prog k

/-- Transport of a compiled expression along an equality of arities. -/
@[expose] def transportP {k i j : ℕ} (h : i = j) (v : Compiled k i) : Compiled k j := h ▸ v

theorem regs_transportP {k i j : ℕ} (h : i = j) (v : Compiled k i) :
    (transportP h v).regs = v.regs := by
  subst h
  rfl

/-- The registers one node needs above its children's. -/
@[expose] def regsValue : (a : Shape) → (Direction a → ℕ) → ℕ
  | .const _ _, _ => 0
  | .proj _ _, _ => 0
  | .sbs _, _ => 0
  | .comp _ m, r => m + max (r (.inl ())) (finMax m fun i ↦ r (.inr i))
  | .srn _ b _, r =>
      2 * b + 3 + max (finMax b fun l ↦ r (.inl l))
        (max (finMax b fun l ↦ r (.inr (.inl l))) (finMax b fun l ↦ r (.inr (.inr l))))

theorem regsValue_comp (n m : ℕ) (r : Direction (.comp n m) → ℕ) :
    regsValue (.comp n m) r = m + max (r (.inl ())) (finMax m fun i ↦ r (.inr i)) := rfl

theorem regsValue_srn (a b : ℕ) (j : Fin b) (r : Direction (.srn a b j) → ℕ) :
    regsValue (.srn a b j) r = 2 * b + 3 + max (finMax b fun l ↦ r (.inl l))
      (max (finMax b fun l ↦ r (.inr (.inl l))) (finMax b fun l ↦ r (.inr (.inr l)))) := rfl

/-- The program of one node from its children's. -/
@[expose] def compileValue {k : ℕ} : (a : Shape) → (c : Direction a → Σ i, Compiled k i) →
    (∀ b, (c b).1 = rc a b) → Compiled k (q a)
  | .const _ w, _, _ =>
    ⟨0, fun _ out _ _ ↦ ⟨_, inferInstance, const w out⟩⟩
  | .proj _ i, _, _ =>
    ⟨0, fun env out _ _ ↦ ⟨_, inferInstance, copy (env i) out⟩⟩
  | .sbs b, _, _ =>
    ⟨0, fun env out _ _ ↦ ⟨_, inferInstance, sbs b (env 0) (env 1) out⟩⟩
  | .comp n m, c, h =>
    ⟨regsValue (.comp n m) fun d ↦ (c d).2.regs, fun env out free hfree ↦
      let r : Fin m → Fin k := fun i ↦ ⟨free + i, by
        have := i.isLt
        rw [regsValue_comp] at hfree
        omega⟩
      let args := fun i ↦ (transportP (h (.inr i)) (c (.inr i)).2).prog env (r i) (free + m) (by
        rw [regs_transportP]
        have := le_finMax m (fun i ↦ (c (.inr i)).2.regs) i
        rw [regsValue_comp] at hfree
        omega)
      let head := (transportP (h (.inl ())) (c (.inl ())).2).prog r out (free + m) (by
        rw [regs_transportP]
        rw [regsValue_comp] at hfree
        omega)
      ⟨(seqFin m (fun i ↦ (args i).State) (fun i ↦ (args i).tm)).1 ⊕ head.State,
        @FinEnum.finSum _ _ (seqFinEnum m _ _ fun i ↦ (args i).enum) head.enum,
        seq (seqFin m (fun i ↦ (args i).State) (fun i ↦ (args i).tm)).2 head.tm⟩⟩
  | .srn a b j, c, h =>
    ⟨regsValue (.srn a b j) fun d ↦ (c d).2.regs, fun env out free hfree ↦
      have hk : free + (2 * b + 3) ≤ k := by
        rw [regsValue_srn] at hfree
        omega
      let R : Fin k := ⟨free, by omega⟩
      let V : Fin k := ⟨free + 1, by omega⟩
      let Tmp : Fin k := ⟨free + 2, by omega⟩
      let vals : Fin b → Fin k := fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩
      let scr : Fin b → Fin k := fun l ↦ ⟨free + 3 + b + l, by have := l.isLt; omega⟩
      let free' := free + (2 * b + 3)
      let params := Fin.tail env
      let X := env 0
      let bases := fun l ↦ (transportP (h (.inl l)) (c (.inl l)).2).prog params (vals l) free' (by
        rw [regs_transportP]
        have := le_finMax b (fun l ↦ (c (.inl l)).2.regs) l
        rw [regsValue_srn] at hfree
        omega)
      let steps := fun (i : Bool) (l : Fin b) ↦
        (transportP (h (stepDir i l)) (c (stepDir i l)).2).prog
          (Fin.cons V (Fin.append vals params)) (scr l) free' (by
            rw [regs_transportP]
            rw [regsValue_srn] at hfree
            cases i
            · have h1 : (c (stepDir false l)).2.regs ≤
                  finMax b fun l ↦ (c (.inr (.inl l))).2.regs :=
                le_finMax b (fun l ↦ (c (.inr (.inl l))).2.regs) l
              omega
            · have h1 : (c (stepDir true l)).2.regs ≤
                  finMax b fun l ↦ (c (.inr (.inr l))).2.regs :=
                le_finMax b (fun l ↦ (c (.inr (.inr l))).2.regs) l
              omega)
      let body := fun (i : Bool) ↦
        seq (seqFin b (fun l ↦ (steps i l).State) (fun l ↦ (steps i l).tm)).2
          (seq (seqFin b (fun _ ↦ _) (fun l ↦ copy (scr l) (vals l))).2
            (seq (sbs i V X Tmp) (copy Tmp V)))
      ⟨_, by
        refine @FinEnum.finSum _ _ inferInstance ?_
        refine @FinEnum.finSum _ _ inferInstance ?_
        refine @FinEnum.finSum _ _ (seqFinEnum b _ _ fun l ↦ (bases l).enum) ?_
        refine @FinEnum.finSum _ _ ?_ inferInstance
        refine @FinEnum.finSum _ _ (FinEnum.finFin 4) ?_
        refine @FinEnum.finSum _ _ ?_ ?_
        · refine @FinEnum.finSum _ _ (seqFinEnum b _ _ fun l ↦ (steps false l).enum) ?_
          refine @FinEnum.finSum _ _ (seqFinEnum b _ _ fun _ ↦ inferInstance) inferInstance
        · refine @FinEnum.finSum _ _ (seqFinEnum b _ _ fun l ↦ (steps true l).enum) ?_
          refine @FinEnum.finSum _ _ (seqFinEnum b _ _ fun _ ↦ inferInstance) inferInstance,
        seq (copyRev X R) (seq (const [] V) (seq (seqFin b (fun l ↦ (bases l).State)
          (fun l ↦ (bases l).tm)).2 (seq (caseLoop R (body false) (body true))
            (copy (vals j) out))))⟩⟩

/-- {lit}`compileValue` as an algebra for {name}`Geb.SizeBounded.sig` in the slice
over {lit}`ℕ`. -/
@[expose] def compileStep {k : ℕ} :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Compiled k)) → Σ i, Compiled k i :=
  fun z ↦ ⟨sig.q z.1.1,
    compileValue z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The compilation of a tree: its arity together with its compiled program at that
arity, by the slice W-type's eliminator. -/
@[expose] def compile (k : ℕ) : sig.W → Σ n, Compiled k n :=
  SlicePFunctor.W.elim sig (Σ n, Compiled k n) (Sigma.fst (β := Compiled k)) compileStep rfl

/-- The index component of a tree's compilation is its arity. -/
theorem fst_compile (k : ℕ) (z : S) : (compile k z).1 = arity z :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ n, Compiled k n) (Sigma.fst (β := Compiled k))
    compileStep rfl) z

/-- The compiled program of an expression at a given arity. -/
@[expose] def compileAt (k n : ℕ) (e : S) (he : arity e = n) : Compiled k n :=
  transportP ((fst_compile k e).trans he) (compile k e).2
```

Then, replacing the inline `body` and the final machine of the `srn` case
above by the two helpers, define before `compileValue`:

```lean
/-- The body of the recursion loop for the bit {lit}`i`: the step programs into the
scratch registers, the copies of the scratch registers into the value registers,
and the bounded successor of the processed suffix by the recursion argument
into a scratch register copied back into the suffix. -/
@[expose] def srnBody {k b : ℕ} (i : Bool) (V X Tmp : Fin k) (vals scr : Fin b → Fin k)
    (steps : Fin b → Prog k) : Prog k :=
  ⟨_,
    @FinEnum.finSum _ _ (seqFinEnum b _ _ fun l ↦ (steps l).enum)
      (@FinEnum.finSum _ _ (seqFinEnum b _ _ fun _ ↦ inferInstance) inferInstance),
    seq (seqFin b (fun l ↦ (steps l).State) (fun l ↦ (steps l).tm)).2
      (seq (seqFin b (fun _ ↦ _) (fun l ↦ copy (scr l) (vals l))).2
        (seq (sbs i V X Tmp) (copy Tmp V)))⟩

/-- The program of a recursion node: the reversed copy of the recursion argument,
the empty processed suffix, the bases into the value registers, the loop, and
the selected value into the output register. -/
@[expose] def srnProg {k b : ℕ} (R V X : Fin k) (vals : Fin b → Fin k) (out : Fin k)
    (j : Fin b) (bases : Fin b → Prog k) (bodyF bodyT : Prog k) : Prog k :=
  ⟨_,
    @FinEnum.finSum _ _ inferInstance
      (@FinEnum.finSum _ _ inferInstance
        (@FinEnum.finSum _ _ (seqFinEnum b _ _ fun l ↦ (bases l).enum)
          (@FinEnum.finSum _ _
            (@FinEnum.finSum _ _ (FinEnum.finFin 4)
              (@FinEnum.finSum _ _ bodyF.enum bodyT.enum))
            inferInstance))),
    seq (copyRev X R) (seq (const [] V) (seq (seqFin b (fun l ↦ (bases l).State)
      (fun l ↦ (bases l).tm)).2 (seq (caseLoop R bodyF.tm bodyT.tm) (copy (vals j) out))))⟩
```

and write the `srn` case's program as

```lean
srnProg R V X vals out j bases (srnBody false V X Tmp vals scr (steps false))
  (srnBody true V X Tmp vals scr (steps true))
```

with `steps` a function of the bit and the component as in the verified
text. If an `inferInstance` fails to find the choice-free instance for a
primitive's state type, give it as `@FinEnum.finSum _ _ FinEnum.unit ...`
explicitly, following the state types `seq` builds.

Add after `regs_transportP`:

```lean
/-- Transport composes. -/
theorem transportP_transportP {k i j l : ℕ} (h : i = j) (g : j = l) (v : Compiled k i) :
    transportP g (transportP h v) = transportP (h.trans g) v := by
  subst h
  subst g
  rfl
```

and after `compileAt`:

```lean
/-- The compiled program of an expression of a given arity. -/
@[expose] def SOf.compile (k : ℕ) {n : ℕ} (e : SOf n) : Compiled k n := compileAt k n e.1 e.2
```

- [ ] **Step 2: Build**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Basic`

- [ ] **Step 3: Write `Compile.lean`, import it from `Machine.lean`, build, lint**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine && lake lint`
Expected: success; `Basic.lean` is strict and must pass the axiom linter
(no `Classical.choice`: every instance is a scoped choice-free one).

- [ ] **Step 4: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): compile the algebra's expressions into programs

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 3: the step-bound fold (`Compile/Bound.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Bound.lean`
- Modify: `Compile.lean` (import).

**Interfaces:**

- Consumes: `Shape`, `Direction`, `sig`, `finMax`, `le_finMax`, `nsiValue`
  from `SizeBounded/Basic.lean`.
- Produces: `stepValue`, `stepBound`, `stepBound_mk`, `le_nsiValue`.

- [ ] **Step 1: Write**

```lean
/-- The step bound of one node from its children's, as functions of the length bound. -/
@[expose] def stepValue : (a : Shape) → (Direction a → ℕ → ℕ) → ℕ → ℕ
  | .const _ _, _ => fun B ↦ 4 * B + 9
  | .proj _ _, _ => fun B ↦ 5 * B + 12
  | .sbs _, _ => fun B ↦ 7 * B + 16
  | .comp _ m, t => fun B ↦ m * finMax m (fun i ↦ t (.inr i) B) + 1 + t (.inl ()) B
  | .srn _ b _, t => fun B ↦
      let body := b * max (finMax b fun l ↦ t (.inr (.inl l)) B)
        (finMax b fun l ↦ t (.inr (.inr l)) B) + 1 + (b * (5 * B + 12) + 1) + (7 * B + 16)
        + (5 * B + 12)
      (5 * B + 12) + (4 * B + 9) + (b * finMax b (fun l ↦ t (.inl l) B) + 1)
        + (B * (body + 2 * B + 6) + 3) + (5 * B + 12)

/-- The step bound of an expression as a function of the length bound, read off
its syntax by folding {lit}`stepValue` over the tree. -/
@[expose] def stepBound : sig.toPFunctor.W → ℕ → ℕ :=
  WType.elim (ℕ → ℕ) fun x ↦ stepValue x.1 x.2

/-- The fold's computation rule. -/
theorem stepBound_mk (a : Shape) (f : Direction a → sig.toPFunctor.W) :
    stepBound (WType.mk a f) = stepValue a fun d ↦ stepBound (f d) := rfl

/-- Each child's constant is at most its node's. -/
theorem le_nsiValue : ∀ (a : Shape) (k : Direction a → ℕ) (d : Direction a),
    k d ≤ Geb.SizeBounded.nsiValue a k := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove `le_nsiValue`**

`intro a k d; cases a` (`const`, `proj`, `sbs`: `exact d.elim0`); `comp`:
`cases d` with `inl ()` giving `Nat.le_max_left` and `inr i` giving
`Nat.le_trans (le_finMax m _ i) (Nat.le_max_right _ _)`; `srn`: `cases d`
twice, each branch a `le_finMax` composed with `Nat.le_max_left` /
`Nat.le_max_right`. The `nsiValue` equations are `rfl` after `cases a`.

- [ ] **Step 4: Import, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): read each expression's step bound off its syntax

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 4: the correctness predicate and the base cases (`Compile/Correct.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Correct.lean`
- Modify: `Compile.lean` (import), `GebMeta.lean` (allowlist
  `Machine.Compile.Correct`).

**Interfaces:**

- Consumes: Tasks 2 and 3; `const_transforms`, `copy_transforms`,
  `sbs_transforms`; `evalValue`, `nsiValue`.
- Produces: `Correct`, `CorrectSigma`, `Correct.transport`,
  `correct_const`, `correct_proj`, `correct_sbs`.

- [ ] **Step 1: Write**

```lean
/-- The compiled program of arity {lit}`n` computes {lit}`f` with constant
{lit}`K` and step bound {lit}`Tf`: from every admissible allocation (an injective
environment below the first free register, an output register below it and
outside the environment) and every length bound at least {lit}`K`, its machine
transforms valuations by a function that puts the value in the output register,
leaves every other register below the first free one unchanged, and preserves the
bound. -/
@[expose] def Correct {k n : ℕ} (p : Compiled k n) (f : Sem n) (K : ℕ) (Tf : ℕ → ℕ) : Prop :=
  ∀ (env : Fin n → Fin k) (out : Fin k) (free : ℕ) (hfree : free + p.regs ≤ k),
    Function.Injective env → (∀ i, (env i).val < free) → out.val < free →
    (∀ i, env i ≠ out) → ∀ B, K ≤ B →
    ∃ F : (Fin k → List Bool) → Fin k → List Bool,
      Transforms (p.prog env out free hfree).tm F (Tf B) B ∧
      (∀ σ, F σ out = f (σ ∘ env)) ∧
      (∀ σ (i : Fin k), i.val < free → i ≠ out → F σ i = σ i) ∧
      (∀ σ, Bounded σ B → Bounded (F σ) B)

/-- Correctness of an indexed pair, the indices agreeing. -/
@[expose] def CorrectSigma {k : ℕ} (p : Σ i, Compiled k i) (m : Σ i, Sem i) (K : ℕ)
    (Tf : ℕ → ℕ) : Prop :=
  ∃ h : p.1 = m.1, Correct (transportP h p.2) m.2 K Tf

/-- Correctness transports along an equality of arities. -/
theorem Correct.transport {k i j : ℕ} (h : i = j) {p : Compiled k i} {f : Sem i} {K : ℕ}
    {Tf : ℕ → ℕ} (hp : Correct p f K Tf) : Correct (transportP h p) (transport h f) K Tf := by
  subst h
  exact hp

/-- A constant node is correct with its length as constant. -/
theorem correct_const {k n : ℕ} (w : List Bool) (c : Direction (.const n w) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.const n w) b) (s : Direction (.const n w) → Σ i, Sem i)
    (hs : ∀ b, (s b).1 = rc (.const n w) b) (K : Direction (.const n w) → ℕ)
    (Tf : Direction (.const n w) → ℕ → ℕ) :
    Correct (compileValue (.const n w) c h) (evalValue (.const n w) s hs)
      (nsiValue (.const n w) K) (stepValue (.const n w) Tf) := _

/-- A projection node is correct with constant zero. -/
theorem correct_proj {k n : ℕ} (i : Fin n) (c : Direction (.proj n i) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.proj n i) b) (s : Direction (.proj n i) → Σ i, Sem i)
    (hs : ∀ b, (s b).1 = rc (.proj n i) b) (K : Direction (.proj n i) → ℕ)
    (Tf : Direction (.proj n i) → ℕ → ℕ) :
    Correct (compileValue (.proj n i) c h) (evalValue (.proj n i) s hs)
      (nsiValue (.proj n i) K) (stepValue (.proj n i) Tf) := _

/-- A successor node is correct with constant zero. -/
theorem correct_sbs {k : ℕ} (b : Bool) (c : Direction (.sbs b) → Σ i, Compiled k i)
    (h : ∀ d, (c d).1 = rc (.sbs b) d) (s : Direction (.sbs b) → Σ i, Sem i)
    (hs : ∀ d, (s d).1 = rc (.sbs b) d) (K : Direction (.sbs b) → ℕ)
    (Tf : Direction (.sbs b) → ℕ → ℕ) :
    Correct (compileValue (.sbs b) c h) (evalValue (.sbs b) s hs)
      (nsiValue (.sbs b) K) (stepValue (.sbs b) Tf) := _
```

The three lemmas are stated with the (vacuous) children so that the
per-node dispatch of Task 10 applies them uniformly; if `unusedArguments`
rejects `c`, `h`, `s`, `hs`, `K` or `Tf` in one of them, keep the ones the
statement needs (`c`, `h`, `s`, `hs` appear in it) and drop the rest,
adjusting Task 10's dispatch.

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

Each: `intro env out free hfree hinj henv hout hne B hK`; the transformer
is `fun σ ↦ Function.update σ out v` with `v` the node's value at
`σ ∘ env`: `w`, `σ (env i)`, `sbsSem b (σ (env 0)) (σ (env 1))`; refine
`⟨_, const_transforms w out B, ?_, ?_, ?_⟩` (resp. `copy_transforms (env i)
out (hne i) B`, `sbs_transforms b (env 0) (env 1) out (fun heq ↦ ?_)
(hne 0) (hne 1) B` where `env 0 ≠ env 1` is `hinj` applied to a
`Fin.zero_ne_one`-style disequality). The output clause is
`Function.update_self`; the frame clause is `Function.update_of_ne`; the
bound clause is `Bounded.mono`-free: `intro σ hσ i; by_cases hi : i = out`,
the `out` case giving `w.length ≤ B` from `hK` (`nsiValue (.const n w) K =
w.length` by `rfl`), `(σ (env i)).length ≤ B` from `hσ`, or
`(sbsSem b _ _).length ≤ B` by `unfold sbsSem; split <;> simp only
[List.length_cons] <;> omega` with `hσ (env 0)` and `hσ (env 1)`; the other
case is `hσ i`. The `compileValue` and `evalValue` applications reduce by
`rfl` once the shape is a constructor, so `change` the goal to the
primitive's form if `refine` does not see through them.

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): state compiled correctness and prove the base forms

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 5: valuations after a family of fresh writers (`Compile/Family.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Family.lean`
- Modify: `Compile.lean` (import).

**Interfaces:**

- Consumes: `composeFin`, `composeFin_zero`, `composeFin_succ`.
- Produces: `composeFin_of_lt`, `composeFin_fresh`, `composeFin_copy`,
  `srnEnv_injective`.

The situation both `comp` and `srn` produce: a family `F : Fin m → val → val`
whose member `l` writes only registers at or above `lo` and its own fresh
register `r l = ⟨lo + l, _⟩`, and reads only registers below `lo`.

- [ ] **Step 1: Write**

```lean
/-- A family each of whose members changes nothing below {lit}`lo` leaves every
register below {lit}`lo` unchanged. -/
theorem composeFin_of_lt {k : ℕ} (lo : ℕ) : ∀ (m : ℕ)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool),
    (∀ l σ (i : Fin k), i.val < lo → F l σ i = σ i) →
    ∀ σ (i : Fin k), i.val < lo → composeFin m F σ i = σ i := _

/-- A family whose member {lit}`l` writes the value {lit}`g l` of the registers
below {lit}`lo` into the register {lit}`lo + l` and changes no other register
below {lit}`lo + m` leaves register {lit}`lo + l` holding {lit}`g l` of the
original valuation's registers below {lit}`lo`. -/
theorem composeFin_fresh {k : ℕ} (lo : ℕ) : ∀ (m : ℕ) (hm : lo + m ≤ k)
    (F : Fin m → (Fin k → List Bool) → Fin k → List Bool)
    (g : Fin m → (Fin k → List Bool) → List Bool),
    (∀ l σ σ', (∀ (i : Fin k), i.val < lo → σ i = σ' i) → g l σ = g l σ') →
    (∀ l σ, F l σ ⟨lo + l, by have := l.isLt; omega⟩ = g l σ) →
    (∀ (l : Fin m) σ (i : Fin k), i.val < lo + m → i ≠ ⟨lo + l, by have := l.isLt; omega⟩ →
      F l σ i = σ i) →
    ∀ σ (l : Fin m), composeFin m F σ ⟨lo + l, by have := l.isLt; omega⟩ = g l σ := _

/-- A family of copies into distinct destinations, none a source, leaves each
destination holding its source's original value and every other register
unchanged. -/
theorem composeFin_copy {k m : ℕ} (dst src : Fin m → Fin k)
    (hdst : Function.Injective dst) (hds : ∀ l l', dst l ≠ src l') :
    ∀ (σ : Fin k → List Bool),
      (∀ l, composeFin m (fun l σ ↦ Function.update σ (dst l) (σ (src l))) σ (dst l) =
        σ (src l)) ∧
      (∀ (i : Fin k), (∀ l, i ≠ dst l) →
        composeFin m (fun l σ ↦ Function.update σ (dst l) (σ (src l))) σ i = σ i) := _

/-- The environment of a recursion step, the processed suffix, the value registers
and the parameters, is injective when the parameters are and lie below the fresh
registers. -/
theorem srnEnv_injective {k a b : ℕ} (free : ℕ) (hk : free + (2 * b + 3) ≤ k)
    (params : Fin a → Fin k) (hparams : ∀ p, (params p).val < free)
    (hinj : Function.Injective params) :
    Function.Injective (Fin.cons (⟨free + 1, by omega⟩ : Fin k)
      (Fin.append (fun l : Fin b ↦ (⟨free + 3 + l, by have := l.isLt; omega⟩ : Fin k))
        params)) := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`composeFin_copy`: `Nat.rec` on `m` with `dst`, `src` generalized; the
step reads the last copy's `Function.update_self` / `update_of_ne` against
the induction hypothesis (the last copy's source is no earlier destination
by `hds`, and no earlier destination is the last by `hdst`).
`srnEnv_injective`: `intro i j hij`, then `Fin.cases` on `i` and `j` and
`Fin.addCases` within, nine cases closed by `Fin.ext_iff`, `omega` and
`hparams`/`hinj` (`Fin.cons_zero`, `Fin.cons_succ`, `Fin.append_left`,
`Fin.append_right` unfold the environment).

The first two, both by `Nat.rec` on `m` with `F` (and `g`) generalized, as
`composeFin_bounded` is. `composeFin_of_lt`: base `composeFin_zero`; step
`composeFin_succ`, then the last member's frame at `i` after the induction
hypothesis. `composeFin_fresh`: step case, `Fin.lastCases` on `l`: for the
last member, `composeFin_succ` and its output clause at
`composeFin m (F ∘ castSucc) σ`, whose registers below `lo` agree with
`σ`'s by `composeFin_of_lt`, so `g (last) (composeFin ..) = g (last) σ` by
the insensitivity hypothesis; for an earlier member `l.castSucc`, the last
member's frame (its register `lo + l < lo + m + 1` and differs from
`lo + m`) reduces to the induction hypothesis. `Fin.castSucc` and
`Fin.last` values: `Fin.coe_castSucc`, `Fin.val_last`; disequalities of
`Fin` by `Fin.ext_iff` and `omega`.

- [ ] **Step 4: Import, build, lint** (strict module).

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): describe valuations after a family of fresh writers

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 6: the substitution case (`Compile/Comp.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Comp.lean`
- Modify: `Compile.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 5; `Transforms.seqFin`, `Transforms.seq`,
  `Transforms.mono_time`, `Transforms.congr`, `le_finMax`,
  `transport_transport`, `transportP_transportP`, `regs_transportP`.
- Produces: `correct_comp`.

- [ ] **Step 1: Write**

```lean
/-- A substitution node is correct when its children are: the arguments run into
fresh registers in sequence, then the head reads them. -/
theorem correct_comp {k n m : ℕ} (c : Direction (.comp n m) → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc (.comp n m) b) (s : Direction (.comp n m) → Σ i, Sem i)
    (hs : ∀ b, (s b).1 = rc (.comp n m) b) (K : Direction (.comp n m) → ℕ)
    (Tf : Direction (.comp n m) → ℕ → ℕ)
    (hk : ∀ b, CorrectSigma (c b) (s b) (K b) (Tf b)) :
    Correct (compileValue (.comp n m) c h) (evalValue (.comp n m) s hs)
      (nsiValue (.comp n m) K) (stepValue (.comp n m) Tf) := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`intro env out free hfree hinj henv hout hne B hK`. For each child `d`,
turn `hk d : ∃ e, Correct (transportP e (c d).2) (s d).2 (K d) (Tf d)` into
correctness at the arity `rc (.comp n m) d`: `Correct (transportP (h d)
(c d).2) (transport (hs d) (s d).2) (K d) (Tf d)` by `Correct.transport`
and the two transport-composition lemmas (the equalities are proofs of the
same `ℕ` equation, so `transportP (h d) (c d).2 = transportP (hs d)
(transportP e (c d).2)` after `transportP_transportP` and proof
irrelevance). Apply each argument's correctness at `env`, `r i`, `free + m`
(the proof obligations are those the fold discharges; `hinj`, `henv`,
`r i` is above `free` so `≠ env j` and `out`), at `B` with `K (.inr i) ≤ B`
from `hK` and `le_nsiValue`; obtain `F i`. Sequence them with
`Transforms.seqFin B (finMax m fun i ↦ Tf (.inr i) B)` after
`Transforms.mono_time` (`le_finMax`), the bound clause from each child's.
Apply the head's correctness at `r`, `out`, `free + m` (`r` injective by
`Fin.ext_iff` and `omega`, `r i < free + m`, `out < free < free + m`,
`r i ≠ out`), obtain `G`. The node's transformer is
`fun σ ↦ G (composeFin m F σ)` by `Transforms.seq`, with bound
`m * finMax .. + 1 + Tf (.inl ()) B`, which is `stepValue (.comp n m) Tf B`
by `rfl`. Output clause: `G (composeFin m F σ) out = head ((composeFin m
F σ) ∘ r)`, and `(composeFin m F σ) (r i) = arg i (σ ∘ env)` by
`composeFin_fresh` with `lo := free`, the insensitivity hypothesis from the
argument's own output clause reading only `env` (below `free`), so the
value is `evalValue (.comp n m) s hs (σ ∘ env)` after unfolding
`evalValue`'s `comp` case. Frame clause: below `free` and not `out`,
`composeFin_of_lt` then the head's frame (`out` is the head's `out`, `i <
free < free + m`). Bound clause: `composeFin_bounded` then the head's.

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): prove the substitution node's compilation correct

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 7: the recursion body's transformer (`Compile/Body.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Body.lean`
- Modify: `Compile.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: `srnBody`, `Transforms.seqFin`, `Transforms.seq`,
  `copy_transforms`, `sbs_transforms`, `composeFin_of_lt`,
  `composeFin_fresh`, `composeFin_copy`, `composeFin_bounded`.
- Produces: `srnBody_transforms`.

- [ ] **Step 1: Write**

```lean
/-- The recursion body transforms the valuation as its parts do: each step's value
into its scratch register, then into its value register; the processed suffix
extended by the bounded successor; every register below the first fresh one
unchanged. Stated for a bit {lit}`i`, step programs each correct for a step
meaning, and the register allocation of the compiler. -/
theorem srnBody_transforms {k a b : ℕ} (i : Bool) (free : ℕ)
    (hk : free + (2 * b + 3) ≤ k) (params : Fin a → Fin k) (X : Fin k)
    (hparams : ∀ p, (params p).val < free) (hX : X.val < free)
    (steps : Fin b → Prog k) (hstep : Fin b → Sem (b + a + 1)) (T B : ℕ)
    (hsteps : ∀ l, ∃ F : (Fin k → List Bool) → Fin k → List Bool,
      Transforms (steps l).tm F T B ∧
      (∀ σ, F σ ⟨free + 3 + b + l, by have := l.isLt; omega⟩ =
        hstep l (σ ∘ Fin.cons ⟨free + 1, by omega⟩
          (Fin.append (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩) params))) ∧
      (∀ σ (r : Fin k), r.val < free + (2 * b + 3) →
        r ≠ ⟨free + 3 + b + l, by have := l.isLt; omega⟩ → F σ r = σ r) ∧
      (∀ σ, Bounded σ B → Bounded (F σ) B)) :
    ∃ G : (Fin k → List Bool) → Fin k → List Bool,
      Transforms (srnBody i ⟨free + 1, by omega⟩ X ⟨free + 2, by omega⟩
        (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩)
        (fun l ↦ ⟨free + 3 + b + l, by have := l.isLt; omega⟩) steps).tm G
        (b * T + 1 + (b * (5 * B + 12) + 1) + (7 * B + 16) + (5 * B + 12)) B ∧
      (∀ σ, G σ ⟨free + 1, by omega⟩ = sbsSem i (σ ⟨free + 1, by omega⟩) (σ X)) ∧
      (∀ σ (l : Fin b), G σ ⟨free + 3 + l, by have := l.isLt; omega⟩ =
        hstep l (σ ∘ Fin.cons ⟨free + 1, by omega⟩
          (Fin.append (fun l ↦ ⟨free + 3 + l, by have := l.isLt; omega⟩) params))) ∧
      (∀ σ (r : Fin k), r.val < free + 1 → G σ r = σ r) ∧
      (∀ σ, Bounded σ B → Bounded (G σ) B) := _
```

The registers, as the compiler allocates them: `R = free`, `V = free + 1`,
`Tmp = free + 2`, `vals l = free + 3 + l`, `scr l = free + 3 + b + l`;
`free' = free + (2 * b + 3)`. The frame conclusion `r < free + 1` covers
`R`, `X` and the parameters.

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

Choose the steps' transformers `F l` from `hsteps`; `Transforms.seqFin` at
`T` sequences them (bound clause from each). The copies: `Transforms.seqFin
B (5 * B + 12)` over `fun l ↦ copy (scr l) (vals l)` with `copy_transforms`
(`scr l ≠ vals l` by `omega`). Then `sbs_transforms i V X Tmp` (`V ≠ X` from
`hX`, `V ≠ Tmp`, `X ≠ Tmp` from `hX`) and `copy_transforms Tmp V`. Chain
with `Transforms.seq` three times; the transformer `G` is the composite.
Its clauses: `composeFin_fresh` at `lo := free + 3 + b` for the steps,
whose reads (`V`, `vals`, `params`) are all below that `lo`;
`composeFin_copy` with `dst := vals`, `src := scr` for the copies (each
copy reads its own scratch register, above the value registers, so
`composeFin_fresh` does not apply there); `Function.update_self` and
`Function.update_of_ne` for the last two. The
time bound is the sum the four `Transforms.seq` produce, equal to the
stated one by `rfl` or `omega`.

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): describe the recursion body's transformer

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 8: the loop computes the recursion (`Compile/LoopEval.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/LoopEval.lean`
- Modify: `Compile.lean` (import).

**Interfaces:**

- Consumes: `loopF`, `loopF_nil`, `loopF_cons`, `evalSRN`, `sbsSem`.
- Produces: `loopF_evalSRN`, `loopF_frame`.

A pure statement about `loopF` and `evalSRN`, with no machine: strict.

- [ ] **Step 1: Write**

```lean
/-- The loop's transformer computes simultaneous recursion: with the recursion
register holding the reverse of the remaining word, the suffix register the
processed suffix, and the value registers the recursion at that suffix, the loop
leaves the value registers holding the recursion at the whole word. The bodies
are assumed to extend the suffix by the bounded successor, which conses while the
suffix is shorter than the argument, to write each step's value, and to leave
the argument, the recursion register and the parameters alone. -/
theorem loopF_evalSRN {k a b : ℕ} (R V X : Fin k) (vals : Fin b → Fin k)
    (params : Fin a → Fin k) (hRV : R ≠ V) (hRX : R ≠ X) (hRvals : ∀ l, R ≠ vals l)
    (hRparams : ∀ p, R ≠ params p)
    (g : Fin b → Sem a) (h : Bool → Fin b → Sem (b + a + 1))
    (FF FT : (Fin k → List Bool) → Fin k → List Bool)
    (hV : ∀ (i : Bool) σ, (if i then FT else FF) σ V = sbsSem i (σ V) (σ X))
    (hvals : ∀ (i : Bool) σ l, (if i then FT else FF) σ (vals l) =
      h i l (σ ∘ Fin.cons V (Fin.append vals params)))
    (hX : ∀ (i : Bool) σ, (if i then FT else FF) σ X = σ X)
    (hR : ∀ (i : Bool) σ, (if i then FT else FF) σ R = σ R)
    (hparams : ∀ (i : Bool) σ p, (if i then FT else FF) σ (params p) = σ (params p)) :
    ∀ (r u : List Bool) (σ : Fin k → List Bool), σ R = r → σ V = u →
      σ X = r.reverse ++ u → (∀ l, σ (vals l) = evalSRN g h u l (σ ∘ params)) →
      (∀ l, loopF R FF FT r σ (vals l) = evalSRN g h (r.reverse ++ u) l (σ ∘ params)) ∧
        loopF R FF FT r σ X = σ X ∧ (∀ p, loopF R FF FT r σ (params p) = σ (params p)) := _

/-- The loop leaves every register below a bound unchanged when its recursion
register is at or above it and its bodies leave such registers unchanged. -/
theorem loopF_frame {k : ℕ} (R : Fin k) (FF FT : (Fin k → List Bool) → Fin k → List Bool)
    (lo : ℕ) (hR : lo ≤ R.val)
    (hF : ∀ σ (i : Fin k), i.val < lo → FF σ i = σ i)
    (hT : ∀ σ (i : Fin k), i.val < lo → FT σ i = σ i) :
    ∀ (r : List Bool) (σ : Fin k → List Bool) (i : Fin k), i.val < lo →
      loopF R FF FT r σ i = σ i := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`loopF_frame`: `List.rec` on `r` with `σ` generalized; the step is
`loopF_cons`, the body's frame (`cases c`), and `Function.update_of_ne`
(`i ≠ R` since `i < lo ≤ R`).

`loopF_evalSRN`: `intro r; refine List.rec ?_ ?_ r` with `u`, `σ` and the
hypotheses in the motive (they follow `r` in the statement, so the motive is
what remains).
Base: `loopF_nil`; `[].reverse ++ u = u`. Step `c :: r`: `loopF_cons`; let
`σ₁ := Function.update σ R r` (its `V`, `X`, `vals`, `params` are `σ`'s by
`Function.update_of_ne` and the disequalities, its `R` is `r`), and
`σ₂ := (if c then FT else FF) σ₁`. Then `σ₂ V = sbsSem c (σ V) (σ X) = c ::
σ V` since `(σ V).length + 1 ≤ (σ X).length`: `σ X = (c :: r).reverse ++ u
= r.reverse ++ c :: u` (`List.reverse_cons`, `List.append_assoc`,
`List.singleton_append`), so its length is `r.length + 1 + u.length`
(`List.length_append`, `List.length_reverse`), and `unfold sbsSem;
rw [ite_eq_left (by omega)]`. `σ₂ (vals l) = h c l (σ₁ ∘ Fin.cons V
(Fin.append vals params))`, and that environment is `Fin.cons (σ V)
(Fin.append (fun l ↦ evalSRN g h u l (σ ∘ params)) (σ ∘ params))` by
`funext` with `Fin.cases` and `Fin.addCases` (as `length_stepEnv_le` in
`SizeBounded/Basic.lean` does), which is `evalSRN g h (c :: u) l (σ ∘
params)` by `evalSRN`'s `cons` equation (`rfl` after `unfold evalSRN` or
`show`-free `change`). `σ₂ X = σ X = r.reverse ++ (c :: u)`, `σ₂ R = r`,
`σ₂ ∘ params = σ ∘ params`. Apply the induction hypothesis at `σ₂`, `u :=
c :: u`; its conclusion's `r.reverse ++ c :: u` is `(c :: r).reverse ++ u`.

- [ ] **Step 4: Import, build, lint** (strict module).

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): prove the loop computes simultaneous recursion

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 9a: the valuation entering the loop (`Compile/SrnInit.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/SrnInit.lean`
- Modify: `Compile.lean` (import).

**Interfaces:**

- Consumes: `composeFin_of_lt`, `composeFin_fresh`.
- Produces: `srnInit_valuation`.

The transformer the first three phases of `srnProg` produce, described
without machines: strict.

- [ ] **Step 1: Write**

```lean
/-- The valuation entering the recursion loop: the recursion register holds the
reverse of the argument, the processed suffix is empty, each value register holds
its base at the parameters, and every register below the first fresh one is
unchanged. -/
theorem srnInit_valuation {k a b : ℕ} (free : ℕ) (hk : free + (2 * b + 3) ≤ k)
    (params : Fin a → Fin k) (X : Fin k) (hparams : ∀ p, (params p).val < free)
    (hX : X.val < free) (Fb : Fin b → (Fin k → List Bool) → Fin k → List Bool)
    (hbase : Fin b → Sem a)
    (hout : ∀ l σ, Fb l σ ⟨free + 3 + l, by have := l.isLt; omega⟩ = hbase l (σ ∘ params))
    (hframe : ∀ (l : Fin b) σ (r : Fin k), r.val < free + (2 * b + 3) →
      r ≠ ⟨free + 3 + l, by have := l.isLt; omega⟩ → Fb l σ r = σ r) :
    ∀ σ : Fin k → List Bool,
      let G := composeFin b Fb (Function.update
        (Function.update σ ⟨free, by omega⟩ (σ X).reverse) ⟨free + 1, by omega⟩ [])
      G ⟨free, by omega⟩ = (σ X).reverse ∧ G ⟨free + 1, by omega⟩ = [] ∧
        (∀ l : Fin b, G ⟨free + 3 + l, by have := l.isLt; omega⟩ = hbase l (σ ∘ params)) ∧
        (∀ r : Fin k, r.val < free → G r = σ r) := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`intro σ`; the two updates are below `free + 3` and the bases' family
leaves everything below `free + 3` unchanged (`composeFin_of_lt` at
`lo := free + 3`, from `hframe` since `free + 3 ≤ free + (2 * b + 3)` and
the value registers are at or above `free + 3`), which gives the first,
second and fourth clauses after `Function.update_self` /
`Function.update_of_ne`; the third is `composeFin_fresh` at `lo := free + 3`
with `g l σ := hbase l (σ ∘ params)`, insensitive to registers at or above
`free + 3` since `params p < free`, the two updates likewise leaving
`params` alone.

- [ ] **Step 4: Import, build, lint** (strict module).

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): describe the valuation entering the recursion loop

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 9b: the recursion case (`Compile/Srn.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Srn.lean`
- Modify: `Compile.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 2 to 9a; `Transforms.caseLoop`, `loopF_bounded`,
  `loopF_frame`, `loopF_evalSRN`, `srnInit_valuation`, `srnEnv_injective`,
  `srnBody_transforms`, `copyRev_transforms`, `const_transforms`,
  `copy_transforms`, `Transforms.seqFin`, `Transforms.seq`,
  `Transforms.mono_time`, `Transforms.congr`, `srnBases`, `srnSteps`,
  `evalValue`.
- Produces: `correct_srn`.

- [ ] **Step 1: Write**

```lean
/-- A recursion node is correct when its children are. -/
theorem correct_srn {k a b : ℕ} (j : Fin b) (c : Direction (.srn a b j) → Σ i, Compiled k i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) (s : Direction (.srn a b j) → Σ i, Sem i)
    (hs : ∀ d, (s d).1 = rc (.srn a b j) d) (K : Direction (.srn a b j) → ℕ)
    (Tf : Direction (.srn a b j) → ℕ → ℕ)
    (hk : ∀ d, CorrectSigma (c d) (s d) (K d) (Tf d)) :
    Correct (compileValue (.srn a b j) c h) (evalValue (.srn a b j) s hs)
      (nsiValue (.srn a b j) K) (stepValue (.srn a b j) Tf) := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`intro env out free hfree hinj henv hout hne B hK`; the registers as Task
7 names them, `X := env 0`, `params := Fin.tail env`. Children's correctness
at their arities as in Task 6 (`Correct.transport`, transport composition),
each at `B` with `K d ≤ B` by `le_nsiValue`. Bases: apply at `params`,
`vals l`, `free'`; sequence with `Transforms.seqFin B (finMax b fun l ↦
Tf (.inl l) B)`. Steps: apply at `Fin.cons V (Fin.append vals params)`,
`scr l`, `free'` (injectivity by `srnEnv_injective`, with `params`
injective by `hinj` through `Fin.tail` and below `free` by `henv`); this yields
`hsteps` for `srnBody_transforms` at `T := max (finMax b fun l ↦ Tf (.inr
(.inl l)) B) (finMax b fun l ↦ Tf (.inr (.inr l)) B)` after `mono_time`,
for each bit, with `hstep l := transport (hs (stepDir i l)) (s (stepDir i
l)).2`, which is `srnSteps s hs i l` by `rfl`. Obtain `GF`, `GT` and their
clauses. `Transforms.caseLoop R` with `hFR`/`hTR` from the frame clause at
`R = free < free + 1`, `hFb`/`hTb` from the bound clauses. Chain:
`copyRev_transforms X R` (`X ≠ R` since `X < free`), `const_transforms []
V`, the bases, the loop, `copy_transforms (vals j) out` (`vals j ≠ out`
since `out < free`), by `Transforms.seq` four times; `Transforms.mono_time`
to `stepValue (.srn a b j) Tf B` (unfold `stepValue`; `omega` after
`Nat.mul_le_mul_left` for the loop's `B * (..)` term, since the body bound
inside is at most the `stepValue`'s `body`). Output clause: at `σ`, the
valuation before the loop is `srnInit_valuation`'s `G` (the composite of
the `copyRev`, `const` and bases transformers is that expression by
`rfl` or `Transforms.congr`), with `R = (σ X).reverse`, `V = []`,
`vals l = srnBases s hs l (σ ∘ params)`, `X` and `params` unchanged; apply
`loopF_evalSRN` at `r := (σ X).reverse`, `u := []` (so `r.reverse ++ u = σ
X` by `List.reverse_reverse`, `List.append_nil`), with `evalSRN g h [] l =
g l` (`rfl`), and the bodies' clauses from Task 7; conclude `vals j` holds
`evalSRN (srnBases s hs) (srnSteps s hs) (σ X) j (σ ∘ params)`, which the
final `copy` puts in `out`; that is `evalValue (.srn a b j) s hs (σ ∘ env)`
since `(σ ∘ env) 0 = σ X` and `Fin.tail (σ ∘ env) = σ ∘ params` (`rfl`).
Frame clause: `srnInit_valuation`'s fourth clause, then `loopF_frame` at
`lo := free` (`R = free`, the bodies' frame from Task 7 at `r < free + 1`),
then `copy`'s `Function.update_of_ne` (`out` excluded). Bound clause:
`loopF_bounded` and each primitive's.

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): prove the recursion node's compilation correct

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 10: the theorem (`Compile/Theorem.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Theorem.lean`
- Modify: `Compile.lean`, `GebMeta.lean`.

**Interfaces:**

- Consumes: Tasks 4, 6, 9b; `SlicePFunctor.W.induction`, `elim_mk`,
  `fst_compile`, `fst_eval`, `transportP_transportP`,
  `transport_transport`.
- Produces: `correct_compileValue`, `correct_compile`, `SOf.correct`.

- [ ] **Step 1: Write**

```lean
/-- One node's program is correct when its children's are. -/
theorem correct_compileValue {k : ℕ} (a : Shape) (c : Direction a → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc a b) (s : Direction a → Σ i, Sem i) (hs : ∀ b, (s b).1 = rc a b)
    (K : Direction a → ℕ) (Tf : Direction a → ℕ → ℕ)
    (hk : ∀ b, CorrectSigma (c b) (s b) (K b) (Tf b)) :
    Correct (compileValue a c h) (evalValue a s hs) (nsiValue a K) (stepValue a Tf) := by
  cases a with
  | const n w => exact correct_const w c h s hs K Tf
  | proj n i => exact correct_proj i c h s hs K Tf
  | sbs b => exact correct_sbs b c h s hs K Tf
  | comp n m => exact correct_comp c h s hs K Tf hk
  | srn a b j => exact correct_srn j c h s hs K Tf hk

/-- Every expression's program is correct, with the constant {lit}`nsiConst` and
the bound {lit}`stepBound` read off its syntax. -/
theorem correct_compile (k : ℕ) : ∀ e : S,
    CorrectSigma (compile k e) (eval e) (nsiConst e.1) (stepBound e.1) :=
  SlicePFunctor.W.induction fun x ih ↦
    ⟨rfl, correct_compileValue x.1.1 (fun b ↦ compile k (x.1.2 b)) _ (fun b ↦ eval (x.1.2 b)) _
      (fun b ↦ nsiConst (x.1.2 b).1) (fun b ↦ stepBound (x.1.2 b).1) ih⟩

/-- The compiled program of an expression of a given arity computes its meaning. -/
theorem SOf.correct (k : ℕ) {n : ℕ} (e : SOf n) :
    Correct (SOf.compile k e) e.sem (nsiConst e.1.1) (stepBound e.1.1) := _
```

If `correct_compile`'s term does not elaborate as written (the `rfl` for
`(compile k (W.mk x)).1 = (eval (W.mk x)).1` and the `_` compatibility
proofs), prove it as a `by` block: `refine SlicePFunctor.W.induction fun x
ih ↦ ⟨rfl, ?_⟩` then `exact correct_compileValue ...`, the `elim_mk`
equations being `rfl`.

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove `SOf.correct`**

`obtain ⟨h, hc⟩ := correct_compile k e.1`; `SOf.compile k e = transportP
((fst_compile k e.1).trans e.2) (compile k e.1).2` and `e.sem = transport
((fst_eval e.1).trans e.2) (eval e.1).2` by `rfl`; apply `Correct.transport
((fst_eval e.1).trans e.2) hc`, then rewrite `transportP _ (transportP h _)`
by `transportP_transportP` and close by proof irrelevance of the `ℕ`
equality (`rfl` after `congr`-free `exact`, or `Eq.mpr` with `propext`-free
`cast` as `SOf.sem_eq_account` does with `transport_eq_of_sigma_eq`).

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

Run: `lake build Geb.Prototypes.Computability.SizeBounded.Machine && lake lint`

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): prove every compiled expression correct

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 11: plan exit check

- [ ] **Step 1: Run the pre-push checklist**

Run: `scripts/pre-push.sh`
Expected: exit 0. Fix what it reports (`lake shake` on the new modules'
imports in particular) in a further `fix(computability)` commit.

- [ ] **Step 2: Report**

State which tasks are complete, the shape of `stepValue` (for plan 3's
`IsPolyBounded` proof), any deviation from the plan, and any lemma plan 3
will need that this plan did not provide.
