# Size-Bounded Machine Bound, Plan 3: Bounds, Wrapper, Transport, Tests, Docs

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove, for every `e : SOf 1`,
`∃ c d, ComputableInTimeAndSpace (fun w ↦ e.sem ![w])
(fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (n + 1))`,
with the compiled program of plan 2 wrapped in an input reader and an output
writer, transported to `Fin` symbols and states, its step bound proved
polynomial and its space bound linear; execute the compiler in a test; document.

**Architecture:** An `Emits` contract generalizes plan 1's `RunsTo` by an output
word, with a family lemma that closes every phase proof from a closed-form
configuration family. Two input-reading phases and one emitting phase are the
only machines that move the input head or emit. `Wrapper.lean` sequences reader,
program and writer and proves the composite `Emits` the meaning within an
explicit step count at the length bound `max n (nsiConst e)`. `Transport.lean`
relabels a machine over `Bool` and any state type to `Fin 2` and `Fin s` along
`FinEnum.equiv`, with `configs`, `outputString`, `spaceUsed` and `initCfg`
commuting. `Bound.lean` reads the register need off the syntax and proves
`stepBound` `IsPolyBounded` by the closure lemmas of `Cost.lean`. `Main.lean`
assembles the target statement.

**Tech Stack:** Lean 4 (v4.34.0-rc2), mathlib, Cslib
(`Turing.MultiTapeTM`), jj (colocated), `lake build`/`lake lint`/`lake shake`.

**Spec:** `docs/superpowers/specs/2026-09-13-size-bounded-machine-design.md`
(§ Bounds, § Wrapper, § Modules, § Tests, § Target statement).

## Global Constraints

- Every new module under `Geb/` is literate: `set_option doc.verso true`;
  module docstring with `# ...` title, prose, `# Main definitions` and/or
  `# Main statements`, `# Tags`; header form as `Machine/Compile/Comp.lean`.
  Docstring roles:
  `{name}` for a bare constant name declared earlier in the module or
  imported; `{lit}` for applications, forward references and non-constants;
  `{cite}` for a literature key of `docs/references.bib`. A test module under
  `GebTests/` follows its sibling
  `GebTests/Prototypes/Computability/SizeBounded/BitTree.lean` (plain module
  docstring, `set_option linter.privateModule false`).
- `public import` only for modules whose declarations the module's public
  statements mention; plain `import` for elaboration-only needs.
  `scripts/pre-push.sh` runs
  `lake shake --add-public --keep-implied --keep-prefix Geb GebTests GebLang`
  and must pass.
- No `induction` tactic (recursors, `Fin.cases`, `Fin.addCases`,
  `SlicePFunctor.W.induction`, `WType.rec` as terms are fine); no
  `noncomputable`; no `sorry`; no `fin_cases`; deprecated
  `if_pos`/`if_neg`/`dif_pos`/`dif_neg` are errors (use
  `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`);
  `linter.style.show` rejects a goal-changing tactic `show` (use `change`);
  unused theorem hypotheses fail the build; `constructor <;> omega` for
  conjunctions.
- Modules whose statements mention `step`, `configs`, `outputString`,
  `spaceUsedByTape`, `spaceUsed`, `Reaches`, `RunsTo`, `Emits` or
  `Transforms` are listed in `GebMeta.classicalAllowedModules`
  (`GebMeta.lean`), and so is the test module; `Bound.lean` stays strict.
  After editing the list run `lake build GebMeta` before `lake lint`.
- Choice-free proofs in strict modules: avoid `by_cases`, `by_contra`,
  `congr` (use `congrArg`/`funext`), `omega` on `↔`/`∧` goals or with
  `¬(a ∧ b)` hypotheses, `!=` on `Fin`, `Function.update_idem`,
  `simp (config := {decide := true})`. Verify with the `lean_verify` MCP tool.
- Line length 100; two-space indentation. Committed prose formal, dry, no
  value-laden adjectives, no process history.
- Version control is jj: `jj commit -m "<message>"` with the message given in
  the task, ending with the two trailer lines
  `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` and
  `Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt`,
  then `jj bookmark set feat/size-bounded-machine -r @-`. Never push; no
  mutating `git` commands. Never run `lake env lean`.
- Build with `lake build Geb.Prototypes.Computability.SizeBounded.Machine`
  (or the module), `lake lint`; the exit check runs `scripts/pre-push.sh`.

## File Structure

Under `Geb/Prototypes/Computability/SizeBounded/Machine/` (namespace
`Geb.SizeBounded.Machine`; `open Turing MultiTapeTM` as the existing modules
do):

- `Program.lean` (modify): `Arrives` below `Reaches`; extract
  `spaceUsedByTape_le_of_pos`.
- `Emit.lean` (create; allowlisted): `Emits`, `RunsTo.toEmits`,
  `Emits.toRunsTo`, `Emits.ofFamily`, `RunsTo.ofFamily`,
  `Emits.spaceUsedByTape_le`, `Emits.spaceUsed_le`.
- `Seq.lean` (modify): `RunsTo.seqEmits`; `RunsTo.seq` becomes its corollary.
- `Phase/Input.lean` (create; allowlisted): `inRight`, `inBack`, `inLeft`,
  their configuration families and `RunsTo` lemmas.
- `Phase/Output.lean` (create; allowlisted): `emitLeft`, its family and
  `Emits` lemma.
- `Bound.lean` (create; strict): `regsBound`, `regsBound_mk`, `regs_compile`,
  `SOf.regs`, `isPolyBounded_stepValue`, `isPolyBounded_stepBound`; and in
  `SizeBounded/Cost.lean` the bridges `finMax_le_finSum`, `isPolyBounded_id`,
  `isPolyBounded_finMax`, `isPolyBounded_max`.
- `Wrapper.lean` (create; allowlisted): `reader`, `reader_runsTo`, `writer`,
  `writer_emits`, `ReaderState`, `WriterState`, `tapes`, `program`, `State`,
  `machine`, `bound`, `time`, `machine_emits`.
- `Transport.lean` (create; allowlisted): `bitEmb`, `relabel`, `relabelCfg`,
  `inputSymbol_relabel`, `step_relabel`, `configs_relabel`,
  `outputString_relabel`, `initCfg_relabel`, `spaceUsed_relabel`.
- `Main.lean` (create; allowlisted): `computableInTimeAndSpace_sem`.
- `Exec.lean` (create; allowlisted): `ExecCfg`, `execStep`, `execOutputSymbol`
  and their simulation of Cslib's `step`, for the test.
- Indexes: `Machine.lean` gains `Emit`, `Bound`, `Wrapper`, `Transport`,
  `Main`, `Exec`; `Phase.lean` gains `Phase.Input`, `Phase.Output`.
- `GebTests/Prototypes/Computability/SizeBounded/Machine.lean` (create;
  allowlisted); its index `GebTests/Prototypes/Computability/SizeBounded.lean`
  (modify).
- `docs/index.md`, `TODO.md`, `GebMeta.lean`.

Interfaces from plans 1 and 2 every task may use (exact):

```lean
-- Register.lean
@[expose] def tapeOf (w : List Bool) : ℤ → Option Bool   -- cell z holds w.reverse[z]?
theorem tapeOf_nil : tapeOf [] = fun _ ↦ none
theorem tapeOf_cons (b : Bool) (w : List Bool) : ...      -- the write at cell w.length
theorem tapeOf_of_lt (w) (z) (h0 : 0 ≤ z) (h : z < w.length) : ...
theorem tapeOf_of_le (w) (z) (h : w.length ≤ z) : tapeOf w z = none
theorem tapeOf_update_none (b) (w) : Function.update (tapeOf (b :: w)) (w.length : ℤ) none = tapeOf w
@[expose] def Parked (cfg) : Prop := ∀ i, cfg.workTapePos i = 0
@[expose] def Holds (cfg) (σ : Fin k → List Bool) : Prop := ∀ i, cfg.workTapes i = tapeOf (σ i)
@[expose] def Bounded (σ : Fin k → List Bool) (B : ℕ) : Prop := ∀ i, (σ i).length ≤ B
theorem Bounded.update (hσ : Bounded σ B) (hw : w.length ≤ B) : Bounded (Function.update σ j w) B
-- Program.lean
theorem step_of_state (tm) (cfg) (q) (hq : cfg.state = some q) : tm.step cfg = { ... }  -- see its statement
structure Reaches (tm) (cfg cfg') (t B : ℕ) : Prop where
  live : ∀ t' < t, (tm.configs cfg t').state ≠ none
  configs_eq : tm.configs cfg t = cfg'
  output : tm.outputString cfg t = []
  pos : ∀ t' ≤ t, ∀ i, -1 ≤ (tm.configs cfg t').workTapePos i ∧ (tm.configs cfg t').workTapePos i ≤ B
structure RunsTo (tm) (cfg cfg') (t B : ℕ) : Prop extends Reaches tm cfg cfg' t B where
  halted : cfg'.state = none
theorem RunsTo.spaceUsedByTape_le (h : RunsTo tm cfg cfg' t B) (i : Fin k) : tm.spaceUsedByTape cfg t i ≤ B + 2
@[expose] def after (cfg) (σ) : Cfg k Bool State input := { cfg with state := none, workTapes := fun i ↦ tapeOf (σ i) }
@[expose] def Transforms (tm) (F) (T B : ℕ) : Prop :=
  ∀ {input} (cfg : Cfg k Bool State input) (σ), cfg.state = some tm.q₀ → Parked cfg → Holds cfg σ →
    Bounded σ B → Bounded (F σ) B → ∃ t ≤ T, RunsTo tm cfg (after cfg (F σ)) t B
-- Seq.lean
@[expose] def seq (P : MultiTapeTM k Bool S₁) (Q : MultiTapeTM k Bool S₂) : MultiTapeTM k Bool (S₁ ⊕ S₂)
@[expose] def liftL (Q) (cfg : Cfg k Bool S₁ input) : Cfg k Bool (S₁ ⊕ S₂) input :=
  { cfg with state := some (cfg.state.elim (.inr Q.q₀) .inl) }
@[expose] def liftR (cfg : Cfg k Bool S₂ input) : Cfg k Bool (S₁ ⊕ S₂) input := { cfg with state := cfg.state.map .inr }
theorem liftL_halt ...; theorem liftL_start ...; theorem seq_q₀ ...
theorem seq_configs_left (P Q cfg) : ∀ t, (∀ t' < t, (P.configs cfg t').state ≠ none) → (seq P Q).configs (liftL Q cfg) t = liftL Q (P.configs cfg t)
theorem seq_configs_right (P Q cfg t) : (seq P Q).configs (liftR cfg) t = liftR (Q.configs cfg t)
theorem seq_outputString_left (P Q cfg) : ∀ t, (∀ t' < t, ...) → (seq P Q).outputString (liftL Q cfg) t = P.outputString cfg t
theorem seq_outputString_right (P Q cfg t) : (seq P Q).outputString (liftR cfg) t = Q.outputString cfg t
theorem RunsTo.seq (h₁ : RunsTo P cfg cfg₁ t₁ B) (h₂ : RunsTo Q { cfg₁ with state := some Q.q₀ } cfg₂ t₂ B) :
    RunsTo (seq P Q) (liftL Q cfg) (liftR cfg₂) (t₁ + t₂) B
-- Phase/Return.lean, Phase/Clear.lean
theorem moveLeft_runsTo (i) (cfg) (hq : cfg.state = some ()) (B) (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B)
    (hi : 0 ≤ cfg.workTapePos i) : RunsTo (moveLeft i) cfg { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i - 1) } 1 B
theorem returnTape_runsTo (i) (cfg : Cfg k Bool (Unit ⊕ Unit) input) (hq : cfg.state = some (returnTape i).q₀) (w) (hw : cfg.workTapes i = tapeOf w)
    (p : ℤ) (hp : cfg.workTapePos i = p) (hp0 : 0 ≤ p) (hpw : p ≤ w.length) (B) (hpos) :
    RunsTo (returnTape i) cfg { cfg with state := none, workTapePos := Function.update cfg.workTapePos i 0 } (p + 2).toNat B
theorem walkEnd_runsTo (i) (cfg) (hq : cfg.state = some ()) (w) (hw : cfg.workTapes i = tapeOf w) (hp : cfg.workTapePos i = 0) (B) (hB : w.length ≤ B) (hpos) :
    RunsTo (walkEnd i) cfg { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) } (w.length + 1) B
-- Compile/Basic.lean, Compile/Bound.lean, Compile/Correct.lean, Compile/Theorem.lean
structure Prog (k : ℕ) : Type 1 where State : Type; enum : FinEnum State; tm : MultiTapeTM k Bool State
structure Compiled (k n : ℕ) : Type 1 where regs : ℕ; prog : (env : Fin n → Fin k) → (out : Fin k) → (free : ℕ) → free + regs ≤ k → Prog k
@[expose] def regsValue : (a : Shape) → (Direction a → ℕ) → ℕ
@[expose] def compile (k : ℕ) : sig.W → Σ n, Compiled k n    -- SlicePFunctor.W.elim ... compileStep rfl
theorem regs_transportP ... : (transportP h p).regs = p.regs
@[expose] def SOf.compile (k : ℕ) {n : ℕ} (e : SOf n) : Compiled k n := compileAt k n e.1 e.2  -- = transportP _ (compile k e.1).2
@[expose] def stepValue : (a : Shape) → (Direction a → ℕ → ℕ) → ℕ → ℕ   -- clauses below in Task 4
@[expose] def stepBound : sig.toPFunctor.W → ℕ → ℕ := WType.elim (ℕ → ℕ) fun x ↦ stepValue x.1 x.2
@[expose] def Correct (p : Compiled k n) (f : Sem n) (K : ℕ) (Tf : ℕ → ℕ) : Prop :=
  ∀ (env : Fin n → Fin k) (out : Fin k) (free : ℕ) (hfree : free + p.regs ≤ k), Function.Injective env →
    (∀ i, (env i).val < free) → out.val < free → (∀ i, env i ≠ out) → ∀ B, K ≤ B →
    ∃ F, Transforms (p.prog env out free hfree).tm F (Tf B) B ∧ (∀ σ, F σ out = f (σ ∘ env)) ∧
      (∀ σ (i : Fin k), i.val < free → i ≠ out → F σ i = σ i) ∧ (∀ σ, Bounded σ B → Bounded (F σ) B)
theorem SOf.correct (k : ℕ) {n : ℕ} (e : SOf n) : Correct (SOf.compile k e) e.sem (nsiConst e.1.1) (stepBound e.1.1)
-- SizeBounded/Basic.lean, SizeBounded/Cost.lean (namespace Geb.SizeBounded)
@[expose] def NSI (k : ℕ) (f : Sem n) : Prop := ∀ (x : Fin n → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) → (f x).length ≤ max m k
theorem nsi_sem {n : ℕ} (e : SOf n) : NSI (nsiConst e.1.1) e.sem
@[expose] def finMax : (m : ℕ) → (Fin m → ℕ) → ℕ := Nat.rec (fun _ ↦ 0) fun m ih f ↦ max (ih fun i ↦ f i.castSucc) (f (Fin.last m))
@[expose] def finSum : (m : ℕ) → (Fin m → ℕ) → ℕ := Nat.rec (fun _ ↦ 0) fun m ih f ↦ ih (fun i ↦ f i.castSucc) + f (Fin.last m)
@[expose] def IsPolyBounded (p : ℕ → ℕ) : Prop := ∃ c d, ∀ m, p m ≤ c * (m + 1) ^ d
theorem isPolyBounded_of_le (h : ∀ m, q m ≤ p m) (hp : IsPolyBounded p) : IsPolyBounded q
theorem isPolyBounded_const (k) : IsPolyBounded fun _ ↦ k
theorem isPolyBounded_succ : IsPolyBounded fun m ↦ m + 1
theorem isPolyBounded_add (hp) (hq) : IsPolyBounded fun m ↦ p m + q m
theorem isPolyBounded_mul (hp) (hq) : IsPolyBounded fun m ↦ p m * q m
theorem isPolyBounded_finSum : ∀ (k) (p : Fin k → ℕ → ℕ), (∀ i, IsPolyBounded (p i)) → IsPolyBounded fun m ↦ finSum k fun i ↦ p i m
theorem isPolyBounded_shift (K) (hp : IsPolyBounded p) : IsPolyBounded fun m ↦ p (max m K)
-- Cslib (Turing.MultiTapeTM)
def ComputesInTimeAndSpace (tm) (input output : List Symbol) (t s : ℕ) : Prop :=
  (tm.configs (tm.initCfg input) t).state = none ∧ tm.outputString (tm.initCfg input) t = output ∧ tm.spaceUsed (tm.initCfg input) t = s
def ComputesFunInTimeAndSpace (tm) (f : List IOSymbol → List IOSymbol) (toMachineSymbol : IOSymbol ↪ Symbol) (t s : ℕ → ℕ) : Prop :=
  ∀ input, ∃ t' ≤ t input.length, ∃ s' ≤ s input.length, ComputesInTimeAndSpace tm (input.map toMachineSymbol) ((f input).map toMachineSymbol) t' s'
def ComputableInTimeAndSpace (f : List IOSymbol → List IOSymbol) (t s : ℕ → ℕ) : Prop :=
  ∃ (k sym state : ℕ) (toMachineSymbol : _) (tm : MultiTapeTM k (Fin sym) (Fin state)), ComputesFunInTimeAndSpace tm f toMachineSymbol t s
def initCfg (input : List Symbol) : Cfg k Symbol State input := ⟨some tm.q₀, 1, fun _ _ => none, fun _ => 0⟩
def Cfg.inputSymbol (cfg) : Option Symbol := if h₁ : cfg.inputPos = 0 then none else if h₂ : cfg.inputPos = input.length + 1 then none else input[cfg.inputPos.val - 1]
lemma inputSymbolInner (p : ℕ) (h₁ : cfg.inputPos.val = 1 + p) (h₂ : p < input.length) : cfg.inputSymbol = some input[p]
def moveInputPos (pos : Fin (n + 2)) (m : SignType) : Fin (n + 2)   -- clamped; moveInputPos_zero, moveInputPos_neg_of_ne_left (p ≠ 0), moveInputPos_pos_of_ne_right (p.val ≠ n + 1)
def spaceUsedByTape (cfg) (t) (i) : ℕ := (tm.visitedByTapeHead cfg t i).card
def spaceUsed (cfg) (t) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i
lemma configs_succ_eq_step' : tm.configs cfg (t + 1) = tm.step (tm.configs cfg t)
lemma outputString_succ : tm.outputString cfg (t + 1) = tm.outputString cfg t ++ (tm.outputSymbol (tm.configs cfg t)).toList
lemma outputString_add_eq_append : tm.outputString cfg (t + s) = tm.outputString cfg t ++ tm.outputString (tm.configs cfg t) s
```

---

### Task 1: the emitting contract and the family lemma (`Emit.lean`)

**Files:**

- Modify: `Machine/Program.lean`: insert `Arrives` above `Reaches`; `Reaches`
  extends it; `Reaches.trans` becomes `Arrives.trans` plus a corollary;
  extract `spaceUsedByTape_le_of_pos` above `RunsTo.spaceUsedByTape_le`.
- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Emit.lean`
  (imports `Program`).
- Modify: `Machine/Seq.lean` (`public import ...Machine.Emit`;
  `Reaches.liftL`/`Reaches.liftR` become `Arrives.liftL`/`Arrives.liftR` plus
  corollaries; add `RunsTo.seqEmits`; `RunsTo.seq` becomes its corollary),
  the nine phase proofs (their `refine ⟨⟨?_, ?_, ?_, ?_⟩, rfl⟩`-shaped closings
  take the new field nesting), `Machine.lean` (import after `Program`),
  `GebMeta.lean` (allowlist `...Machine.Emit` after `...Machine.Program`).

**Interfaces:**

- Consumes: `Reaches`, `RunsTo`, `Reaches.trans`, `Reaches.liftL/liftR`,
  `seq_configs_left/right`, `seq_outputString_left/right`, `liftL_halt`
  (three explicit arguments: `Q`, `cfg`, `h`), `liftR_state`,
  `liftL_state_ne_none`, cslib's `configs_succ_eq_step'`, `outputString_succ`,
  `outputString_add_eq_append`, `visitedByTapeHead`, `mem_visitedByTapeHead`.
- Produces: `Arrives`, `Arrives.trans`, `Arrives.liftL`, `Arrives.liftR`,
  `Emits`, `RunsTo.toEmits`, `Emits.toRunsTo`, `Emits.ofFamily`,
  `RunsTo.ofFamily`, `spaceUsedByTape_le_of_pos`, `Emits.spaceUsedByTape_le`,
  `Emits.spaceUsed_le`, `RunsTo.seqEmits`. `Reaches`, `RunsTo`,
  `Reaches.trans`, `Reaches.liftL/liftR`, `RunsTo.seq` keep their statements.

- [ ] **Step 1: `Program.lean`: the base structure**

Above `Reaches`:

```lean
/-- From {lit}`cfg`, {lit}`tm` arrives at {lit}`cfg'` at step {lit}`t`, halted
at no earlier step, every head within {lit}`[-1, B]` throughout. -/
structure Arrives {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg cfg' : Cfg k Bool State input) (t B : ℕ) : Prop where
  /-- No step before {lit}`t` is halted. -/
  live : ∀ t' < t, (tm.configs cfg t').state ≠ none
  /-- The configuration at step {lit}`t`. -/
  configs_eq : tm.configs cfg t = cfg'
  /-- Every head stays within {lit}`[-1, B]`. -/
  pos : ∀ t' ≤ t, ∀ i, -1 ≤ (tm.configs cfg t').workTapePos i ∧
    (tm.configs cfg t').workTapePos i ≤ B

/-- An arrival emitting nothing. -/
structure Reaches {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg cfg' : Cfg k Bool State input) (t B : ℕ) : Prop extends Arrives tm cfg cfg' t B where
  /-- Nothing is emitted. -/
  output : tm.outputString cfg t = []
```

`Reaches.trans`'s present proof becomes `Arrives.trans` (drop its `output`
field), and

```lean
/-- Reaches compose. -/
theorem Reaches.trans ... (h₁ : Reaches tm cfg cfg' t₁ B) (h₂ : Reaches tm cfg' cfg'' t₂ B) :
    Reaches tm cfg cfg'' (t₁ + t₂) B :=
  ⟨h₁.toArrives.trans h₂.toArrives, by
    rw [outputString_add_eq_append, h₁.output, h₁.configs_eq, h₂.output]; rfl⟩
```

(keep the present binder list; `Reaches.mono`, `RunsTo.mono`,
`RunsTo.halt_configs` are unchanged, their field accesses resolving through
`toArrives`). Then the extraction:

```lean
/-- A tape whose head stays within {lit}`[-1, B]` over {lit}`t` steps visits at
most {lit}`B + 2` cells. -/
theorem spaceUsedByTape_le_of_pos {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (cfg : Cfg k Bool State input) (t B : ℕ) (i : Fin k)
    (h : ∀ t' ≤ t, -1 ≤ (tm.configs cfg t').workTapePos i ∧ (tm.configs cfg t').workTapePos i ≤ B) :
    tm.spaceUsedByTape cfg t i ≤ B + 2 := by
  -- the body of the present RunsTo.spaceUsedByTape_le, with `h.pos t' (by omega) i`
  -- replaced by `h t' (by omega)`
```

and `RunsTo.spaceUsedByTape_le h i` becomes
`spaceUsedByTape_le_of_pos _ _ _ _ i fun t' ht' ↦ h.pos t' ht' i`.

Every phase proof that closes with `refine ⟨⟨?_, ?_, ?_, ?_⟩, rfl⟩` (the four
being `live`, `configs_eq`, `output`, `pos`) now closes with
`refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩` (`live`, `configs_eq`, `pos`, then
`output`); reorder the four bullet proofs accordingly (the `output` bullet
moves last). Build `Geb.Prototypes.Computability.SizeBounded.Machine.Phase`
to find every such site (`Phase/Return.lean`, `Phase/Clear.lean`,
`Phase/Walk.lean`, `Phase/Sbs.lean`, `Phase/Write.lean`).

- [ ] **Step 2: `Emit.lean`**

```lean
/-- An arrival at a halted configuration having emitted exactly {lit}`out`. -/
structure Emits {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (cfg cfg' : Cfg k Bool State input) (out : List Bool) (t B : ℕ) : Prop
    extends Arrives tm cfg cfg' t B where
  /-- The word emitted. -/
  output : tm.outputString cfg t = out
  /-- The target is halted. -/
  halted : cfg'.state = none

/-- A run emits nothing. -/
theorem RunsTo.toEmits {k : ℕ} {State : Type} {input : List Bool} {tm : MultiTapeTM k Bool State}
    {cfg cfg' : Cfg k Bool State input} {t B : ℕ} (h : RunsTo tm cfg cfg' t B) :
    Emits tm cfg cfg' [] t B :=
  ⟨h.toArrives, h.output, h.halted⟩

/-- Emitting nothing is a run. -/
theorem Emits.toRunsTo {k : ℕ} {State : Type} {input : List Bool} {tm : MultiTapeTM k Bool State}
    {cfg cfg' : Cfg k Bool State input} {t B : ℕ} (h : Emits tm cfg cfg' [] t B) :
    RunsTo tm cfg cfg' t B :=
  ⟨⟨h.toArrives, h.output⟩, h.halted⟩

/-- A closed-form family of live configurations, each the step of the previous,
whose last steps to a halted configuration, is an emission: the accumulator
{lit}`o` collects the symbols the family emits. -/
theorem Emits.ofFamily {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (f : ℕ → Cfg k Bool State input) (o : ℕ → List Bool) (n B : ℕ)
    (cfg' : Cfg k Bool State input)
    (hlive : ∀ s ≤ n, (f s).state ≠ none)
    (hstep : ∀ s < n, tm.step (f s) = f (s + 1))
    (hhalt : tm.step (f n) = cfg') (hcfg' : cfg'.state = none)
    (h0 : o 0 = []) (hout : ∀ s ≤ n, o (s + 1) = o s ++ (tm.outputSymbol (f s)).toList)
    (hpos : ∀ s ≤ n, ∀ i, -1 ≤ (f s).workTapePos i ∧ (f s).workTapePos i ≤ B)
    (hpos' : ∀ i, -1 ≤ cfg'.workTapePos i ∧ cfg'.workTapePos i ≤ B) :
    Emits tm (f 0) cfg' (o (n + 1)) (n + 1) B := by
  have key : ∀ s, s ≤ n → tm.configs (f 0) s = f s ∧ tm.outputString (f 0) s = o s := by
    refine Nat.rec ?_ ?_
    · intro _
      exact ⟨configs_zero, h0.symm⟩
    · intro s ih hs
      obtain ⟨hc, ho⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [configs_succ_eq_step', hc, hstep s (by omega)]
      · rw [outputString_succ, ho, hc, hout s (by omega)]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, hcfg'⟩
  · intro t' ht'
    rw [(key t' (by omega)).1]
    exact hlive t' (by omega)
  · rw [configs_succ_eq_step', (key n (le_refl n)).1, hhalt]
  · intro t' ht' i
    rcases Nat.lt_or_ge t' (n + 1) with h | h
    · rw [(key t' (by omega)).1]
      exact hpos t' (by omega) i
    · have : t' = n + 1 := by omega
      rw [this, configs_succ_eq_step', (key n (le_refl n)).1, hhalt]
      exact hpos' i
  · rw [outputString_succ, (key n (le_refl n)).1, (key n (le_refl n)).2, hout n (le_refl n)]

/-- The family lemma for a family that emits nothing. -/
theorem RunsTo.ofFamily {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (f : ℕ → Cfg k Bool State input) (n B : ℕ) (cfg' : Cfg k Bool State input)
    (hlive : ∀ s ≤ n, (f s).state ≠ none)
    (hstep : ∀ s < n, tm.step (f s) = f (s + 1))
    (hhalt : tm.step (f n) = cfg') (hcfg' : cfg'.state = none)
    (hout : ∀ s ≤ n, tm.outputSymbol (f s) = none)
    (hpos : ∀ s ≤ n, ∀ i, -1 ≤ (f s).workTapePos i ∧ (f s).workTapePos i ≤ B)
    (hpos' : ∀ i, -1 ≤ cfg'.workTapePos i ∧ cfg'.workTapePos i ≤ B) :
    RunsTo tm (f 0) cfg' (n + 1) B :=
  (Emits.ofFamily tm f (fun _ ↦ []) n B cfg' hlive hstep hhalt hcfg' rfl
    (fun s hs ↦ by rw [hout s hs]; rfl) hpos hpos').toRunsTo

/-- Over an emission the head of each tape visits at most {lit}`B + 2` cells. -/
theorem Emits.spaceUsedByTape_le {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {out : List Bool}
    {t B : ℕ} (h : Emits tm cfg cfg' out t B) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ B + 2 :=
  spaceUsedByTape_le_of_pos tm cfg t B i fun t' ht' ↦ h.pos t' ht' i

/-- Over an emission the machine uses at most {lit}`k * (B + 2)` cells. -/
theorem Emits.spaceUsed_le {k : ℕ} {State : Type} {input : List Bool}
    {tm : MultiTapeTM k Bool State} {cfg cfg' : Cfg k Bool State input} {out : List Bool}
    {t B : ℕ} (h : Emits tm cfg cfg' out t B) : tm.spaceUsed cfg t ≤ k * (B + 2) := by
  unfold spaceUsed
  refine le_trans (Finset.sum_le_sum fun i _ ↦ h.spaceUsedByTape_le i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
```

- [ ] **Step 3: `Seq.lean`**

`Reaches.liftL`'s and `Reaches.liftR`'s present proofs become
`Arrives.liftL`/`Arrives.liftR` (drop the `output` field), with
`Reaches.liftL h := ⟨h.toArrives.liftL Q, <the present output proof>⟩` and
likewise `liftR`. Then:

```lean
/-- A run of {lit}`P` followed by an emission of {lit}`Q` from {lit}`P`'s final
tapes is an emission of the composite. -/
theorem RunsTo.seqEmits {k : ℕ} {S₁ S₂ : Type} {input : List Bool}
    {P : MultiTapeTM k Bool S₁} {Q : MultiTapeTM k Bool S₂}
    {cfg cfg₁ : Cfg k Bool S₁ input} {cfg₂ : Cfg k Bool S₂ input} {out : List Bool} {t₁ t₂ B : ℕ}
    (h₁ : RunsTo P cfg cfg₁ t₁ B)
    (h₂ : Emits Q { cfg₁ with state := some Q.q₀ } cfg₂ out t₂ B) :
    Emits (seq P Q) (liftL Q cfg) (liftR cfg₂) out (t₁ + t₂) B where
  toArrives := -- the present RunsTo.seq's `toReaches` term, with `toArrives` in place of
    -- `toReaches` and `Arrives.liftL`/`Arrives.liftR`/`Arrives.trans` in place of the
    -- `Reaches` forms
    sorry
  output := by
    rw [outputString_add_eq_append, seq_outputString_left P Q cfg t₁ h₁.live, h₁.output,
      List.nil_append, seq_configs_left P Q cfg t₁ h₁.live, h₁.configs_eq,
      liftL_halt _ _ h₁.halted, seq_outputString_right, h₂.output]
  halted := by rw [liftR_state, h₂.halted]; rfl

/-- Runs compose under sequencing. -/
theorem RunsTo.seq ... := (h₁.seqEmits h₂.toEmits).toRunsTo
```

The `sorry` marks where the present `RunsTo.seq` term is transplanted; it is
gone when the task is done. Check `liftL_halt`'s and `liftR_state`'s exact
statements with `lean_hover_info` and adjust the rewrites.

- [ ] **Step 4: Build**

Run: `lake build GebMeta`, then
`lake build Geb.Prototypes.Computability.SizeBounded.Machine && lake lint`

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the emitting contract and the family lemma

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 2: the input-reading phases (`Phase/Input.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Phase/Input.lean`
- Modify: `Machine/Phase.lean` (import after `Write`), `GebMeta.lean`
  (allowlist `...Machine.Phase.Input` after `...Machine.Phase.Write`).

**Interfaces:**

- Consumes: `RunsTo.ofFamily`, `step_of_state`, `tapeOf`, `tapeOf_cons`,
  cslib's `inputSymbolInner`, `Cfg.inputSymbol`, `moveInputPos_zero`,
  `moveInputPos_neg_of_ne_left`, `moveInputPos_pos_of_ne_right`.
- Produces: `inRight`, `inBack`, `inLeft`, `inRight_runsTo`, `inBack_runsTo`,
  `inLeft_runsTo`.

- [ ] **Step 1: Write**

```lean
/-- Move the input head right until it reads the blank past the input. -/
@[expose] def inRight {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ inp _ :=
    { inputMove := if inp.isSome then 1 else 0
      workActions := fun _ ↦ (none, 0)
      outS := none
      q' := if inp.isSome then some () else none }

/-- Move the input head one cell left. -/
@[expose] def inBack {k : ℕ} : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ := { inputMove := -1, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- Walk the input head left, writing each symbol read at register {lit}`j`'s
head and advancing that head, until the input head reads the blank before the
input. -/
@[expose] def inLeft {k : ℕ} (j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ inp _ :=
    match inp with
    | some b =>
      { inputMove := -1
        workActions := fun l ↦ if l = j then (some (some b), 1) else (none, 0)
        outS := none
        q' := some () }
    | none => { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- The configuration of {name}`inRight` after {lit}`s` steps from the input
head at the first symbol. -/
@[expose] def inRightCfg {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input) (s : ℕ) :
    Cfg k Bool Unit input :=
  { cfg with state := some (), inputPos := ⟨min (1 + s) (input.length + 1), by omega⟩ }

/-- {name}`inRight` from the input head at the first symbol runs
{lit}`input.length + 1` steps and leaves the head past the input. -/
theorem inRight_runsTo {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val = 1) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo inRight cfg { cfg with state := none, inputPos := ⟨input.length + 1, by omega⟩ }
      (input.length + 1) B := _

/-- {name}`inBack` from the input head past the input runs one step and leaves
the head at the last symbol, or at the blank before an empty input. -/
theorem inBack_runsTo {k : ℕ} {input : List Bool} (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val = input.length + 1) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo inBack cfg { cfg with state := none, inputPos := ⟨input.length, by omega⟩ } 1 B := _

/-- The configuration of {name}`inLeft` after {lit}`s` steps from the input
head at the last symbol and register {lit}`j` empty and parked: the head has
moved {lit}`s` cells left and {lit}`j` holds the last {lit}`s` symbols in the
reversed layout. -/
@[expose] def inLeftCfg {k : ℕ} {input : List Bool} (j : Fin k) (cfg : Cfg k Bool Unit input)
    (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    inputPos := ⟨input.length - s, by omega⟩
    workTapes := Function.update cfg.workTapes j (tapeOf (input.drop (input.length - s)))
    workTapePos := Function.update cfg.workTapePos j (s : ℤ) }

/-- {name}`inLeft` from the input head at the last symbol and register {lit}`j`
empty and parked runs {lit}`input.length + 1` steps; {lit}`j` then holds the
input in the reversed layout with its head at {lit}`input.length`, and the
input head is at the blank before the input. -/
theorem inLeft_runsTo {k : ℕ} {input : List Bool} (j : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (hp : cfg.inputPos.val = input.length)
    (hj : cfg.workTapes j = tapeOf []) (hpj : cfg.workTapePos j = 0) (B : ℕ)
    (hB : input.length ≤ B) (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    RunsTo (inLeft j) cfg
      { cfg with
        state := none
        inputPos := ⟨0, by omega⟩
        workTapes := Function.update cfg.workTapes j (tapeOf input)
        workTapePos := Function.update cfg.workTapePos j (input.length : ℤ) }
      (input.length + 1) B := _
```

- [ ] **Step 2: Build** (statements only; the `_` placeholders fail, which is expected)

- [ ] **Step 3: Prove**

Each lemma is `RunsTo.ofFamily` at its family (for `inBack`, the constant
family `fun _ ↦ { cfg with state := some () }` and `n := 0`), so it needs:
`f 0 = cfg` (`Cfg.ext`; `hq`, `hp`, `hj`, `hpj` supply the fields, with
`Function.update_eq_self` after rewriting `0 = cfg.workTapePos j`), `hlive`
(`rfl`-level: `some () ≠ none`), `hstep`, `hhalt`, `hout` (`rfl`), `hpos`,
`hpos'`. The step and halt equations are `rw [step_of_state _ _ () rfl]` then
`Cfg.ext` with four field goals, as `walkEnd_runsTo` in `Phase/Clear.lean`
does; the input-head field is where these phases differ:

- `inRight`, step `s < n`: the input symbol at position `1 + s` is
  `some input[s]` by `inputSymbolInner s` (`min (1 + s) (n + 1) = 1 + s` by
  `omega`), so `isSome` is `true`, `q' = some ()`, and
  `moveInputPos ⟨1 + s, _⟩ 1 = ⟨1 + s + 1, _⟩` by
  `moveInputPos_pos_of_ne_right` (`1 + s ≠ n + 1`). Halt at `s = n`: position
  `n + 1`, `Cfg.inputSymbol` unfolds to `none` by its second `dite`
  (`dite_eq_left`/`dite_eq_right` with `Fin.ext`), so `isSome` is `false`,
  `q' = none`, `moveInputPos _ 0 = _` by `moveInputPos_zero`.
- `inBack`: one step; `moveInputPos ⟨n + 1, _⟩ (-1) = ⟨n, _⟩` by
  `moveInputPos_neg_of_ne_left` (`⟨n + 1, _⟩ ≠ 0` by `Fin.ext_iff`, `omega`).
- `inLeft j`, step `s < n`: position `n - s ≥ 1`, symbol `some input[n - s - 1]`
  by `inputSymbolInner (n - s - 1)` (`n - s = 1 + (n - s - 1)` by `omega`);
  the `match` reduces on `some`; the write:
  `Function.update (Function.update cfg.workTapes j (tapeOf v)) j
  (Function.update (tapeOf v) (s : ℤ) (some input[n - s - 1]))` with
  `v := input.drop (n - s)` must equal
  `Function.update cfg.workTapes j (tapeOf (input.drop (n - (s + 1))))`:
  `Function.update_idem`-free: rewrite the outer update by
  `Function.update_of_ne`/`Function.update_self` under `funext`, or state the
  composite directly under `funext l` with `if h : l = j` (this module is
  allowlisted, so `Function.update_idem` and `by_cases` are permitted; prefer
  them to long detours); the tape equation is
  `tapeOf_cons` at `w := input.drop (n - s)` (whose length is `s`) with
  `Register.lean`'s `drop_length_sub_succ input s (hs : s < n) :
  input.drop (n - (s + 1)) = input.reverse[s] :: input.drop (n - s)` and
  `List.getElem_reverse` (`input.reverse[s] = input[n - 1 - s]`, which is the
  symbol `inputSymbolInner (n - s - 1)` reads);
  `j`'s head `s + 1`; input head `n - s - 1` by `moveInputPos_neg_of_ne_left`.
  Halt at `s = n`: position `0`, symbol `none` (first `dite`), `match` on
  `none`, all fields unchanged except `state`; `input.drop 0 = input`
  (`List.drop_zero`).
- `hpos` for `inLeft`: `j`'s head `s ≤ n ≤ B`; other heads by `hpos` and
  `Function.update_of_ne`; `hpos'` likewise with `n ≤ B`.

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the input-reading phase machines

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 3: the emitting phase (`Phase/Output.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Phase/Output.lean`
- Modify: `Machine/Phase.lean` (import after `Input`), `GebMeta.lean`
  (allowlist after `Phase.Input`).

**Interfaces:**

- Consumes: `Emits.ofFamily`, `step_of_state`, `tapeOf_of_lt`, `tapeOf_neg`,
  `List.take_succ_eq_append_getElem`, `List.getElem_reverse`.
- Produces: `emitLeft`, `emitLeft_emits`.

- [ ] **Step 1: Write**

```lean
/-- Walk register {lit}`i`'s head left, emitting each bit read, until it reads a
blank. -/
@[expose] def emitLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work i with
    | some b =>
      { inputMove := 0
        workActions := fun l ↦ if l = i then (none, -1) else (none, 0)
        outS := some b
        q' := some () }
    | none => { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- The configuration of {name}`emitLeft` after {lit}`s` steps from the head at
the last cell of a register holding {lit}`w`. -/
@[expose] def emitCfg {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (w : List Bool) (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    workTapePos := Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s) }

/-- {name}`emitLeft` from the head at cell {lit}`w.length - 1` of a register
holding {lit}`w` runs {lit}`w.length + 1` steps, emits {lit}`w`, and leaves the
head at cell {lit}`-1`. -/
theorem emitLeft_emits {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (hp : cfg.workTapePos i = (w.length : ℤ) - 1) (B : ℕ) (hB : w.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Emits (emitLeft i) cfg
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (-1) }
      w (w.length + 1) B := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`Emits.ofFamily (emitLeft i) (emitCfg i cfg w) (fun s ↦ w.take s) w.length B _`,
then `List.take_length` (or `List.take_of_length_le`) turns `w.take (n + 1)`
into `w`. The symbol read at step `s < n` is
`tapeOf w ((n : ℤ) - 1 - s) = some w[s]` by `tapeOf_of_lt` and
`List.getElem_reverse` (`w.reverse[n - 1 - s] = w[s]`); `hout s`:
`w.take (s + 1) = w.take s ++ [w[s]]` by `List.take_succ_eq_append_getElem`
(for `s < n`), with `(some w[s]).toList = [w[s]]` by `rfl`; at `s = n` the
head is at `-1`, the symbol is `none` (`tapeOf_neg`), and the obligation
`w.take (n + 1) = w.take n ++ []` is `List.take_of_length_le` twice and
`List.append_nil` — split `hout` by `Nat.lt_or_ge s n`. Halt at `s = n`: the
same `none`. Heads: `-1 ≤ n - 1 - s ≤ B` for `s ≤ n` by `omega`.

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add the emitting phase machine

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 4: the register need and the polynomial step bound (`Bound.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Bound.lean` (strict)
- Modify: `Geb/Prototypes/Computability/SizeBounded/Cost.lean` (bridges, after
  `isPolyBounded_shift`), `Machine.lean` (import after `Compile`).

**Interfaces:**

- Consumes: `regsValue`, `compile`, `regs_transportP`, `SOf.compile`,
  `stepValue`, `stepBound`, `finMax`, `finSum`, `IsPolyBounded` and its
  closure lemmas, `SlicePFunctor.W.induction`, `WType.rec`.
- Produces: `finMax_le_finSum`, `isPolyBounded_id`, `isPolyBounded_finMax`,
  `isPolyBounded_max`, `isPolyBounded_linear` (in `Cost.lean`); `regsBound`, `regsBound_mk`,
  `regs_compileValue`, `regs_compile`, `SOf.regs`, `isPolyBounded_stepValue`,
  `isPolyBounded_stepBound` (in `Bound.lean`).

- [ ] **Step 1: Write the bridges in `Cost.lean`**

```lean
/-- The maximum of a finite family is at most its sum. -/
theorem finMax_le_finSum : ∀ (m : ℕ) (f : Fin m → ℕ), finMax m f ≤ finSum m f :=
  Nat.rec (fun _ ↦ Nat.le_refl 0) fun m ih f ↦
    Nat.max_le.mpr ⟨Nat.le_trans (ih fun i ↦ f i.castSucc) (Nat.le_add_right _ _),
      Nat.le_add_left _ _⟩

/-- The identity is bounded by a polynomial. -/
theorem isPolyBounded_id : IsPolyBounded fun m ↦ m :=
  isPolyBounded_of_le (fun m ↦ Nat.le_succ m) isPolyBounded_succ

/-- The maximum of a finite family of polynomially bounded functions is. -/
theorem isPolyBounded_finMax (k : ℕ) (p : Fin k → ℕ → ℕ) (hp : ∀ i, IsPolyBounded (p i)) :
    IsPolyBounded fun m ↦ finMax k fun i ↦ p i m :=
  isPolyBounded_of_le (fun m ↦ finMax_le_finSum k fun i ↦ p i m) (isPolyBounded_finSum k p hp)

/-- The maximum of two polynomially bounded functions is. -/
theorem isPolyBounded_max {p q : ℕ → ℕ} (hp : IsPolyBounded p) (hq : IsPolyBounded q) :
    IsPolyBounded fun m ↦ max (p m) (q m) :=
  isPolyBounded_of_le (fun m ↦ Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩)
    (isPolyBounded_add hp hq)

/-- A linear function is bounded by a polynomial. -/
theorem isPolyBounded_linear (c d : ℕ) : IsPolyBounded fun m ↦ c * m + d :=
  isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const c) isPolyBounded_id)
    (isPolyBounded_const d)
```

- [ ] **Step 2: Write `Bound.lean`**

```lean
/-- The register need of an expression, read off its syntax by folding
{name}`regsValue` over the tree. -/
@[expose] def regsBound : sig.toPFunctor.W → ℕ := WType.elim ℕ fun x ↦ regsValue x.1 x.2

/-- The fold's computation rule. -/
theorem regsBound_mk (a : Shape) (f : Direction a → sig.toPFunctor.W) :
    regsBound (WType.mk a f) = regsValue a fun d ↦ regsBound (f d) := rfl

/-- One node's register need is {name}`regsValue` of its children's. -/
theorem regs_compileValue {k : ℕ} (a : Shape) (c : Direction a → Σ i, Compiled k i)
    (h : ∀ b, (c b).1 = rc a b) :
    (compileValue a c h).regs = regsValue a fun d ↦ (c d).2.regs := by
  cases a <;> rfl

/-- The compiled program's register need is the syntactic one, at every number
of registers. -/
theorem regs_compile (k : ℕ) : ∀ e : S, (compile k e).2.regs = regsBound e.1 :=
  SlicePFunctor.W.induction fun x ih ↦ by
    change (compileValue x.1.1 (fun d ↦ compile k (x.1.2 d)) _).regs =
      regsValue x.1.1 fun d ↦ regsBound (x.1.2 d).1
    rw [regs_compileValue]
    exact congrArg _ (funext ih)

/-- The register need of an expression of a given arity. -/
theorem SOf.regs (k : ℕ) {n : ℕ} (e : SOf n) : (SOf.compile k e).regs = regsBound e.1.1 := by
  change (transportP _ (compile k e.1).2).regs = _
  rw [regs_transportP, regs_compile]

/-- One node's step bound is polynomially bounded when its children's are. -/
theorem isPolyBounded_stepValue (a : Shape) (t : Direction a → ℕ → ℕ)
    (ht : ∀ d, IsPolyBounded (t d)) : IsPolyBounded (stepValue a t) := by
  cases a with
  | const n w => exact isPolyBounded_linear 4 9
  | proj n i => exact isPolyBounded_linear 5 12
  | sbs b => exact isPolyBounded_linear 7 16
  | comp n m =>
    exact isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_mul (isPolyBounded_const m) (isPolyBounded_finMax m _ fun i ↦ ht (.inr i)))
      (isPolyBounded_const 1)) (ht (.inl ()))
  | srn a b j =>
    have hbody : IsPolyBounded fun B ↦ b * max (finMax b fun l ↦ t (.inr (.inl l)) B)
        (finMax b fun l ↦ t (.inr (.inr l)) B) + 1 + (b * (5 * B + 12) + 1) + (7 * B + 16)
        + (5 * B + 12) :=
      isPolyBounded_add (isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
        (isPolyBounded_mul (isPolyBounded_const b)
          (isPolyBounded_max (isPolyBounded_finMax b _ fun l ↦ ht (.inr (.inl l)))
            (isPolyBounded_finMax b _ fun l ↦ ht (.inr (.inr l)))))
        (isPolyBounded_const 1))
        (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b) (isPolyBounded_linear 5 12))
          (isPolyBounded_const 1)))
        (isPolyBounded_linear 7 16)) (isPolyBounded_linear 5 12)
    -- `dsimp only [stepValue]` zeta-reduces the `let body`; if the `let`
    -- survives, `change` the goal to the reduced form
    exact isPolyBounded_add (isPolyBounded_add (isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_linear 5 12) (isPolyBounded_linear 4 9))
      (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const b)
        (isPolyBounded_finMax b _ fun l ↦ ht (.inl l))) (isPolyBounded_const 1)))
      (isPolyBounded_add (isPolyBounded_mul isPolyBounded_id (isPolyBounded_add (isPolyBounded_add
        hbody (isPolyBounded_mul (isPolyBounded_const 2) isPolyBounded_id))
        (isPolyBounded_const 6))) (isPolyBounded_const 3)))
      (isPolyBounded_linear 5 12)

/-- Every expression's step bound is polynomially bounded. -/
theorem isPolyBounded_stepBound : ∀ w : sig.toPFunctor.W, IsPolyBounded (stepBound w) :=
  WType.rec (motive := fun w ↦ IsPolyBounded (stepBound w)) fun a f ih ↦
    isPolyBounded_stepValue a _ ih
```

The closure terms match `stepValue`'s clauses by definitional unfolding; if
`exact` fails to unify a `fun B ↦ ...` shape,
`refine isPolyBounded_of_le (fun B ↦ le_of_eq ?_) <term>`
with `rfl`/`omega`-closed equalities, or `change` the goal to the clause's
right side first. The `stepValue` clauses, for reference:

```lean
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
```

- [ ] **Step 3: Build**

- [ ] **Step 4: Build; `lean_verify` every theorem of `Bound.lean` and the
  five bridges: no `Classical.choice` (strict modules).**

- [ ] **Step 5: Import, build, lint**

- [ ] **Step 6: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): bound the register need and prove the step bound polynomial

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 5: the top-level machine (`Wrapper.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Wrapper.lean`
- Modify: `Machine.lean` (import after `Bound`), `GebMeta.lean` (allowlist
  after `...Machine.Phase.Output`).

**Interfaces:**

- Consumes: Tasks 1 to 4; `returnTape_runsTo`, `walkEnd_runsTo`,
  `moveLeft_runsTo`, `RunsTo.seq`, `RunsTo.seqEmits`, `liftL_start`,
  `SOf.correct`, `SOf.regs`, `nsiConst`, `stepBound`, `after`, `Parked`,
  `Holds`, `Bounded`, `tapeOf_nil`, `FinEnum.finSum`, `Matrix.vecCons`
  notation (`Mathlib.Data.Fin.VecNotation`).
- Produces: `reader`, `reader_runsTo`, `writer`, `writer_emits`,
  `ReaderState`, `WriterState`, `tapes`, `program`, `State`, `machine`,
  `bound`, `time`, `machine_emits`.

- [ ] **Step 1: Write**

```lean
/-- The input reader: the input head to the right end, one cell back, the walk
left writing the input at register {lit}`j` in the reversed layout, and the
return of {lit}`j`'s head. -/
@[expose] def reader {k : ℕ} (j : Fin k) :=
  seq inRight (seq inBack (seq (inLeft j) (returnTape j)))

/-- The state type of {name}`reader`. -/
abbrev ReaderState : Type := Unit ⊕ (Unit ⊕ (Unit ⊕ (Unit ⊕ Unit)))

/-- {name}`reader` from the initial input head and an empty parked register
{lit}`j` runs {lit}`3 * input.length + 5` steps and leaves {lit}`j` holding the
input, parked, the input head at the blank before the input. -/
theorem reader_runsTo {k : ℕ} {input : List Bool} (j : Fin k)
    (cfg : Cfg k Bool ReaderState input) (hq : cfg.state = some (reader j).q₀)
    (hp : cfg.inputPos.val = 1) (hj : cfg.workTapes j = tapeOf []) (hpark : Parked cfg)
    (B : ℕ) (hB : input.length ≤ B) :
    RunsTo (reader j) cfg
      { cfg with
        state := none
        inputPos := ⟨0, by omega⟩
        workTapes := Function.update cfg.workTapes j (tapeOf input) }
      (3 * input.length + 5) B := _

/-- The output writer: register {lit}`i`'s head to its first blank, one cell
back, and the walk left emitting the register's word. -/
@[expose] def writer {k : ℕ} (i : Fin k) := seq (walkEnd i) (seq (moveLeft i) (emitLeft i))

/-- The state type of {name}`writer`. -/
abbrev WriterState : Type := Unit ⊕ (Unit ⊕ Unit)

/-- {name}`writer` from a parked register {lit}`i` holding {lit}`w` runs
{lit}`2 * w.length + 3` steps and emits {lit}`w`. -/
theorem writer_emits {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool WriterState input) (hq : cfg.state = some (writer i).q₀)
    (w : List Bool) (hw : cfg.workTapes i = tapeOf w) (hpark : Parked cfg) (B : ℕ)
    (hB : w.length ≤ B) :
    Emits (writer i) cfg
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (-1) }
      w (2 * w.length + 3) B := _

/-- The registers of an expression's machine: the input register, the output
register, and the compiled program's need. -/
@[expose] def tapes (e : SOf 1) : ℕ := regsBound e.1.1 + 2

/-- The compiled program of {lit}`e` reading register {lit}`0`, writing register
{lit}`1`, with the registers from {lit}`2` free. -/
@[expose] def program (e : SOf 1) : Prog (tapes e) :=
  (SOf.compile (tapes e) e).prog ![⟨0, by unfold tapes; omega⟩] ⟨1, by unfold tapes; omega⟩ 2
    (by rw [SOf.regs]; unfold tapes; omega)

/-- The state type of an expression's machine. -/
abbrev State (e : SOf 1) : Type := ReaderState ⊕ ((program e).State ⊕ WriterState)

/-- The state type is enumerable, by the compiled program's enumeration and the
scoped instances for sums and {lit}`Unit`. -/
instance (e : SOf 1) : FinEnum (State e) :=
  @FinEnum.finSum _ _ inferInstance (@FinEnum.finSum _ _ (program e).enum inferInstance)

/-- The machine of an expression: the reader, the compiled program, the writer. -/
@[expose] def machine (e : SOf 1) : MultiTapeTM (tapes e) Bool (State e) :=
  seq (reader ⟨0, by unfold tapes; omega⟩)
    (seq (program e).tm (writer ⟨1, by unfold tapes; omega⟩))

/-- The length bound the machine runs under on an input of length {lit}`n`: the
length or the expression's constant. -/
@[expose] def bound (e : SOf 1) (n : ℕ) : ℕ := max n (nsiConst e.1.1)

/-- The machine's step count on an input of length {lit}`n`. -/
@[expose] def time (e : SOf 1) (n : ℕ) : ℕ :=
  (3 * n + 5) + stepBound e.1.1 (bound e n) + (2 * bound e n + 3)

/-- The machine of {lit}`e` on {lit}`w` emits {lit}`e`'s meaning at {lit}`w`,
in the reader's, the program's and the writer's steps, every head within the
bound. -/
theorem machine_emits (e : SOf 1) (w : List Bool) :
    ∃ cfg' t', t' ≤ (3 * w.length + 5) + stepBound e.1.1 (bound e w.length) +
        (2 * (e.sem ![w]).length + 3) ∧
      Emits (machine e) ((machine e).initCfg w) cfg' (e.sem ![w]) t' (bound e w.length) := _
```

The scoped `FinEnum` instances live in `Geb.Mathlib.Data.FinEnum`
(`open scoped` its namespace as `Compile/Basic.lean` does; copy that module's
`open` line).

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`reader_runsTo`: `RunsTo.seq` three times over `inRight_runsTo`,
`inBack_runsTo`, `inLeft_runsTo`, `returnTape_runsTo` (at `p := input.length`,
so `(p + 2).toNat = input.length + 2`), each applied at
`{ <previous final> with state := some <next>.q₀ }` as `copyRev_transforms`
in `Primitives/CopyRev.lean` does; the start is
`liftL _ { cfg with state := some () }`
which `liftL_start` identifies with `cfg` (given `hq`), and the end
`liftR { ... state := none ... }` is the stated configuration by `rfl` up to
the rewrites `Function.update cfg.workTapePos j 0 = cfg.workTapePos`
(`hpark j`, `Function.update_eq_self`) and `Function.update_idem`. Time
`(n + 1) + (1 + ((n + 1) + (n + 2))) = 3n + 5` by `RunsTo.mono`-free
`Nat.add_assoc` rewriting or by restating the target with `show`-free `change`
and `omega`-closed `congrArg`; if the shapes resist, prove the lemma at the
sum the chain produces and conclude by `RunsTo.mono` with an equality (check
`RunsTo.mono`'s statement in `Program.lean`; it weakens `t` or `B` — if it
does not fit,
`rw [show (n + 1) + (1 + ((n + 1) + (n + 2))) = 3 * n + 5 by omega] at h`).

`writer_emits`: `RunsTo.seq` (`walkEnd_runsTo` at `w`, `moveLeft_runsTo` from
head `w.length` to `w.length - 1`) then `RunsTo.seqEmits` with
`emitLeft_emits`; time `(n + 1) + (1 + (n + 1)) = 2n + 3`.

`machine_emits`: with `n := w.length`, `B := bound e n`,
`X := (⟨0, _⟩ : Fin (tapes e))`,
`out := (⟨1, _⟩ : Fin (tapes e))`:

1. `(machine e).initCfg w` is `liftL _ cfg₀` up to `liftL_start`, with
   `cfg₀ := { state := some (reader X).q₀, inputPos := 1,
   workTapes := fun _ _ ↦ none, workTapePos := fun _ ↦ 0 }`; apply
   `reader_runsTo X` at `cfg₀`
   (`hp : (1 : Fin (n + 2)).val = 1` by `rfl`/`Fin.val_one`; `hj` by
   `tapeOf_nil`; `hpark` by `fun _ ↦ rfl`; `hB : n ≤ max n K` by
   `Nat.le_max_left`), obtaining `h₁ : RunsTo (reader X) cfg₀ cfg₁ (3n + 5) B`.
2. `obtain ⟨F, hT, hout, -, hbound⟩ :=`
   `SOf.correct (tapes e) e ![X] out 2 _ hinj henv hout' hne B hK`
   with `hinj : Function.Injective ![X]` (`fun a b _ ↦ Subsingleton.elim a b`),
   `henv : ∀ i, (![X] i).val < 2`
   (`fun i ↦ by rw [Fin.fin_one_eq_zero i]; decide`
   or `Nat.zero_lt_two`), `hout' : out.val < 2`, `hne : ∀ i, ![X] i ≠ out`
   (`Fin.ne_of_val_ne`), `hK : nsiConst e.1.1 ≤ bound e n` (`Nat.le_max_right`).
3. `σ₀ := Function.update (fun _ ↦ []) X w`; apply `hT` at
   `{ cfg₁ with state := some (program e).tm.q₀ }` and `σ₀`: `Parked` (cfg₁'s
   heads are cfg₀'s, all `0`), `Holds` (`Function.update_self` for `X`,
   `Function.update_of_ne` and `tapeOf_nil` otherwise), `Bounded σ₀ B`
   (`Bounded.update (fun _ ↦ Nat.zero_le _) hB`), `Bounded (F σ₀) B`
   (`hbound`); obtain `t ≤ stepBound e.1.1 B` and
   `h₂ : RunsTo (program e).tm _ (after _ (F σ₀)) t B`.
4. `hF : F σ₀ out = e.sem ![w]`: `hout σ₀` then `σ₀ ∘ ![X] = ![w]` by
   `funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; exact Function.update_self ..`
   (the right side `![w] 0 = w` is `Matrix.cons_val_zero`/`rfl`).
5. `writer_emits out` at `{ after _ (F σ₀) with state := some (writer out).q₀ }`
   with `hw` from `after`'s `workTapes` and `hF`, `hpark` from `after`
   keeping positions, `hB'` from `hbound _ (Bounded.update ..) out`.
6. Compose: `h₁.seqEmits (h₂.seqEmits h₃)` after `liftL_start`/`seq_q₀`
   identify the start configurations; the final configuration and the time
   `(3n + 5) + (t + (2 * |e.sem ![w]| + 3))` are the witnesses, the bound by
   `t ≤ stepBound ..` and `omega` (an emission is exact in its time, which is
   why the statement is existential in `t'`).

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): wrap the compiled program in a reader and a writer

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 6: relabeling to `Fin` symbols and states (`Transport.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Transport.lean`
- Modify: `Machine.lean` (import after `Wrapper`), `GebMeta.lean` (allowlist
  after `...Machine.Wrapper`).

**Interfaces:**

- Consumes: cslib's `MultiTapeTM`, `Cfg`, `step`, `configs`, `outputSymbol`,
  `outputString`, `initCfg`, `spaceUsed`, `spaceUsedByTape`,
  `visitedByTapeHead`, `moveInputPos`; mathlib's `finTwoEquiv : Fin 2 ≃ Bool`,
  `Equiv.toEmbedding`, `Fin.cast`.
- Produces: `bitEmb`, `relabel`, `relabelCfg`, `inputSymbol_relabel`,
  `workTapeSymbols_relabel`, `step_relabel`, `configs_relabel`,
  `outputSymbol_relabel`, `outputString_relabel`, `initCfg_relabel`,
  `spaceUsed_relabel`.

- [ ] **Step 1: Write**

```lean
/-- Bits as the two machine symbols. -/
@[expose] def bitEmb : Bool ↪ Fin 2 := finTwoEquiv.symm.toEmbedding

/-- A machine over bits and any state type, relabeled over the two symbols and
an initial segment of the naturals along an equivalence of its states. -/
@[expose] def relabel {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) {s : ℕ}
    (eS : State ≃ Fin s) : MultiTapeTM k (Fin 2) (Fin s) where
  q₀ := eS tm.q₀
  tr q inp work :=
    let o := tm.tr (eS.symm q) (inp.map finTwoEquiv) fun i ↦ (work i).map finTwoEquiv
    { inputMove := o.inputMove
      workActions := fun i ↦ ((o.workActions i).1.map (Option.map bitEmb), (o.workActions i).2)
      outS := o.outS.map bitEmb
      q' := o.q'.map eS }

/-- A configuration relabeled. -/
@[expose] def relabelCfg {k : ℕ} {State : Type} {input : List Bool} {s : ℕ} (eS : State ≃ Fin s)
    (cfg : Cfg k Bool State input) : Cfg k (Fin 2) (Fin s) (input.map bitEmb) where
  state := cfg.state.map eS
  inputPos := Fin.cast (by rw [List.length_map]) cfg.inputPos
  workTapes := fun i z ↦ (cfg.workTapes i z).map bitEmb
  workTapePos := cfg.workTapePos

theorem inputSymbol_relabel ... : (relabelCfg eS cfg).inputSymbol = cfg.inputSymbol.map bitEmb
theorem workTapeSymbols_relabel ... : (relabelCfg eS cfg).workTapeSymbols i = (cfg.workTapeSymbols i).map bitEmb := rfl
theorem step_relabel ... : (relabel tm eS).step (relabelCfg eS cfg) = relabelCfg eS (tm.step cfg)
theorem configs_relabel ... (t : ℕ) : (relabel tm eS).configs (relabelCfg eS cfg) t = relabelCfg eS (tm.configs cfg t)
theorem outputSymbol_relabel ... : (relabel tm eS).outputSymbol (relabelCfg eS cfg) = (tm.outputSymbol cfg).map bitEmb
theorem outputString_relabel ... (t : ℕ) : (relabel tm eS).outputString (relabelCfg eS cfg) t = (tm.outputString cfg t).map bitEmb
theorem initCfg_relabel ... (input : List Bool) : (relabel tm eS).initCfg (input.map bitEmb) = relabelCfg eS (tm.initCfg input)
theorem spaceUsed_relabel ... (t : ℕ) : (relabel tm eS).spaceUsed (relabelCfg eS cfg) t = tm.spaceUsed cfg t
```

(Write each with the full binder list
`{k : ℕ} {State : Type} {input : List Bool} {s : ℕ}`
`(tm : MultiTapeTM k Bool State) (eS : State ≃ Fin s)`
`(cfg : Cfg k Bool State input)` and a docstring.)

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

- `inputSymbol_relabel`: `unfold Cfg.inputSymbol`; the two `dite`s on the
  relabeled position agree with the originals (`Fin.ext_iff`, `Fin.coe_cast`,
  `List.length_map`); in the third branch `List.getElem_map`.
- `step_relabel`: `cases hq : cfg.state`; the `none` branch is `rfl` after
  `unfold step` on both sides (`Option.map` of `none`); the `some q` branch:
  `unfold step`, `rw [inputSymbol_relabel]`, the relabeled transition is
  `tm.tr q ...` after `Equiv.symm_apply_apply` (on states), `Option.map_map` and
  `finTwoEquiv (bitEmb b) = b` (`Equiv.apply_symm_apply`; state it once
  as `have hb : ∀ b, finTwoEquiv (bitEmb b) = b :=`
  `fun b ↦ Equiv.apply_symm_apply _ _`
  and `Option.map_map`/`Option.map_id'`); then `Cfg.ext`: state by `rfl`,
  `inputPos` by a lemma `moveInputPos_cast (h : n = m) (p) (d) :`
  `moveInputPos (Fin.cast (by omega) p) d = Fin.cast _ (moveInputPos p d)`
  (`Fin.ext`; `unfold moveInputPos`; both `dite`s on the same `ℤ` value) —
  add it to this module; `workTapes` by `funext i z` with a `match` on the
  action's write (`none`: `rfl`; `some s`: `Function.update_apply` on both
  sides, `Option.map`), `workTapePos` by `rfl`.
- `configs_relabel`: `Nat.rec` with `configs_succ_eq_step'` and `step_relabel`.
- `outputSymbol_relabel`: `cases cfg.state`; `rfl` after `unfold outputSymbol`
  and the symbol-map identities as in `step_relabel`.
- `outputString_relabel`: `Nat.rec` with `outputString_succ`, `List.map_append`,
  `configs_relabel`, `outputSymbol_relabel`, and `Option.toList_map`-style
  `(o.map f).toList = o.toList.map f` (`cases o <;> rfl`).
- `initCfg_relabel`: `Cfg.ext`; `Fin.cast` of `1` is `1` (`Fin.ext`,
  `Fin.val_one`, `Fin.coe_cast`); tapes `none.map = none`.
- `spaceUsed_relabel`: `unfold spaceUsed spaceUsedByTape visitedByTapeHead`
  (check `visitedByTapeHead`'s definition: a `Finset.image` of `workTapePos`
  over `Finset.range`); `Finset.sum_congr rfl`; `configs_relabel` and the
  `workTapePos` field of `relabelCfg` (`rfl`).

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): relabel machines over the two symbols and finite states

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 7: the theorem (`Main.lean`)

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Main.lean`
- Modify: `Machine.lean` (import after `Transport`), `GebMeta.lean` (allowlist
  after `...Machine.Transport`).

**Interfaces:**

- Consumes: `machine`, `machine_emits`, `bound`, `time`, `tapes`, `State`,
  `isPolyBounded_stepBound`, `isPolyBounded_shift`, `isPolyBounded_add`,
  `isPolyBounded_mul`, `isPolyBounded_const`, `isPolyBounded_id`,
  `isPolyBounded_max`, `nsi_sem`, `relabel`, `configs_relabel`,
  `outputString_relabel`, `initCfg_relabel`, `spaceUsed_relabel`,
  `Emits.spaceUsed_le`, `bitEmb`, `FinEnum.equiv`, `FinEnum.card`.
- Produces: `computableInTimeAndSpace_sem`.

- [ ] **Step 1: Write**

```lean
/-- The machine's step count is polynomially bounded in the input length. -/
theorem isPolyBounded_time (e : SOf 1) : IsPolyBounded (time e) :=
  isPolyBounded_add (isPolyBounded_add
      (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 3) isPolyBounded_id)
        (isPolyBounded_const 5))
      (isPolyBounded_shift _ (isPolyBounded_stepBound e.1.1)))
    (isPolyBounded_add (isPolyBounded_mul (isPolyBounded_const 2)
      (isPolyBounded_max isPolyBounded_id (isPolyBounded_const _))) (isPolyBounded_const 3))

/-- The meaning of a unary expression is computable by a multi-tape machine in
polynomial time and linear space: the machine reading of
{cite}`Mazzanti2016` Theorem 5.7, by the compiled program of the expression
rather than the paper's Theorem 5.3 encoding into a single recursion. -/
theorem computableInTimeAndSpace_sem (e : SOf 1) :
    ∃ c d : ℕ, ComputableInTimeAndSpace (fun w ↦ e.sem ![w])
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (n + 1)) := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`obtain ⟨c₁, d, hd⟩ := isPolyBounded_time e`; `K := nsiConst e.1.1`;
`c₂ := tapes e * (K + 2)`;
`refine ⟨max c₁ c₂, d, tapes e, 2, FinEnum.card (State e), bitEmb,`
`relabel (machine e) FinEnum.equiv, fun w ↦ ?_⟩`.
`obtain ⟨cfg', t', ht', h⟩ := machine_emits e w`; `n := w.length`.
`refine ⟨t', ?_, (relabel _ _).spaceUsed (initCfg _) t', ?_, ?_, ?_, rfl⟩`:

- time: `t' ≤ time e n` (unfold `time` and `bound`) from `ht'` and
  `|e.sem ![w]| ≤ bound e n`
  (`nsi_sem e ![w] n (fun i ↦ by rw [Fin.fin_one_eq_zero i]; exact le_refl _)`),
  then `hd n`, then `Nat.mul_le_mul_right _ (Nat.le_max_left _ _)`.
- space: `rw [initCfg_relabel, spaceUsed_relabel]`; `Emits.spaceUsed_le h`
  gives `≤ tapes e * (bound e n + 2)`; `bound e n + 2 ≤ (K + 2) * (n + 1)`
  since `max n K ≤ n + K` (`Nat.max_le.mpr`), `n ≤ (K + 2) * n`
  (`Nat.le_mul_of_pos_left`), and `(K + 2) * (n + 1) = (K + 2) * n + (K + 2)`
  (`Nat.mul_succ`); then `Nat.mul_le_mul_left`, `Nat.mul_assoc`, and
  `Nat.mul_le_mul_right _ (Nat.le_max_right _ _)`.
- halted: `rw [initCfg_relabel, configs_relabel, h.configs_eq]`; the state is
  `cfg'.state.map _` with `h.halted`: `rw [h.halted]; rfl`.
- output: `rw [initCfg_relabel, outputString_relabel, h.output]`.

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): prove every unary expression polynomial-time linear-space

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 8a: an executable configuration (`Machine/Exec.lean`)

Iterating Cslib's `step` in compiled code is exponential in the step count:
every configuration's `workTapes` and `workTapePos` fields are closures over
the previous configuration, and each read re-enters the previous transition.
Measured on the recognizer's machine: 132 steps under a second, 138 steps
22 seconds, doubling per step. The test therefore runs a configuration whose
tapes are finite maps and whose heads are a vector, with a proof that it
simulates `step`.

**Files:**

- Create: `Geb/Prototypes/Computability/SizeBounded/Machine/Exec.lean`
- Modify: `Machine.lean` (import after `Main`), `GebMeta.lean` (allowlist
  `...Machine.Exec` after `...Machine.Main`).

**Interfaces:**

- Consumes: Cslib's `Cfg`, `step`, `step_of_halt`, `outputSymbol`,
  `initCfg`, `configs`, `configs_succ_eq_step'`, `moveInputPos`,
  `Cfg.inputSymbol`, `Cfg.workTapeSymbols`; `Program.lean`'s
  `step_of_state`; core `Vector` (`Vector.ofFn`, `Vector.replicate`,
  `Vector.getElem_ofFn`, `Vector.getElem_replicate`, `Fin.getElem_fin`);
  `Std.HashMap` (`insert`, `erase`, `getElem?_insert`, `getElem?_erase`,
  `getElem?_emptyc`, from `Std.Data.HashMap.Lemmas`).
- Produces: `ExecCfg`, `ExecCfg.toCfg`, `ExecCfg.init`, `writeCell`,
  `execStep`, `execOutputSymbol`, `toCfg_init`, `toCfg_execStep`,
  `execOutputSymbol_eq`, `toCfg_execStep_iterate`.

- [ ] **Step 1: Write**

```lean
/-- A configuration with materialized tapes: each tape a finite map from cells
to bits, blank where absent, the heads a vector. -/
structure ExecCfg (k : ℕ) (State : Type) (input : List Bool) where
  /-- The state, {lit}`none` when halted. -/
  state : Option State
  /-- The input head's position, shifted by one as in {name}`Turing.MultiTapeTM.Cfg`. -/
  inputPos : Fin (input.length + 2)
  /-- The tapes. -/
  tapes : Vector (Std.HashMap ℤ Bool) k
  /-- The heads. -/
  heads : Vector ℤ k

/-- The configuration an executable configuration denotes. -/
@[expose] def ExecCfg.toCfg {k : ℕ} {State : Type} {input : List Bool}
    (c : ExecCfg k State input) : Cfg k Bool State input :=
  { state := c.state
    inputPos := c.inputPos
    workTapes := fun i z ↦ c.tapes[i][z]?
    workTapePos := fun i ↦ c.heads[i] }

/-- The initial executable configuration: blank tapes, parked heads. -/
@[expose] def ExecCfg.init {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State)
    (input : List Bool) : ExecCfg k State input :=
  ⟨some tm.q₀, 1, Vector.replicate k ∅, Vector.replicate k 0⟩

/-- A tape after one action at a cell: unchanged, erased, or written. -/
@[expose] def writeCell (tape : Std.HashMap ℤ Bool) (z : ℤ) :
    Option (Option Bool) → Std.HashMap ℤ Bool
  | none => tape
  | some none => tape.erase z
  | some (some b) => tape.insert z b

/-- The symbols under the heads. -/
@[expose] def ExecCfg.symbols {k : ℕ} {State : Type} {input : List Bool}
    (c : ExecCfg k State input) (i : Fin k) : Option Bool :=
  c.tapes[i][c.heads[i]]?

/-- One step, with every field computed once. -/
@[expose] def execStep {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (c : ExecCfg k State input) : ExecCfg k State input :=
  match c.state with
  | none => c
  | some q =>
    let o := tm.tr q c.toCfg.inputSymbol c.symbols
    { state := o.q'
      inputPos := moveInputPos c.inputPos o.inputMove
      tapes := Vector.ofFn fun i ↦ writeCell c.tapes[i] c.heads[i] (o.workActions i).1
      heads := Vector.ofFn fun i ↦ c.heads[i] + (o.workActions i).2 }

/-- The symbol emitted by one step. -/
@[expose] def execOutputSymbol {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (c : ExecCfg k State input) : Option Bool :=
  match c.state with
  | none => none
  | some q => (tm.tr q c.toCfg.inputSymbol c.symbols).outS

/-- The initial executable configuration denotes the initial configuration. -/
theorem toCfg_init {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) (input : List Bool) :
    (ExecCfg.init tm input).toCfg = tm.initCfg input := _

/-- The symbols under the heads are the denoted configuration's. -/
theorem symbols_eq {k : ℕ} {State : Type} {input : List Bool} (c : ExecCfg k State input) :
    c.symbols = c.toCfg.workTapeSymbols := rfl

/-- One executable step denotes one step. -/
theorem toCfg_execStep {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State)
    (c : ExecCfg k State input) : (execStep tm c).toCfg = tm.step c.toCfg := _

/-- The emitted symbol is the denoted configuration's. -/
theorem execOutputSymbol_eq {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (c : ExecCfg k State input) :
    execOutputSymbol tm c = tm.outputSymbol c.toCfg := _

/-- Iterated executable steps denote the configurations. -/
theorem toCfg_execStep_iterate {k : ℕ} {State : Type} {input : List Bool}
    (tm : MultiTapeTM k Bool State) (c : ExecCfg k State input) :
    ∀ t : ℕ, ((execStep tm)^[t] c).toCfg = tm.configs c.toCfg t := _
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Prove**

`toCfg_init`: `Cfg.ext`; the tape field is `funext i z` with
`Vector.getElem_replicate` and `Std.HashMap.getElem?_emptyc`; the head field
likewise with `Vector.getElem_replicate`.

`toCfg_execStep`: `cases hq : c.state`. Halted: `unfold execStep`, `rw [hq]`,
and `step_of_halt` on the right (`c.toCfg.state = none` by `hq`). Live:
`rw [step_of_state _ _ q hq]` on the right (the state of `c.toCfg` is
`c.state`), `unfold execStep`, `rw [hq]`, `Cfg.ext`; `state` and `inputPos` by
`rfl` (`symbols_eq` identifies the transition's third argument); `workTapes`
by `funext i z`, `Vector.getElem_ofFn`, then `cases (o.workActions i).1`
(after naming `o`): `none` is `rfl`, `some none` is
`Std.HashMap.getElem?_erase` against `Function.update_apply` with
`beq_iff_eq` and `by_cases` on `z = c.heads[i]` (allowlisted module),
`some (some b)` is `Std.HashMap.getElem?_insert` likewise; `workTapePos` by
`funext i` and `Vector.getElem_ofFn`.

`execOutputSymbol_eq`: `cases hq : c.state`; both sides reduce
(`unfold execOutputSymbol outputSymbol`, `rw [hq]`; `symbols_eq`).

`toCfg_execStep_iterate`: `Nat.rec` with `Function.iterate_succ_apply'`,
`toCfg_execStep`, `configs_succ_eq_step'`.

- [ ] **Step 4: Import, allowlist, `lake build GebMeta`, build, lint**

`Exec.lean` imports: `public import ...Machine.Program` (for
`step_of_state` if a statement mentions it; otherwise plain) and
`public import Std.Data.HashMap.Lemmas` (or whatever module supplies
`Std.HashMap` and its lemmas; check `lake shake` accepts it).

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
feat(computability): add an executable configuration that simulates the step

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 8: the executed compiler (`GebTests/.../SizeBounded/Machine.lean`)

**Files:**

- Create: `GebTests/Prototypes/Computability/SizeBounded/Machine.lean`
- Modify: `GebTests/Prototypes/Computability/SizeBounded.lean` (add the
  import), `GebMeta.lean` (allowlist
  `GebTests.Prototypes.Computability.SizeBounded.Machine` beside the other
  `GebTests.*` entries).

**Interfaces:**

- Consumes: `machine`, `time`, `isBitTree`, `Geb.BitTree.validBool`,
  `ExecCfg.init`, `execStep`, `execOutputSymbol`.
- Produces: the module.

The step bound `time isBitTree n` is of the order of `10^7` already at
`n = 5`, so the machine is run to its actual halt by a fuelled loop over the
executable configuration of Task 8a (Cslib's `step` iterated in compiled code
is exponential in the step count). The recognizer's value is `[true]` on an
encoding and `[]` otherwise
(`isBitTree.sem ![y] = if ... then [true] else []` in
`SizeBounded/BitTree.lean`), never `[false]`.

- [ ] **Step 1: Write**

```lean
module

public import Geb.Prototypes.Computability.SizeBounded.Machine -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.SizeBounded.Machine -- shake: keep; #guard needs it
public import Geb.Prototypes.Computability.SizeBounded.BitTree -- shake: keep; #guard needs it
public meta import Geb.Prototypes.Computability.BitTree.Scanner -- shake: keep; #guard needs it

/-!
# The bit-tree recognizer's machine on worked bitstrings

The compiled machine of the recognizer, stepped until it halts, emits the
recognizer's value on each of the worked words of the recognizer's test module.

## Main statements

The machine halts within its step bound and its output on each word is the
recognizer's value there: `[true]` on an encoding, `[]` otherwise.

## Tags

non-size-increasing, Turing machine, compilation, recognizer
-/

set_option linter.privateModule false

open Geb.SizeBounded Geb.SizeBounded.Machine Turing MultiTapeTM

/-- The recognizer's machine, named so that this module references a constant of
the module under test. -/
def bitTreeMachine := machine isBitTree

/-- Step a machine until it halts, collecting its output in reverse; `none`
when the fuel runs out first. -/
def stepUntilHalt {k : ℕ} {State : Type} {input : List Bool} (tm : MultiTapeTM k Bool State) :
    ℕ → ExecCfg k State input → List Bool → Option (List Bool)
  | 0, _, _ => none
  | fuel + 1, c, acc =>
    match c.state with
    | none => some acc.reverse
    | some _ =>
      stepUntilHalt tm fuel (execStep tm c) ((execOutputSymbol tm c).toList.reverse ++ acc)

/-- The machine's output on a word, run to its halt within its step bound. -/
def run (w : List Bool) : Option (List Bool) :=
  stepUntilHalt bitTreeMachine (time isBitTree w.length + 1) (ExecCfg.init bitTreeMachine w) []

/-- The recognizer's value on a word. -/
def expected (w : List Bool) : Option (List Bool) :=
  some (if Geb.BitTree.validBool w then [true] else [])

#guard run [false, false] = expected [false, false]
```

and one `#guard` per remaining worked word of
`GebTests/Prototypes/Computability/SizeBounded/BitTree.lean`'s `workedWords`
(`[false, true, true, false]`, `[true, false, false, false, false]`, `[]`,
`[true]`, `[true, false, false]`, `[false, false, false, false]`,
`[true, true, true]`), each on one line under 100 characters. The two
`public meta import`s are the ones a first attempt measured as required
(`(program isBitTree).State` must be visible downstream; `validBool` lives
in `BitTree.Scanner`); keep whichever the build demands and drop the rest.

- [ ] **Step 2: Build and measure**

Run: `time lake build GebTests.Prototypes.Computability.SizeBounded.Machine`
and record the wall time. If `#guard` fails to elaborate for a module-system
reason, the message names the inaccessible constant: add the
`public meta import` it asks for. If a `#guard` evaluates to `false`, print
`run w` for that word with a scratch `#eval` (a throwaway file, not
committed) and report BLOCKED with the value: `none` means the machine did
not halt within its bound, which contradicts `machine_emits`; `some out`
with a wrong `out` means the compiler or the test is wrong. If evaluation
takes minutes, report the time and BLOCKED; do not reduce the fuel below
the bound, since the bound is what the theorem promises.

- [ ] **Step 3: Import, allowlist, `lake build GebMeta`,
  `lake build GebTests`, `lake lint`**

- [ ] **Step 4: Commit**

```bash
jj commit -m "$(cat <<'MSG'
test(computability): run the recognizer's compiled machine on worked words

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 9: close the phase runs by the family lemma

**Files:**

- Modify: `Machine/Phase/Return.lean` (`moveLeft_runsTo`, `retLeft_runsTo`),
  `Phase/Clear.lean` (`walkEnd_runsTo`, `blankLeft_runsTo`),
  `Phase/Walk.lean` (`copyWalk_runsTo`, `revWalk_runsTo`),
  `Phase/Sbs.lean` (`sbsWalk_runsTo`), `Phase/Write.lean`
  (`writeBit_runsTo`, `constWalk_runsTo`), `Phase/Input.lean` and
  `Phase/Output.lean` if any of their proofs did not use the family lemma.

**Interfaces:**

- Consumes: `RunsTo.ofFamily`. Produces: the same lemmas, statements unchanged.

- [ ] **Step 1: Rewrite each closing block**

Every phase proof ends with a
`key : ∀ s ≤ n, configs cfg s = f s ∧ outputString cfg s = []`
by `Nat.rec` and an assembly of the `RunsTo` fields (renested by Task 1);
replace both by one
application `RunsTo.ofFamily _ (f) n B _ hlive hstep hhalt rfl hout hpos hpos'`
after `rw [← hzero]` (the family at `0` is `cfg`), keeping the `hstep`,
`hhalt`, `hout`, `hzero` facts the proof already proves. A one-step machine
(`moveLeft`, `writeBit`, `blankLeft` if so) uses `n := 0`. Statements do not
change. If a proof's shape does not fit within an hour of work, leave it and
name it in the report.

- [ ] **Step 2: Build, lint** (no `GebMeta` change).

- [ ] **Step 3: Commit**

```bash
jj commit -m "$(cat <<'MSG'
refactor(computability): close the phase runs by the family lemma

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Pp8LEMe1s1jeYUCEEhMUUt
MSG
)"
jj bookmark set feat/size-bounded-machine -r @-
```

---

### Task 10: documentation

**Files:**

- Modify: `docs/index.md` (after the `SizeBounded/Cost.lean` entry),
  `TODO.md` (§ The non-size-increasing algebra as the resource discipline),
  `Geb/Prototypes/Computability/SizeBounded/Machine/Compile/Theorem.lean` and
  `Machine/Main.lean` (citations), `Geb/Prototypes/Computability/SizeBounded/BitTree.lean`
  and `docs/index.md`'s `BitTree.lean` entry (the sentence "The polynomial-time,
  linear-space reading is [Mazzanti2016] Theorem 5.7, cited and not reproved"
  now points at `computableInTimeAndSpace_sem`).

- [ ] **Step 1: `docs/index.md`**

Add entries, in this order, each in the style of the `SizeBounded/Cost.lean`
entry (path in backticks, prose naming the main declarations with their full
names, "Depends on `...`", and the choice status in the wording the
`BitTreeScanner/Bound.lean` entry uses for a module that depends on
`Classical.choice` through Cslib's `spaceUsed`):

1. `Geb/Prototypes/Computability/SizeBounded/Machine.lean` — the machine
   calculus: registers in the reversed layout (`Geb.SizeBounded.Machine.tapeOf`),
   the contracts `Geb.SizeBounded.Machine.RunsTo`, `Geb.SizeBounded.Machine.Emits`
   and `Geb.SizeBounded.Machine.Transforms`, sequencing
   `Geb.SizeBounded.Machine.seq` and `Geb.SizeBounded.Machine.seqFin` with
   their lifting lemmas, and the family lemma `Geb.SizeBounded.Machine.Emits.ofFamily`.
2. `.../Machine/Phase.lean` — the phase machines, each with its closed-form run.
3. `.../Machine/Primitives.lean` — `copy`, `const`, `sbs`, `copyRev` and their
   `Transforms` contracts.
4. `.../Machine/Loop.lean` — `caseLoop`, `loopF`, `Transforms.caseLoop`.
5. `.../Machine/Compile.lean` — `compile`, `stepBound`, `Correct`,
   `SOf.correct`.
6. `.../Machine/Bound.lean` — `regsBound`, `isPolyBounded_stepBound`.
7. `.../Machine/Wrapper.lean` — `reader`, `writer`, `machine`, `machine_emits`.
8. `.../Machine/Transport.lean` — `relabel` and its commutation lemmas.
9. `.../Machine/Main.lean` — `computableInTimeAndSpace_sem`, the machine
   reading of [Mazzanti2016] Theorem 5.7.

- [ ] **Step 2: `TODO.md`**

In the section's intro, replace "What is cited rather than proved is the
paper's Theorem 5.7, the machine-level polynomial-time and linear-space reading
of membership." by a sentence stating that
`Geb.SizeBounded.Machine.computableInTimeAndSpace_sem` proves that reading for
every unary expression by a compiled multi-tape machine. Delete the first
follow-up bullet ("`SizeBounded/Cost.lean` proves the paper's Lemma 2.2 ...
The machine bound remains: ...") down to "at a polynomial and a linear
function." Keep the other bullets.

- [ ] **Step 3: citations**

`Compile/Theorem.lean`'s module docstring: a sentence that `SOf.correct` is the
compiler's half of the soundness of {cite}`Mazzanti2016` Theorem 5.7, the
compiler replacing the paper's Theorem 5.3 encoding of simultaneous recursion
into a single recursion. `Main.lean` already cites in `computableInTimeAndSpace_sem`'s
docstring; its module docstring cites likewise. `BitTree.lean`'s module
docstring and `docs/index.md`'s `BitTree.lean` entry: "cited and not reproved"
becomes a pointer to `computableInTimeAndSpace_sem`.

- [ ] **Step 4: `markdownlint-cli2 docs/index.md TODO.md`; build (docstrings
  are checked)**

- [ ] **Step 5: Commit**

```bash
jj commit -m "$(cat <<'MSG'
doc(computability): index the machine bound and cite its theorem

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
Expected: exit 0 (the docs-coverage reminder is satisfied by Task 10). Fix
what it reports in a further `fix(computability)` commit.

- [ ] **Step 2: Report**

State which tasks are complete, the measured outcome of Task 8's `#guard`
(compiled evaluation, or the `decide` fallback with its cost), any phase Task 9
left unrewritten, and what the completeness assessment
(FPTIMELINSPACE ∩ NSI ⊆ S) can build on: `computableInTimeAndSpace_sem`,
`Correct`, and the absence of any lower-bound or machine-to-expression
machinery.
