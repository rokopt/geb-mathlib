<!-- markdownlint-disable-next-line MD041 -->
# B5 machine precedent: mathlib's Turing-machine idiom

Findings from reading mathlib's two concrete Turing-machine constructions
with step lemmas,
`Mathlib/Computability/TuringMachine/ToPartrec.lean`
(`Turing.PartrecToTM2`, a TM2 machine simulating partial recursive
functions) and
`Mathlib/Computability/TuringMachine/StackTuringMachine.lean`
(`Turing.TM2` and `Turing.TM2to1`, the TM2 model and its TM1 emulator),
against what Tasks 7 to 11 of
[2026-08-13-b5-time-space-bound-plan.md](2026-08-13-b5-time-space-bound-plan.md)
need. The two files use a different concrete API from Cslib's
`Turing.MultiTapeTM`/`Cfg`/`configs`; no lemma name below is available to
cite directly. Each finding states what transfers as method, and, for a
finding resting on the `induction` tactic, its recursor-application form,
since `docs/rules/lean-coding.md` § Recursion and induction through
recursors bars `induction`.

- **Transfers: one named resolution lemma per transition case, closed by
  `rfl` after the state argument is pinned.**
  `Turing.PartrecToTM2.tr_move`, `.tr_push`, `.tr_read`, `.tr_clear`,
  `.tr_copy`, `.tr_succ`, `.tr_pred`, `.tr_ret_cons₁`, `.tr_ret_cons₂`,
  `.tr_ret_comp`, `.tr_ret_fix`, `.tr_ret_halt`
  (`ToPartrec.lean`, lines 346–399) each state
  `tr (Λ'.<constructor> …) = <literal Stmt'> := rfl` and are marked
  `@[simp]`; every later proof cites the relevant one by name rather than
  unfolding `tr`. This is the shape of Task 6's ten `tr_*`
  transition-resolution lemmas. It does not transfer as a *resolution
  route*: `tr` there dispatches by matching an inductive constructor of
  `Λ'`, so each case closes by `rfl` on the pattern match alone. The tree
  scanner's `treeScanner.tr` dispatches by an `ite` chain on `Fin 4`
  equality (Task 2 Step 2's measured encoding), which does not reduce by
  a bare pattern-match `rfl`; the plan's own `step_of_state`—naming the
  state via an equality hypothesis before rewriting—is what discharges
  the case split there, and has no analogue needed in `ToPartrec.lean`.

- **Does not transfer: automatic per-constructor equation-lemma simp
  sets.** `StackTuringMachine.lean` registers
  `attribute [simp] stepAux.eq_1 stepAux.eq_2 stepAux.eq_3 stepAux.eq_4
  stepAux.eq_5 stepAux.eq_6 stepAux.eq_7 step.eq_1 step.eq_2`
  (lines 175–176), exposing `Turing.TM2.stepAux` and `Turing.TM2.step`'s
  auto-generated equation lemmas—one per constructor of the matched
  argument—as a simp set, in place of hand-stated resolution theorems.
  This shortcut is available only because the matched argument is an
  inductive type. `treeScanner.tr`'s outer dispatch is not an inductive
  match, so it has no such generated equations to register; Task 6's ten
  lemmas must be hand-stated and hand-proved, as the plan already does.

- **Transfers, with a recursor form: reaching a configuration after many
  steps, proved by recursion on the exact step count, one step per
  case.**
  `Turing.TM2to1.tr_respects_aux₁` (`StackTuringMachine.lean`,
  lines 639–652) proves, for `n ≤ S.length`, a `Reaches₀` from a fixed
  configuration to itself after `n` explicit rightward tape moves, by
  `induction n with | zero => rfl | succ n IH => apply (IH
  (le_of_lt H)).tail; …`. The successor case obtains the `n`-step result
  from `IH`, then appends one more step by a `simp only` unfolding
  `TM1.step`/`TM1.stepAux`/`tr` and a small rewrite chain. This is the
  mathlib declaration structurally closest to Task 7's `configs_seek` and
  Task 10's `configs_sweep`: the step count is the induction's own index,
  the base case closes by reflexivity, the successor case defers to the
  hypothesis and then discharges one further step. The recursor form of
  `induction n with | zero => tac₀ | succ n IH => tac₁` is
  `refine Nat.rec ?_ (fun n IH ↦ ?_) n` (or, where the statement carries
  a `generalizing` clause, the generalised variables become universal
  quantifiers in the motive before the `Nat.rec` application, so that
  `IH` already has the right type)—the same shape Task 10's
  `configs_sweep` statement is written in directly, carrying
  `∀ k, ∀ h : k + j = w.length, …` in the motive rather than generalising
  after the fact.

- **Transfers, with a recursor form: reaching a configuration after many
  steps, proved by recursion on a decreasing structural measure, not on
  the step count.**
  `Turing.PartrecToTM2.move_ok` (`ToPartrec.lean`, lines 584–610) proves
  a `Reaches₁` by `induction L₁ generalizing S s with | nil => … | cons a
  L₁ IH => refine TransGen.head rfl ?_; …`; each case discharges exactly
  one `TM2.step` (`TransGen.head`/`TransGen.head'`) and defers the rest
  to `IH`. `Turing.PartrecToTM2.clear_ok` and `.copy_ok` (lines 639–666
  and 669–682) follow the same shape, with the recursion running over a
  list rather than over the step count directly. The recursor-application
  form of `induction L₁ generalizing S s with | nil => tac₀ | cons a L₁
  IH => tac₁` is `refine List.rec (motive := fun L₁ ↦ ∀ S s, …) ?_ (fun a
  L₁ IH ↦ fun S s ↦ ?_) L₁`: the `generalizing` clause is exactly the
  motive's leading `∀`-binders. This is the general translation every
  `induction … generalizing … with` in these two files needs before it
  transfers to the barred-`induction` discipline; none of Tasks 7–11's
  own recursions is over a list, but the translation rule is what a
  reader applies to any further mathlib idiom found later that rests on
  `induction`.

- **Does not transfer: relational, existentially witnessed configuration
  invariants.** `Turing.PartrecToTM2.TrCfg` (`ToPartrec.lean`,
  lines 546–549) relates a `Cfg` to a `Cfg'` by an existential over the
  emulator's incidental local-store value: `∃ s, c' = ⟨…, s, …⟩`. The
  preceding docstring (lines 542–545) states why: in normal operation the
  local store holds "an arbitrary garbage value," so no equality pins it
  down. `Turing.PartrecToTM2.trNormal_respects` and `.tr_ret_respects`
  (lines 841–874, 877–930) state their conclusions as `∃ b₂, TrCfg (…)
  b₂ ∧ Reaches₁ (TM2.step tr) ⟨…⟩ b₂`—existential in both the target
  configuration and the step count. `seekCfg`, `plantCfg` and `sweepCfg`
  have no incidental field: every field is a closed form, so the
  configuration equalities Tasks 7–10 need
  (`treeScanner.configs (…) j = sweepCfg w k h`) are strictly stronger
  and already the design's commitment. A relational invariant is
  unneeded here and importing the pattern would weaken what is already
  provable.

- **Does not transfer: exact step-count composition across phases.**
  `Turing.PartrecToTM2.tr_eval` (`ToPartrec.lean`, line 945) and the
  `trNormal_respects`/`tr_ret_respects` lemmas it composes state
  correctness via `Reaches₁`/`TransGen`, which witness that some finite
  positive number of steps connects two configurations without counting
  or bounding that number. Composition is by `TransGen.head`/`.trans`/
  `Reaches₀.tail` (for example `trNormal_respects`'s `cons` case, lines
  856–863, which chains `move_ok`, a rewrite, `copy_ok`, and the
  recursive call by `TransGen.head rfl <| (move_ok …).trans ?_`). No
  lemma in either file states or composes an exact numeral step count;
  there is no analogue
  of `configs_add`/`configs_succ_eq_step'`/`outputString_add_eq_append`
  to transcribe, and Task 11's `2 * w.length + 3` composition is
  unprecedented in either file. What transfers is only the shape common
  to both: decompose a run into named phases, discharge each by a lemma
  about that phase alone, and compose last by the closure operator's own
  transitivity or head lemma—which is already how Task 11 is
  structured, with `configs_add` and the phase theorems in the role
  `TransGen.trans` and `move_ok`/`copy_ok`/`head_stack_ok` play here.

- **Transfers as an idiom, not as a literal lemma: name a field-update
  fact once and cite it everywhere, rather than re-deriving it inline.**
  `Turing.PartrecToTM2.K'.elim_update_main`, `.elim_update_rev`,
  `.elim_update_aux`, `.elim_update_stack` (`ToPartrec.lean`,
  lines 522–536) each state `Function.update (K'.elim a b c d) k v =
  K'.elim (… updated …)` for one of the four stacks, closed once by
  `funext x; cases x <;> rfl`; every subsequent step-composition lemma
  (`move_ok`, `copy_ok`, `succ_ok`, `pred_ok`) cites the relevant one by
  `simp only` instead of re-deriving the update. Cslib's `workTapes`
  field is a `ℤ`-indexed function rather than a four-constructor sum, so
  the update fact is per-position (`sweepCfg_workTapes`) rather than
  per-tape, and Task 9's `have hw : … workTapeSymbols = fun _ ↦ …`
  pattern already plays the same role for the read side. The
  transferable point is economy of statement—prove the update or read
  fact once, before the step lemmas that need it, and cite it by name—
  which is also Task 6's own stated reason for factoring the
  transition-resolution lemmas out of the step lemmas in the first
  place.
