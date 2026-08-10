# Ranked-alphabet tree encoding — session handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Read these first](#read-these-first)
- [Where the branch stands](#where-the-branch-stands)
- [Compiler facts established by building](#compiler-facts-established-by-building)
- [What remains in B1](#what-remains-in-b1)
  - [B1-a: the image characterisation](#b1-a-the-image-characterisation)
  - [B1-b: `Ranked/Binary.lean`](#b1-b-rankedbinarylean)
  - [B1-c: test mirrors](#b1-c-test-mirrors)
  - [B1-d: indices, docs, bibliography](#b1-d-indices-docs-bibliography)
  - [B1-e: rewrite the plan from what built](#b1-e-rewrite-the-plan-from-what-built)
  - [B1-f: follow-on notes and artifact removal](#b1-f-follow-on-notes-and-artifact-removal)
- [Outstanding review findings not yet applied](#outstanding-review-findings-not-yet-applied)
- [The remaining branches](#the-remaining-branches)
- [Process this session must follow](#process-this-session-must-follow)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Read these first

- `CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`, `docs/rules/lean-coding.md`,
  `docs/rules/upstream-eligible.md`, `docs/rules/markdown-writing.md`,
  `docs/rules/ci-and-workflow.md`.
- The spec: `docs/superpowers/specs/2026-08-09-ranked-tree-recognizers-design.md`.
  It is current as of two adversarial rounds and describes all five branches.
- The plan: `docs/superpowers/plans/2026-08-09-ranked-tree-encoding.md`. It is
  **stale in places** — it describes proof scripts that were superseded by
  what actually compiled. Treat the committed Lean as authoritative and
  rewrite the plan from it (B1-e below). Do not execute the plan's Tasks 1 to
  8 or 11; they are done or superseded.
- The three merged modules this work generalises:
  `Geb/Mathlib/Data/Tree/Binary.lean`, `Geb/Mathlib/Data/Tree/Preorder.lean`,
  `Geb/Mathlib/Computability/Cobham/{Basic,Tree}.lean`.

## Where the branch stands

Branch `feat/ranked-tree-recognizers`, six commits on `main`, nothing pushed:

1. `doc(cobham): spec the extensions of the tree recognizers`
2. `doc: record the tree-recognizer extensions workstream`
3. `doc(tree): plan the ranked-alphabet encoding branch`
4. `doc(tree): correct the spec against the first adversarial round`
5. `doc(tree): rewrite the plan against the first adversarial round`
6. `feat(tree): add the ranked-alphabet encoding and its descent`

Three modules build clean, and every declaration in them measures
`[propext, Quot.sound]`:

- `Geb/Mathlib/Data/Tree/Ranked/Basic.lean` — `RankedAlphabet` (fields
  `card`, `width`, `width_pos`, `card_le_two_pow_width`, `arity`), `Term`,
  `Term.mk`, `Term.size`, `size_mk`, `Term.induction`.
- `Geb/Mathlib/Data/Tree/Ranked/Code.lean` — `code`, `decodeBits`,
  `decodeBits_cons`, `arOf`, `length_code`, `mod_two_mul`, `decodeBits_code`,
  `arOf_decodeBits_code`, `testBit_decodeBits`.
- `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` — `spell`, `spell_mk`,
  `length_spell`, `width_le_length_spell`, `size_le_sum_ofFn`, `decodeBlock`,
  `parseChildren`, `parseChildren_succ`, `parseStep`, `parseAux`,
  `parseAux_succ`, `parse`, `decodeBlock_code_append`,
  `parseChildren_flatten`, `parseAux_spell`, `parse_spell`, `encoding`,
  `spell_injective`, `getElem_code_eq`, `decodeBlock_eq_some`,
  `parseChildren_eq_some`, `parseAux_eq_some`, `parse_eq_some_iff`, `Scan`,
  `scanStep`, `scanFrom`, `scanFinal`, `validBool`, `Valid` and its
  `DecidablePred` instance, `scanFrom_nil`, `scanFrom_cons`,
  `scanFrom_append`, `scanFrom_not_live`, `scanFrom_short`, `scanFrom_code`,
  `scanFrom_flatten`, `scanFrom_spell`, `valid_spell`.

Verify with:

```bash
lake build Geb.Mathlib.Data.Tree.Ranked.Preorder
```

## Compiler facts established by building

Each cost a failed build. Departing from one will not compile.

1. **`Term.mk R i ch`, never `R.Term.mk i ch`.** Generalized field notation
   resolves `R.Term` first, and a `Type` carries no `mk`.
2. **`Nat.mod_mul` depends on `Classical.choice`.** `Code.lean`'s
   `mod_two_mul` replaces it and is proved from `Nat.div_add_mod`,
   `Nat.mul_add_mod` and `Nat.mod_eq_of_lt`, all choice-free. `omega` cannot
   discharge the identity: the modulus is a variable. Expect the same trap in
   any further `Nat` division reasoning, and re-measure with
   `#print axioms` after each.
3. **`omega` proving a non-`False` goal can pull in `Classical.choice`.**
   `parseAux_spell`'s zero case uses
   `exact absurd hf (by rw [size_mk]; exact Nat.not_succ_le_zero _)`.
4. **`simp only [] at h` after a `split` is an error** (`simp made no
   progress`) — the `split` already iota-reduces the hypothesis. But
   `simp only []` on the **goal** is required in `parseChildren_flatten` and
   `parseAux_spell` to reduce a `match some …`.
5. **Import placement.** `List.sum_map_mul_left` is in
   `Mathlib.Algebra.BigOperators.Ring.List`, not `…Group.List` (which is a
   directory, not a module). `List.le_sum_of_mem` needs
   `Mathlib.Algebra.Order.BigOperators.Group.List` and routes through
   ordered-algebra instances the axiom rules warn about; `size_le_sum_ofFn`
   proves the needed bound directly instead, and that import is absent.
6. **`linter.flexible` is an error here**: a bare `simp` that modifies the
   goal must be terminal. **`linter.unnecessarySeqFocus` is an error**:
   `tac1 <;> tac2` where `tac1` leaves one goal fails.
7. **`decide` cannot be used on `parse w = some t`** — mathlib has no
   `DecidableEq (WType …)`. State such assertions through `Option.isSome` or
   by mapping `spell` over the result.
8. **Test modules** need `set_option linter.privateModule false` (the
   `GebTests/Mathlib/Data/Tree/Preorder.lean` pattern) or
   `@[expose] public section` (the `GebTests/Mathlib/CategoryTheory/FinCat/Basic.lean`
   pattern). Fixtures shared across test modules need **`public import`** of
   the module declaring them **and** `@[expose]`, or every downstream
   `decide` fails with the instance stuck.
9. **`![…]` needs `Mathlib.Data.Fin.VecNotation`**, or it parses as boolean
   negation applied to a list.
10. **A term at a concrete alphabet**: `fun i ↦ absurd i.isLt (by decide +revert)`
    discharges an empty child family; `fun i ↦ i.elim0` and `by omega` do not.
    A `Fin.cast` whose target is a metavariable does not elaborate — name the
    target with `show`.
11. **Sweep budgets**: `set_option maxRecDepth 100000 in decide` is valid in
    tactic position and is needed at 511 words; 127 words works at the
    default. `native_decide` is banned (compiler-trust axiom).

## What remains in B1

### B1-a: the image characterisation

This is the hard part, and every adversarial round flagged it. It goes in
`Preorder.lean` above the closing `end` / `end RankedAlphabet`.

Four lemmas, in this order:

```lean
/-- The residue of a successor, in terms of the residue. -/
theorem add_one_mod (a n : ℕ) (hn : 0 < n) :
    (a + 1) % n = if a % n + 1 = n then 0 else a % n + 1

/-- A live scan's incomplete block holds the word's length modulo the width:
block boundaries align with the word's right end. -/
theorem length_buf_scanFinal_of_live (R : RankedAlphabet) :
    ∀ w : List Bool, (R.scanFinal w).live = true →
      (R.scanFinal w).buf.length = w.length % R.width

/-- A live scan with something pending has read at least one block. -/
theorem width_le_length_of_live_of_buf_nil_of_one_le_depth (R : RankedAlphabet)
    (w : List Bool) (hlive : (R.scanFinal w).live = true)
    (hbuf : (R.scanFinal w).buf = []) (hd : 1 ≤ (R.scanFinal w).depth) :
    R.width ≤ w.length

/-- The converse of `scanFrom_code`: a live scan over a full block exhibits
that block as a symbol's code. -/
theorem exists_code_of_scanFrom_live (R : RankedAlphabet) (blk : List Bool)
    (s : Scan) (hlen : blk.length = R.width) (hbuf : s.buf = [])
    (hs : s.live = true) (h : (R.scanFrom blk s).live = true) :
    ∃ i : Fin R.card, R.code i = blk ∧ R.arity i ≤ s.depth ∧
      R.scanFrom blk s = ⟨[], s.depth - R.arity i + 1, true⟩
```

then the main argument:

```lean
theorem exists_spell_append_of_live_of_buf_nil_of_one_le_depth (R : RankedAlphabet) :
    ∀ (n : ℕ) (w : List Bool), w.length ≤ n →
      (R.scanFinal w).live = true → (R.scanFinal w).buf = [] →
      1 ≤ (R.scanFinal w).depth →
        ∃ t rest, R.spell t ++ rest = w ∧
          (R.scanFinal rest).live = true ∧ (R.scanFinal rest).buf = [] ∧
          (R.scanFinal rest).depth + 1 = (R.scanFinal w).depth

theorem eq_nil_of_live_of_buf_nil_of_depth_eq_zero (R : RankedAlphabet)
    (w : List Bool) (hlive : (R.scanFinal w).live = true)
    (hbuf : (R.scanFinal w).buf = []) (hd : (R.scanFinal w).depth = 0) : w = []

theorem exists_spell_of_valid (R : RankedAlphabet) {w : List Bool} (h : R.Valid w) :
    ∃ t, R.spell t = w

theorem valid_iff_exists_spell (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ ∃ t, R.spell t = w

theorem valid_iff_isSome_parse (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ (R.parse w).isSome
```

The last three are short and were already written out in the superseded plan;
copy them from there, correcting `parse_eq_some_iff.mp ht` to
`(parse_eq_some_iff R).mp ht` (`parse_eq_some_iff` takes `R` explicitly, so
its type is a `∀`, not an `Iff`).

**Split the leading block, not the trailing one.** `spell` is prefix
notation, so the head symbol's block is `w.take R.width`. Use
`w = w.take R.width ++ w.drop R.width`, whence
`scanFinal w = scanFrom (w.take R.width) (scanFinal (w.drop R.width))` by
`scanFrom_append`. A previous sketch split off the last block; that yields a
suffix decomposition, which is not what the goal asks for, and neither piece
is `scanFinal` of anything.

**Two failures already hit, so do not repeat them.** `add_one_mod`'s
`conv_lhs => rw [← Nat.div_add_mod a n, Nat.add_assoc, Nat.mul_add_mod]` left
unsolved goals; work the split out as a standalone `have` first, on the model
of `mod_two_mul`, which does compile. And in
`length_buf_scanFinal_of_live`'s completing branch, a `rw` chain through
`scanStep`/`hcomp`/`har`/`hle` failed to find its pattern; prefer a helper
lemma characterising one step —

```lean
theorem scanStep_buf_of_live (R : RankedAlphabet) (b : Bool) (s : Scan)
    (h : (R.scanStep b s).live = true) :
    s.live = true ∧
      (((b :: s.buf).length = R.width ∧ (R.scanStep b s).buf = []) ∨
        ((b :: s.buf).length ≠ R.width ∧ (R.scanStep b s).buf = b :: s.buf))
```

— proved once by `cases` on `s.live`, on `decide ((b :: s.buf).length = R.width)`,
on `R.arOf …` and on `decide (r ≤ s.depth)`, and then used by both
`length_buf_scanFinal_of_live` and `exists_code_of_scanFrom_live`. The
liveness sub-case that does work is `simp only [scanStep, hc] at hlive`,
which closes the goal outright by reducing the hypothesis to `False`.

`exists_code_of_scanFrom_live` is provable from `scanFrom_short` plus the
`Code.lean` machinery: from `arOf (decodeBits blk) = some r` conclude
`decodeBits blk < R.card`, take `i := ⟨decodeBits blk, _⟩`, and prove
`R.code i = blk` by `List.ext_getElem` with `getElem_code_eq` and
`testBit_decodeBits`, exactly as `decodeBlock_eq_some` does for
`w.take R.width`. Generalising `getElem_code_eq`'s companion from
`w.take R.width` to an arbitrary block of the right length may be worth
factoring out.

### B1-b: `Ranked/Binary.lean`

Imports: `Geb.Mathlib.Data.Tree.Ranked.Preorder`,
`Geb.Mathlib.Data.Tree.Preorder`, `Mathlib.Data.Fin.VecNotation`. Wrap the
declarations in `public section` (an `@[expose]` outside one errors).

```lean
@[expose] def binRanked : RankedAlphabet := ⟨2, 1, Nat.one_pos, by decide, ![0, 2]⟩
```

Put it and everything below inside `namespace RankedAlphabet.Binary` rather
than at the root: two reviewers called a root-level `binRanked` poor upstream
shape, and the plan's own namespace section forbids it.

`leaf`, `node`, `termEquiv` (with `left_inv`, `right_inv`),
`spell_termEquiv`, `valid_iff`. For `termEquiv.toFun`, `Fin.cases` on the
head index is required, **and the successor branch needs a second nested
`Fin.cases`**: in that branch the index is a variable `x✝ : Fin 1`, and
`x✝.succ` is not defeq to `⟨1, _⟩`, so a cast against `⟨1, _⟩` type-mismatches.

`valid_iff` is short once `spell_termEquiv` exists; it goes through
`valid_iff_exists_spell` and `BinTree.valid_iff_exists_print`.

### B1-c: test mirrors

`GebTests/Mathlib/Data/Tree/Ranked/{Basic,Code,Preorder,Binary}.lean` plus
`GebTests/Mathlib/Data/Tree/Ranked.lean`. Fact 8 above governs their headers.
Shared fixtures (`sampleAlphabet` at `⟨4, 2, by decide, by decide, ![0,1,2,3]⟩`,
a nullary term, a binary term) live in the `Basic` mirror and are imported by
the others; only that module declares a `RankedAlphabet` literal, so only it
imports `Mathlib.Data.Fin.VecNotation`.

Assertions worth having, all of which were checked by evaluation during
design and returned `true`: `spell` and `parse` on the two sample terms;
`Valid` accepting the two sample spellings and rejecting a two-term word, a
mid-block word and an underflowing word; `validBool` agreeing with
`(parse ·).isSome` on every word of length ≤ 6; and, in the `Binary` mirror,
`binRanked.validBool` agreeing with `decide (BinTree.Valid ·)` on every word
of length ≤ 8 (needs `maxRecDepth`; it was verified true to length 10).

### B1-d: indices, docs, bibliography

`Geb/Mathlib/Data/Tree/Ranked.lean` and its test twin, in the three-line
docstring form `Geb/Mathlib/Data/Tree.lean` uses; add the `public import` to
`Geb/Mathlib/Data/Tree.lean` and the plain `import` to its test twin. One
`docs/index.md` entry per new module.

`docs/references.bib` gains the three confirmed entries —
`BenoitDemaineMunroRamanRamanRao2005` (Algorithmica 43(4):275–292, 2005),
`Mehlhorn1980` (ICALP 1980), `BraunmuhlVerbeek1983` (FCT 1983, LNCS
158:40–51) — **only if something committed cites them**. Two reviewers
objected that after the spec is deleted nothing does. Either have B1-f's
`TODO.md` text cite them by key, or defer each to the branch that first needs
it. `BarringtonCorbett1989` stays out: neither its bibliographic detail nor
its DLOGTIME-uniform TC⁰ claim has been verified against the article.

Full check: `lake build && lake test && lake lint && lake lint -- GebTests &&
lake shake --add-public --keep-implied --keep-prefix Geb GebTests &&
bash scripts/lint-imports.sh`, then the markdown checks, then
`bash scripts/pre-push.sh`. Read `#print axioms` on
`valid_iff_exists_spell`, `spell_injective` and `Binary.valid_iff`.

### B1-e: rewrite the plan from what built

`docs/superpowers/plans/2026-08-09-ranked-tree-encoding.md` forecasts code
that has since been written differently. Rewrite it to describe what the
commits actually contain, then run **one** confirming adversarial round
(three fresh general-purpose `Agent` invocations: Lean correctness, process
conformance, design coherence) rather than the open-ended loop — the code is
now the artifact under test, and a reviewer can build it.

### B1-f: follow-on notes and artifact removal

`TODO.md` § Extensions of the tree recognizers currently reads as four open
investigations. Rewrite it to record: B1 done, B2–B5 with their dependencies,
and the spec's Deferred list. Add the two deferrals: `BarringtonCorbett1989`
unverified, under § Citation corrections deferred to their own branch; and
the divergence between `docs/rules/lean-coding.md` § Naming conventions
(which forbids a namespace prefix in a declaration body) and the merged
`Geb/Mathlib/Data/Tree/Preorder.lean`, which uses `BinTree.induction` inside
`namespace BinTree`. Deciding that belongs on its own branch.

Then delete the spec and this handoff and the plan, per `CONTRIBUTING.md`
§ Concern shape: spec and plan commits, then implementation with its
persistent documentation and `TODO.md` notes, then removal.

## Outstanding review findings not yet applied

From two adversarial rounds, still open:

- The spec's `Scanner` (B2 content) needs `step₀ step₁ : COf 1` lifted by
  `comp` with `proj 2 1`, not `COf 2`. `Cobham.evalRec`'s step takes the
  remaining suffix as its first argument and the recursive value as its
  second, so a `COf 2` step cannot be a `List.foldr` step; `combFalseStep`
  and `combTrueStep` both reference slot 1 only. `length_le` also names
  `stepSem`/`baseSem`, which are not fields — inline the fold or move the
  bound to a smart constructor. `growth = 0` needs its own bound clause.
- The spec's `decideValid_computableInTimeAndSpace` signature is wrong:
  `ComputableInTimeAndSpace` takes three arguments and existentially
  quantifies the machine alphabet; the embedding is an input/output
  embedding, and it is the existential `sym`, not the embedding, that admits
  wide work-tape symbols. `f` must return a list, not a `Bool`.
- The spec's `PFunctor` non-reuse paragraph invents a cost: `PFunctor.W P` is
  definitionally `WType P.B`, so no coercion is owed. Restate as "no B1–B5
  consumer needs the initial-algebra apparatus".
- The spec's paramorphism paragraph claims an obstruction that `Scanner` as
  specified does not actually impose; restate it as the head-locality
  constraint § The state layout adopts, with its quadratic cost.
- `Fold.run_spell` is ill-typed (`List Bool` versus `Fin (2 ^ p)`); name the
  `p`-bit encoding on the right.
- The spec's § Answers, in brief still says the present recognizer is an
  instance of the general scan without the "up to the failed state"
  qualifier § Choice carries.
- Prose: emphasis bolds, rhetorical negation ("is not decoration", "mandatory,
  not optional"), metaphors ("load-bearing", "sanity anchor", "sticky
  failure"), and one process-narrating sentence, all against
  `CONTRIBUTING.md` § Style and references and § Document only the
  persistent.
- `docs/rules/lean-coding.md` § `lean-lsp` MCP search and proof tools does not
  list `lean_verify`; adding it is a separate branch.

## The remaining branches

Per the spec's § Scope and branches:

- **B2** — `Geb/Mathlib/Computability/Cobham/Scan.lean`: the `Scanner`
  combinator (with the correction above), the ranked recognizer as an
  instance, and the present `isTree` re-expressed as the width-one instance.
  Depends on B1.
- **B3** — `Geb/Mathlib/Computability/Cobham/Fold.lean`: the Tier-A
  catamorphism at a finite carrier and `Fold.run_spell`. Depends on B2.
- **B4** — absorb `BinTree` into `RankedAlphabet.Term` and delete the
  duplication. Depends on B1 and B2. Note the merged `BinTree` has six
  in-repo consumers.
- **B5** — `Geb/Internal/`: linear time and space against Cslib's
  `MultiTapeTM`, over `ComputableInTimeAndSpace` applied to a computable
  decision function (not `DecidableInTimeAndSpace`, whose `indicator` is
  `noncomputable` and `Classical`). `Geb/Mathlib/` may not import `Cslib.*`
  and `Geb/Cslib/` may not import `Geb.Mathlib.*`, so the statement is
  confined to `Geb/Internal/`. This branch differs in kind from the others
  and its difficulty is unbounded by anything done so far; B1–B4 stand
  without it.

Each gets its own spec-or-plan cycle, its own adversarial review to
convergence, and its own branch.

## Process this session must follow

- Invoke the phase skill before acting: `superpowers:writing-plans` for a new
  plan, `superpowers:executing-plans` or
  `superpowers:subagent-driven-development` to execute one,
  `superpowers:verification-before-completion` before claiming anything
  passes.
- Adversarial review of every spec and plan to convergence — no blocker and
  no serious finding — each round a **fresh** general-purpose `Agent`, never a
  continued one, re-fetching the mathlib guides each round. Respond in
  writing to every finding: fix, defer with rationale, or reject as
  cosmetic-taste.
- Verify agent claims against the source before acting on them. Both rounds
  produced confidently stated findings that were wrong, and both rounds
  caught confidently stated claims of mine that were wrong. Build it or read
  it.
- `jj` for every state-mutating VCS operation; never a mutating `git`
  subcommand. Local commits are fine; **no push** without the user's
  line-by-line review.
- Do not draft PR descriptions, Zulip messages or GitHub comments.
- Prefer building over arguing. The single most productive change in this
  workstream was writing the Lean and letting the compiler adjudicate; two
  rounds of reviewing a document that described Lean did not converge.
