# Tree-recognizer extensions — workstream record

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Read these first](#read-these-first)
- [Where the workstream stands](#where-the-workstream-stands)
- [Facts established by building](#facts-established-by-building)
- [B2: the scan combinator (done)](#b2-the-scan-combinator-done)
- [The case combinator (done)](#the-case-combinator-done)
- [B6: the generic ranked recognizer (done)](#b6-the-generic-ranked-recognizer-done)
- [B3: the fold (done)](#b3-the-fold-done)
- [B4: absorbing `BinTree`](#b4-absorbing-bintree)
- [B5: the time and space bound](#b5-the-time-and-space-bound)
- [What completion means](#what-completion-means)
- [Process this session must follow](#process-this-session-must-follow)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Read these first

- [CONTRIBUTING.md](../../../CONTRIBUTING.md), [AGENTS.md](../../../AGENTS.md),
  [CLAUDE.md](../../../CLAUDE.md),
  [docs/rules/lean-coding.md](../../rules/lean-coding.md),
  [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md),
  [docs/rules/markdown-writing.md](../../rules/markdown-writing.md),
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md).
- [TODO.md](../../../TODO.md) § Extensions of the tree recognizers. It carries
  every roadmap item with its dependencies and the design constraints below,
  and records which are done. It is the persistent record; the specification
  that stated B1 was removed with it, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.
- [docs/index.md](../../index.md), entries for
  `Geb/Mathlib/Data/Tree/Ranked/*` and
  `Geb/Mathlib/Computability/Cobham/*`.

B4 and B5 have no specification: each gets
its own brainstorming phase, its own spec and plan, its own adversarial
review to convergence, and its own segment. Do not treat this document as a
spec: it records state and constraints, not decisions.

## Where the workstream stands

B1, B2, the case combinator, B6 and B3 are done and unpushed, on one line
off `main`; B4 and B5 are not started. The per-item table in
[the session handoff](2026-08-10-tree-recognizer-session-handoff.md)
§ Status of every roadmap item is the current record, and this document
describes what each remaining item is.

B1 is not merged. Nothing in this workstream has been pushed.

`Geb/Mathlib/Data/Tree/Ranked/` holds four modules:

- `Basic.lean` — `RankedAlphabet` (fields `card`, `width`, `width_pos`,
  `card_le_two_pow_width`, `arity`), `Term` as the W-type of the finitary
  polynomial functor on `Fin card`, `Term.mk`, `Term.size`, `size_mk`,
  `Term.induction`, `size_le_sum_ofFn`.
- `Code.lean` — `code`, `decodeBits`, `arOf`, `length_code`, `mod_two_mul`,
  `decodeBits_code`, `arOf_decodeBits_code`, `getElem_code_eq`,
  `testBit_decodeBits`.
- `Preorder.lean` — `spell`; the fuel-bounded descent `decodeBlock`,
  `parseChildren`, `parseStep`, `parseAux`, `parse`; `encoding` as a
  `Computability.Encoding` and `spell_injective` from it; the scan `Scan`,
  `scanStep`, `scanFrom`, `scanFinal`, `validBool`, `Valid` with its
  `DecidablePred` instance; and the image characterisation
  `valid_iff_exists_spell` and `valid_iff_isSome_parse`.
- `Binary.lean` — `binRanked`, `leafSym`, `nodeSym`, `leaf`, `node`,
  `termEquiv : BinTree ≃ binRanked.Term`, `spell_termEquiv`, `valid_iff`.

Every declaration measures `[propext, Quot.sound]`. `spell_termEquiv` is an
equality of words, so the merged two-symbol encoding is an instance of the
ranked one rather than a parallel construction; `valid_iff` carries the scan's
language to `BinTree.Valid`.

The mirrors under `GebTests/Mathlib/Data/Tree/Ranked/` declare the fixtures
`sampleAlphabet` (`card = 2 ^ width`), `narrowAlphabet` (`card < 2 ^ width`, so
one block spells no symbol) and `wordsUpTo`, and sweep `validBool` against the
descent and against `BinTree.Valid` over every word of length at most eight.

## Facts established by building

Items 1 to 16 each cost a failed build — 1 to 11 during B1, 12 to 16 during
the ranked-recognizer segment. Items 17 to 23 were established during the
fold segment, several by measurement rather than by a failed build. The
three marked corrected were stated wrongly in the
previous handoff and cost a second failed build; do not reinstate them from
any older document.

1. **`Term.mk R i ch`, never `R.Term.mk i ch`.** Generalized field notation
   resolves `R.Term` first, and a `Type` carries no `mk`.
2. **A symbol index must carry an assigned bound proof (corrected).**
   `R.arity i` reduces for a literal index, so `Fin (arity ⟨0, h⟩)` is `Fin 0`
   and `Fin (arity ⟨1, h⟩)` is `Fin 2` — but only once `h` is assigned. Written
   inline, `⟨0, by decide⟩` leaves `h` an unassigned metavariable while the
   child family elaborates, and the family's domain is then neither. Name the
   index, as `leafSym` and `nodeSym` do. Against an index that is itself a
   pattern variable the goal carries a free variable, which `decide` refuses,
   and presents the arity as an atom, which `omega` cannot unfold; ascribe the
   bound with `show (0 : ℕ) < 2`. The previous handoff's
   `by decide +revert` is not the working form in either situation.
3. **`Nat.land` is not exposed, so a block does not reduce during
   elaboration.** Prove a `code` equality by `decide`, which the kernel
   evaluates, not by `rfl`, and rewrite through the result downstream.
4. **`Nat.mod_mul` depends on `Classical.choice`**, and `omega` cannot
   discharge a residue identity whose modulus is a variable.
   `RankedAlphabet.mod_two_mul` and `RankedAlphabet.add_one_mod` replace the
   two that were needed. Expect the same trap in any further `Nat` division
   reasoning, and re-measure after each.
5. **`omega` proving a non-`False` goal can pull in `Classical.choice`.** It
   did not in B1, but `lake lint` is what settles it, not inspection.
6. **`decide` on a `Term` equality is available (corrected).** mathlib has no
   `DecidableEq (WType …)`; `Geb/Mathlib/Data/W/Basic.lean` supplies one for
   `[DecidableEq α] [∀ a, FinEnum (β a)]`. B1's mirrors state the descent's
   value through `Option.map` of the spelling anyway, which costs neither that
   import nor the `FinEnum` instances its `decide` would reduce through. The
   previous handoff's claim that no instance exists is wrong.
7. **Sweep budgets are per-computation, not per-word-count (corrected).**
   `set_option maxRecDepth 100000 in decide` is valid in tactic position. The
   word count is not what decides whether it is needed: at 127 words the
   `validBool`-against-`parse` sweep closes at the default depth while
   `length_wordsUpTo_six`, which builds the same enumeration, does not. Measure
   rather than predict. `native_decide` is banned (compiler-trust axiom).
8. **`linter.flexible`, `linter.unnecessarySeqFocus` and `linter.style.show`
   are errors here.** A bare `simp` that modifies the goal must be terminal;
   `tac1 <;> tac2` where `tac1` leaves one goal fails; and a `show` that
   changes the goal must be `change`.
9. **`simp only [] at h` after a `split` is an error** (`simp made no
   progress`) — the `split` already iota-reduces the hypothesis. `simp only []`
   on the goal is sometimes required, to reduce a `match some …`.
10. **Import placement.** `List.sum_map_mul_left` is in
    `Mathlib.Algebra.BigOperators.Ring.List`. `List.le_sum_of_mem` needs
    `Mathlib.Algebra.Order.BigOperators.Group.List` and routes through
    ordered-algebra instances the axiom rules warn about; `size_le_sum_ofFn`
    proves the bound directly instead.
11. **Test modules** need `set_option linter.privateModule false` or
    `@[expose] public section`. Fixtures shared across test modules need a
    `public import` of the declaring module and `@[expose]`. Group
    `public import`s before plain `import`s, separated by a blank line.
12. **A projection of a `Scan` constructor does not reduce syntactically.**
    After `obtain ⟨buf, depth, live⟩ := s`, or under `{ s with depth := … }`,
    the goal carries `{ buf := buf, … }.live` rather than `live`. A `cases`
    on a scrutinee written in the fields then matches nothing and silently
    splits nothing, and the following `rw` fails with a pattern that is
    visibly present in the printed goal. `dsimp only` reduces them, and is
    needed once after the definitions are unfolded and again after each
    `cases`.
13. **`rw` closes a goal by `rfl` at reducible transparency only.** A branch
    ending in an equation true by unfolding an `@[expose] def` needs an
    explicit `rfl` after the rewrite.
14. **`rw [List.length_cons]` inside a chain rewrites the first matching
    instantiation**, which under `scanStep`'s unfolding is the block's
    length rather than the word's. Supply the word's length as a `have` for
    `omega`.
15. **`List.takeWhile_replicate` depends on `Classical.choice`**, through
    `List.filter_replicate`, whose proof is a `simp_all` and so does not
    show it in the source. This is a fourth route beyond `omega`
    discharging an `Iff` goal, `DecidableEq (Fin n → Bool)` resolving
    through `Fintype.decidablePiFintype`, and `RankedAlphabet.Scan`
    deriving no `DecidableEq`; the two-case reduction that replaces it
    measures clean. `DecidableEq (Fin n → Bool)` was measured the same way
    and does depend on `Classical.choice`, while `DecidableEq (List Bool)`
    depends on nothing.
16. **Two concurrent `lake build` invocations corrupt package `.trace`
    files** and fail unrelated mathlib targets. The `lean-lsp` tools that
    run Lean count as a second process. Build alone.
17. **`constAtOf` takes the arity explicitly**, `constAtOf (n : ℕ)
    (u : List Bool) : COf n`; the calls are `constAtOf 0 …` for the base
    and `constAtOf 1 …` for a branch.
18. **`rw` does not unfold `foldStep`.** `stepWord_foldStep` opens with a
    `change` to the `diagOf (casesOf …)` form before `stepWord_diagOf`
    applies, and needs a second `change` to present the goal as `casesSem`
    before `casesSem_eq` applies.
19. **`scanSem_cons` is not a `rfl`**, so `foldSem ![b :: w]` is not
    definitionally the step applied to `foldSem ![w]` and a `change` does
    not reach it. `foldSem_cons` is stated and proved from `scanSem_cons`,
    its last step `cases b <;> rfl` discharging `scanStepWord`'s `if`.
20. **`Cobham.scanSem_eq_eval` instantiates directly at this base and
    step**, and `Cobham.scanOf` likewise, so `foldSem_eq_eval` and `foldOf`
    reuse them rather than restating them as `rfl` and `⟨fold …, rfl⟩`.
    Both forms compile and both measure `[propext, Quot.sound]`; the
    instantiating form is the one `Cobham/RankedTree.lean` uses.
    `scanSem_eq_eval` is itself a `rfl`, unlike `casesSem_eq_eval`, whose
    transport is opaque.
21. **`#eval` of a fold value fails** with "Could not find native
    implementation of external declaration `Cobham.constAt`" — the
    cross-module IR gap
    [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Lean 4
    module system records. The mirror asserts by `decide`, which the
    kernel evaluates and which needs no `public meta import`.
22. **The sweep budget is seven.** At 255 words the sweep closes in about
    twelve seconds under `set_option maxRecDepth 100000 in decide`; at 511
    words it reaches the 200000-heartbeat `isDefEq` limit and fails. At
    127 words it closes in about six seconds.
23. **`linter.hashCommand` logs at info, not error**, so `#print axioms`
    is available inside a `Geb/` module for measuring a prototype. It
    remains barred from committed library code by review, not by the
    linter.

## B2: the scan combinator (done)

Done. `Geb/Mathlib/Computability/Cobham/Scan.lean` gives the scan
combinator, and `Geb/Mathlib/Computability/Cobham/Tree.lean`'s recognizer
is rebuilt on it. See [docs/index.md](../../index.md), entries for
`Geb/Mathlib/Computability/Cobham/Scan.lean` and
`Geb/Mathlib/Computability/Cobham/Tree.lean`.

The generic ranked recognizer was carried out of B2 into a branch of its
own, B6, described below: the combinator is the two-symbol recognizer's
scan, and instantiating it at an arbitrary `RankedAlphabet` is separate
work.

## The case combinator (done)

Done. `Geb/Mathlib/Computability/Cobham/Cases.lean` gives definition by
cases over a fixed number of scrutinee bits, and `Cobham/Basic.lean` the
constant-word, iterated-predecessor and diagonal combinators its branches
are built from. It carries no roadmap letter: it is shared machinery both
B6 and B3 need, since a dispatch over `2 ^ width` block values cannot be
written out at a symbolic width. See [docs/index.md](../../index.md).

## B6: the generic ranked recognizer (done)

Done. `Geb/Mathlib/Computability/Cobham/RankedTree.lean` expresses
`RankedAlphabet.validBool`, the validity scan of the preorder encoding, as
a member of Cobham's class at an arbitrary ranked alphabet, and
`isRankedSem_binRanked_eq_singleton_iff_isTreeSem` identifies it at the
two-symbol alphabet with the recognizer `Cobham/Tree.lean` carries. See
[docs/index.md](../../index.md), entries for
`Geb/Mathlib/Computability/Cobham/RankedTree.lean` and
`Geb/Mathlib/Data/Tree/Ranked/{Basic,Code,Preorder}.lean`.

Depended on B1, B2 and the case combinator. The `RankedAlphabet.Scan` bit
layout is the liveness flag, then the incomplete block in a fixed-width
slot delimited by a sentinel, then the pending count in unary as the tail.
The dispatch is the case combinator at `width + maxArity + 2` bits.

## B3: the fold (done)

**B3 is done.** `Geb/Mathlib/Computability/Cobham/Fold.lean` gives the
catamorphism of a list of bits at a carrier admitting a `p`-bit encoding,
as an expression of Cobham's class; see [docs/index.md](../../index.md)
for what it carries, this document's branch descriptions being for work
not yet started. It is a deliverable of the workstream for later
workstreams to build on rather than a dependency of anything here, so
having no consumer in the repository on landing is its expected condition,
not a cost to be justified against
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost.

## B4: absorbing `BinTree`

Depends on B1 and B2.

`BinTree` is absorbed into `RankedAlphabet.Term` at `binRanked`, and the
duplication in `Geb/Mathlib/Data/Tree/Preorder.lean` — `print`, `parse`,
`parseAux_eq_some`, `parse_eq_some_iff`, `print_injective`,
`valid_iff_exists_print`, `valid_iff_isSome_parse`, `depth`, `ok` — is removed.

`termEquiv`, `spell_termEquiv` and `valid_iff` are the bridge B1 delivers, and
every further bridge is a short corollary of them; `binRanked.parse w =
(BinTree.parse w).map termEquiv` is the shape of the rest.

The modules naming `BinTree` are `Geb/Mathlib/Data/Tree/Binary.lean` (its
definition), `Geb/Mathlib/Data/Tree/Preorder.lean`,
`Geb/Mathlib/Computability/Cobham/Tree.lean`,
`Geb/Mathlib/Computability/BellantoniCook/Tree.lean`,
`Geb/Mathlib/Data/Tree/Ranked/Basic.lean` (docstring only),
`Geb/Mathlib/Data/Tree/Ranked/Binary.lean`, and the mirrors
`GebTests/Mathlib/Data/Tree/Preorder.lean` and
`GebTests/Mathlib/Data/Tree/Ranked/Binary.lean`.

Until B4 lands, the duplication is on `main`. That is the declared staging, not
an oversight.

## B5: the time and space bound

`Geb/Internal/`. Depends on B2. This branch differs in kind from the others and
its difficulty is unbounded by anything done so far.

The target is linear time and space for the recognizer against Cslib's
`MultiTapeTM`, sharper than the polynomial-time, linear-space membership that
`isTree_smashFree` gives through [Strahm2003] Theorem 1(2).

Verified against
`.lake/packages/cslib/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`:

- `ComputableInTimeAndSpace (f : List IOSymbol → List IOSymbol) (t s : ℕ → ℕ)`
  takes three explicit arguments and existentially quantifies `k`, the machine
  alphabet `Fin sym`, the state set `Fin state`, the embedding and the machine.
  It is the existential alphabet, not the embedding, that admits a work-tape
  symbol wide enough to hold a stack frame; the embedding is of input and
  output only.
- `f` returns a `List IOSymbol`, not a `Bool`.
- `DecidableInTimeAndSpace` is not the route: it is
  `ComputableInTimeAndSpace (indicator L)`, and `indicator` is `noncomputable`
  and `open Classical`. State the bound over a computable decision function
  instead.

`Geb/Mathlib/` may not import `Cslib.*` and `Geb/Cslib/` may not import
`Geb.Mathlib.*`, so the statement is confined to `Geb/Internal/`.

Record what measuring the algebra term itself gives, as the contrast: `pred`
and `cond` are `boundedRec` nodes rather than generators, so under a strict
reading each costs one unit per bit of its scrutinee, and the scan's total is
the sum of the stack depths — quadratic in the word length on a left comb,
linear on a right comb.

## What completion means

Two items remain, in this order: B4, then B5.

B1 to B4 and B6 stand without B5. The workstream is complete when B4 has
landed, so that no tree encoding is defined twice, B6 having already
landed, so that the recognizer is stated at an arbitrary ranked alphabet.
B3 is a deliverable in its own right. B5 is a separate undertaking whose
failure costs nothing already built, and whose difficulty is unbounded by
anything done so far.

Deferrals are recorded in [TODO.md](../../../TODO.md), not part of
the branches above: the namespace prefix in a declaration body, the
placement of the choice-free `Nat` residue lemmas, and the citation status
of `BarringtonCorbett1989` together with the three succinct-tree
references, which are verified but uncited and so belong to the branch
that first cites one.

Also deferred, not part of the branches above: the Bellantoni-Cook port of
the scan combinator, whose signature is over arities in normal and safe
position and so is a branch rather than a transcription; the paramorphism
whose step receives a subterm's spelling, which the head-locality of the
state layout admits only at quadratic cost; a fold at an infinite carrier,
which needs the `smash` generator; and the depth-first unary degree
sequence encoding, whose condition for adoption is unbounded arity.

`scripts/pre-push.sh` emits a non-blocking WARN that commit `5cfd5ef1`, of
the case-combinator segment, carries a 73-character subject, one over
[docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
§ Commit-message convention's "under 72 when possible." That commit is not
part of any remaining branch, so it is left alone; the WARN is open and
non-blocking.

## Process this session must follow

- Invoke the phase skill before acting: `superpowers:brainstorming` before any
  spec, `superpowers:writing-plans` for a plan,
  `superpowers:executing-plans` or `superpowers:subagent-driven-development` to
  execute one, `superpowers:verification-before-completion` before claiming
  anything passes.
- Adversarial review of every spec and plan to convergence — no blocker and no
  serious finding — each round a fresh general-purpose `Agent`, never a
  continued one, re-fetching the mathlib guides each round. Respond in writing
  to every finding: fix, defer with rationale, or reject as cosmetic-taste.
- Verify agent claims, and claims inherited from a handoff, against the source
  before acting on them. Three of this document's own facts are corrections of
  a previous handoff that were confidently stated and wrong.
- Prefer building over arguing. In B1 the two rounds spent reviewing a document
  that described Lean did not converge; the round run against compiled code
  converged with no blocker.
- `jj` for every state-mutating VCS operation; never a mutating `git`
  subcommand. Local commits are fine; no push without the user's line-by-line
  review.
- Do not draft PR descriptions, Zulip messages or GitHub comments.
- This document is transient. Remove it in the final commits of whichever
  branch last needs it, per
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.
