# Verso manual plan: adversarial review, round 1

Reviewer: fresh-context agent, 2026-08-14. Verification sources:
the repository files the plan modifies; verso at `v4.34.0-rc1`
(the `Article` structure, `inlines!`, `citep`, `#doc`/`%doc`,
`manualMain`, `verso-serve`, `{include}`, the `signature` block's
fresh-scope elaboration, `verso.code.warnLineLength`); Lake and
batteries `runLinter` at the pins; the public precedent
`anoma/geb`; `Geb/Mathlib/Data/W/Basic.lean` for the planned
`{name}` targets and the `WType.para` signature block. The round
executed the plan's bash where read-only: every planned commit
subject passes `scripts/check-commit-msg.sh`, the quoting
expands as intended, and the `check_coverage` replacement was run
verbatim against the real `Geb` tree and a synthetic `manual/`
tree, passing both and failing exactly as Step 3 of Task 7
expects when an import is removed. The round also discharged a
header-linter concern from primary sources: mathlib's header
linter skips `srcDir` libraries by its root-file heuristic.

Verdict: **converged**, with no blocker and no serious findings.
Seven minor and four cosmetic-taste findings were left to the
author; all are fixed below, in this round's commit.

## Findings and responses

Minor.

1. The planned `.lean` files put `open` between the imports and
   the module docstring, against the repository's docstring
   placement rule; it builds only because the header linter skips
   `srcDir` libraries. Fixed: every snippet orders imports, then
   the docstring, then `open`.
2. A mathlib style-linter failure first becomes possible at
   Task 4 (when `Geb.Mathlib.Data.W.Basic` joins the closure),
   where the plan gave no instruction. Fixed: Task 4 Step 5
   cross-references Task 3 Step 3's disable-and-record procedure.
3. The serve checks used a foreground `sleep` (blocked for agent
   executors) and `kill %1` (job control; and the `exec`'d server
   can orphan). Fixed: `curl --retry` does the waiting, the PID
   is captured, and a `pkill -f verso-serve` catches an orphan,
   in both Task 5 and Task 9.
4. Two spec § Verification items (the `doc-build.yml` pass and
   the clean-`.lake` build) had no executable step. Fixed: Task 9
   states both are deferred to the first CI run after the user's
   review and push, with the rationale.
5. The bibliography's `L. Meertens` is not a literal
   transcription of the `.bib`'s `Meertens, Lambert`. Fixed: the
   step states the precedent's initialed rendering convention and
   the `.bib`'s authority over every field.
6. Task 1 Step 4's stop-diagnosis had a single exit (re-check
   placement). Fixed: a second exit reports the diff instead of
   iterating.
7. A module-system failure in `Main.lean` would surface at
   Task 2 Step 6, after the Step 5 check concluded. Fixed: the
   fallback is anchored to Steps 5 and 6 jointly.

Cosmetic-taste.

1. `update.yml` step-name line number corrected to 42.
2. The illustrative nolints entry now uses the real generated-def
   name shape (`GebManual.Root.«the canonical document object
   name»`).
3. Task 4's Interfaces block now attributes `WType` and
   `WType.elim` to mathlib, re-exported through the module's
   `public import`.
4. The bibliography docstring's forward reference to a rule
   section that exists only after Task 8 is dropped; the
   docstring states the fact without the cross-reference.
