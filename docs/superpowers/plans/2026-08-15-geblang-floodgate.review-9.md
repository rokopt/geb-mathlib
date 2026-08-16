# Floodgate plan, adversarial review round 9: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [What the round established](#what-the-round-established)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a ninth fresh general-purpose agent, which assembled the
whole plan onto a copy of the tree and re-ran everything against it.

## Verdict

Round 9: **CONVERGED**. No blocker, no serious, one minor, one
cosmetic-taste, no spec defect.

Both findings are fixed.

## Minor

**M1, the spelling `TODO.md` entry names `docs/index.md` as a carrier
of the capitalised spelling, which an earlier step of the same task
has already emptied.** Fixed. That file's only two occurrences sit
inside the bullet list Task 5 Step 7 replaces wholesale, so the
post-plan count is zero.

This is round 8's M2 repeated three steps away: that round removed
`scripts/extract-pr.sh` from the same list for the same reason and did
not check the sibling instance. The list has now been measured against
the assembled tree rather than against the tree as it stands today,
which is the check that should have been applied both times.

## Cosmetic-taste

**C1, the new `README.md` paragraph restates its own neighbour.**
Fixed by dropping the redundant sentence rather than the paragraph:
the first sentence says something the amended neighbour does not,
that `GebLang/` is upstream-eligible per module by closure. Round 5
raised the same shape and recorded it as dropped; that instance
survived, and this is it.

## What the round established

The reviewer assembled the plan mechanically onto a copy of the tree,
so a byte mismatch in any quoted before-text would have surfaced as a
failure. All 45 matched exactly once. Four end mid-line by design;
each resulting line was measured, the longest at 75 columns.

- The three self-tests: 39 of 39 extraction assertions, 53 of 53 lint
  cases, 5 of 5 transitive cases.
- Both linters on the assembled tree: clean at 197 and 196 files,
  exactly the counts the plan predicts and for the reasons it gives.
- All 195 files in the four existing subtrees extract with no
  difference outside import lines, and no extracted import line
  retains a repository prefix.
- `markdownlint-cli2` reports one issue before `doctoc` runs, the
  stale `AGENTS.md` anchor that Task 5 Step 10 says `doctoc` fixes,
  and none after.
- Both sweeps re-run on the assembled tree find no defect outside the
  plan's own known-instance list.

Round 8's five changes were each verified by application. The
`Batteries.*` correction holds in the way that matters: all three
umbrella-and-bullet pairs now agree with each other and with Task 4
Step 1's `check_subtree` calls, and `docs/rules/upstream-eligible.md`'s
six-row table matches all six calls prefix for prefix.

The eighth attack on the role-strip found one surviving shape, and
established that it is unreachable: a role-less code span followed by
a second span on the same line. Plan 1 makes a role-less span a
`doc.verso.suggestions` warning, and `weak.warningAsError` makes that
an error, so no compiling `GebLang/` source can contain one.

One observation the reviewer recorded that is worth keeping: Task 1
repairs a second extraction defect beyond the `meta import` gap the
`TODO.md` entry records. The current script rewrites no test
self-prefix at all, so every `GebTests/Mathlib/` file with a sibling
test import ships today with `GebTests.Mathlib.` intact. The new arm
tables fix it and the new self-test asserts it; the spec named this
as a pre-existing gap with no `TODO.md` entry, and no entry is left
stale by the repair.
