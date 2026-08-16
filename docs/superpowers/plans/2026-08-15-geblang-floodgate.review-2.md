# Floodgate plan, adversarial review round 2: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Blocker](#blocker)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Re-verification after the fixes](#re-verification-after-the-fixes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a second fresh general-purpose agent, no conversation
context, over `docs/superpowers/plans/2026-08-15-geblang-floodgate.md`,
reading round 1's record only after forming its own view. It
re-transcribed and re-ran every script the plan writes rather than
carrying round 1's results forward.

## Verdict

Round 2: NOT CONVERGED. One blocker, two serious, nine minor, two
cosmetic-taste, no spec defect.

Every finding is fixed. Nothing is deferred and nothing is rejected.

## Blocker

**B1, the Verso role-strip silently deletes mathematics from eight
existing files on extraction.** Fixed, and this is the finding of the
round.

The pattern was `s/\{[A-Za-z][A-Za-z0-9_]*[^}]*\}`/`/g`, applied to
every non-import line of all six arms. The `[^}]*` tail makes it
match any brace group opening with a letter and closing before a
backtick, which is what a universe ascription and a subtype inside a
code span both look like. Reproduced directly:

- `` `F : C ⥤ Cat.{v₂, u₂}` `` becomes `` `F : C ⥤ Cat.` ``
- `` `{g : B → k.1 // k.2 ∘ g = i}` `` becomes an empty code span
- `` `{a + i}` `` becomes an empty code span

The reviewer found nine such matches across eight files in
`Geb/Mathlib/` and `GebTests/Mathlib/`. A shipped PR would have
carried them. Worse, the plan's own comment asserted the opposite,
that the four `Geb`/`GebTests` arms have nothing to match, so nothing
in the plan would have caught it.

Two changes, both verified:

- The pattern is now `s/[{][A-Za-z][A-Za-z0-9_]*[}]`/`/g`: a bare
  identifier between the braces and nothing else. Bracket expressions
  replace the backslash-escaped braces, which is also the more
  portable `sed -E` form.
- The strip runs only in the two arms whose sources carry
  `doc.verso` markup, through a `convert_roles` flag and a
  `role_filter` function. `doc.verso` is set for the `GebLang`
  library alone, so no other arm has anything to convert and running
  it there was pure risk.

A role taking arguments is now left unconverted rather than risking
the wider pattern; the script says so, and says to add the exact form
when one is first used. The plan gains a self-test case whose
`Geb/Mathlib/` fixture docstring carries both a universe ascription
and a subtype, asserting they survive.

## Serious

**S1, a passage stating the superseded whole-line Rule 2 exemption is
left standing, and round 1's record claimed otherwise.** Fixed. The
reviewer is right on both counts. The import-rules section of
`docs/rules/upstream-eligible.md` opens by saying a self-prefix must
not appear outside `^import` lines, and Task 5 Step 4 revised six
things, none of them that paragraph. Round 1's response claimed the
fix was in the plan. It was not; only the `scripts/lint-imports.sh`
half was.

The count was wrong too: there are four such passages in the linter's
header, not three. `scripts/lint-imports.sh:33-37`, on the test
roots' two self-prefixes, was untouched.

Task 5 Step 4 now quotes and replaces the section's opening
paragraph, which also gains `GebLang/` and `GebTests/Lang/` as
locations that are not subtrees of `Geb/`. Task 3 Step 4 now covers
all four header passages plus the `<required-init>` usage sentence,
which M6 caught separately.

**S2, Task 4 widens `Geb/Mathlib/`'s allowed list and leaves
`docs/process.md` asserting the old one, where the sweep cannot find
it.** Fixed. `docs/process.md` § Two-track development states the
list as `Mathlib.*`, `Batteries.*` and `Geb.Mathlib.*`, which Task 4
Step 1 falsifies. The reviewer ran Task 6's grep and confirmed the
paragraph is not among its hits: the sweep looks for the literal
`Geb.*`, which does not occur in `Geb.Mathlib.*`.

Task 4 gains a step correcting the paragraph in the same commit that
falsifies it, with a note on why it cannot be left to the sweep, and
the following steps are renumbered.

## Minor

Each is fixed.

- M1, the sweep's greps are line-oriented over an 80-column corpus,
  so a wrapped enumeration escapes them. Task 6 gains a multi-line
  scan as its own step, with the instances it alone reaches named:
  `docs/aristotle.md`, which no other task touches, and
  `docs/rules/upstream-eligible.md` § Two-track development's opening
  paragraph. The reviewer's third instance,
  `scripts/tests/test-lint-imports.sh`'s header sentence, is caused
  by this plan's own `setup_empty` change rather than found by the
  sweep, and is now listed as such.
- M2, `docs/rules/upstream-eligible.md`'s "That rationale applies to
  a module whose own upstream target is mathlib4" was left narrowing
  what the preceding paragraph had just generalised. Round 1 fixed
  the `scripts/lint-imports.sh` twin and not the Markdown one; both
  now get the same re-flow.
- M3, two quoted before-blocks were partial lines needing an unstated
  re-flow: both are now quoted whole, with the re-flow given. The
  plan already flagged this hazard for the Batteries paragraph, so
  the omission was inconsistent with its own practice.
- M4, the `CONTRIBUTING.md` § Floodgate test before-text dropped
  "in their respective subtrees": corrected.
- M5, "the commit after this one" in a permanent script comment is a
  development-history reference, which `CONTRIBUTING.md` § Document
  only the persistent forbids. It was round 1's fix for M9, so that
  fix created a new defect; the comment is now in the present tense
  and the ordering rationale stays in the plan's § Commit ordering,
  where it already was.
- M6, the `check_subtree` usage block did not document the new `?`
  form: added.
- M7, Task 3 Step 2's line range was stated against the pristine file
  after Step 1 had shifted it. The block is now identified by its
  opening comment rather than by line number.
- M8, the plan over-claimed that no ordering closes the plan-split
  window. Task 1's script change and its self-test run on synthetic
  fixtures and would pass with no `GebLang/` in the tree, so the
  constraint is the spec's mandated split rather than a technical
  impossibility. The paragraph now says that, and adds the lint gap
  beside the extraction gap.
- M9, "the two added by this plan" over one added and two extended.

## Cosmetic-taste

Both fixed.

- C1, `scripts/lint-imports.sh` would ship with both spellings of
  `Cslib`: the `TODO.md` trigger entry Task 5 records now names the
  scripts as well as the documents.
- C2, backslash-escaped braces in `sed -E`: replaced with bracket
  expressions as part of the B1 fix.

## Re-verification after the fixes

The B1 fix changes the extraction script's behaviour, so the round-1
and round-2 self-test results do not carry over. Re-run after the
edits:

- Every file in the four existing upstream-eligible subtrees extracts
  with no change outside its import lines. Compared 195 files;
  non-import diffs: 0. Under the old pattern eight of them changed.
- The extraction self-test passes all of its assertions, including
  the two new ones asserting a universe ascription and a subtype
  survive, and the two asserting the role markup is still stripped
  from a `GebLang/` source.
- A `GebLang/` fixture carrying `{lit}`, `{name}` and `{option}`
  roles extracts with all three converted to bare code spans and a
  `Cat.{v, u}` ascription intact.
- `scripts/check-transitive-imports.sh` reports
  `clean (195 file(s) checked)` on the real tree, and its self-test
  passes five of five.

The `scripts/lint-imports.sh` edits are unchanged by this round
except in header comments, so the reviewer's own run of them stands:
53 self-test cases with no failure, and `clean (197 file(s) checked)`
against the real tree plus plan 1's two files.
