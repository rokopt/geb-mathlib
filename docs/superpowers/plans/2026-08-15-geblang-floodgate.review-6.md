# Floodgate plan, adversarial review round 6: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Blocker](#blocker)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Re-verification after the fixes](#re-verification-after-the-fixes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a sixth fresh general-purpose agent, told to assume the
role-strip was still wrong and to enumerate leading contexts
systematically rather than guess.

## Verdict

Round 6: NOT CONVERGED. One blocker, one serious, three minor, three
cosmetic-taste.

Every finding is fixed. The blocker is the fifth consecutive round in
which the same substitution has been wrong, and this round's fix
changes its kind rather than its calibration.

## Blocker

**B1, the role-strip deletes a single-token brace group that ends a
longer code span.** Fixed. Round 5 protected the two positions it had
examined, a group following a `.` and a group following a backtick,
and left the position a code span most often puts one in: after a
space or an operator, at the end of the span. Ten of twenty realistic
Lean shapes were mangled:

```text
`s ∪ {a}`   ->  `s ∪ `
`x ∈ {a}`   ->  `x ∈ `
`theorem foo {n}`  ->  `theorem foo `
```

A separate false negative in the same expression: `_` in the leading
class blocked Verso's emphasis marker, so ``_{name}`Nat`_`` shipped
literal braces.

**The fix changes the kind of the pattern, and that is the point.**
Every previous round calibrated "any identifier in braces" against
the counterexamples in hand, and each calibration was locally right
and globally wrong, because a brace group holding an identifier is
ordinary Lean. The pattern now matches the closed set of role names
this repository writes, which plan 1 already fixes in
`docs/rules/lean-coding.md` § Literate modules: `name`, `option`,
`lit`.

```bash
role_strip='s/(^|[^A-Za-z0-9.`])[{](lit|name|option)[}]`/\1`/g'
```

Verified: none of the twenty Lean shapes is touched, all twenty
leading contexts convert including `_`-emphasis, the extraction
self-test passes unchanged, and a realistic `GebLang` docstring in
mathlib house style extracts with its roles converted and its
`s ∪ {a}`, `x ∈ {a}`, `Type.{u}` and `{u}` all intact.

A role outside the set now ships as literal braces rather than being
silently eaten. That is the right failure direction, and the script
says so: braces upstream are visible and get fixed, deleted
mathematics is not.

The author applied this fix once and did not notice that the script
carrying it had aborted on an unrelated assertion, so the first
verification run still reported the old behaviour. It was caught by
re-reading the extracted script rather than trusting the edit, which
is the same discipline this review has been enforcing on the plan.

## Serious

**S1, three passages of the script state an import-line exemption
that round 4 removed, contradicting a fourth.** Fixed. Round 4
changed `role_filter`'s comment to say no line is exempt and left the
header, the `role_strip` comment and the copy-step comment saying
roles are converted off import lines, or in everything else. These
are permanent comments in a shipped script; a reader trusting them
would not expect a role in an import line's trailing comment to be
converted, which is what round 4 decided should happen. All three now
say every line.

## Minor

Each is fixed.

- M1, § File structure omitted `docs/aristotle.md` and
  `manual/GebManual/Introduction.lean`, both of which Task 6 names as
  sweep instances and says are in no other task's list.
- M2, the `TODO.md` entry recording the `Cslib` spelling migration
  named two carriers where the plan leaves five more, and did not
  record the second half-done migration at all: the same document now
  calls `GebLang/` and `GebTests/Lang/` locations rather than
  subtrees, while its heading and its table's first column still say
  subtree. The entry now covers both migrations and all the carriers.
- M3, Task 1 Step 5's expectation named only `{name}`, so it would
  pass on a file where `{lit}` and `{option}` shipped unconverted.
  All three roles are now named.

## Cosmetic-taste

- C1, a stray blank line making one list loose among tight ones.
- C2, the cross-subtree paragraph read as restricting `Geb/Cslib/` to
  mathlib-track `GebLang.*`, which the widened list does not do.
- C3, a `TODO.md` opening line quoted truncated mid-line in Task 1
  where rounds 3 and 4 fixed the same shape in Tasks 3 and 4.

## Re-verification after the fixes

- The extraction self-test passes every assertion.
- All 195 files in the four existing subtrees extract with no
  difference outside import lines.
- A realistic `GebLang` docstring extracts with all roles converted
  and no Lean touched.
- `scripts/tests/test-check-transitive-imports.sh` passes five of
  five.

The reviewer's own run before these fixes found the rest clean: 53 of
53 lint cases, both linters clean on the tree at 197 and 196 files,
all 25 quoted before-texts matching exactly once, and every edited
document coherent end to end.
