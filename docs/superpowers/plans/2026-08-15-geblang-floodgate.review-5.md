# Floodgate plan, adversarial review round 5: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Blocker](#blocker)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Re-verification after the fixes](#re-verification-after-the-fixes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a fifth fresh general-purpose agent, told to assume the
role-strip was still wrong and to attack it with realistic future
`GebLang` content.

## Verdict

Round 5: NOT CONVERGED. One blocker, one serious, five minor, four
cosmetic-taste, no spec defect.

Every finding is fixed.

## Blocker

**B1, the role-strip deletes a single-token brace group: a universe
ascription, a singleton, an implicit binder group.** Fixed, and this
is the fourth consecutive round in which this one substitution has
been wrong.

Every example the earlier rounds checked was a multi-token group:
`Cat.{v, u}`, `{g : B → k.1 // p g}`, `{a + i}`. All are excluded by
the requirement that the braces hold a bare identifier. Nobody
checked the single-token forms, which are exactly what the pattern
matches:

```text
{lit}`Type.{u}`   ->  `Type.`
{lit}`{S}`        ->  ``
`{p}`             ->  ``
```

Since the substitution is global it fires inside a role's own
argument, and the empty results are worse than empty: two adjacent
backticks open a double-backtick span in CommonMark and swallow the
prose after them.

This is native to the mathematics in scope, not contrived. This
repository writes `FinSetSkel.{u}` 110 times and `Category.{vI}` 111
times in Lean, and 260 mathlib files carry the exact docstring shape.
A `GebLang` content module on polynomial functors and W-types will
write it in prose on the first day.

The pattern now also requires the brace group to open the line or to
follow a character that can neither end a Lean identifier nor close a
code span:

```bash
role_strip='s/(^|[^A-Za-z0-9_.`])[{][A-Za-z][A-Za-z0-9_]*[}]`/\1`/g'
```

Verified: `Type.{u}` and `{S}` survive inside a converted role's
argument, a role-less `` `{p}` `` is untouched, and the three roles
in plan 1's placeholder still convert. The script's comment now
tabulates the four excluded shapes and says which restriction
excludes each, since the single-token cases are the ones four rounds
of review kept missing.

The reviewer also found that no test covered this: both fixtures
carrying Lean-shaped braces sit in the `Geb/Mathlib/` arm, where
`convert_roles=0`. The `GebLang/` fixture now carries a universe
ascription, a binder group and a role-less span, with an assertion on
each.

## Serious

**S1, the `docs/process.md` before-text is a truncated paragraph
whose replacement re-adds the closing sentence, so applying it
duplicates that sentence.** Fixed. Round 4's C3 was applied as prose
only: the note claimed the paragraph was replaced whole while the
quoted block still stopped a sentence short. The block now includes
the closing sentence, so the note is true rather than compensatory.

Round 4 reported every before-text matching exactly once, and that
check passes here: a truncated quotation is still a unique fragment.
Extent mismatch is invisible to it.

## Minor

Each is fixed.

- M1, "three further passages" followed by five. Round 2 corrected
  this count once already; it went stale again when this round's
  import-keyword step added passages. Now stated as five and
  enumerated.
- M2, the new case-36 comment over-claimed: Rule 2's blanking also
  blanks the second token of a prose line whose first token is the
  word `import`, the two being the same shape. The comment now says
  so, matching what the plan already documents for `role_filter`.
- M3, a two-item list rendered as one bullet plus a bare paragraph.
- M4, a wrapped sentence putting `2.` at line start, which Markdown
  reads as an ordered-list item.
- M5, `TODO.md` § Verso adoption scope 1 belongs in the sweep's
  known instances: it calls Verso docstrings contraindicated for the
  upstream-eligible subtrees, and this workstream makes `GebLang/`
  upstream-eligible with Verso docstrings.

## Cosmetic-taste

- C1, the `check_subtree` usage-comment replacement left a ragged
  line: now pinned through the sentence's tail.
- C2, a new `README.md` sentence restating its own neighbour:
  the redundant half is dropped.
- C3, a loose list item among tight ones: normalised.
- C4, the `Cslib`-spelling `TODO.md` entry named two carriers and not
  the other two this plan edits: all four now named.

## Re-verification after the fixes

The B1 fix changes the substitution again, so nothing carries over:

- All 195 files in the four existing subtrees extract with no
  difference outside import lines.
- The extraction self-test passes every assertion, including the four
  new ones on the converting arm.
- `scripts/tests/test-check-transitive-imports.sh` passes five of
  five.

The reviewer's own run before the fix found the rest clean: 53 of 53
lint cases, both linters clean on the tree at 197 and 196 files,
every other quoted before-text matching once, and every edited
document coherent end to end.
