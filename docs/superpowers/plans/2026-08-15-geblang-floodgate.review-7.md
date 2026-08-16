# Floodgate plan, adversarial review round 7: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Blocker](#blocker)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Found by the author, not the reviewer](#found-by-the-author-not-the-reviewer)
- [Re-verification after the fixes](#re-verification-after-the-fixes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a seventh fresh general-purpose agent, asked whether the
closed role vocabulary round 6 introduced is itself collision-free.

## Verdict

Round 7: NOT CONVERGED. One blocker, one serious, eight minor, five
cosmetic-taste, no spec defect.

Every finding is fixed except one cosmetic-taste finding about a
paragraph whose em dashes match the file they land in.

## Blocker

**B1, the closed vocabulary is not collision-free: `name`, `lit` and
`option` are themselves ordinary Lean identifiers.** Fixed. This is
the sixth consecutive round in which this substitution has been
wrong, and the reviewer identified why round 6's fixture set could
not have caught it: all twenty shapes it checked spell the brace
group `{a}`, `{n}`, `{u}`, `{S}`, and none uses a reserved word. The
collision is invisible unless you look for it.

A code span ending in a singleton brace group is idiomatic, and it
collides exactly when the metavariable is spelled with a role name:

```text
{lit}`freeVars (var name) = {name}`  ->  `freeVars (var name) = `
{lit}`opts = {option}`               ->  `opts = `
```

`GebLang` holds the Geb language's core data structures. A term
syntax with a `lit` constructor and a `name` field, and a lemma about
`freeVars (var name)`, is the expected content, not a contrived case;
the reviewer also found the shape live in mathlib's own tree.

The fix consumes the code span through its closing backtick, so the
match is single-pass and a brace group inside a span is never read a
second time:

```bash
role_strip='s/(^|[^A-Za-z0-9.`])[{](lit|name|option)[}]`([^`]*)`/\1`\3`/g'
```

Verified against every fixture the plan carries and every shape the
earlier rounds established, plus the four colliding forms and the
mathlib instances. The `fork4` fixture gains a span ending in
`{name}`, so the collision cannot be reintroduced.

That fixture in turn exposed an assertion defect: `lacks '{name}'`
now fails on a file where the conversion is correct, the surviving
span legitimately ending in `{name}`. The assertion names the exact
role application instead, and the self-test says why a looser test
would misread surviving mathematics as unconverted markup.

## Serious

**S1, three Lean umbrella docstrings enumerate the allowed imports,
are falsified by Task 4, and neither sweep reaches them.** Fixed.
`Geb/Mathlib.lean`, `Geb/Cslib.lean` and `Geb/Internal.lean` each
list their namespace's permitted imports in prose. Task 4 falsifies
the first two directly; the third by omission, since Task 5 adds
`GebLang.*` to the `docs/index.md` bullet that parallels it, which
would have left two documents stating contradictory rules.

Both sweep patterns look for the path form `Geb/Mathlib/` and these
docstrings use the dotted module form, so an enumeration in Lean
source is invisible to a sweep written for prose. Task 6's own
Interfaces block says an instance the greps miss is a defect rather
than a gap in its list, and by that standard these were three. Task 4
gains a step correcting all three in the commit that falsifies them,
and names them in its Files block.

## Minor

Each is fixed.

- M1, § Executor context said the plan changes no Lean source, which
  its own § File structure contradicts. The consequence matters:
  `GebMeta.lean` is imported by all three root libraries, so the
  final pre-push run is a full rebuild rather than the no-op the
  executor was told to expect.
- M2, nothing compiled the manual edit. `scripts/manual.sh build` is
  now run after it.
- M3, the spelling `TODO.md` entry named seven of fifteen carriers
  and missed `docs/references.md`, which carries the same
  heading-plus-entry shape the entry calls out elsewhere. All are now
  named.
- M4, four new Vale errors at error level, in replacement prose
  rather than in quoted before-text. Reworded.
- M5, the plan-split window named Task 3 for both halves; the
  `paths:` frontmatter is extended by Task 5, so the rule-document
  half is two commits longer.
- M6, a pointer to a list of items for the user's review that does
  not exist in the plan. It now points at Task 6's closing step.
- M7, three header paragraphs inserted without the `#` separator
  every other paragraph in that header uses.
- M8, nothing tied the closed role set to the roles actually written.
  The rule-document bullet now says the extraction script converts
  exactly those three, that core registers others, and that using one
  means editing `role_strip` or shipping literal braces.

## Cosmetic-taste

Four fixed, one rejected.

- C1 and C5, the cost note understated the ratio and used a
  transient shape. Rewritten to state the ratio without a date-bound
  claim.
- C2, a header paragraph true only after the following task.
- C3, the import-keyword step's justification named the wrong part
  of Rule 1 as what rejects a doubled-space line. The conclusion held; the
  reason now matches the code.
- C4, the multi-line sweep followed `.claude/rules/`'s symlinks into
  `docs/rules/`, where `grep -r` does not, doubling those hits.
  `.claude` is now in the skip set, with the reason.
- The `docs/index.md` bullet's spaced em dashes are **not** changed.
  They match the six sibling bullets already in that file, and Vale
  does not flag them there. Rewriting one bullet to a different
  punctuation style than its neighbours would be the worse outcome.

## Found by the author, not the reviewer

A stray `</content>` line closed this plan file and four review
records, left by the tool call that first wrote each. It survived
seven rounds. `markdownlint` treats it as an inline HTML block and
Vale skips it, so no gate in the repository would have caught it, and
no reviewer read the last line of a 2879-line file. Removed from all
five.

## Re-verification after the fixes

- The extraction self-test passes all 39 assertions, including the
  new span-ending-in-`{name}` case.
- All 195 files in the four existing subtrees extract with no
  difference outside import lines.
- `scripts/tests/test-check-transitive-imports.sh` passes five of
  five.

The reviewer's own run before these fixes found the rest clean: all
30 quoted before-texts matching uniquely, 53 of 53 lint cases, both
linters clean on the tree at 197 and 196 files, the rewrite tables
complete and pairwise non-overlapping across all six arms, and the
spec's § Verification fully covered.
