# Library plan, adversarial review round 4: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Blocker](#blocker)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [The `doc.verso.module` question, decided](#the-docversomodule-question-decided)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a fourth fresh general-purpose agent, no conversation
context, reading the three earlier records only after forming its own
view.

## Verdict

Round 4: NOT CONVERGED. One blocker, one serious, five minor, two
cosmetic-taste, no new spec defect.

Every finding is fixed.

## Blocker

**B1, the `TODO.md` scope-1 replacement contains a mangled clause
naming an entry that does not exist.** Fixed. The text the executor
would have copied verbatim read "doc-gen4 drops not render
`GebLang`'s Verso docstrings", a collision between the entry title
Task 4 writes and an older phrasing.

This was round 3's own M1 fix, and the cause is worth recording: the
fix was applied as a blind string replacement of `doc-gen4 does` by
`doc-gen4 drops`, which hit the middle of a sentence rather than the
cross-reference it was aimed at. That is the third time in this
artifact that a fix has been worse than the defect it replaced, and
all three were mechanical edits made without reading the result. The
passage is now rewritten whole and read back.

Nothing in the Markdown gate catches prose of this kind: the
reviewer applied the edit to a scratch `TODO.md` and `markdownlint`,
`doctoc` and Vale were all clean.

## Serious

**S1, the `ci-and-workflow.md` cache-get re-flow leaves an orphan
line mid-paragraph.** Fixed. The pinned region ended mid-sentence, so
the re-flow could not complete and the committed result would have
carried a 22-character line between two full ones. This is the same
defect round 3's M4 fixed in `scripts/pre-push.sh` and that round 3's
M3 claimed to have fixed in this file; it had not. The pinned region
now runs to the end of the sentence group and the replacement
re-flows through it.

## Minor

Each is fixed.

- M1, a replacement described as covering six lines where the
  paragraph has five.
- M2, the stub-comment before-text quoted three lines against a
  five-line replacement, so a literal substitution would have
  duplicated two lines. Now quoted whole.
- M3, the `serve` poll could not cover its own first compile: the
  step now builds `verso-serve` first, raises the retry budget to ten
  minutes, and redirects the background server's output to a file,
  which is also where the port it chose is readable.
- M4, the umbrella docstring asserted an allowance plan 2 creates
  ("every other library here may import them"). Reworded to state
  what is true at that commit, that its modules import nothing of
  this repository. This was a second forward dependency of plan 1 on
  plan 2, where the plan claimed there was one.
- M5, the docs-coverage reminder fires during the final pre-push run,
  because Task 5 puts `GebLang/` in its pattern and `docs/index.md`
  is plan 2's to touch. The step now says to expect it.

## Cosmetic-taste

Both fixed.

- C1, the `literate.toml` comment said the target filter runs "before
  any module is fetched". Every library's module list is fetched
  first; only the per-module literate facets are gated. The
  compilation-bounding conclusion holds, and the comment now says why
  accurately.
- C2, the placeholder's module title and opening sentence claimed the
  module holds the library's core data structures. It holds one
  placeholder. Retitled to what the module is actually for.

## The `doc.verso.module` question, decided

Round 3 escalated whether to set `doc.verso.module = false`, which
would have put module prose in both pipelines at the cost of roles in
module docstrings. Round 4 confirmed both factual claims behind the
escalation: Verso's literate renderer carries a Markdown module
docstring through to the rendered page, and doc-gen4 reads one.

The user has decided against it: `GebLang` is Verso throughout. The
option is an escape hatch for a package with existing Markdown module
docstrings to preserve, and this library starts empty. Task 4 now
records the decision and its reason rather than an open question, the
`lakefile.toml` block stays exactly as the spec specifies, and the
`TODO.md` entry recording the doc-gen4 gap stands; it closes when
doc-gen4 grows the Verso module-doc path its own source says is
intended.
