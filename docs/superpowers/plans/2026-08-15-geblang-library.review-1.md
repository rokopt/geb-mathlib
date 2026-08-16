# Library plan, adversarial review round 1: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Blockers](#blockers)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Escalated to the user: a spec defect](#escalated-to-the-user-a-spec-defect)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: fresh general-purpose agent, no conversation context, over
`docs/superpowers/plans/2026-08-15-geblang-library.md` with
`docs/superpowers/plans/2026-08-15-geblang-floodgate.md` read for the
cross-plan interface.

## Verdict

Round 1: NOT CONVERGED. Two blockers, six serious, nine minor, two
cosmetic-taste, and one claim that the spec states a fact contrary to
the pinned tooling.

Every finding is fixed. Nothing is deferred and nothing is rejected.
The author re-verified each finding against the same sources before
acting; the two blockers and four of the six serious findings were
reproduced by running the tooling rather than by reading it.

## Blockers

**B1, the `{name}` role forward-references within `GebLang/Basic.lean`
and fails to elaborate.** Fixed. Reproduced: the module docstring's
`## Main definitions` entry named a constant its own file declares
later, and `lean -Ddoc.verso=true` reports an unknown-constant error
at the docstring. The entry now takes `{lit}`; the declaration
docstring keeps the checked `{name}` role the spec's § Placeholder
content asks for, and the umbrella's `{name}` reference resolves
because it imports the declaring module. The plan states the rule in
§ Global constraints so later content does not rediscover it.

**B2, a code span with no role is a warning, and
`weak.warningAsError` makes it an error.** Fixed. Reproduced under
the exact option set of `lakefile.toml`: `doc.verso.suggestions`
defaults to `true`, so
`` `doc.verso` `` and `` `GebLang` `` each failed the build.

The reviewer offered two fixes. The plan takes the second, explicit
roles on every code span, and rejects the first, adding
`doc.verso.suggestions = false` to the library's `leanOptions`:
turning the suggestion off would discard exactly the checking the
spec adopts `doc.verso` for, and it would do so for all future
content, not for the placeholder. Both corrected sources were
elaborated under the full option set and exit 0.

## Serious

**S1, `lake build GebLang:docs` was appended after the `geb-docs`
artifact upload.** Fixed: it is now inserted directly after
`lake build Geb:docs`, before the upload that carries
`.lake/build/doc`.

**S2, the pinned doc-gen4 does not render Verso docstrings.** Fixed,
and escalated below. Verified at `.lake/packages/doc-gen4`
(`db53577d4634df2604840cabb4bc74685300afe4`): declaration docstrings
are flattened to Markdown, so a `{name}` role renders unlinked
(`DocGen4/Output/DocString.lean:388-389`), and module docstrings do
not reach the page at all, `doc.verso` storing them in
`versoModuleDocExt` while doc-gen4 reads only `getModuleDoc?`
(`DocGen4/Process/Analyze.lean:154`;
`DocGen4/DB/Schema.lean:166`). The reviewer's sharpest point is that
the plan's checks could not have detected this, so the conditional
branch would never have fired and a false statement would have been
committed to `TODO.md`. Task 4 now states the measured behaviour,
measures four discriminating quantities rather than two undiscerning
ones, and records the gap unconditionally; Task 6's § Verso adoption
revision no longer claims the doc-gen4 half of the gate is met.

**S3, the site-scope check greps page content, which contains the
import list.** Fixed: the check now enumerates page files.
`show_imports` defaults to `true` and the renderer emits each page's
imports, so the `GebLang` page legitimately contains the string
`GebMeta`, which the umbrella imports.

**S4, the `public meta import` lacked its `-- shake: keep`
annotation.** Fixed. Every existing counterpart in the tree carries
it, and `lake shake` runs later in the same plan.

**S5, `lake lint` does not print the linter's `noErrorsFound` string
on a passing run.** Fixed: the expected output is
`-- Linting passed for GebLang.`, per
`.lake/packages/batteries/scripts/runLinter.lean:180`. The plan adds
how to make the axiom linter visibly fire, since a passing run does
not name it.

**S6, a wrong line range in `scripts/pre-push.sh` would have produced
an incoherent comment.** Fixed. This finding generalised: fragile
line references have been replaced with quoted before-text throughout
the `pre-push.sh` and `test-lint-driver.sh` steps, which is what the
plan-format rules require anyway.

## Minor

Each is fixed.

- M1, two more off-by-one ranges: subsumed by the S6 rewrite to
  quoted before-text.
- M2, § Global constraints asserted a no-leakage rule the umbrella's
  own docstring breaks: the sentence is now scoped to `GebLang/`
  modules, and states that the umbrella is outside the rule as
  `Geb/Mathlib.lean` is outside its subtree's.
- M3, the diagnostic note about a missing `public meta import` named
  the wrong failure mode: corrected to an elaboration error.
- M4, `test-lint-driver.sh`'s item 2 kept a sentence the change
  falsifies: the whole item is now quoted before and after.
- M5, the `TODO.md` scope-2 insertion point was ambiguous: the plan
  now names the bullet's closing sentence and says to append after
  it.
- M6, plan 1 commits a sentence about a tool behaviour plan 2
  creates: accepted as a real forward dependency and named as one in
  the plan, with the condition under which it would have to move.
- M7, `lake query :literateHtml` output purity: the facet's
  first-run Pages-setup log is now stated, along with why the CI
  capture and the `serve` verb are safe in order.
- M8, a scratch file under `/tmp`: now `mktemp -d`.
- M9, the mathlib linters do not run on a zero-import module: added
  to § Executor context, since the style constraints on that file are
  held by review rather than by tooling.

## Cosmetic-taste

Both fixed rather than rejected; each was a one-line change.

- C1, `check_coverage GebLang ""` now sits between the two existing
  calls, matching the order of the header text.
- C2, an 89-character prose line re-wrapped.

## Escalated to the user: a spec defect

The spec's § Context states that doc-gen4 at its current main renders
Verso-format docstrings natively, citing
`DocGen4/DB/VersoDocString.lean`, so that the same source feeds both
pipelines, and § Verification asks for the pin to be checked during
implementation. The measurement above shows the pin does not render
them: that file writes Verso docstrings into the SQLite database
rather than rendering them.

The spec anticipates a gap and prescribes the response, that the
docstring renders legibly as text and the gap is recorded for the
next doc-gen4 bump, and Task 4 now does exactly that. Two aspects go
beyond what the spec anticipated, and are the user's to weigh:

- The module docstring is not degraded but absent from the doc-gen4
  page. For `GebLang` that is the whole of a module's prose.
- The claim is in § Context, which the plans cite as established
  fact, rather than in a section the implementation was expected to
  revise.

The author has not revised the spec, per the handoff. The plan
proceeds under the spec's own fallback and records the gap.
