# Library plan, adversarial review round 2: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Blocker](#blocker)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Effect on the escalated spec defect](#effect-on-the-escalated-spec-defect)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a second fresh general-purpose agent, no conversation
context, over `docs/superpowers/plans/2026-08-15-geblang-library.md`,
reading round 1's record only after forming its own view.

## Verdict

Round 2: NOT CONVERGED. One blocker, two serious, ten minor, six
cosmetic-taste.

Every finding is fixed. Nothing is deferred and nothing is rejected.
Two findings are incomplete fixes from round 1, which is the result
worth noting: a fresh reviewer catches what a round of self-review
after acting does not.

## Blocker

**B1, `GebTests/Lang/Basic.lean` fails `lake shake`: the plain
`public import` needs the annotation too.** Fixed. Round 1's S4 added
`-- shake: keep; #guard needs it` to the `meta` line alone. The
module declares nothing, so neither import leaves a constant
reference in the olean, and `lake shake` matches the annotation per
import line while distinguishing the `meta` form. The reviewer
reproduced the failure in a minimal two-module package: with the
annotation on the meta line only, shake reports
`remove #[public import T.Anchor]` and exits 1.

The repository's own precedent settles it, and round 1's fix cited
the wrong half of it. `GebTests/Internal/CanonicalSExpr.lean:8-11`,
whose content is likewise only `#guard`s, annotates both lines of
each pair. `GebTests/Mathlib/Data/UnionFind/OfEdges.lean:8-9`
annotates only the `meta` line, and that is why: its own declarations
reference the plain import. The plan now annotates both lines and
states which precedent applies and why.

Had this shipped, Task 5's new `lake shake` step would have failed
two tasks after the commit that caused it.

## Serious

**S2-a, the doc-gen4 measurement predicted an unlinked code span;
doc-gen4 auto-links them.** Fixed. Verified at
`DocGen4/Output/DocString.lean:260-265`: an inline `.code` span is
rendered through `autoLinkInline` unless it is already inside a link,
and `autoLinkInline` emits an anchor for every part that resolves.
The Markdown doc-gen4 consumes is a real conversion of the Verso tree
(`DocGen4/Process/NameInfo.lean:80`, `versoDocToMarkdown`), so a
`{name}` role becomes a plain code span and is then linked exactly as
a Markdown docstring's would be.

This is the second time this task has carried a wrong prediction, and
in the same direction: round 1 replaced an over-optimistic claim with
an over-pessimistic one. The measurement in Step 2 and the `TODO.md`
entry in Step 3 are both rewritten. The recorded gap is now the one
that is real and verified, that a `GebLang` module docstring is
absent from the API-reference page, and the entry no longer claims
declaration docstrings are degraded, because in substance they are
not.

**S2-b, the two Verso rules this workstream discovered were recorded
only in the plan, which is deleted at the end of the branch.** Fixed.
Every-code-span-carries-a-role and `{name}`-does-not-forward-reference
are now bullets in the `docs/rules/lean-coding.md` § Literate modules
section that Task 6 Step 1 writes, alongside a third stating what
each pipeline actually renders. The finding is a good one: both facts
cost a build failure to learn, and `CONTRIBUTING.md` § Concern shape
would have thrown away the record.

## Minor

Each is fixed.

- M1, Task 2 Step 4 still named the wrong failure mode for a missing
  `public meta import`. Round 1's M3 claimed this corrected and did
  not correct it. The reviewer reproduced the real message, an
  elaboration error naming the inaccessible constant and suggesting
  the import; the plan now says that.
- M2, the `lake query` purity apparatus rested on an unverified
  premise. `lake query --help` states that progress goes to standard
  error and results to standard out, so the facet's first-run notice
  never reaches the capture. The paragraph is replaced by that fact,
  keeping the check itself.
- M3, the expected page inventory was wrong: the renderer writes one
  `index.html` per module directory plus a site root and a search
  page. The step now states the real expected set and makes the
  assertion about which module directories exist.
- M4, `lintDriverArgs` precede the command line's arguments, so
  `lake lint -- GebLang` runs the driver on `Geb GebLang` and prints
  a passing line for each. The expected output now says so, and notes
  that this re-lints `Geb` on every `scripts/literate.sh build`.
- M5, the axiom-linter bullet replacement could truncate the bullet:
  a "leaving the rest unchanged" clause is added, as the plan already
  does elsewhere.
- M6, the stub-comment rewrap left a two-word line: the whole
  paragraph is now quoted and replaced.
- M7, `lake build` does not name its targets on a warm run:
  the step now checks `lake query :defaultTargets`.
- M8, `grep -c` exits 1 on a zero count, which is the expected result
  of one of the measurements, so the block would abort under `set -e`:
  `|| true` added to each line, with the reason stated.
- M9, `doc-build.yml`'s `timeout-minutes: 60` against the new load:
  the plan now asks the executor to record the local literate-build
  time and to say if the budget looks close, rather than raising it
  speculatively before any evidence exists.
- M10, the spec asks the new section to say the markup must remain
  acceptable to both pipelines, which Task 4's finding makes
  impossible to write as worded. The plan now states the true
  relation and names the deviation, rather than dropping the sentence
  silently.

## Cosmetic-taste

All six fixed; each was a line or two.

- C1, `scripts/literate.sh`'s header claimed `literate.toml` and the
  output path resolve against the working directory; they are
  package-relative. Only the nolints path is cwd-relative.
- C2, § File structure named the workflows without their
  `.github/workflows/` prefix.
- C3, a citation split across two code spans.
- C4, the blank line between `pre-push.sh` steps.
- C5, a step titled "check the workflow files parse" also ran the
  Markdown linters, over a task that touches no Markdown: the
  Markdown command is dropped.
- C6, "extend the two build bullets" over four bullets.

## Effect on the escalated spec defect

Round 1 escalated the spec's § Context claim that the pinned doc-gen4
renders Verso docstrings natively. Round 2 sharpens rather than
reverses it, and narrows what is actually lost:

- Declaration docstrings: not materially degraded. They are converted
  to Markdown and their code spans are auto-linked, so the page is
  close to what a Markdown docstring produces. The role's checking is
  not lost either, elaboration having performed it.
- Module docstrings: absent from the page entirely. This is the whole
  of the gap, and it is the whole of a `GebLang` module's prose.

The escalation stands on the narrower ground, and the plan's recorded
`TODO.md` entry now matches it.
</content>
