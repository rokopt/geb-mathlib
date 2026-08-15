# Library plan, adversarial review round 5: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Clean](#clean)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a fifth fresh general-purpose agent, no conversation
context, reading the four earlier records only after forming its own
view.

## Verdict

Round 5: NOT CONVERGED. No blocker, three serious, four minor, five
cosmetic-taste, no spec defect.

Every finding is fixed. All three serious findings are damage from
earlier rounds' fixes, which is now the dominant defect source in
this artifact rather than an occasional one.

## Serious

**S1, the doc-gen4 measurement greps for a string no source contains,
so the task's measurement is vacuous.** Fixed. Task 4 Step 2 searched
the rendered page for `Anchor for the Geb language`; round 4's C2
retitled the module docstring, to one naming the library's
documentation pipelines, and did not update the grep that reads it.
The count would have been zero whatever doc-gen4 did, Step 2 reads
zero as the gap being present, and the `TODO.md` entry and the
§ Verso adoption revision both rest on it. The grep now takes
`Anchor for the library`, a fragment of the real title that stops
before the apostrophe.

**S2, the `ci-and-workflow.md` cache-get re-flow still leaves an
orphan line.** Fixed, on the third attempt. Round 3's M3 and round
4's S1 each claimed this fixed; each pinned a longer prefix of the
paragraph and each left a short line stranded. The reviewer diagnosed
why: the sentence that changes ends mid-line inside a filled
paragraph, so no prefix can be re-flowed cleanly, and it checked
three candidate pin points to confirm. The whole bullet is now
pinned and re-flowed, and the plan says why a smaller region will not
do.

**S3, the justification for the new `lean-coding.md` section names
the wrong bullets and states two false things about them.** Fixed.
The passage said "the last two bullets record what this workstream
measured"; the last two are the ordinary-Lean-files bullet, which
restates the spec and measures nothing, and the two-pipelines bullet,
which is measured but is not discoverable by build failure. The
bullets that are both are the two on roles. The sentence now names
the three that were measured and says how each is discovered, which
matters because it is the only argument for keeping this content in a
persistent document under `CONTRIBUTING.md` § Code is cost.

## Minor

Each is fixed.

- M1, a step announcing three edits and giving four.
- M2, three edit artifacts left unwrapped, one over the 80-column
  rule in a way `markdownlint` does not catch.
- M3, the spec deviation was escalated against § Context alone. The
  same finding also reverses a sentence in § Standards and rule
  documents, which has the `TODO.md` revision record the doc-gen4
  half of the gate as met at the pin. Both are now named.
- M4, the `doctoc` title-line warning is false for this step: under
  `--update-only`, on a file that already has markers and no title
  line, `doctoc` leaves it that way. The reviewer verified this by
  forcing a regeneration and getting a byte-identical file. The
  warning is now scoped to a file given markers for the first time.

## Cosmetic-taste

All five fixed.

- C1, a duplicated instruction about where to read the served port.
- C2, a paragraph opening with a lowercase conjunction across an
  intervening paragraph.
- C3, `docstrings_as_text` described as rendering docstrings "beside
  their code"; Verso's own description is prose text rather than
  inside code boxes.
- C4, `|| true` is inert on the two piped `grep -o` lines; kept for
  uniformity, with the reason stated.
- C5, the `mk_all-check` rationale three lines from an edited step is
  left to plan 2's sweep, which the plan now notes rather than
  leaving the adjacency unexplained.

## Clean

The reviewer confirmed by execution: all four Lean sources elaborate
at exit 0 under the full option set; the three negative controls
reproduce exactly; every before-text matches once and all nine edited
files are coherent read end to end; `lake query :defaultTargets`
errors as the plan says and `lake build -v | grep ':default'` prints
what it says; every doc-gen4, Lean-core and Verso citation is exact;
and nothing this plan adds falls inside `scripts/lint-imports.sh`'s
scanned roots, so the floodgate is untouched until plan 2.

It also examined five things no round had: the literate planner's
target filter and its hard validation of `landing_page`; the
page-inventory comment in the HTML renderer, which confirms the
expected set exactly; `lake shake --keep-prefix`'s arity, which makes the widened
invocation a three-module list rather than a prefix plus two;
`doctoc`'s title-line behaviour (M4); and whether another self-test
pins the shake invocation, which `test-lake-shake.sh` does
deliberately and is unaffected.
