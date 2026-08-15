# GebLang literate design: adversarial review, round 6

Reviewer: fresh-context agent, 2026-08-15. A full fresh read
against the repository's prose corpus (`TODO.md`, `README.md`,
`CONTRIBUTING.md`, `AGENTS.md`, `docs/*.md`, all rule files,
script and workflow comments) plus environment spot-checks, all
of which held: the facet fold, the planner's scoping and
landing-page validation, the glob semantics, the `v4.29.0`
landing of the literate pipeline, the flag form of
`--keep-prefix`,
the axiom linter's lack of a per-library filter, and Cslib's
transitive `checkInitImports`. The technical design survived
the round; the findings are completion-of-ripple scheduling
gaps.

Verdict: not converged (no blocker; two serious findings). Every
finding is addressed below; the spec edits land in this round's
commit.

## Findings and responses

Serious.

1. `TODO.md` § Verso adoption is falsified: its scope-1 gate is
   half met at the pin (doc-gen4 renders Verso docstrings), its
   mechanism is superseded for `GebLang` by the extraction-time
   docstring conversion, and its scope-2 exposition bullet
   overlaps the literate site; none of this was scheduled.
   Fixed: the
   revision is scheduled in § Standards and rule documents and
   the `TODO.md` verification item names it.
2. The policy-scope enumerations naming only the existing
   subtrees are falsified in four places none of which were
   scheduled: `CONTRIBUTING.md`'s LLM-policy sentence,
   `AGENTS.md`'s § AI authoring sentence and path-scoped heading
   (with TOC), `README.md` § Process's applies-under line, and
   `docs/rules/upstream-eligible.md`'s in-body applies-to
   sentence. Fixed: all four scheduled.

Minor.

1. The pre-push docs-coverage reminder's path pattern omits
   `GebLang/`. Fixed: widened, with the checklist enumeration in
   `docs/rules/ci-and-workflow.md` following.
2. "Adds a `GebLang` row" was singular; the table's convention
   is one row per subtree including test roots. Fixed: both rows,
   with the conditional `Cslib.Init` noted.
3. The accepted cross-track ordering and the `TODO.md` entry
   recording the same cost as a case against carry no
   acknowledgment of each other. Fixed: mutual cross-references
   scheduled.

Cosmetic-taste.

1. A reflow artifact in § Context. Fixed.
