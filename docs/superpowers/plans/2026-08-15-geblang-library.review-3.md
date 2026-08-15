# Library plan, adversarial review round 3: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Blocker](#blocker)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a third fresh general-purpose agent, no conversation
context, reading the two earlier records only after forming its own
view.

## Verdict

Round 3: NOT CONVERGED. One blocker, one serious, five minor, five
cosmetic-taste, no new spec defect.

Every finding is fixed except the serious one, which is escalated to
the user because it would change a file the spec specifies verbatim.
Nothing is rejected.

## Blocker

**B1, `lake query :defaultTargets` is not a command.** Fixed.
Reproduced: `error: unknown package facet 'defaultTargets'`. This was
round 2's fix for its own M7, and it replaced a weak check with a
broken one, which is the second time a fix in this plan has been
worse than what it replaced.

The step now runs `lake build -v 2>&1 | grep ':default'`. Verified on
the current tree: it prints `Ran «geb-mathlib»/Geb:default` today, so
after Task 1 Step 1 a second line naming `GebLang` is a real
behavioural check rather than a re-reading of the edit.

## Serious

**S1, `doc.verso.module = false` would close the doc-gen4 gap this
plan escalates, and no round had considered it.** Recorded in the
plan and escalated to the user, not adopted.

Lean core registers `doc.verso.module` beside `doc.verso`
(`Lean/DocString/Extension.lean:120`): "whether to use Verso syntax in
module docstrings (falls back to `doc.verso` if not set)". Setting it
false alongside `doc.verso = true` leaves declaration docstrings as
checked Verso, with their roles, and makes module docstrings ordinary
Markdown.

The reviewer asked for one thing to be measured before the option
could be recommended, and the answer is favourable: Verso's literate
renderer does handle a Markdown module docstring. `VersoLiterateMain`
takes the Verso extension when the docstring is a `versoCommentBody`
and otherwise parses the atom with `MD4Lean.parse`, producing
`.markdownModDoc`, which `verso-literate-code` and
`verso-literate-html` both carry through as a module docstring. The
configuration would therefore put module prose in both pipelines, at
the cost of no roles in module docstrings.

It is not adopted here. The spec's § Library and layering gives the
`[lean_lib.leanOptions]` block verbatim with `doc.verso = true` and
nothing else, and a second option changes the library's authoring
model for all future content. That is the user's call, not the
executor's, so the plan records the option, the measurement and the
trade-off, and says what to re-run if the user adopts it. It is the
third item on the list for the user's review.

Worth noting for that decision: the plan's placeholder module
docstring already uses `{lit}` rather than `{name}`, because a role
cannot forward-reference within a module, so the roles actually lost
in a module docstring are fewer than the option's description
suggests.

## Minor

Each is fixed.

- M1, Task 6 cross-referenced the `TODO.md` entry by a title Task 4
  no longer gives it. Nothing catches a dangling prose reference:
  `scripts/check-md-links.sh` checks paths only.
- M2, the TOC entry the plan writes omits the backticks `doctoc`
  reproduces from the heading, so `doctoc --dryrun` in the pre-push
  checklist would fail. The plan's own fallback for a missing
  `doctoc` would have committed the wrong entry.
- M3, the `ci-and-workflow.md` cache-get before-text was not a
  literal excerpt and its replacement would have produced an
  over-length line: quoted whole, with the re-flow given.
- M4, the `pre-push.sh` cache comment edit left a short line
  mid-paragraph, the same defect the plan re-flows the stub comment
  to avoid: now replaces the whole paragraph.
- M5, § Executor context warned only about the literate build's cost.
  The first `lake build GebLang:docs` in a workspace with no
  `.lake/build/doc` is comparable: it compiles doc-gen4 and its
  SQLite dependency and generates the core documentation first.

## Cosmetic-taste

All five fixed.

- C1, a banner comment narrower than its siblings.
- C2, a citation pointing at the passing line while describing the
  failure path.
- C3, the suggested way to see the axiom linter fire is not
  performable on a `Nat` placeholder: every `Classical.choice`-
  dependent inhabitant of `Nat` is `noncomputable`, which
  `CONTRIBUTING.md` forbids. The step now points at
  `scripts/tests/test-axiom-linter.sh` instead.
- C4, the `serve` verb compiles one executable more than `build`.
- C5, `@[expose] public section` is not required for the placeholder.
  Kept, with the reason stated: content replacing the module will be
  consumed across module boundaries.

The reviewer confirmed clean, by execution, the parts earlier rounds
changed: all four Lean sources elaborate at exit 0 under the full
option set; both `-- shake: keep` annotations are necessary and
neither is redundant; round 2's auto-linking correction is right and
the `Nat` link target exists in the doc build; the `lake lint`,
`lake query` and page-inventory expectations hold; and the plan's new
prose introduces no Vale error anywhere it writes.
