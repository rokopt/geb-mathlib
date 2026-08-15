# Floodgate plan, adversarial review round 1: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [What the reviewer established by execution](#what-the-reviewer-established-by-execution)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Escalated to the user: the plan-split window](#escalated-to-the-user-the-plan-split-window)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: fresh general-purpose agent, no conversation context, over
`docs/superpowers/plans/2026-08-15-geblang-floodgate.md` with
`docs/superpowers/plans/2026-08-15-geblang-library.md` read for the
cross-plan interface.

## Verdict

Round 1: NOT CONVERGED. No blocker, two serious, eleven minor, two
cosmetic-taste, no spec defect.

Every finding is fixed. Nothing is deferred and nothing is rejected.

## What the reviewer established by execution

The reviewer transcribed the plan's proposed scripts into a scratch
tree and ran them, rather than reading them. That evidence is the
reason this round found no blocker, and it is worth recording:

- The extraction self-test, the eight existing assertions plus the
  plan's new ones, passes.
- The lint self-test with the plan's edits applied, cases 6 and 29
  inverted and the new cases appended, passes.
- The transitive-check self-test passes.
- Both linters report `clean (195 file(s) checked)` on the real tree,
  and the narrowed Rule 2 flags nothing that exists today: the import
  lines carrying trailing comments all carry `-- shake: keep` text
  with no self-prefix in it.
- Extraction of plan 1's two placeholder sources produces
  `Mathlib/Basic.lean` and `MathlibTest/Basic.lean` with both import
  forms rewritten and the role markup converted.

The reviewer also answered each shell question the brief raised:
the `BASH_REMATCH` group numbering is right, the nested heredoc does
not consume the outer loop's stdin, the quoted-variable `case`
pattern matches literally, the `sed` address plus `!` plus `s` form
is valid, both worklist walks terminate on a cycle, the Rule 2
capture group is the outer one, the `errors` increment survives, and
nothing used is outside bash 3.2. The upstream claims check out at
the pins: Cslib requires mathlib, imports Batteries directly, and
keeps its tests under `CslibTests/`, and Cslib's own
`checkInitImports` is transitive.

## Serious

**S1, `docs/rules/upstream-eligible.md` would ship self-contradictory
about the narrowed Rule 2.** Fixed. The section's opening paragraph
states the superseded whole-line exemption twenty-five lines above the
sentence Task 5 Step 4 was updating. Task 5 Step 4 now replaces the
opening paragraph too.

The finding generalised, and the generalisation is the more valuable
half: the same superseded wording appears three times in
`scripts/lint-imports.sh`'s own header, which M1 and M11 caught. Task
3 Step 4 now quotes and replaces all three.

**S2, a self-test case announced two rejections and delivered one, and
a spec-enumerated mirror case had no fixture.** Fixed. Task 4 Step 4
gains a `GebLang.` leakage fixture in `GebTests/Mathlib/` and a
`Geb.Cslib.*` import fixture there, so the mirror runs the same
acceptance and rejection cases as its source root, which is what the
spec's § Verification asks for. The comment that named two
rejections is corrected, and the cases are renumbered.

## Minor

Each is fixed.

- M1 and M11, the linter header's opening paragraph and its
  `check_subtree` usage comment kept the superseded whole-line
  exemption and the unconditional init rule: both are now quoted and
  replaced in Task 3 Step 4, with S1.
- M2, the Rule 2 diagnostic echoed the blanked copy of the line, so
  it quoted text appearing nowhere in the file. The diagnostic now
  takes the line number from the blanked copy and the text from the
  file. Verified on a fixture: it reports both the comment-tail
  violation and the body violation, quoting what the author wrote.
- M3, a case's comment claimed to test the `meta import` trigger
  while its fixture also satisfied the requirement, so it passed
  either way: split into a case that triggers on a lone
  `meta import` and asserts the failure, and a case that satisfies it.
- M4, the cross-plan boundary: escalated below rather than merely
  fixed, since it is a property of the spec's plan split. The plan's
  § Global constraints no longer asserts the invariant
  unconditionally.
- M5, the sweep grep did not exclude `docs/superpowers/`, so half its
  hits were the transient documents the branch later deletes:
  excluded, with the reason stated.
- M6, "three widened lists" over four lists: three widened prefixes.
- M7, the Batteries-rationale replacement needed a re-flow the plan
  did not mention, the first sentence ending mid-line: the whole
  paragraph is now quoted before and after. The reviewer's second
  point, that the retained "That rationale applies to a module whose
  own upstream target is mathlib4" reads oddly after a rationale
  covering Cslib as well, is fixed in the same rewrite.
- M8, two repository files can name one upstream destination
  (`GebLang/Foo.lean` and `Geb/Mathlib/Foo.lean` both map to
  `Mathlib/Foo.lean`): recorded in the extraction script's header,
  with the observation that the destination path is printed on every
  run. No detection machinery is added; the spec does not ask for it,
  and the collision is a naming choice a reader makes deliberately.
- M9, a header paragraph stating a fact one commit before it becomes
  true: hedged to name the commit that makes it true.
- M10, the role-strip comment claimed too much, that no Lean
  expression produces the pattern: softened to name the construct that does, and
  to say why the four `Geb`/`GebTests` arms run the strip harmlessly.
- The reviewer's observation that Cslib's `checkInitImports` filters
  to the `Cslib` root and so never covers `CslibTests` is recorded
  here rather than in the plan: our conditional rule is stricter than
  upstream on the test tree, which costs nothing and keeps one rule
  for both.

## Cosmetic-taste

Both fixed rather than rejected.

- C1, the rule-document edits write `Cslib` into a document whose
  heading and several untouched sentences use the other spelling.
  Normalising the document is a separate concern under
  `CONTRIBUTING.md` § Concern shape, so Task 5 gains a step recording
  it as a `TODO.md` trigger rather than bundling it.
- C1's parenthetical, that this environment's settings disable a Vale
  agent tool, is handled differently: rather than assert what a hook
  does, both plans now tell the executor to run
  `vale --minAlertLevel=error` and `markdownlint-cli2` themselves,
  which is true whatever the harness is configured to do.
- C2, a commit subject counting "the third library": renamed to name
  `GebLang`.

## Escalated to the user: the plan-split window

The plan asserted that the floodgate invariant holds at every commit
of the branch. The reviewer showed it does not hold at the end of
plan 1: `GebLang/Basic.lean` and `GebTests/Lang/Basic.lean` exist
there, and until this plan's Task 1 `scripts/extract-pr.sh` rejects
both roots outright and leaves their role markup unconverted.

No ordering of the two plans closes the window. The extraction
extension has nothing to extract until the library exists, and the
spec mandates the split with the library first. This plan's Task 1 is
its first commit so that the window is as short as the split allows,
and § Global constraints now states the window rather than asserting
around it.

What is left for the user is whether the window is acceptable, since
`CONTRIBUTING.md` § Floodgate test is written as an at-all-times
property. Two considerations: the branch is not pushed between the
plans, so no merged state exhibits it; and the files in the window are
a placeholder declaration and a `#guard`, which no upstream PR would
carry.
</content>
