# Floodgate plan, adversarial review round 4: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Re-verification after the fixes](#re-verification-after-the-fixes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a fourth fresh general-purpose agent, no conversation
context, which re-executed every script from the plan text as it then
stood and attacked the role-strip a third time.

## Verdict

Round 4: NOT CONVERGED. No blocker, one serious, three minor, eight
cosmetic-taste, no spec defect.

Every finding is fixed. The role-strip survived its third attack with
no blocker, which is the first round that has been true of it.

## Serious

**S1, the new `ci-and-workflow.md` bullet binds "the first" and "the
second" to the wrong pair and ships two false statements.** Fixed.
Both ordinals sit inside a bullet whose two named items are the
checker and its self-test, so as written the sentence said the
checker bounds direct imports and its self-test bounds the closure.
Both scripts are now named explicitly, matching how every other
passage in the plan states the same contrast.

## Minor

Each is fixed.

- M1, the new import-keyword step justified itself with two false
  claims about Rule 1. Rule 1's collection is not defeated by a
  doubled space, and the rejection comes from its own prefix
  comparison, which this step does not touch. The change is right and
  its last sentence was right; the justification is now rewritten to
  what the reviewer measured.
- M2, `role_filter` exempted import lines from role conversion, which
  also exempted any docstring line opening with the word `import` and
  shipped its roles as literal braces. The reviewer proposed a
  tightened address requiring a module-shaped token; that does not
  discriminate, an English word being the same shape, and it was
  tested and rejected on that ground. The address is dropped
  instead: no line is exempt. An import line's module path holds no
  braces, and a role in a trailing comment wants converting like any
  other. Verified after the change: the prose roles convert, real
  import lines still rewrite, all 195 existing files still extract
  with no non-import difference, and the self-test passes.
- M3, `track_of` resolves a `GebLang.` module with no file on disk to
  mathlib-track and emits it under `Mathlib.`, with nothing before
  `lake build` catching it. The default is defensible; the silence
  was not, and the walk's comment now states it.

## Cosmetic-taste

Six of eight taken; two declined with reasons.

- C1, two abutting roles convert to spans CommonMark merges. Declined
  as a change: no Verso prose writes that, and guarding it would cost
  more than it saves. Recorded here rather than in the script.
- C2, the read loop adds a trailing newline to a source lacking one:
  now stated in the script's comment.
- C3, a `docs/process.md` replacement ending mid-line: the paragraph
  is now replaced whole.
- C4, `docs/rules/upstream-eligible.md` half-migrates from the word
  subtree to the word location, while its heading and table column
  keep the older one. Folded into the `TODO.md` trigger entry Task 5 Step 11
  records, which already covers a retitling pass over that document.
- C5, two ragged shell-comment wraps: re-flowed.
- C6, cases 8 and 9 got "restate those two the same way" where every
  other prose edit is quoted: both are now quoted before and after.
- C7, Tasks 1 and 3 edit `TODO.md` and commit with no Markdown check,
  unlike Tasks 4 and 5: both now run the checks before committing.
- C8, `TODO.md` § Repo-relative paths says the extraction script
  rewrites import lines only, which Task 1 falsifies as a description
  of the script though the entry's own claim survives. Added to Task
  6's known instances.

## Re-verification after the fixes

The M2 fix changes the extraction script again, so nothing carries
over:

- All 195 files in the four existing subtrees extract with no
  difference outside import lines.
- The extraction self-test passes every assertion.
- A `GebLang/` docstring whose prose lines begin with `import` and
  `meta import` now has its roles converted, and a real import line
  in the same file is still rewritten to its destination prefix.

The reviewer's own run before these fixes found the rest clean: 53 of
53 lint cases, 5 of 5 transitive cases, both linters clean on the
tree at 197 and 196 files, every quoted before-text matching exactly
once across all six tasks, and `docs/rules/upstream-eligible.md`
coherent end to end after all fourteen of its edits.
