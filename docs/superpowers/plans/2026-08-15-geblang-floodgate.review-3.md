# Floodgate plan, adversarial review round 3: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Re-verification after the fixes](#re-verification-after-the-fixes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: a third fresh general-purpose agent, no conversation
context, which re-transcribed and re-ran every script the plan writes
and attacked the role-strip, the track walk and the Rule 2 diagnostic
with adversarial inputs.

## Verdict

Round 3: NOT CONVERGED. No blocker, two serious, ten minor, four
cosmetic-taste, no spec defect.

Every finding is fixed. Nothing is deferred and nothing is rejected.

## Serious

**S1, the role strip ran over an arm whose sources carry no roles,
and there too it deleted Lean.** Fixed. `GebTests/Lang/` belongs to
the `GebTests` library, which does not set `doc.verso`; plan 1 says
so outright. Setting `convert_roles=1` there contradicted the
script's own comment and round 2's gating rationale, which was that
running the strip where nothing needs converting is pure risk.
Reproduced: a `GebTests/Lang/` docstring reading
`` `Nat.rec {motive}` `` extracted as `` `Nat.rec ` ``.

The arm now sets `convert_roles=0`, and the comment names one arm
rather than two. Verified after the fix: the same fixture extracts
unchanged.

The reviewer's second half of this finding is the sharper one, and it
is now in the script. The narrow pattern excludes the two constructs
round 2 cited, but it does not exclude a lone brace-delimited
identifier ending a code span, `` `Nat.rec {motive}` `` being exactly
that. The comment claimed safety; it now names the residual and says
what bounds it, that the one arm running the strip holds docstrings
whose author is writing Verso.

**S2, the `GebTests/Cslib/` arm's per-track `GebLang.` rewrite had no
self-test case, which the spec's § Verification requires.** Fixed.
The fixture imported no `GebLang.` module at all, so that arm's
`GebLang. @src` entry was never exercised. It now imports one module
of each track, with the two matching assertions. This is the same
mirror-coverage omission round 1 graded serious in the lint
self-test, in a different file.

## Minor

Each is fixed.

- M1, the § Literate modules section plan 1 writes has six bullets,
  not three, so "add a fourth bullet" named no insertion point: the
  instruction now says which bullet to follow.
- M2, `manual/GebManual/Introduction.lean` enumerates the
  upstream-directed layout exhaustively and is falsified by this
  workstream. Only the multi-line scan reaches it, and Task 6's
  fix-everything step named Step 1 alone. The file is now a named
  instance and the step covers both scans.
- M3, `docs/rules/lean-coding.md`'s two "binding upstream references"
  sentences are left incomplete once Cslib's constraints extend to
  Cslib-track `GebLang/` modules. They sit 139 lines apart, so no
  windowed scan pairs them; both are now named instances.
- M4, case 36's comment still stated the superseded line-anchored
  rule while its title was retitled. The comment is now quoted and
  replaced, and cases 8 and 9 get the same treatment.
- M5, `scripts/tests/test-extract-pr.sh`'s header describes a rewrite
  the plan replaces. The plan corrects the parallel sentence in the
  lint self-test's header and had missed this twin.
- M6, § Executor context claimed Vale binds through `.vale.ini`
  regardless. It does not: nothing in `scripts/` or the workflows
  invokes it. Worse, the files this plan edits are already dirty, so
  "run Vale and read the output" had no pass criterion. Both plans
  now state the criterion as no *new* alert against the file's
  output before the edit.
- M7, the plan's replacement prose introduces six Vale errors while
  removing more than it adds. Two are sentence-initial `Mathlib`,
  two are capitalised `Subtree` in section cross-references, one is
  `write-good.ThereIs`, one is a spelling. Since nothing runs Vale
  the effect is advisory, but the differential criterion of M6 makes
  them visible to the executor, which is the right handling: the
  prose is reworded where a rewording is honest and left where the
  section name is the section's name.
- M8, `check-transitive-imports.sh` is the slowest step in the
  checklist, several times `lint-imports.sh` over the same files,
  because Pass 1 recomputes each root's closure and greps every file
  in it twice. The script now names the ceiling and the repair
  (caching `reaches_cslib` per file) rather than carrying the cost
  silently.
- M9, `import_kw_re` ends in a literal single space, so a doubled
  space after the keyword defeats Rule 1's collection and Rule 2's
  blanking and produces two diagnostics for one malformed line. A
  step now widens it to `import[[:space:]]+`, matching the form the
  extraction script uses.
- M10, "Add after it" was ambiguous once an earlier step had inserted
  a paragraph in the same place: the instruction now names the
  neighbour and the resulting order.

## Cosmetic-taste

- C1, a `./`-prefixed source path was rejected with the generic
  usage error, and `find .` is the natural way to produce one:
  the script now strips the prefix.
- C2, a quoted `TODO.md` opening line stopping at the colon: the plan
  says the entry beginning with that line, which the reviewer judged
  exact enough. No change.
- C3, a role taking arguments ships as literal braces with nothing
  detecting it: the script's comment now says so explicitly rather
  than only saying to add the form when one is used.
- C4, a `GebLang/` docstring line beginning with the word `import` is
  treated as an import line by the rewrite loop. Left as it is: the
  construct is a docstring line starting with a bare keyword, which
  neither the placeholder nor any plausible content writes, and
  guarding it would cost more than it saves.

## Re-verification after the fixes

The S1 fix changes the extraction script, so earlier results do not
carry over. Re-run after the round-3 edits:

- All 195 files in the four existing upstream-eligible subtrees
  extract with no change outside import lines.
- The extraction self-test passes every assertion, including the two
  new `GebTests/Cslib/` per-track cases.
- A `GebTests/Lang/` docstring carrying `` `Nat.rec {motive}` ``
  extracts unchanged.
- `scripts/tests/test-check-transitive-imports.sh` passes five of
  five.
- A `./`-prefixed source path resolves to the right destination.

One consequence of this round's renumbering: the round-2 record
refers to the header-comment work as Task 3 Step 4, which the new
import-keyword step makes Step 5. Review records are history rather
than requirements, so the earlier record stands as written.
