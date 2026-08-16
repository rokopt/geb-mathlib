# Floodgate plan, adversarial review round 8: response

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verdict](#verdict)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [The role-strip, seventh attack](#the-role-strip-seventh-attack)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewer: an eighth fresh general-purpose agent, asked to attack the
role-strip a seventh time and to verify round 7's other changes by
applying them.

## Verdict

Round 8: NOT CONVERGED. No blocker, one serious, two minor, two
cosmetic-taste, no spec defect.

Every finding is fixed. The role-strip held.

## Serious

**S1, the new umbrella-docstring step fixes one contradiction and
creates another.** Fixed. Task 4 Step 8's stated reason for touching
`Geb/Internal.lean` is that `docs/index.md`'s parallel bullet gains
`GebLang.*`, so leaving the docstring alone would have two documents
disagree. The replacement it specifies adds two prefixes, `GebLang.*`
and `Batteries.*`, where Task 5 Step 7's bullet adds only the first.
After the plan runs, the docstring would say `Geb/Internal/` may
import `Batteries.*` and `docs/index.md` would say it may not.

Nothing arbitrates: `Geb/Internal/` is outside
`scripts/lint-imports.sh` entirely, and neither sweep reaches either
statement. The `.lean` text is the correct one, `Batteries.*` being
genuinely importable there and now admitted to every upstream-eligible
subtree by Task 4 Step 2, so the `docs/index.md` bullet gains it too.

The reviewer checked all three umbrella-and-bullet pairs; the other
two agree with each other and with the widened `check_subtree` calls.

## Minor

Both fixed.

- M1, the `Geb/Mathlib.lean` replacement pinned a sentence that ends
  mid-line, stranding the rest as a 95-column line against 70-column
  neighbours. Under `lean-coding.md`'s 100-character limit, so no gate
  catches it. The whole paragraph is now quoted and re-flowed, as
  three other steps in this plan already do for the same reason. The
  other two umbrellas are unaffected, their sentences ending at a line
  end.
- M2, the spelling `TODO.md` entry listed `scripts/extract-pr.sh` as a
  carrier of the capitalised spelling. Task 1 rewrites that file
  whole, in the accepted spelling, four commits earlier, so the entry
  would be false the moment it landed. Dropped from the list, with a
  note on why `scripts/lint-imports.sh` stays.

## Cosmetic-taste

Both fixed.

- The new self-test was never made executable, unlike ten of the
  eleven scripts already in `scripts/tests/`. Nothing breaks, every
  invocation being through `bash`, but the odd one out is the new one.
- Task 6's confirmation sentence for `scripts/pre-push.sh` named five
  of plan 1's six edits to it.

## The role-strip, seventh attack

No defect. This is the first round in which it has survived, and the
attack was the widest yet: an odd number of backticks on a line, a
double-backtick span, a backslash inside a span, an empty span, three
roles on one line, a role at end of file with no trailing newline, a
role split across a line break, and a role-like token inside a fenced
code block. Each converts correctly or degrades to the documented
visible-braces failure; none deletes mathematics.

The reviewer also ran the substitution over all 230 `.lean` files in
the repository rather than the four subtrees alone. One file changes:
`manual/GebManual/WTypes.lean`, whose six `{name}` roles convert
correctly. That file is outside every extraction arm, so the run was a
probe rather than a prediction, but it is the first evidence from real
Verso prose rather than fixtures.

Round 7's other changes verified: the three umbrella docstrings'
before-texts match byte-for-byte, the Task 4 renumbering leaves all
eleven cross-references resolving, the widened `TODO.md` entry matches
the tree, and the `.claude` skip is correct, that directory holding
four symlinks into `docs/rules/` which `grep -r` does not follow but
`open()` does.

Re-run after this round's fixes: extraction self-test 39 of 39, lint
self-test 53 of 53, transitive self-test 5 of 5, both linters clean on
the tree at 197 and 196 files, and all 195 files in the four existing
subtrees extracting with no difference outside import lines.
