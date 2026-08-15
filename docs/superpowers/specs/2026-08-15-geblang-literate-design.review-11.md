# GebLang literate design: adversarial review, round 11

Reviewer: fresh-context agent, 2026-08-15. Subject: closure of
round 10's responses. Every round-10 fix verified against the
scripts and the environment: the per-imported-module-track
rewrite is complete and implementable, the four arms' rewrites
and four-form coverage check out, the commit ordering and
two-plan structure are coherent, the three `TODO.md` resolutions
dangle nothing, and the residue sweep found only sanctioned
deferrals.

Verdict: not converged (no blocker; one serious finding). Every
finding is addressed below; the spec edits land in this round's
commit.

## Findings and responses

Serious.

1. Test-sibling imports inherited round 10's blocker class:
   `GebTests.Lang.*` sibling imports (and the existing arms'
   `GebTests.<subtree>.` imports, a pre-existing gap with real
   in-tree instances and no `TODO.md` entry) had no specified
   extraction rewrite, and a Cslib-track `GebTests/Lang/` test
   importing a mathlib-track sibling has no shippable form at
   all. Fixed on all three directions the reviewer identified:
   the extraction gains test-sibling rewrites to the destination
   test tree (uniform for the existing arms, whose closures the
   check proves single-track; per-track for `GebTests.Lang.`),
   the pre-existing gap folds into this workstream's script
   revision, and the mixed case, which cannot ship, is
   forbidden by a
   second pass of the transitive-import check (a Cslib-track
   `GebTests/Lang/` module's imported siblings must be
   Cslib-track), stated in the rule file and exercised by the
   self-tests.

Minor.

1. The lint self-test fixtures named only the two `Geb/`
   subtrees, dropping the mirror case the resolved cross-track
   `TODO.md` entry had flagged. Fixed: the acceptance and
   rejection cases run in the `GebTests/Mathlib/` and
   `GebTests/Cslib/` mirror fixtures too.
