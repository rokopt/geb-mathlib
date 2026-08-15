# GebLang literate design: adversarial review, round 7

Reviewer: fresh-context agent, 2026-08-15. A full fresh read plus
a grep sweep of the committed corpus for prose the design
falsifies, and environment spot-checks (facet fold, decoder,
planner validation, Rule 1b's satisfying form, the shake flag
form, the fixture shape of the lint self-test), all of which
held. The technical design survived the round; the findings are
the remaining documentation ripple.

Verdict: not converged (no blocker; one serious finding). Every
finding is addressed below; the spec edits land in this round's
commit.

## Findings and responses

Serious.

1. The two-track porting-destination statements
   (`docs/rules/upstream-eligible.md` § Two-track development:
   the two `Geb/` subtrees are "the only destinations for ported
   content"; the parallel sentence in `docs/process.md`) are
   falsified by `GebLang` as a third destination, and neither was
   scheduled. Fixed: both scheduled in § Standards and rule
   documents.

Minor.

1. Whether the Cslib-specific constraints beyond `Cslib.Init`
   (notation locality, PR titles, pre-coordination) bind
   Cslib-track `GebLang` modules was unstated. Fixed: the
   section's scope extends to them; they ship to Cslib, so the
   constraints bind at authoring time.
2. The README introduction's upstream-route enumeration is a
   third README sibling the design falsifies. Fixed: scheduled.
3. Two further sentences in `docs/rules/ci-and-workflow.md`
   (the lint-invocation enumeration and the cache rationale's
   import closure) go stale with the third root library. Fixed:
   scheduled.
4. § Verification's `TODO.md` item omitted the cross-track
   entry's half of the mutual cross-reference. Fixed: named.

Cosmetic-taste.

1. The `test-lint-driver.sh` header's coverage sentence goes
   stale with the third scan; scheduled.
2. The `TODO.md` scope-2 edit was stated too loosely; the spec
   now says the bullet gains a reference to the literate site.
