# GebLang literate design: adversarial review, round 8

Reviewer: fresh-context agent, 2026-08-15. Verified round 7's
fixes as written, ran an independent falsification sweep with
fresh search terms, spot-checked the environment claims once
more (all held), and read the spec end to end for a zero-context
plan writer.

Verdict: not converged (no blocker; one serious finding). Every
finding is addressed below; the spec edits land in this round's
commit. In response to the class persisting across rounds, the
spec now carries an enumeration-sweep commitment: implementation
greps the committed corpus for upstream-location,
porting-destination, subtree, mirror, and root-library
enumerations and updates each for `GebLang`, verified as its own
§ Verification item, so any straggler is an implementation
defect rather than a spec gap.

## Findings and responses

Serious.

1. The `GebTests.lean` module docstring's mirror enumeration is
   falsified by `GebTests/Lang/` and was unscheduled. Fixed:
   named in the enumeration sweep's known-instances list.

Minor.

1. `CONTRIBUTING.md`'s LLM-policy bullet closes with a
   "both subtrees" sentence contradicting the scheduled edit
   three lines above. Fixed: the closing sentence joins the
   bullet's edit.
2. The `mk_all-check` rationale comment in `ci.yml` goes stale
   with the new glob. Fixed: named in the sweep list.
3. The README § Upstream targets recast-and-move sentence is a
   third porting enumeration. Fixed: named in the consolidated
   README bullet.
4. The `TODO.md` cross-track entry's pointer to the
   independence sentence of § Floodgate test stales when that
   sentence is reworded. Fixed: the reconciliation is scheduled
   with the entry's other edits.
5. A garbled sentence from round 7's fix (duplicated "section").
   Fixed.
6. The `docs/index.md` mirroring phrase and the `GebMeta.lean`
   namespace enumeration. Fixed: named in the sweep list.

Cosmetic-taste.

1. The split README bullets are consolidated into one; the
   guard-script items are consolidated into the
   `test-lint-driver.sh` bullet; the docs-coverage reminder's
   message text is named in the sweep list beside its path
   pattern.
