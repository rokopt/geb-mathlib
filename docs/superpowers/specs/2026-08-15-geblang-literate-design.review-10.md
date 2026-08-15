# GebLang literate design: adversarial review, round 10

Reviewer: fresh-context agent, 2026-08-15. Subject: the
post-round-9 revision made at the user's direction (nothing
deferred; `Geb/Cslib/` gains `Geb.Mathlib.*` and `Batteries.*`).
The user's decisions were taken as settled; only their execution
was reviewed, against the repository scripts (including
`scripts/extract-pr.sh` and its self-test), the full `TODO.md`,
the rule documents, and the verso checkout. Removing the
`TODO.md` cross-track entry was confirmed to dangle nothing.

Verdict: not converged (one blocker; two serious findings). Every
finding is addressed below; the spec edits land in this round's
commit.

## Findings and responses

Blocker.

1. The extraction extension as specified did not keep the
   widened imports shippable: a destination-uniform `GebLang.`
   rewrite emits a non-compiling import when a Cslib-destined
   source imports a mathlib-track `GebLang` sibling, and the
   four existing arms gained no rewrites for their widened lists
   (the resolved `TODO.md` entry had itself named the needed
   second rewrite pair). Fixed: the rewrite is per-imported-
   module track; the two `Mathlib` arms gain `GebLang.` to
   `Mathlib.`; the two `Cslib` arms gain `Geb.Mathlib.` to
   `Mathlib.` and per-track `GebLang.`; § Verification exercises
   each case, including the cross-track import.

Serious.

1. A leftover deferral parenthetical in § CI and pre-push
   contradicted the revision and dangled. Fixed: the check and
   its self-test run in `ci.yml` beside the `lint-imports`
   steps.
2. Two standing `TODO.md` triggers fire on this workstream (the
   Rule 2 comment-tail exemption, on revising `lint-imports.sh`;
   the `meta import` rewrite gap, on revising `extract-pr.sh`)
   and were unaddressed; the second interacts materially with
   the new rewrites. Fixed: both fold in (the exemption narrows
   to the import path; every rewrite covers all four import
   forms) and both entries are resolved and removed.

Minor.

1. The two closure walks' import-form coverage was unspecified.
   Fixed: both follow all four forms.
2. `GebTests/Lang/` extraction appeared only in § Tests. Fixed:
   the extension accepts those sources, mapping into the
   destination's test tree as the existing arms do, with a
   fixture in § Verification.
3. Induced-leakage cases for the widened prefixes on existing
   entries were untested. Fixed: added, with the comment-tail
   case.
4. The placeholder's extraction status was stated in two
   tensions. Fixed: nothing ships from it; its `{name}` role
   doubles as the conversion fixture, and the tool run against
   it is a verification item.
5. The widening bullets did not name the `lint-imports.sh`
   header table and Batteries rationale paragraph. Fixed.

Cosmetic-taste: the orphaned "A" reflow and the Goal's doubled
phrase, both fixed.

The reviewer's scope judgment: the branch remains one coherent
concern (under the no-deferral direction every cluster is
entailed by the library landing floodgate-clean) but sits at or
past the single-branch ceiling; the recommended mitigation is
two plans under this one spec, with the extraction-and-lint
commits ordered before any allowed-list widening commit so the
floodgate holds at every merged state. Adopted: the planning
phase produces two plans in that order.
