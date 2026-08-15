# GebLang literate design: adversarial review, round 5

Reviewer: fresh-context agent, 2026-08-15. Scope: a full fresh
read of the spec as the document a plan will be written from,
plus spot-checks of every environment-facing claim (all held,
including the facet-fold discrepancy against the users guide, the
decoder keys, the transitive Cslib check, the pinned doc-gen4's
Verso support, and the axiom linter's lack of a per-library
filter, which sustains § Verification's coverage assumption).
Design-to-verification tracing was found complete in both
directions apart from the findings below.

Verdict: not converged (no blocker; one serious finding). Every
finding is addressed below; the spec edits land in this round's
commit.

## Findings and responses

Serious.

1. Two `docs/index.md` § Directory structure statements are
   falsified without a scheduled update: the `Geb/Internal/`
   bullet's import enumeration (which gains `GebLang.*` now,
   since that allowance activates in this workstream) and the
   `GebTests/` bullet's subdirectory list (which gains
   `GebTests/Lang/` now). Fixed: both scheduled in § Standards
   and rule documents.

Minor.

1. `docs/rules/lean-coding.md`'s description of the axiom
   linter's coverage omits `GebLang`. Fixed: scheduled.
2. The `paths:` extension was silent on the `GebTests/Lang.lean`
   index. Fixed: included, following the umbrella-plus-directory
   pattern, with the contrast to the exempted `GebLang.lean`
   umbrella stated.
3. The conditional `Cslib.Init` rule specified its triggers but
   not its satisfying form; a symmetric reading would pass files
   Cslib's upstream check rejects. Fixed: only a plain or
   `public` import satisfies, matching the existing Rule 1b
   form.
4. The self-test items exercised only the `GebLang/` entry.
   Fixed: induced `GebTests.Lang.` leakage in `GebTests/Lang/`
   joins the list.

Cosmetic-taste.

1. The site-content check omitted the generator's `Main`. Fixed.
2. An informal comparative reworded.
