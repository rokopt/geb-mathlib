# GebLang literate design: adversarial review, round 3

Reviewer: fresh-context agent, 2026-08-15. Sources: the
repository's scripts and their self-tests, workflows, lakefile,
umbrellas, rule documents, `TODO.md`; the verso checkout; the
toolchain's Lake sources; Cslib's `CheckInitImports`; the pinned
doc-gen4; `teorth/analysis` re-fetched. Every prior-round fix it
spot-checked held (the corrected `literate.toml` against the
decoder, the facet-walk text, multi-prefix leakage support, the
widened `lake shake` form, the transitive-check
no-false-positive argument, the `defaultTargets` interaction with
`lean-action` and the cache stamp). The round also judged scope:
near the single-branch ceiling, with the upstream-integration
cluster the part that pushes it there.

Verdict: not converged (no blocker; four serious findings).
Every finding is addressed below; the spec edits land in this
round's commit.

## Findings and responses

Serious.

1. The consumption allowance would land before the extraction
   machinery, opening an interim hole in the lint-enforced
   floodgate (a `Geb/Mathlib/` module could legally import the
   placeholder while `extract-pr.sh` rejects `GebLang/` paths).
   Fixed by adopting the reviewer's sequencing: this workstream
   widens no existing allowed-import list; the consumption
   cluster (allowed-list additions, leakage-prefix additions,
   the transitive-import check, the extraction extension) is
   assigned to the first content workstream and recorded in
   `TODO.md`, so every merged state keeps the floodgate
   lint-enforced. The rule documents adopt the transitive policy
   now with its activation point stated. This also returns the
   branch to the lean scope the reviewer recommended.
2. The leakage-prefix additions omitted the `GebTests` mirrors.
   Fixed: the deferred cluster names all four entries.
3. A Cslib-track `GebLang` module's `Batteries.*` imports
   contradicted the repository's `Geb/Cslib/` discipline.
   Resolved by documented acceptance: Cslib itself imports
   Batteries directly, so the extraction target accepts them;
   the spec and rule file state the asymmetry against
   `Geb/Cslib/`'s stricter lists.
4. `docs/process.md` § Floodgate test and `README.md` § Upstream
   targets are falsified by the design but were not scheduled
   for update. Fixed: both join § Standards and rule documents.

Minor.

1. § Verification did not exercise the rounds' additions. Fixed:
   the `lint-imports` self-test items (induced `import Geb`,
   induced leakage, the conditional `Cslib.Init` in both
   directions) and the `TODO.md` presence check are listed; the
   transitive-check self-test now covers both root kinds and is
   deferred with its script.
2. The conditional `Cslib.Init` rule is a mechanism extension to
   `lint-imports.sh`, and its direct-import form is sufficient
   only because Cslib's upstream check is transitive. Fixed: the
   spec states both.
3. The docstring wording conflated the conversion (roles
   stripped to code spans, performed by tooling) with the
   degradation (braces rendered literally by a consumer without
   the option). Fixed: the two are distinguished and shipped
   files carry the converted form.
4. `GebTests/Lang/`'s upstream posture was unstated. Fixed:
   deferred with the consumption cluster, stated in § Tests.
5. Comments in `ci.yml` and `pre-push.sh` describing
   `defaultTargets` as `Geb` only, and the pre-push checklist in
   `docs/rules/ci-and-workflow.md`, were unscheduled. Fixed:
   both scheduled in § CI and pre-push.
