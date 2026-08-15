# GebLang literate design: adversarial review, round 2

Reviewer: fresh-context agent, 2026-08-15. Verification sources:
the repository's scripts (including `scripts/extract-pr.sh`,
which round 1 did not examine), workflows, lakefile, and umbrella
files; the verso checkout at `v4.34.0-rc1` (facets,
configuration decoder, planner, extractor); `subverso`; the Lean
toolchain source (docstring elaboration, declaration modifiers,
Lake globs and options); the pinned doc-gen4; `teorth/analysis`
and the verso `v4.28.0`/`v4.29.0` tags fetched fresh. Every
round-1 fix was spot-checked and confirmed (the corrected
`literate.toml` parses and decodes as intended; the facet-walk
text matches the lakefile; `doc.verso` reaches the extractor
through Lake's `leanOptionArgs`; the landing-page and glob
semantics keep `GebMeta` out of the site by construction).

Verdict: not converged (no blocker; four serious findings, all
concerning the shipping story). Every finding is addressed below;
the spec edits land in this round's commit.

## Findings and responses

Serious.

1. The transitive floodgate wording asserted a mechanical
   shipping capability that `scripts/extract-pr.sh` does not
   provide (it
   rejects `GebLang/` paths, rewrites no `GebLang.` prefixes, and
   has no destination mapping). Fixed by explicit deferral with
   the principle stated: retargeting is defined as the mechanical
   rewrites extraction already performs (import prefixes) plus
   docstring-format conversion; extending the extraction script
   and its self-test to `GebLang` is deferred to the first
   content workstream, recorded in `TODO.md`, and no `GebLang`
   content may ship before that tooling lands.
2. Verso-role docstrings render literally in consumers that do
   not set `doc.verso` (mathlib, Cslib), contradicting the
   not-a-rewrite claim. Fixed: § Import rules defines the
   docstring-format conversion (roles degrade to code spans) as
   part of the mechanical retargeting rewrite, in the same class
   as the import-prefix rewrite; § Placeholder content notes the
   placeholder is not subject to extraction, so its `{name}` role
   stands.
3. The transitive-import check omitted the `GebTests/Mathlib/`
   mirror, whose tests extract upstream too. Fixed: the walk's
   roots include `GebTests/Mathlib/`, and the followed prefixes
   include `GebTests.*`; the no-false-positive argument the
   reviewer supplied (on a lint-clean tree the walk cannot enter
   `Geb/Cslib/`) is recorded in the spec.
4. Cslib-track `GebLang` modules would fail Cslib's
   `checkInitImports` without a `Cslib.Init` rule, and a
   subtree-wide mandate would force every module Cslib-track.
   Fixed: the conditional rule (a `GebLang` module importing any
   `Cslib.*` must import `Cslib.Init`), enforced by
   `lint-imports.sh`.

Minor.

1. The Goal contradicted the umbrella's `GebMeta` import. Fixed:
   the Goal carries the carve-out.
2. Placeholder and test docstrings were directed to state
   development-history references. Fixed: docstrings state
   enduring purpose only; the replacement expectations live in
   `TODO.md`.
3. The `doc-build.yml` paths filter omitted `GebLang.lean`, the
   landing page's prose source. Fixed: added.
4. Leakage prefixes were unspecified. Fixed: `GebLang.` is the
   new entry's self-prefix and joins the leakage prefixes of the
   two upstream-eligible entries.
5. § Alternatives claimed a one-literal-per-product CI guard that
   no section specified. Fixed: the lint-driver guard's workflow
   check gains the `scripts/literate.sh build` literal.

Cosmetic-taste.

1. Two colloquialisms and one hedge ("if absent") reworded; the
   paths-filter fact is stated directly.

The reviewer also recorded one statically unverifiable point,
adequately covered by § Verification: the literate extractor
re-elaborates sources in a non-module frontend context, and no
verso test project exercises a `module`-form file, so end-to-end
behavior rests on the `literate.sh build`/`serve` checks.
