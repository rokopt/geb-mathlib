# GebLang literate design: adversarial review, round 1

Reviewer: fresh-context agent, 2026-08-15. Verification sources:
the repository's binding documents and scripts; the verso checkout
at `v4.34.0-rc1` (the literate configuration decoder, planner, and
the
`literateHtml` facet in its lakefile); the Lean core toolchain
source (`doc.verso` registration); the pinned doc-gen4; the
`teorth/analysis` precedent by fetch. The round confirmed the
`doc.verso` per-library `leanOptions` form, the pinned doc-gen4's
Verso-docstring rendering (the spec's contingency is unneeded but
harmless), the `literate.toml` key names, the coverage-scan and
`lint-imports` extension points, and the CI file shapes.

Verdict: not converged (no blocker; four serious findings). Every
finding is addressed below; the spec edits land in this round's
commit.

## Findings and responses

Serious.

1. The `literate.toml` snippet placed `docstrings_as_text` and
   `landing_page` after the `[[targets]]` header, making them
   silently ignored keys of the target entry. Fixed: the
   root-level keys precede every table header, and the spec
   states the pitfall.
2. The facet-walk mechanism was mis-stated: at the pin the
   `literateHtml` facet enumerates every library and executable
   (the users-guide text says default targets; the lakefile folds
   over `pkg.leanLibs` and `pkg.leanExes`), so a run without
   `literate.toml` would render and build `Geb`, `GebTests`,
   `GebMeta`,
   `GebManual`, and `Main`. Fixed: § Context and § Literate
   rendering state the actual behavior, and § Verification checks
   the site contains no module of those libraries. The
   `[[targets]]` scoping conclusion stands, strengthened.
3. Allowing `Geb/Cslib/` to import mathlib-track `GebLang`
   modules recreates, one level removed, the dependency shape
   `docs/rules/upstream-eligible.md` forbids between the two
   subtrees, and no check guards it. Response: accepted and
   documented rather than forbidden. The direction matches the
   user's dependency-ordering stance for the shared bottom layer,
   the ordering cost (mathlib merge, then Cslib pin advance) is
   stated in § Import rules, and the rule file documents the
   asymmetry. The converse direction is enforced: the
   transitive-import check forces any `GebLang` module in a
   `Geb/Mathlib/` closure to be mathlib-track. Flagged for the
   user's spec review as a deliberate policy choice.
4. § Standards omitted the `upstream-eligible.md` sections the
   design falsifies. Fixed: the section now names the § Floodgate
   test revision, the import-rules-table additions, the
   cross-track documentation, and the `lint-imports.sh` header
   and self-test updates.

Minor.

1. `Geb/Internal/` has no allowed-import list in
   `lint-imports.sh` to join. Fixed: the spec states it is
   unrestricted and needs no amendment.
2. The Goal named Lean core among the importable libraries while
   the allowed list admits no core prefix. Fixed: the Goal now
   matches the list (mathlib, Batteries, Cslib, and what they
   carry).
3. Cslib is not served by the mathlib binary cache. Fixed: the
   cost claim now says the default build already provides the
   closure, with the cache covering mathlib only.
4. The landing page (`GebLang` umbrella) contradicted
   § Placeholder content, which assigned its prose to the
   placeholder module. Fixed: the umbrella's docstring is the
   landing page; the placeholder module proves per-module
   rendering and the `{name}` role.
5. `GebTests.lean` must import the new test subtree for the
   driver and lint to reach it. Fixed: § Tests states the
   umbrella edit and the index file.

Cosmetic-taste.

1. Colloquialisms and a growing-population count. Fixed:
   reworded, and the subtree references now state the property
   rather than the count.
