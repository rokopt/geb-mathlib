# Verso manual design: adversarial review, round 2

Reviewer: fresh-context agent, 2026-08-14. Verification sources:
this repository's binding documents and scripts; Lake sources at
`lean4@v4.34.0-rc1`; a fresh clone of verso at `v4.34.0-rc1`;
verso-templates; reference-manual; batteries `runLinter` and
Cslib as pinned; Reservoir; and the experimental repository
`anoma/geb` directly (public, contrary to round 1's premise).
The round confirmed every round-1 fix it spot-checked (the
transitive-require set, the pin-precedence direction, the inert
`topNamespace` linter, the axiom-linter import boundary, the
generator invocation, the `lintDriverArgs` behavior, `srcDir` on
both target kinds). Verdict: not converged (no blocker; one
serious finding). Every finding is addressed below; the spec
edits land in this round's commit.

## Findings and responses

Serious.

1. The `module`-keyword commitment for document modules is
   unverified (no surveyed Verso project declares `module` in a
   `#doc` file), inexpressible through the § Linting exemption
   mechanism (the module rule is not a linter), and carried no
   verification item or fallback. Fixed: § Generator executable
   states the survey result, defers the question to
   implementation, and records the fallback (non-`module`
   document files with an exemption recorded in
   `docs/rules/lean-coding.md`, as the precedent recorded);
   § Verification gains the corresponding item.

Minor.

1. The claim that later rounds cannot consult the experimental
   repository is false; `anoma/geb` is public and this round
   verified the precedent details against it. Fixed: § Precedents
   now records the details as verified directly, and the
   § Verification bullet re-deriving them at implementation is
   replaced by the `module`-compatibility item.
2. `docBlame` nolints for the bibliography entries would be dead
   configuration: the bibliography `def`s are hand-written and
   carry docstrings under this repository's rules (the precedent's
   carry docstrings and only `topNamespace` nolints). Fixed:
   § Linting scopes the `docBlame` entries to the `#doc`-generated
   `def`s only. This defect was introduced by the round-1 fix to
   its minor finding 1.
3. The Lake option-combination direction was stated backwards
   (package options appending onto the library's). Fixed:
   § Linting now states that the library's options append onto
   the package's, which is what makes the overrides work, matching
   the lakefile's own comment.
4. The § Dependency snippet intro ("above the mathlib require")
   admitted an insertion between `doc-gen4` and `mathlib`, where
   verso's `MD4Lean@main` would win under Lake's reverse-order
   traversal. Fixed: both the intro and the analysis paragraph
   state the placement ahead of both requires.

Cosmetic-taste.

1. "First among the git requires" clashed with the snippet's
   Reservoir `scope` form. Fixed: the phrasing names the two
   requires verso precedes.
2. § Build, serve, reload retained the universal
   no-watch-mode-anywhere claim that round 1 narrowed elsewhere.
   Fixed: narrowed to Verso and the surveyed projects.
3. § Verification hardcoded `http://localhost:8000/` despite the
   next-free-port fallback. Fixed: the check defers to the URL
   `verso-serve` prints.
4. "Thin at first" (§ Content) is colloquial. Fixed: "initially
   brief".
5. The static `test-lint-driver.sh` extension needs a
   `srcDir`-aware module-to-path mapping and a `Main` exemption
   in its orphan scan. Fixed: § Linting records both.
