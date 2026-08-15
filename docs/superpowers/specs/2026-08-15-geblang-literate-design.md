# GebLang literate library: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Transcription or novelty](#transcription-or-novelty)
- [Context](#context)
- [Design](#design)
  - [Library and layering](#library-and-layering)
  - [Import rules](#import-rules)
  - [Transitive-import check](#transitive-import-check)
  - [Literate rendering](#literate-rendering)
  - [Commands](#commands)
  - [CI and pre-push](#ci-and-pre-push)
  - [Tests](#tests)
  - [Standards and rule documents](#standards-and-rule-documents)
  - [Placeholder content](#placeholder-content)
- [Alternatives considered](#alternatives-considered)
- [Out of scope](#out-of-scope)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Goal

Add `GebLang`, a library for the core data structures of the Geb
language, written in Verso's literate style: prose in ordinary
module and declaration docstrings, rendered both by `doc-gen4` (as
for the existing code) and by Verso's literate HTML pipeline (as a
static site). `GebLang` sits at the bottom of the repository's
dependency order: its content modules import nothing of this
repository outside `GebLang`, only mathlib, Batteries, and Cslib
(and what they carry from Lean core; the umbrella additionally
imports `GebMeta` to register the axiom linter, per § Library and
layering). `Geb/Internal/` and its test mirror may import it from
this workstream on; the upstream-eligible subtrees may once the
consumption cluster of § Import rules lands. This workstream
builds the infrastructure (library, layering rules, both
documentation pipelines, commands, CI, and one placeholder
module with one placeholder test) and defers real content, and
the extraction tooling, to follow-on workstreams.

## Transcription or novelty

This workstream introduces no mathematical definitions or
theorems; it is build infrastructure and layering policy. The
placeholder declaration (§ Placeholder content) carries no
mathematical claim. Citation rules apply to future content, not to
this workstream.

## Context

- Verso's literate flow ships inside the pinned `verso` package
  (`v4.34.0-rc1`; the feature landed in `v4.29.0`). Its Lake
  facets arrive with the require: `lake build :literateHtml`
  renders module docstrings as page prose and declarations as
  highlighted code, and emits a static site;
  `lake query :literateHtml` prints the output path. At this pin
  the facet enumerates every library and executable of the root
  package (its users-guide text says default targets; the
  lakefile's fold is over `pkg.leanLibs` and `pkg.leanExes`), so
  a run without `literate.toml` would include `Geb`, `GebTests`,
  `GebMeta`, `GebManual`, and the generator's `Main`, and would
  build them all. `literate.toml`'s `[[targets]]` filtering runs in the
  planner before any module is fetched, so scoping the site also
  bounds what it compiles.
- Literate source files are ordinary Lean files: no `#doc`, no
  Verso imports, no Verso commands. Consequently
  `linter.hashCommand` stays enabled for them, the `module`
  discipline applies unchanged, and building the library never
  compiles Verso. Verso compiles only when rendering the site
  (the `verso-literate` executables), as it does for the manual.
- The builtin option `doc.verso` (Lean core) switches a package's
  or library's docstrings to checked Verso markup (`{name}`,
  `{lean}` roles). It is a compile-time mode: a consumer compiling
  the same file without the option renders the markup literally.
  Setting it per-library confines checked markup to `GebLang`
  while the upstream-eligible subtrees keep mathlib-conventional
  Markdown docstrings.
- `doc-gen4` at its current main renders Verso-format docstrings
  natively (`DocGen4/DB/VersoDocString.lean`), so the same source
  feeds both pipelines. The repository's pinned doc-gen4 is
  verified for this during implementation (§ Verification).
- Precedent: `teorth/analysis` runs the literate site and doc-gen4
  side by side from the same sources (`literate.toml`,
  `lake build :literateHtml`, doc-gen4 into a `docs/` path), with
  `doc.verso` enabled in its lakefile.
- The manual workstream (merged) established the `verso` pin and
  ordering, the bump automation, the CI patterns in
  `doc-build.yml`, and the `scripts/manual.sh` command shape this
  design mirrors.

## Design

### Library and layering

A new top-level library, sibling to `Geb`:

```text
GebLang.lean        umbrella; imports GebMeta and the GebLang modules
GebLang/
└── Basic.lean      placeholder module (§ Placeholder content)
```

`lakefile.toml` gains:

```toml
[[lean_lib]]
name = "GebLang"
globs = ["GebLang.*"]

[lean_lib.leanOptions]
doc.verso = true
```

and `defaultTargets` becomes `["Geb", "GebLang"]`: the library is
ordinary Lean code whose import closure the default build already
provides (mathlib through its binary cache, Cslib built from
source as now), so it belongs in the default build, unlike the
manual. The umbrella imports `GebMeta` (as `Geb.lean` and
`GebTests.lean` do) so the axiom linter registers for
`lake lint -- GebLang`; `GebMeta` is meta-tooling, not a content
subtree, so the layering constraint is unaffected.
`lintDriverArgs` stays `["Geb"]`; `GebLang` is linted by explicit
`lake lint -- GebLang`, the `GebTests` pattern.

### Import rules

The dependency order places `GebLang` at the bottom:

- `GebLang/` modules import only `Mathlib.*`, `Batteries.*`,
  `Cslib.*`, and `GebLang.*`, and never `Geb.*` or `GebTests.*`.
- `GebTests/Lang/` (§ Tests) may import `GebLang.*`,
  `GebTests.Lang.*`, and the libraries `GebLang/` itself may.
- A `GebLang/` or `GebTests/Lang/` module that imports any
  `Cslib.*` module (in any import form: `import`,
  `public import`, `meta import`, `public meta import`) must
  import `Cslib.Init` (Cslib's `checkInitImports` requirement).
  The rule is conditional so that mathlib-track modules are not
  forced to import Cslib, and it is a mechanism extension to
  `scripts/lint-imports.sh` (its `required_init` is today
  unconditional per subtree). The direct-import form suffices
  because the upstream check is transitive over the import graph:
  a Cslib-track module importing only extracted `GebLang`
  siblings inherits `Cslib.Init` through them. Only a plain or
  `public` import of `Cslib.Init` satisfies the requirement,
  matching the existing Rule 1b form, which excludes `meta`
  imports; the trigger accepts all four forms while the
  satisfying import must not be `meta`.
- A Cslib-track `GebLang` module may keep its `Batteries.*`
  imports: Cslib itself imports Batteries directly, so the
  extraction target accepts them. This is less restrictive than
  the repository's own `Geb/Cslib/` lists, which exclude
  `Batteries.*`; the rule file states the asymmetry.

`scripts/lint-imports.sh` encodes the `GebLang/` and
`GebTests/Lang/` entries in this workstream, with `GebLang.` as
the library entry's self-prefix and `GebTests.Lang.` (beside
`GebLang.`) as the test entry's leakage prefixes, per the
existing mirror pattern; its header comment and self-test extend
accordingly.

This workstream does not widen any existing allowed-import list:
until the extraction tooling handles `GebLang` sources, a
`Geb/Mathlib/` or `Geb/Cslib/` module importing `GebLang.*`
would break the lint-enforced floodgate, so the allowance and
the tooling must land together. The consumption cluster is
assigned to the first `GebLang` content workstream, recorded in
`TODO.md`; it comprises `GebLang.*` in the allowed lists of
`Geb/Mathlib/`, `Geb/Cslib/`, and their `GebTests` mirrors,
`GebLang.` in those four entries' leakage prefixes (a
`GebLang.`-qualified reference in an extracted body would dangle
upstream exactly as a `Geb.Mathlib.`-qualified one would), the
transitive-import check below, and the `scripts/extract-pr.sh`
extension (path acceptance, prefix rewriting, a destination
mapping, the docstring conversion) with its self-test.
(`Geb/Internal/` and its mirror are unrestricted in
`scripts/lint-imports.sh`, so they may import `GebLang.*` from
this workstream on, involving no extraction.)

The rule documents adopt the transitive floodgate policy now,
stating its activation point: dependency-ordered PRs remain
shippable at all times, with a module's `GebLang` dependencies
shipped first, each retargeted by its own import closure
(mathlib-track when it reaches no `Cslib.*`; Cslib-track
otherwise). `GebLang` is written to the upstream-eligible
standards, so retargeting is mechanical: the extraction rewrites
import prefixes (as `scripts/extract-pr.sh` already does for the
`Geb/` subtrees) and strips Verso-role markup from docstrings,
leaving plain Markdown (a checked name reference becomes a bare
code span). The stripping is a conversion the tooling performs,
distinct from the degradation an unconverted docstring would
display (role braces rendered literally); shipped files carry
the converted form.

Cross-track ordering is accepted by design in one direction: a
`Geb/Cslib/` module may import a mathlib-track `GebLang` module,
and shipping it then waits for the mathlib PR to merge and for
Cslib's mathlib pin to advance. This is the dependency shape
`docs/rules/upstream-eligible.md` forbids between `Geb/Cslib/`
and `Geb/Mathlib/`; for `GebLang`, the shared bottom layer, the
ordering cost is accepted rather than forbidden, and the rule
file documents the asymmetry (§ Standards and rule documents).
The converse direction needs no allowance: a `GebLang` module in
any `Geb/Mathlib/` closure is forced mathlib-track by the
transitive-import check.

### Transitive-import check

Deferred to the first content workstream with the consumption
cluster above; designed here so that workstream inherits it. A
`Geb/Mathlib/` module whose `GebLang` dependencies reach
`Cslib.*` has become Cslib-track and belongs in `Geb/Cslib/`.
`scripts/check-transitive-imports.sh` detects this: a source-level
walk of the repository-internal import closure (the technique of
`scripts/tests/test-lint-driver.sh`'s coverage scan) from every
`Geb/Mathlib/` and `GebTests/Mathlib/` module (the mirror
extracts upstream too), following `Geb.*`, `GebTests.*`, and
`GebLang.*` imports transitively, failing if the closure contains
any `Cslib.*` import line. On a lint-clean tree the walk cannot
enter `Geb/Cslib/` (no allowed import reaches it from the
mathlib-track roots), so a failure is a genuine misplacement, not
a false positive. Pre-push and `ci.yml` run it beside
`lint-imports.sh`. A self-test
(`scripts/tests/test-check-transitive-imports.sh`) verifies the
passing state and induced failures from both root kinds,
following the existing script-test conventions.

### Literate rendering

`literate.toml` at the repository root:

```toml
docstrings_as_text = true
landing_page = "GebLang"

[metadata]
title = "The Geb language"

[[targets]]
library = "GebLang"
```

The root-level keys precede every table header: a key placed
after `[[targets]]` becomes a key of that target entry and is
silently ignored by the target decoder. The `[[targets]]` scoping
is required: without it the facet renders and builds every
library and executable of the package (§ Context), `GebManual`
included. `docstrings_as_text` renders declaration docstrings as
page prose, the `teorth/analysis` setting. Further keys
(ordering, per-module titles, themes) are deferred until content
exists.

### Commands

`scripts/literate.sh`, mirroring `scripts/manual.sh` (repository-root
resolution, two verbs, usage text with the reload note):

- `build`: `lake build GebLang`, `lake lint -- GebLang`,
  `lake build :literateHtml`.
- `serve`: `lake exe verso-serve "$(lake query :literateHtml)"`.

The first `build` compiles the `verso-literate` executables from
source (minutes, as for the manual); rebuilding after a docstring
edit is incremental.

### CI and pre-push

- `ci.yml`: `GebLang` builds via `defaultTargets` under the
  existing `lean-action` step; explicit steps add
  `lake lint -- GebLang` and extend the `lake shake` invocation
  to `Geb GebTests GebLang`. (The transitive-import check joins
  when its cluster lands.) The comments in `ci.yml` and
  `scripts/pre-push.sh` that describe `defaultTargets` as `Geb`
  only are updated to name both root libraries.
- `doc-build.yml`: gains `lake build GebLang:docs` beside the
  existing `Geb:docs` (doc-gen4 for the new library),
  `bash scripts/literate.sh build`, and a `geb-literate` artifact
  upload of the literate site (path from
  `lake query :literateHtml`); the paths filter gains
  `GebLang.lean` (the umbrella carries the landing page's prose),
  `GebLang/**`, `scripts/literate.sh`, and `literate.toml`
  (`GebTests/**` is already present).
- `scripts/pre-push.sh`: adds `lake lint -- GebLang`, the
  widened `lake shake`, and `GebLang/` in the docs-coverage
  reminder's path pattern (the library is content-bearing, so
  its concepts belong in `docs/index.md`). The literate HTML
  build stays out of pre-push, as the manual's does.
  `docs/rules/ci-and-workflow.md` § Pre-push checklist gains the
  new steps and the widened reminder enumeration.
- `scripts/tests/test-lint-driver.sh`: the coverage scan gains
  `check_coverage GebLang ""` (the library lives at the package
  root, so the existing generalization applies directly), and its
  workflow check gains the `scripts/literate.sh build` literal
  beside the manual's, one literal per product, so `doc-build.yml`
  cannot silently lose the literate build.

### Tests

`GebTests/Lang/` inside the existing `GebTests` library, mirroring
the subtree structure. One module,
`GebTests/Lang/Basic.lean`, holding a `#guard` (or trivial
`example`) exercising the placeholder declaration, validating the
test driver path, the new import rules, and the lint path end to
end. `GebTests.lean` gains `public import GebTests.Lang` (and a
`GebTests/Lang.lean` index, per the one-indexing-file-per-directory
layout) so the test driver and `lake lint -- GebTests` reach the
module. It is removed when real tests arrive; that expectation is
recorded in `TODO.md`, not in the docstring, which states only
what the module tests. Whether `GebTests/Lang/` tests extract
upstream with their subjects is deferred with the consumption
cluster (§ Import rules); until then the subtree has no
extraction path.

### Standards and rule documents

- `GebLang` binds to the upstream-eligible standards: mathlib
  style and naming, the module system, constructive-only
  discipline, citation rules, and the LLM-contribution policy.
  `docs/rules/upstream-eligible.md` extends its `paths:` to
  `GebLang/**` and `GebTests/Lang/**` (not the `GebLang.lean`
  umbrella, which imports `GebMeta` and is exempt from the
  content rules, a stated deviation from the
  umbrella-plus-directory pattern of the existing entries; the
  `GebTests/Lang.lean` index, which imports no `GebMeta`, is
  included, following that pattern),
  states the per-module destination-open posture (the existing
  core/Batteries-targeted precedent), revises its § Floodgate
  test to the transitive form (extraction is dependency-ordered
  through `GebLang`, no longer independent between subtrees),
  adds `GebLang/` and `GebTests/Lang/` rows to its
  subtree-import-rules table (with the conditional `Cslib.Init`
  requirement noted on both), updates its in-body applies-to
  sentence with the new paths, and documents the accepted
  `Geb/Cslib/` cross-track ordering (§ Import rules) with a
  cross-reference to the `TODO.md` entry that records the same
  ordering cost as the case against allowing `Geb/Cslib/` to
  import `Geb.Mathlib.*`: the two evaluations differ
  deliberately, and each document points at the other. The
  widening of the four existing rows is
  deferred with the consumption cluster, so the file's statement
  that `scripts/lint-imports.sh` enforces its table stays true
  at every merged state; the pending widening is described in
  the floodgate prose with its activation point, and in
  `TODO.md`.
- `docs/rules/lean-coding.md` gains a literate-conventions
  section: module docstrings are the rendered page prose;
  `doc.verso` roles are available in `GebLang` (and only there);
  the docstring markup must remain acceptable to both pipelines.
  Its description of the axiom linter's coverage (`Geb` and
  `GebTests` declarations) gains `GebLang`.
- `README.md` documents the library and the
  `scripts/literate.sh` commands, and its § Upstream targets
  gains `GebLang` with the destination-open, activation-gated
  posture; `docs/index.md` § Directory structure gains
  `GebLang/`, adds `GebLang.*` to the `Geb/Internal/` bullet's
  import enumeration (that allowance activates now), and adds
  `GebTests/Lang/` to the `GebTests/` bullet's subdirectory
  list; `docs/rules/ci-and-workflow.md` records the literate
  build's CI placement.
- `CONTRIBUTING.md`: the floodgate paragraph's transitive
  rewording with its activation point (§ Import rules),
  `GebLang` in the § Repo structure line, and `GebLang/` added
  to the LLM-contribution-policy sentence's binding locations.
- `AGENTS.md`: the § AI authoring sentence and the path-scoped
  section heading (with its TOC entry) that enumerate
  `Geb/Mathlib/` and `Geb/Cslib/` gain `GebLang/`.
- `README.md` § Process: the line stating where
  `upstream-eligible.md` applies gains the new paths.
- `TODO.md` § Verso adoption is revised: the doc-gen4 half of
  its scope-1 gate is met at the pin (verified by this
  workstream), the extraction-time docstring conversion
  (§ Import rules) supersedes the entry's
  mathlib-migration-based mechanism for `GebLang`, and the
  scope-2 exposition bullet is related to the literate site this
  workstream builds.
- `docs/process.md`: its § Floodgate test rationale is revised
  for the transitive form (a third eligible location; extraction
  dependency-ordered through `GebLang` rather than independent
  per subtree), since the process document carries the rationale
  for every rule being changed.

### Placeholder content

`GebLang/Basic.lean` holds a single small declaration with a
docstring, exercising both pipelines: its docstring uses one
checked `{name}` role (proving `doc.verso` elaboration), and its
module docstring proves per-module page rendering. The landing
page's prose is the `GebLang.lean` umbrella's module docstring
(`landing_page = "GebLang"` in § Literate rendering). The
declaration is chosen at implementation to be subsumable by the
first content workstream; its docstring states its enduring
purpose (anchoring the two documentation pipelines), the
replacement expectation is recorded in `TODO.md` (docstrings
carry no development-history references), and the module is
replaced, not grown, when content lands. The placeholder is not
subject to extraction, so its `{name}` role does not contradict
§ Import rules' docstring-conversion story.

## Alternatives considered

- A separate `GebLangTests` library. Rejected: the existing
  `GebTests` library already carries the test driver registration,
  the `#guard` allowance, the axiom linter, and shake coverage;
  a new library would duplicate that machinery for one
  placeholder.
- A `Geb/Lang/` subtree instead of a top-level library. Rejected:
  the `Geb` library's `globs = ["Geb.*"]` would place it inside the
  existing build, lint, and floodgate machinery, all of which
  distinguish the `Geb/` subtrees by path; a sibling
  library leaves them untouched.
- Enabling `doc.verso` package-wide. Rejected: upstream-eligible
  docstrings must render correctly in consumers that do not set
  the option (mathlib does not), so checked Verso markup is
  confined to the library whose extraction pipeline wants it.
- Extending `scripts/manual.sh` with literate verbs instead of a
  second script. Rejected: the two products (authored manual,
  literate site) have different build closures and consumers; two
  small parallel scripts keep each legible, and the CI grep
  guards stay one-literal-per-product.

## Out of scope

- Real `GebLang` content and its citations; migration of the
  `Geb/Internal/` concrete-syntax modules.
- Publication (GitHub Pages) of either site; artifacts remain the
  CI product.
- Literate conversion of any existing library.
- Ordering, theming, or multi-page structure in `literate.toml`
  beyond the scoping and landing page above.

## Verification

- `lake build`, `lake test`, `lake lint`, and
  `lake lint -- GebLang` pass; the axiom linter runs on `GebLang`
  (its umbrella imports `GebMeta`) and the placeholder passes it.
- `bash scripts/literate.sh build` succeeds;
  `bash scripts/literate.sh serve` serves a site whose landing
  page shows the umbrella's prose and whose placeholder-module
  page shows the `{name}` role resolved; no `Geb`, `GebTests`,
  `GebMeta`, or `GebManual` module, and not the generator's
  `Main`, appears in the site.
- `lake build GebLang:docs` succeeds and the pinned doc-gen4
  renders the Verso-format docstring (checked during
  implementation; if the pin predates doc-gen4's Verso support,
  the docstring renders legibly as text and the gap is recorded
  for the next doc-gen4 bump).
- `scripts/lint-imports.sh` passes, and its self-test extension
  exercises both new entries: an induced `import Geb` in a
  `GebLang/` module is rejected, induced `GebLang.` leakage
  (in `GebLang/`) and `GebTests.Lang.` leakage (in
  `GebTests/Lang/`) outside import lines are rejected, and the
  conditional `Cslib.Init` rule is exercised in both directions
  (a `Cslib.*`-importing module without `Cslib.Init` fails; a
  module without Cslib imports needs no `Cslib.Init`).
- `TODO.md` carries the deferred-cluster entry (§ Import rules),
  the placeholder-replacement expectations (§ Tests,
  § Placeholder content), and the revised § Verso adoption entry
  (§ Standards and rule documents).
- `scripts/tests/test-lint-driver.sh` passes with the `GebLang`
  coverage scan.
- `scripts/pre-push.sh` passes end to end.
- `doc-build.yml` and `ci.yml` pass on the topic branch (deferred
  to the push after user review, as before).

## References

- Verso literate flow at `v4.34.0-rc1`: `src/verso-literate/`,
  the `literateHtml` package facet, and the users-guide chapter
  `doc/UsersGuide/Literate.lean` in
  `https://github.com/leanprover/verso`.
- `doc.verso` builtin option: Lean core `Lean/DocString/Extension.lean`
  (toolchain `v4.34.0-rc1`).
- doc-gen4 Verso docstring rendering:
  `https://github.com/leanprover/doc-gen4`
  (`DocGen4/DB/VersoDocString.lean`).
- Precedent: `https://github.com/teorth/analysis` (`literate.toml`,
  `build-web.sh`, literate site and doc-gen4 side by side).
- The manual workstream's spec and outcomes: repository history
  (the `doc/verso-manual` merge).
