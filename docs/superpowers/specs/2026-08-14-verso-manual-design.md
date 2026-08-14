# Verso manual: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Transcription or novelty](#transcription-or-novelty)
- [Precedents](#precedents)
  - [Experimental repository](#experimental-repository)
  - [Ecosystem](#ecosystem)
- [Design](#design)
  - [Dependency](#dependency)
  - [Layout](#layout)
  - [Generator executable](#generator-executable)
  - [Build, serve, reload](#build-serve-reload)
  - [CI](#ci)
  - [Linting](#linting)
  - [Content](#content)
  - [Documentation updates](#documentation-updates)
- [Alternatives considered](#alternatives-considered)
- [Out of scope](#out-of-scope)
- [Verification](#verification)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Goal

Add a [Verso](https://github.com/leanprover/verso) manual to the
repository: the build infrastructure (dependency, document library,
generator executable, build and serve commands, CI step) plus an
initial project-overview document. The manual presents Geb as a
programming language whose specification, interpreter, and compiler
are developed as formal mathematics; this repository develops that
mathematics in Lean 4 against mathlib. The manual complements
`doc-gen4` (already built by `doc-build.yml`): `doc-gen4` renders
per-declaration API documentation, while the manual is authored
prose with type-checked references into the code.

## Transcription or novelty

This workstream introduces no mathematical definitions or theorems;
it is build infrastructure and expository prose. The citation rule
of `CONTRIBUTING.md` § Cite the literature when transcribing applies
to works the manual's prose cites: each such work is keyed in
`docs/references.bib`, and the manual's bibliography entries use the
same keys.

## Precedents

### Experimental repository

The experimental repository (`geb/geb-lean`) introduced a Verso
manual for its ramified-recurrence area on 2026-07-22. Its
architecture, adopted here:

- `verso` required at the tag named after the Lean toolchain,
  declared ahead of mathlib so mathlib's transitive pins survive
  Lake's reverse-order root resolution.
- A `lean_lib` of document modules in the `Manual` genre (a root
  `Part`, section modules, a bibliography module) and a `lean_exe`
  whose `main` passes the root document to `manualMain`.
- The manual library excluded from `defaultTargets`, the test
  driver, and the local pre-push checks; CI runs
  `lake build <lib>`, `lake lint -- <lib>`, then the generator.
- Lint accommodations: `docBlame` nolints for the `def`s Verso
  elaborates from each `#doc` block, `topNamespace` nolints for
  bibliography keys (Verso resolves a `citep` key to a top-level
  `def`), and `linter.hashCommand` disabled for the library (the
  `#doc` command is the document syntax).
- `open Verso.Genre.Manual.InlineLean` is required in document
  modules: the `name`, `signature`, `lean`, and `leanTerm` roles
  are not reached by `open Verso.Genre Manual`.

Defects in that implementation, corrected here:

- Its CI step initially ran `lake lint` without a preceding
  `lake build`. `lake lint` loads `.olean` files but does not
  compile them, and the library is outside `defaultTargets`, so a
  clean CI checkout failed with `unknown module prefix`; developer
  machines with warm `.lake` trees never reproduced it. The fix
  (its PR #281) prepended `lake build <lib>`. Here the build, lint,
  and generate commands live in one script run identically by CI
  and locally, so the divergence cannot recur silently.
- Document sources sat as a fourth top-level module tree beside the
  code, tests, and axiom checks, with the executable root loose at
  the package root; generated HTML landed in `_out/` at the package
  root (Verso's default). Here everything Verso-related lives under
  one directory (§ Layout).
- No serve or reload instructions existed anywhere; the build
  commands appeared only in a CI file and a pre-commit comment.
  Here a script provides `build` and `serve` verbs and the
  documentation states the build, browse, and reload workflow
  (§ Build, serve, reload).

### Ecosystem

- Verso's tags are named after Lean toolchains; its README directs
  a project on toolchain `leanprover/lean4:vX` to pin `rev = "vX"`.
  A `v4.34.0-rc1` tag exists, matching this repository's
  `lean-toolchain` and its `mathlib`, `cslib`, and `doc-gen4` pins.
- The document-library-plus-generator-executable pattern is the
  layout of [verso-templates](https://github.com/leanprover/verso-templates)
  and of Verso projects generally
  ([fp-lean](https://github.com/leanprover/fp-lean),
  [teorth/analysis](https://github.com/teorth/analysis),
  [reference-manual](https://github.com/leanprover/reference-manual)).
  Projects whose documents import their formalization keep the
  documents in the same Lake package (teorth/analysis); separate
  doc packages (fp-lean's `book/`) suit projects that quote code
  via SubVerso anchors instead of importing it.
- Local preview: the `verso` package ships a `verso-serve`
  executable (`lake exe verso-serve <output-dir>`, port 8000).
  No Verso project has a watch or auto-reload mechanism; the
  observed workflow everywhere is re-run the generator (Lake
  rebuilds only the changed modules), then refresh the browser.
- Verso has no binary cache analogous to mathlib's; it and its
  transitive dependencies (SubVerso, MD4Lean) compile from source
  on first build.

## Design

### Dependency

`lakefile.toml` gains, above the mathlib require (whose
declared-last comment continues to hold):

```toml
# Pinned in lockstep with `lean-toolchain`; bump `rev` when bumping
# the toolchain version. Verso's tags are named after Lean
# toolchains; if a bump targets a toolchain Verso has not yet
# tagged, the bump waits for the tag (`update.yml` reports the
# failed update rather than committing it).
[[require]]
name = "verso"
scope = "leanprover"
rev = "v4.34.0-rc1"
```

`update.yml` rewrites every `rev = "..."` line in `lakefile.toml`
to the target toolchain tag, so the verso pin participates in the
existing bump automation unchanged. The failure mode is a target
toolchain Verso has not tagged; the workflow's existing
build-before-commit behavior surfaces it as a reported failure.

### Layout

All Verso sources and output live under one directory, using Lake's
per-target `srcDir`:

```text
manual/
├── GebManual.lean      library root (imports GebManual.Root)
├── GebManual/
│   ├── Root.lean       root Part; includes the chapters
│   ├── Introduction.lean
│   ├── ...             further chapters, added per area
│   └── Bibliography.lean
├── Main.lean           generator executable root
└── _out/               generated HTML; gitignored
```

`lakefile.toml` targets:

```toml
[[lean_lib]]
name = "GebManual"
srcDir = "manual"

[lean_lib.leanOptions]
weak.verso.code.warnLineLength = 100
weak.linter.hashCommand = false

[[lean_exe]]
name = "geb-manual"
srcDir = "manual"
root = "Main"
supportInterpreter = true
```

`GebManual` joins neither `defaultTargets` nor the test driver, so
`lake build`, `lake test`, and the default `lake lint` are
unaffected and no contributor compiles Verso implicitly. `Main` is
outside the `GebManual` module prefix, so `lake lint -- GebManual`
does not reach it. `.gitignore` gains `/manual/_out`.

### Generator executable

`manual/Main.lean`, in the shape of the precedent:

```lean
import GebManual

open Verso.Genre.Manual

/-- Generate the Geb manual. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc GebManual.Root)
    (options := args)
    (config := {
      sourceLink := some "https://github.com/rokopt/geb-mathlib",
      issueLink := some "https://github.com/rokopt/geb-mathlib/issues"
    })
```

### Build, serve, reload

`scripts/manual.sh` with two verbs:

- `build`: `lake build GebManual`, `lake lint -- GebManual`,
  `lake exe geb-manual -- --output manual/_out`. The explicit
  build-before-lint order is the corrected form of the
  experimental repository's CI defect, and CI runs this same
  script, so local and CI invocations cannot diverge.
- `serve`: `lake exe verso-serve manual/_out/html-multi`, printing
  the URL (`http://localhost:8000/`) before starting.

Reload after an edit is: re-run `build`, refresh the browser. The
script's usage text states this; there is no watch mode anywhere in
the Verso ecosystem to reuse.

### CI

`doc-build.yml` (the existing doc-gen4 workflow) gains
`manual/**` and `scripts/manual.sh` in its `paths` filter and two
steps after the doc-gen4 build:

```yaml
- run: bash scripts/manual.sh build
- name: Upload the generated manual
  uses: actions/upload-artifact@<pinned-sha>  # v7.0.1
  with:
    name: geb-manual
    path: manual/_out/html-multi
    if-no-files-found: error
```

The action SHA follows the pinning policy
(`docs/rules/ci-and-workflow.md` § Action pinning policy).
Publication (GitHub Pages) is out of scope, as it was in the
experimental repository; the uploaded artifact is the CI-visible
product.

### Linting

- `scripts/nolints.json` is introduced (the batteries `runLinter`
  nolints file; the repository has none yet) with `docBlame`
  entries for the `def`s Verso elaborates from `#doc` blocks and
  `topNamespace` entries for bibliography keys.
- The manual library's `leanOptions` disable `linter.hashCommand`
  (the `#doc` command is the document syntax) and set Verso's code
  line-length warning to 100, per the precedent.
- `scripts/tests/test-lint-driver.sh` extends its guard to
  `GebManual` and `doc-build.yml` analogously to the experimental
  repository's guard extension; the exact form follows the
  script's existing table during implementation.
- Rule deltas the manual forces (generated `def`s without
  docstrings, top-level bibliography `def`s, any header or module
  conventions the document modules cannot satisfy) are recorded in
  `docs/rules/lean-coding.md` with their rationale.

### Content

The initial document is a project overview:

- A root `Part` titled Geb.
- An introduction chapter: Geb is a programming language; its
  specification, interpreter, and compiler are developed as formal
  mathematics, which this repository formalizes in Lean 4 against
  mathlib under a constructive discipline; the subtree structure
  (`Geb/Mathlib/` and `Geb/Cslib/` upstream-eligible,
  `Geb/Internal/` downstream-only) and the upstreaming intent.
- One area chapter seeded from the content catalogued in
  `docs/index.md`, thin at first, using `{name}` roles and
  `signature` blocks against `Geb` declarations so the references
  are type-checked. Further chapters are added per area by later
  workstreams.
- `Bibliography.lean` carries entries only for works the chapters
  cite, keyed as in `docs/references.bib`.

### Documentation updates

- `README.md` and `docs/index.md` gain a section naming the manual,
  its build command, its serve command and URL, and the reload
  workflow (the three facts the experimental repository never
  wrote down).
- `docs/rules/ci-and-workflow.md` records the manual's CI-only
  build status and the script; `docs/rules/lean-coding.md` records
  the exemptions per § Linting.

## Alternatives considered

- A separate Lake package under `manual/` with its own lakefile and
  manifest (the fp-lean shape). Rejected: the manual imports `Geb`
  for `{name}` and `signature` references, which forces the
  toolchains to match anyway, so the second package adds a second
  manifest and bump surface without decoupling anything.
- The experimental repository's layout (document tree and
  executable root at the package top level). Rejected: it is the
  layout complaint this design exists to fix; `srcDir` achieves
  the same targets under one directory.
- `verso-blueprint` (the formalization-blueprint genre). Not
  adopted: the goal is a manual presenting the language, not a
  proof-dependency blueprint; the genre can be revisited if a
  blueprint is wanted later.
- A watch/auto-reload mechanism. Not built: nothing exists to
  reuse in the ecosystem, and the rebuild-and-refresh workflow is
  the established practice everywhere Verso is used.

## Out of scope

- GitHub Pages publication of the manual (the artifact upload is
  the CI product; publication is its own workstream, as in the
  experimental repository).
- Migration or restructuring of the existing Markdown
  documentation under `docs/`.
- Manual chapters beyond the introduction and the first area
  chapter.

## Verification

- `bash scripts/manual.sh build` succeeds from a clean `.lake`
  state for the manual targets (build, lint, generate).
- `bash scripts/manual.sh serve` serves the output;
  `http://localhost:8000/` renders the manual with working `{name}`
  hovers and the bibliography.
- `doc-build.yml` passes on the topic branch, including the
  artifact upload.
- `scripts/pre-push.sh` passes: the manual stays outside the
  default build/test/lint graph, and the Markdown checks cover the
  documentation updates.
- The `srcDir` placement of both targets and the `verso-serve`
  invocation are confirmed against the pinned Verso and Lake
  versions during implementation (they are reported by the
  research, not yet exercised in this repository).

## References

- Verso: `https://github.com/leanprover/verso` (README: dependency
  declaration, tag-per-toolchain policy, `verso-serve`).
- Verso tags: `https://github.com/leanprover/verso/tags`
  (`v4.34.0-rc1` present).
- Templates: `https://github.com/leanprover/verso-templates`
  (document library + generator executable + `_out/html-multi`).
- Precedent projects: `https://github.com/teorth/analysis`
  (same-package manual over mathlib),
  `https://github.com/leanprover/fp-lean` (separate doc package),
  `https://github.com/leanprover/reference-manual`.
- Experimental repository: `geb/geb-lean`, PRs #280 (manual) and
  #281 (CI build-before-lint fix).
