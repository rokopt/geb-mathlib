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

The experimental repository (the `geb-lean` package of the `geb`
repository, `https://github.com/anoma/geb`) introduced a Verso
manual for its ramified-recurrence area in the merges titled
"Verso manual for ramified recurrence" and "Fix Verso build
dependencies" (merged 2026-07-23 UTC). Its architecture, adopted
here:

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
  `lake build`; with the library outside `defaultTargets`, a clean
  CI checkout failed with `unknown module prefix`, while developer
  machines with warm `.lake` trees never reproduced it. Its fix
  prepended `lake build <lib>`. Here the build, lint, and generate
  commands live in one script run identically by CI and locally,
  so the ordering is fixed in one place.
- Document sources sat as a fourth top-level module tree beside the
  code, tests, and axiom checks, with the executable root at the
  package root; generated HTML landed in `_out/` at the package
  root (Verso's default). Here everything Verso-related lives under
  one directory (§ Layout).
- No serve or reload instructions existed anywhere; the build
  commands appeared only in a CI file and a pre-commit comment.
  Here a script provides `build` and `serve` verbs and the
  documentation states the build, browse, and reload workflow
  (§ Build, serve, reload).

The experimental repository is public, so its details (the
`Verso.Genre.Manual.InlineLean` open, the nolints entries its
manual carries, its CI step) are verifiable directly; review
round 2 verified them against `anoma/geb`.

### Ecosystem

- Verso's tags are named after Lean toolchains; its README directs
  a project on toolchain `leanprover/lean4:vX` to pin `rev = "vX"`.
  A `v4.34.0-rc1` tag exists, matching this repository's
  `lean-toolchain` and its `mathlib`, `cslib`, and `doc-gen4` pins.
- The document-library-plus-generator-executable pattern is the
  layout of [verso-templates](https://github.com/leanprover/verso-templates)
  and of Verso projects generally
  ([fp-lean](https://github.com/leanprover/fp-lean),
  [reference-manual](https://github.com/leanprover/reference-manual)).
  A document that imports the code it references must share the
  code's toolchain, so such documents sit in the code's Lake
  package; separate doc packages (fp-lean's `book/`) suit projects
  that quote code via SubVerso anchors instead of importing it.
  ([teorth/analysis](https://github.com/teorth/analysis) follows a
  third shape, Verso's literate flow over docstrings, not adopted
  here.)
- Local preview: the `verso` package ships a `verso-serve`
  executable (`lake exe verso-serve <output-dir>`, port 8000).
  Neither Verso nor any surveyed project has a watch or
  auto-reload mechanism; the observed workflow is re-run the
  generator (Lake rebuilds only the changed modules), then refresh
  the browser.
- Verso has no binary cache analogous to mathlib's; it and its
  transitive dependencies (`subverso`, `MD4Lean`, `plausible`,
  `illuminate`) compile from source on first build.

## Design

### Dependency

`lakefile.toml` gains, above both the `doc-gen4` and `mathlib`
requires (whose declared-last comment continues to hold):

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

At `v4.34.0-rc1`, Verso requires `subverso`, `MD4Lean`,
`plausible`, and `illuminate`, each at branch `main`. Two of these
overlap pins the repository already carries: `plausible` is among
the mathlib transitive pins the declared-last comment protects, and
`MD4Lean` arrives already pinned through `doc-gen4`. Verso is
therefore declared ahead of both `doc-gen4` and `mathlib`, so
that under Lake's reverse-order root resolution both existing
pins take precedence over Verso's branch requires.

`update.yml` rewrites every `rev = "..."` line in `lakefile.toml`
to the target toolchain tag, so the `verso` pin participates in
the existing bump automation; the workflow's step name, which
names the requires the rewrite covers, gains the new member. Two
failure modes exist at bump time: a target toolchain Verso has
not tagged, and drift in Verso's branch-pinned transitives, which
`lake update` re-resolves to branch heads. Both surface through
the workflow's existing build-before-commit behavior as a
reported failure rather than a committed breakage.

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
`lake build`, `lake test`, and the default `lake lint` compile
nothing new and no contributor compiles Verso implicitly. The
manifest change does have one-time effects: a workspace load
materializes the new checkouts (`verso`, `subverso`,
`illuminate`), and the pre-push `cache get` stamp mismatches once,
forcing one refetch. `Main` is outside the `GebManual` module
prefix, so `lake lint -- GebManual` does not reach it.
`.gitignore` gains `/manual/_out`.

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

The snippet is abbreviated: the file carries the copyright header
and, where feasible, the `module` discipline
`docs/rules/lean-coding.md` requires, as do the document modules.
No surveyed Verso project declares `module` in a `#doc` file
(Verso's own guide, reference-manual, verso-templates, and the
experimental repository all use plain imports), so whether `#doc`
elaborates inside a `module`-form file is settled during
implementation (§ Verification). The experimental repository
recorded the obstruction it hit: at its pin, `#doc` emitted a
non-`public` `def`, unexported under `module` and so unreachable
by `%doc` and `{include}`. At `v4.34.0-rc1` that mechanism is
gone (Verso's `Doc/Concrete.lean` is itself `module`-form and
`#doc` emits a `public def`), so the expected outcome is
feasibility. If it fails regardless, the document modules stay in
non-`module` form and the exemption is recorded in
`docs/rules/lean-coding.md`, as the experimental repository
recorded it.

### Build, serve, reload

`scripts/manual.sh` with two verbs, resolving the repository root
and running from it as the existing scripts do (`runLinter`
resolves `scripts/nolints.json`, and the generator resolves
`--output manual/_out`, against the working directory):

- `build`: `lake build GebManual`, `lake lint -- GebManual`,
  `lake exe geb-manual --output manual/_out` (Lake's `exe` command
  forwards the trailing arguments to the program verbatim, with no
  `--` separator; `manualMain` rejects an unknown `--` argument).
  Build precedes lint, the order the experimental repository's CI
  fix established, and CI runs this same script, so local and CI
  invocations cannot diverge.
- `serve`: `lake exe verso-serve manual/_out/html-multi`.
  `verso-serve` binds `127.0.0.1`, starts at port 8000 (scanning
  upward, bounded, when it is taken), and prints the URL it
  actually serves.

Reload after an edit is: re-run `build`, refresh the browser. The
script's usage text states this; neither Verso nor any surveyed
project offers a watch mode to reuse.

### CI

`doc-build.yml` (the existing doc-gen4 workflow) gains
`manual/**`, `scripts/manual.sh`, and `scripts/nolints.json` in
its `paths` filter (the manual lint consumes the nolints file, so
a change to it must trigger the workflow) and two steps after the
doc-gen4 build:

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

Cost: the step compiles Verso and its transitive dependencies from
source (no binary cache covers them) inside the job's existing
`timeout-minutes: 60`; if the addition approaches that budget, the
manual moves to its own job. `lake lint -- GebManual` appends its
argument to `lintDriverArgs`, so the driver lints `Geb` before
`GebManual`, the same behavior and cost as the existing
`lake lint -- GebTests` invocation in `ci.yml`.

### Linting

- `scripts/nolints.json` is introduced (the nolints path the
  batteries `runLinter` hardcodes; the repository has none yet)
  with `docBlame` entries for the `def`s Verso elaborates from
  `#doc` blocks, and for those only: the bibliography `def`s are
  hand-written and carry docstrings under this repository's
  rules, so they need no exemption. The precedent's
  `topNamespace` exemptions likewise have no counterpart here:
  under this repository's pins, Cslib's `topNamespace` linter
  carries no `env_linter` attribute, so `runLinter` never runs
  it.
- The axiom linter (`GebMeta.detectNonstandardAxiom`) registers
  through `GebMeta`, which `Geb.lean` and `GebTests.lean` import
  for that purpose. The manual's modules import the specific `Geb`
  modules they reference, not `GebMeta`, so
  `lake lint -- GebManual` runs without the axiom linter. This
  scope boundary is intended: the constructive discipline governs
  the formalization, while the manual's document objects are
  rendering data whose terms depend on Verso's own axiom usage,
  which the repository does not constrain. The boundary is
  recorded in `docs/rules/lean-coding.md`; implementation verifies
  that the manual lint environment does not register the linter,
  and this design point is revisited if a `Geb` module the manual
  imports ever pulls in `GebMeta` transitively.
- The manual library's `leanOptions` append onto the package's
  (`mathlibStandardSet`, `flexible`, `style.header`,
  `warningAsError`), so the library overrides individual linters
  and inherits the rest, and every remaining linter warning in a
  document module is an error. The accommodations known in advance are
  `linter.hashCommand` off (the `#doc` command is the document
  syntax) and Verso's code line-length warning at 100. Any further
  linter the document modules cannot satisfy (the style and header
  linters over `#doc` syntax are the candidates) is disabled in
  the library's `leanOptions` during implementation, each with its
  rationale recorded in `docs/rules/lean-coding.md`.
  `weak.warningAsError` stays on, so the accommodation set is
  exactly the set a clean build requires, no wider.
- `scripts/tests/test-lint-driver.sh` extends by static checks
  only: its reachability scan covers `manual/` (no module orphaned
  from `GebManual.lean`; the scan's module-to-path mapping must
  account for `srcDir`, and `Main` is exempt, being outside the
  library's closure by design), and a workflow check asserts
  `doc-build.yml` retains the `scripts/manual.sh build` step. The
  executed-lint check is not extended to `GebManual`: the script
  runs in `pre-push.sh` and `ci.yml`, and executing the manual
  lint there would compile Verso in both, contradicting § Layout's
  exclusions.

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
  `docs/index.md`, initially brief, using `{name}` roles and
  `signature` blocks against `Geb` declarations so the references
  are type-checked. Further chapters are added per area by later
  workstreams.
- `Bibliography.lean` carries entries only for works the chapters
  cite, keyed as in `docs/references.bib`. The `.bib` file remains
  the authoritative record per `CONTRIBUTING.md` § Cite the
  literature; the Lean entries are a rendering transcription of
  it, and a divergence between the two is corrected against the
  `.bib`. Verso resolves a citation key to a top-level `def`, so
  the shared keys (UpperCamelCase in the `.bib`) depart from the
  lowerCamelCase term-naming rule; the exemption, justified by
  cross-artifact key identity, is recorded in
  `docs/rules/lean-coding.md`.

### Documentation updates

- `README.md` gains a section naming the manual, its build
  command, its serve command, and the reload workflow (the three
  facts the experimental repository never wrote down).
  `docs/index.md` gains only a pointer to the manual: its charter
  is the catalogue of implemented content, so the commands live in
  `README.md`.
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
  layout defect recorded in § Precedents; `srcDir` achieves the
  same targets under one directory.
- `verso-blueprint` (the formalization-blueprint genre). Not
  adopted: the goal is a manual presenting the language, not a
  proof-dependency blueprint; the genre can be revisited if a
  blueprint is wanted later.
- A watch/auto-reload mechanism. Not built: nothing was found to
  reuse in Verso or the surveyed projects, and rebuild-and-refresh
  is the established practice in all of them.

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
- `bash scripts/manual.sh serve` serves the output; the URL
  `verso-serve` prints renders the manual with working `{name}`
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
- The manual lint environment does not register
  `GebMeta.detectNonstandardAxiom` (§ Linting), checked during
  implementation.
- `#doc` elaborates inside a `module`-form file, or the fallback
  of § Generator executable (non-`module` document files with a
  recorded exemption) is taken; settled during implementation.

## References

- Verso: `https://github.com/leanprover/verso` (README: dependency
  declaration, tag-per-toolchain policy, `verso-serve`).
- Verso tags: `https://github.com/leanprover/verso/tags`
  (`v4.34.0-rc1` present).
- Templates: `https://github.com/leanprover/verso-templates`
  (document library + generator executable + `_out/html-multi`).
- Precedent projects:
  `https://github.com/leanprover/fp-lean` (separate doc package),
  `https://github.com/leanprover/reference-manual`,
  `https://github.com/teorth/analysis` (literate docstring flow, a
  shape not adopted here).
- Experimental repository: the `geb-lean` package of
  `https://github.com/anoma/geb`, merges "Verso manual for
  ramified recurrence" and "Fix Verso build dependencies"
  (merged 2026-07-23 UTC).
