# geb-mathlib

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Dependencies](#dependencies)
- [License](#license)
- [Documentation](#documentation)
- [Process](#process)
- [Contributing](#contributing)
- [Upstream targets](#upstream-targets)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

A Lean 4 + mathlib formalisation of Geb, a categorical programming
language whose first-class notions include "programming language"
itself. The repository develops mathematical content in a style
shaped to be plausibly upstreamable to mathlib4 (via the
`Geb/Mathlib/` subtree) or Cslib (via `Geb/Cslib/`), with the Geb
language's core data structures in `GebLang/`, which ships to either
upstream per module, alongside prototypes (under
`Geb/Prototypes/`) whose expression is not yet settled.

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4).
- [cslib](https://github.com/leanprover/cslib).
- Lean 4 toolchain (see `lean-toolchain`).

See `lakefile.toml` for the full dependency declaration.

## License

[Apache 2.0](LICENSE), matching mathlib4.

## Documentation

- [`docs/index.md`](docs/index.md) — topological narrative of
  implemented mathematical content.
- [`docs/process.md`](docs/process.md) — process rationale and
  decision history.
- [`docs/references.md`](docs/references.md) — Lean library and
  mathematical reference catalog.
- The Geb manual (Verso): `scripts/manual.sh build` builds and
  generates it (`manual/_out/html-multi/`);
  `scripts/manual.sh serve` serves it and prints the URL. There
  is no watch mode: after editing under `manual/`, re-run
  `build` and refresh the browser. Built in CI by `doc-build.yml`,
  not by `lake build`.
- The `GebLang` literate site (Verso): `scripts/literate.sh build`
  builds the library, lints it, and renders the site;
  `scripts/literate.sh serve` serves it and prints the URL. It has no
  watch mode: after editing a docstring, re-run `build` and refresh
  the browser. Built in CI by `doc-build.yml`; the library
  itself is in the default `lake build`.

## Process

The contributor-binding rules live in three audience-shaped
entry-point files at the repo root:

- [CONTRIBUTING.md](CONTRIBUTING.md) — universal contributor
  rules (humans + AI agents).
- [AGENTS.md](AGENTS.md) — additions for AI coding agents in
  general.
- [CLAUDE.md](CLAUDE.md) — Claude Code-specific additions.

Path-scoped rules live in [docs/rules/](docs/rules/):

- `lean-coding.md` — applies to all `.lean` files.
- `upstream-eligible.md` — applies under `Geb/Mathlib/`,
  `Geb/Cslib/`, `GebTests/Mathlib/`, `GebTests/Cslib/`, `GebLang/`,
  and `GebTests/Lang/`.
- `markdown-writing.md` — applies to all `.md` files.
- `ci-and-workflow.md` — applies to `.github/workflows/` and
  `scripts/`.

Claude Code's path-scoped loader at
[.claude/rules/](.claude/rules/) consists of symlinks to the
canonical files in `docs/rules/` plus Claude-only delta files
for additions specific to Claude.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). All participants are
expected to follow the project's
[Code of Conduct](CODE_OF_CONDUCT.md).

## Upstream targets

Content in `Geb/Mathlib/` is intended for eventual extraction as
mathlib4 PRs. Where the subtree import rules leave no alternative,
a module there may instead target Lean core or Batteries; that
destination is open, per [TODO.md](TODO.md) § Upstream destination
of core- and Batteries-targeted content. Content addressing
computer-science topics
overlapping [CSLib](https://github.com/leanprover/cslib) targets
CSLib instead and lives in `Geb/Cslib/`. Code in `Geb/Prototypes/`
is a prototype: it works out a construction the language is to
have, without its written form being settled as the one to keep.
A prototype is not eligible for upstream submission while its
expression is provisional; once the expression is settled it is
recast into upstream-eligible form and moved to `Geb/Mathlib/`,
`Geb/Cslib/`, or `GebLang/`.

Content in `GebLang/` is upstream-eligible per module: a module whose
import closure reaches no `Cslib.*` extracts to mathlib4, and one
whose closure reaches it extracts to Cslib.
