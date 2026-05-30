# geb-mathlib

A Lean 4 + mathlib formalisation of Geb, a categorical programming
language whose first-class notions include "programming language"
itself. The repository develops mathematical content in a style
shaped to be plausibly upstreamable to mathlib4 (via the
`Geb/Mathlib/` subtree) or CSLib (via `Geb/Cslib/`) alongside
downstream-only content (under `Geb/Internal/`).

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

## Process

The contributor-binding rules live in
[`CLAUDE.md`](CLAUDE.md). Path-scoped conditional rules live in
[`.claude/rules/`](.claude/rules/):

- `lean-coding.md` — applies to all `.lean` files.
- `upstream-eligible.md` — applies under `Geb/Mathlib/`,
  `Geb/Cslib/`, `GebTests/Mathlib/`, and `GebTests/Cslib/`.
- `markdown-writing.md` — applies to all `.md` files.
- `ci-and-workflow.md` — applies to `.github/workflows/` and
  `scripts/`.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## Upstream targets

Content in `Geb/Mathlib/` is intended for eventual extraction as
mathlib4 PRs. Content addressing computer-science topics
overlapping [CSLib](https://github.com/leanprover/cslib) targets
CSLib instead and lives in `Geb/Cslib/`. Code in `Geb/Internal/`
is not eligible for upstream submission; some of it may eventually be
recast into an upstream-eligible form and moved to `Geb/Mathlib/` or
`Geb/Cslib/`, while other Internal code has no upstream home.
