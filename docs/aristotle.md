# Aristotle theorem-proving CLI

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Availability and consent](#availability-and-consent)
- [Contribution-policy constraint](#contribution-policy-constraint)
- [Setup](#setup)
- [Commands](#commands)
- [Long-running proofs](#long-running-proofs)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Harmonic's Aristotle is a hosted system that formalizes and proves
Lean 4 goals, available as the `aristotle` console script shipped by
the `aristotlelib` package and run on demand via `uvx`. Aristotle
returns proofs that depend on Mathlib.

## Availability and consent

This repository does not assume Aristotle is configured in any
contributor's environment. The instructions below apply only when
the `aristotle` CLI and an `ARISTOTLE_API_KEY` are present.

Aristotle is a hosted, metered service: invoking it consumes the
contributor's account resources. Before using it, an agent asks the
contributor whether they want Aristotle used for the task at hand,
even when it is available.

## Contribution-policy constraint

Aristotle output is LLM-generated code. Under
[CONTRIBUTING.md § Submission policy](../CONTRIBUTING.md) it must
not enter `Geb/Mathlib/` or `Geb/Cslib/`; it may be used only in
`Geb/Internal/`, or as a reference the user rewrites line by line
before committing. Disclosure of LLM use remains mandatory.

Returned proofs are also subject to the repository's other rules:

- Constructive discipline. Aristotle scaffolds with whole-`import
  Mathlib` and `open scoped Classical`, and may produce proofs
  that depend on nonconstructive axioms. Run `#print axioms` and
  refactor per [docs/rules/lean-coding.md](rules/lean-coding.md)
  § Constructive-only Lean code before any use. A proof reported
  as relying only on `propext` (and `Quot.sound`) is acceptable;
  one pulling in `Classical.choice` is not.
- Style. The returned file follows Aristotle's conventions, not
  this repository's. Restyle to
  [docs/rules/lean-coding.md](rules/lean-coding.md) and replace
  the blanket `import Mathlib` with specific imports.
- Toolchain. Aristotle pins its own Lean toolchain (observed
  `leanprover/lean4:v4.28.0`), which may differ from this
  repository's `lean-toolchain`. Re-verify any proof under the
  repository's build before relying on it.

## Setup

The API key is read from the `ARISTOTLE_API_KEY` environment
variable. Invoke the CLI through `uvx`, which resolves the current
`aristotlelib`:

```bash
uvx --from aristotlelib aristotle <subcommand> [args]
```

## Commands

The `aristotle` CLI (aristotlelib 2.0.0) exposes these
subcommands; `submit`, `list`, and `download` were exercised
end to end, the remainder are from the 2.0.0 CLI source.

- `list` — list past projects (status, id, creation time).
- `submit "<instructions>" [--project-dir DIR] [--wait]
  [--destination FILE]` — create a project from a natural-language
  prompt, optionally uploading a directory of context files.
- `formalize INPUT_FILE [--wait] [--destination FILE]` — formalize
  a single file.
- `show PROJECT_ID` — task status and recent events.
- `download PROJECT_ID --destination FILE` — fetch the result.
- `ask PROJECT_ID "<instructions>"` — send a follow-up to a
  project.
- `tasks`, `cancel` — list tasks; cancel a task or project.

A connectivity check that costs no proof time:

```bash
uvx --from aristotlelib aristotle list
```

A minimal proof, waiting for completion:

```bash
uvx --from aristotlelib aristotle submit \
  "Prove in Lean 4 (with Mathlib) that n + 0 = n for every n : ℕ." \
  --wait --destination /tmp/aristotle-result.tar.gz
```

`--destination` is a file path, not a directory: the result is a
`.tar.gz` archive of a Lean project, written with `write_bytes`.
Passing an existing directory raises `IsADirectoryError`. Omitting
`--destination` writes `<project_id>_aristotle.tar.gz` to the
working directory. The archive contains the edited project,
including `RequestProject/Main.lean` and an `ARISTOTLE_SUMMARY.md`.

## Long-running proofs

A proof can take from minutes to hours. Submit without `--wait`,
or background the `--wait` form, and retrieve the result later by
`project_id`:

```bash
uvx --from aristotlelib aristotle submit "<instructions>"   # prints project id
uvx --from aristotlelib aristotle list --status IN_PROGRESS
uvx --from aristotlelib aristotle download <project_id> \
  --destination /tmp/result.tar.gz
```

Do not poll in a tight loop; query `list` or `show` at intervals
matched to the expected runtime.

## References

- [aristotlelib on PyPI](https://pypi.org/project/aristotlelib/)
- [Aristotle dashboard](https://aristotle.harmonic.fun/)
