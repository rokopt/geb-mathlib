# geb-mathlib

A Lean 4 + mathlib formalisation of Geb. See `README.md` for the
project's identity and `docs/process.md` for the rationale behind
each rule below.

## Rules

- **No `jj git push` without user line-by-line review.** This includes
  first-creation pushes, force-pushes, branch-deletes, tag-pushes.
- **No raw mutating `git` subcommands.** The PreToolUse hook at
  `scripts/hooks/block-mutating-git.sh` is an allow-list of read-only
  forms; mutating forms (and unknown forms) trigger a permission
  prompt. Use `jj` for state-mutating operations.
- `.remember/*.md` must be markdownlint-clean; clean up after each
  `remember`-skill invocation (the plugin emits non-clean markdown).
  Rationale and operational details: see `docs/process.md`
  § Markdownlint discipline.

## Phase-driven workflow

| Phase | Always-on skill | Helper |
| --- | --- | --- |
| Brainstorming | `superpowers:brainstorming` | `sequential-thinking`; Lean helpers as needed |
| Writing-plan | `superpowers:writing-plans` | `sequential-thinking`; Lean helpers as needed |
| Executing-plan | `superpowers:executing-plans` (or `superpowers:subagent-driven-development`) | phase-relevant Lean skills |
| Lean code work | `lean4` umbrella (sub-skills below) | `lean-lsp`, `serena` MCPs |
| Mathlib search | `lean-lsp` (`leansearch`, `loogle`, `local_search`, `hammer_premise`) | — |
| Pre-commit | `superpowers:verification-before-completion` | — |
| Receiving review | `superpowers:receiving-code-review` | — |

`lean4` sub-skill mapping by activity (drafting, proving, filling
`sorry`, golfing, porting, review, exploration, diagnosis,
checkpointing) lives in `.claude/rules/lean-coding.md` § `lean4`
sub-skill mapping.

Specs and plans are
adversarially-reviewed before execution begins (see
`docs/process.md` § Adversarial review). Verify agent claims
against authoritative sources before committing them to artifacts;
include citations.

## Mathlib upstream guides

Binding for all `.lean` content and all commit messages:

- Contributing index:
  `https://leanprover-community.github.io/contribute/index.html`
- Commit messages:
  `https://leanprover-community.github.io/contribute/commit.html`
- Coding style:
  `https://leanprover-community.github.io/contribute/style.html`
- Naming conventions:
  `https://leanprover-community.github.io/contribute/naming.html`
- Documentation:
  `https://leanprover-community.github.io/contribute/doc.html`

Bullet-point highlights and adversarial-reviewer instructions
are in `.claude/rules/lean-coding.md`. Re-fetch the guides on
every adversarial-review round; they are subject to upstream
revision.

## Tooling

- Skills: `superpowers:*`, `lean4:*`, `claude-md-management:*`,
  `code-review:*`, `pr-review-toolkit:*`, `commit-commands:*`,
  `security-review`; plus `dispatching-parallel-agents`,
  `systematic-debugging`, `test-driven-development`, `remember`,
  `session-report`, `fewer-permission-prompts`,
  `claude-automation-recommender` (one-shot).

## When to consider creating a project-specific skill

If recurring patterns accumulate that don't fit `CLAUDE.md` or
`docs/process.md`, use `skill-creator:skill-creator` to generate a
`geb-development` skill. Default is to wait for friction.

## References

- Process rationale: `docs/process.md`.
- Mathematical / library references catalog: `docs/references.md`.
- Path-scoped rules: `.claude/rules/` (in particular
  `lean-coding.md` for `.lean` files,
  `upstream-eligible.md` for `Geb/Mathlib/` and `Geb/Cslib/`,
  `markdown-writing.md` for `.md`,
  `ci-and-workflow.md` for CI / scripts).
