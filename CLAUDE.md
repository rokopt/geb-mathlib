# geb-mathlib

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Audience](#audience)
- [Rules](#rules)
- [Phase-driven workflow](#phase-driven-workflow)
- [Tooling](#tooling)
- [When to consider creating a project-specific skill](#when-to-consider-creating-a-project-specific-skill)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Audience

This file binds Claude Code. It supplements
[CONTRIBUTING.md](CONTRIBUTING.md) and [AGENTS.md](AGENTS.md),
which apply to every contributor and every AI agent
respectively; the rules below are the Claude-specific additions.

@AGENTS.md
@CONTRIBUTING.md

## Rules

- **No raw mutating `git` subcommands.** The PreToolUse hook at
  `scripts/hooks/block-mutating-git.sh` is an allow-list of read-only
  forms; mutating forms (and unknown forms) trigger a permission
  prompt. Use `jj` for state-mutating operations.

## Phase-driven workflow

| Phase | Always-on skill | Helper |
| --- | --- | --- |
| Brainstorming | `superpowers:brainstorming` | — |
| Writing-plan | `superpowers:writing-plans` | — |
| Executing-plan | `superpowers:executing-plans` (or `superpowers:subagent-driven-development`) | phase-relevant Lean skills |
| Lean code work, mathlib search, literature search and citation | see [docs/rules/lean-coding.md](docs/rules/lean-coding.md) § Lean 4 skill workflows and § `lean-lsp` MCP search and proof tools; literature search uses `theoremsearch` (`theorem_search`), `arxiv-mcp-server` (`search_papers`, `read_paper`), and `deep-research` for multi-source cited surveys | `lean-lsp`, `serena` |
| Pre-commit | `superpowers:verification-before-completion` | — |
| Receiving review | `superpowers:receiving-code-review` | — |

The `superpowers` brainstorming, writing-plans, and
executing-plans skills write spec and plan files under
`docs/superpowers/specs/` and `docs/superpowers/plans/` and leave
them in the working tree. Those files are spec and plan documents
like any other: the lifespan rules in
[CONTRIBUTING.md](CONTRIBUTING.md) § Concern shape apply, so remove
them in the final commits of the topic branch.

## Tooling

- Skills: `superpowers:*`, `lean4:*`, `claude-md-management:*`,
  `code-review:*`, `pr-review-toolkit:*`, `commit-commands:*`,
  `security-review`, `deep-research`; plus
  `dispatching-parallel-agents`, `systematic-debugging`,
  `test-driven-development`, `remember`, `session-report`,
  `fewer-permission-prompts`, `claude-automation-recommender`
  (one-shot).
- MCPs: `lean-lsp`, `serena`, `arxiv-mcp-server`. `session-report` and
  `claude-automation-recommender` are one-shot health checks worth
  running at workstream boundaries.

## When to consider creating a project-specific skill

If recurring patterns accumulate that don't fit `CONTRIBUTING.md`,
`AGENTS.md`, `CLAUDE.md`, `docs/process.md`, `docs/rules/*.md`,
or existing `.claude/rules/*.md`, use
`skill-creator:skill-creator` to generate a `geb-development`
skill. Default is to wait for friction.

## References

- [CONTRIBUTING.md](CONTRIBUTING.md) — universal contributor
  rules (auto-loaded via @import above).
- [AGENTS.md](AGENTS.md) — AI-agent additions on top of
  CONTRIBUTING (auto-loaded via @import above).
- [docs/rules/](docs/rules/) — path-scoped rule files.
- [.claude/rules/](.claude/rules/) — Claude Code's path-scoped
  loader: symlinks to docs/rules/ plus the two Claude-only
  delta files.
- [docs/process.md](docs/process.md) — rationale for every rule.
