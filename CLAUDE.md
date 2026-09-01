# geb-mathlib

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Audience](#audience)
- [Rules](#rules)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Audience

This file binds Claude Code. It supplements
[CONTRIBUTING.md](CONTRIBUTING.md) and [AGENTS.md](AGENTS.md),
which apply to every contributor and every AI agent
respectively; the rules below are the Claude-specific additions.
Skill and MCP guidance is agent-generic and lives in
[AGENTS.md](AGENTS.md) § Skills and MCP servers.

@AGENTS.md
@CONTRIBUTING.md

## Rules

- **No raw mutating `git` subcommands.** The PreToolUse hook at
  `scripts/hooks/block-mutating-git.sh` is an allow-list of read-only
  forms; mutating forms (and unknown forms) trigger a permission
  prompt. Use `jj` for state-mutating operations.

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
