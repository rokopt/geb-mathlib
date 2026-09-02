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

- **Optional `jj` insurance.** `.claude/settings.json` installs
  SessionStart hooks only. `scripts/hooks/block-mutating-git.sh`, a
  PreToolUse hook that turns any mutating `git` form into a
  permission prompt in a `jj` checkout, is not installed; a
  contributor who wants that insurance adds it to
  `.claude/settings.local.json` as the script's header shows.
  Which VCS an agent uses is decided by
  [AGENTS.md](AGENTS.md) § Version control follows the checkout.

## References

- [CONTRIBUTING.md](CONTRIBUTING.md) — universal contributor
  rules (auto-loaded via @import above).
- [AGENTS.md](AGENTS.md) — AI-agent additions on top of
  CONTRIBUTING (auto-loaded via @import above).
- [docs/rules/](docs/rules/) — path-scoped rule files.
- [.claude/rules/](.claude/rules/) — Claude Code's path-scoped
  loader: symlinks to docs/rules/ plus Claude-only delta files.
- [docs/process.md](docs/process.md) — rationale for every rule.
