---
paths:
  - ".github/workflows/**"
  - "scripts/**"
---

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [CI and workflow — Claude-only additions](#ci-and-workflow--claude-only-additions)
  - [Hook-script conventions](#hook-script-conventions)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# CI and workflow — Claude-only additions

Applies to GitHub Actions workflow files and scripts. Additions
specific to Claude Code, on top of the canonical
`docs/rules/ci-and-workflow.md`.

## Hook-script conventions

Hook scripts in `scripts/hooks/` follow Claude Code's hook contract
(verified against
`https://code.claude.com/docs/en/hooks-overview` and
`https://code.claude.com/docs/en/hooks-reference`):

- Read JSON from stdin when invoked.
- Exit 0 to allow; exit 2 to hard-block (with stderr message). For
  PreToolUse hooks that prefer to surface the decision to the user,
  exit 0 with a `hookSpecificOutput.permissionDecision` JSON
  document on stdout (e.g., `permissionDecision: "ask"`); other
  non-zero exits are errors.
- Smoke-test in `scripts/hooks/tests/test-<hook>.sh`; CI runs the
  smoke tests.
- `.claude/settings.json` installs the SessionStart hooks only.
  `block-mutating-git.sh` is opt-in, installed by a contributor in
  `.claude/settings.local.json` per its header.
