---
paths:
  - ".github/workflows/**"
  - "scripts/**"
---

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
