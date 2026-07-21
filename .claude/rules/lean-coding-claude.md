---
paths:
  - "**/*.lean"
---

# Lean coding — Claude-only additions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Lake / build workflow — Claude-tool notes](#lake--build-workflow--claude-tool-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Applies whenever a `.lean` file is open or being edited.
Additions specific to Claude Code, on top of the canonical
`docs/rules/lean-coding.md`.

## Lake / build workflow — Claude-tool notes

- Avoid bash process substitution (`<(...)`, `>(...)`); these
  trigger manual approval prompts. Write intermediate output to a
  file under `/tmp` or in the working tree and read it back.
- Use the `Write` tool / direct file edits rather than shell
  commands for experimental code; place experiments inside the
  codebase, not under `/tmp`.
