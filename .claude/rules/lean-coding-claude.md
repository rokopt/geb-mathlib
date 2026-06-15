---
paths:
  - "**/*.lean"
---

# Lean coding — Claude-only additions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [`lean4` sub-skill mapping](#lean4-sub-skill-mapping)
- [Lake / build workflow — Claude-tool notes](#lake--build-workflow--claude-tool-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Applies whenever a `.lean` file is open or being edited.
Additions specific to Claude Code, on top of the canonical
`docs/rules/lean-coding.md`.

## `lean4` sub-skill mapping

| Activity | Skill | Always-on? |
| --- | --- | --- |
| Drafting from informal math | `lean4:draft`, `lean4:formalize`, `lean4:autoformalize` | Try `autoformalize` early |
| Proving a stated lemma | `lean4:prove`, `lean4:autoprove` | Try `autoprove` when stuck |
| Filling stubborn `sorry`s | `lean4:sorry-filler-deep` | When fast pass fails or proofs are complex |
| Polishing a proof | `lean4:golf` | Yes, post-process |
| Refactoring existing Lean code | `lean4:refactor` | Yes, during refactors |
| Pre-commit Lean review | `lean4:review` | Yes, before any Lean commit |
| Exploring mathlib | `lean4:learn` | As needed |
| Diagnosis | `lean4:doctor` | As needed |
| Save progress | `lean4:checkpoint` | At milestones |

## Lake / build workflow — Claude-tool notes

- Avoid bash process substitution (`<(...)`, `>(...)`); these
  trigger manual approval prompts. Write intermediate output to a
  file under `/tmp` or in the working tree and read it back.
- Use the `Write` tool / direct file edits rather than shell
  commands for experimental code; place experiments inside the
  codebase, not under `/tmp`.
