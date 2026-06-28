---
paths:
  - "**/*.lean"
---

# Lean coding — Claude-only additions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [`lean4` sub-skill mapping](#lean4-sub-skill-mapping)
- [`lean-lsp` search and proof tools](#lean-lsp-search-and-proof-tools)
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

## `lean-lsp` search and proof tools

The `lean-lsp` MCP exposes these search and proof tools. Select
by question.

| Need | Tool |
| --- | --- |
| Does a declaration exist locally? | `lean_local_search` |
| A lemma stating X (natural language) | `lean_leansearch` |
| A lemma matching a type pattern | `lean_loogle` |
| The Lean name for a concept | `lean_leanfinder` |
| Lemmas that close the current goal | `lean_state_search` |
| Premises to feed `simp` / `aesop` | `lean_hammer_premise` |
| Minimise a goal's hypotheses | `lean_minimal_hypotheses` |
| Test tactics without editing the file | `lean_multi_attempt` |
| Profile a proof's tactic hotspots | `lean_profile_proof` |

The natural-language and pattern search tools are rate-limited;
prefer `lean_local_search` first, then verify any found name with
`lean_hover_info`.

## Lake / build workflow — Claude-tool notes

- Avoid bash process substitution (`<(...)`, `>(...)`); these
  trigger manual approval prompts. Write intermediate output to a
  file under `/tmp` or in the working tree and read it back.
- Use the `Write` tool / direct file edits rather than shell
  commands for experimental code; place experiments inside the
  codebase, not under `/tmp`.
