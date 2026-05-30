# AGENTS.md

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Audience](#audience)
- [Agent-specific rules](#agent-specific-rules)
  - [No `jj git push` without user line-by-line review](#no-jj-git-push-without-user-line-by-line-review)
  - [Adversarial review of specs and plans](#adversarial-review-of-specs-and-plans)
  - [Verify agent claims](#verify-agent-claims)
  - [No LLM-drafted text in mathlib-facing channels (enforcement)](#no-llm-drafted-text-in-mathlib-facing-channels-enforcement)
  - [AI authoring modes (for upstream-eligible work)](#ai-authoring-modes-for-upstream-eligible-work)
  - [Credentialing-PR checkpoint (agent behavior)](#credentialing-pr-checkpoint-agent-behavior)
- [Path-scoped rules](#path-scoped-rules)
  - [When editing .lean files](#when-editing-lean-files)
  - [When editing files under Geb/Mathlib/ or Geb/Cslib/](#when-editing-files-under-gebmathlib-or-gebcslib)
  - [When editing .md files](#when-editing-md-files)
  - [When editing files under scripts/ or .github/workflows/](#when-editing-files-under-scripts-or-githubworkflows)
- [References](#references)

<!-- END doctoc -->

## Audience

This file binds AI coding agents in general. The rules below
supplement `CONTRIBUTING.md`, which applies unconditionally.
`CLAUDE.md` adds further rules for Claude Code specifically.

Every contributor is also bound by
[CONTRIBUTING.md](CONTRIBUTING.md); read it before reading the
rest of this file.

## Agent-specific rules

Work in upstream-eligible subtrees is governed by
[CONTRIBUTING.md § Submission policy](CONTRIBUTING.md), which
restricts LLM-generated code.

### No `jj git push` without user line-by-line review

This includes first-creation pushes, force-pushes,
branch-deletes, tag-pushes.

### Adversarial review of specs and plans

Specs and plans are adversarially-reviewed before execution
begins (see `docs/process.md` § Adversarial review). Re-fetch
the upstream guides on every adversarial-review round; they are
subject to upstream revision.

### Verify agent claims

Verify agent claims against authoritative sources before
committing them to artifacts; include citations.

### No LLM-drafted text in mathlib-facing channels (enforcement)

Do not draft PR descriptions, Zulip messages, or GitHub
issue/PR comments. These are user-authored per
[CONTRIBUTING.md § Submission policy](CONTRIBUTING.md).

### AI authoring modes (for upstream-eligible work)

| Authoring mode | Triggered by | AI agent may | User must |
| --- | --- | --- | --- |
| (a) User-driven | Credentialing-PR candidate | Suggest in natural language only | Write every line |
| (b) Co-authoring | Other upstream-eligible work | Draft provisional code | Read, rewrite, commit when fully understood |

### Credentialing-PR checkpoint (agent behavior)

Before starting any work in `Geb/Mathlib/` or `Geb/Cslib/` whose
only dependencies are the targeted upstream (i.e., a true
PR-candidate with no in-flight geb-mathlib deps), the AI agent
asks: "Is this the credentialing PR for this upstream?"

## Path-scoped rules

### When editing .lean files

Lean style, naming, docstring, and module-system rules bind
every .lean file in this repository.
See [docs/rules/lean-coding.md](docs/rules/lean-coding.md) for
the full text.

### When editing files under Geb/Mathlib/ or Geb/Cslib/

Additional upstream-eligibility rules apply (import rules,
authoring modes, subtree boundaries).
See [docs/rules/upstream-eligible.md](docs/rules/upstream-eligible.md)
for the full text.

### When editing .md files

Markdown-writing conventions (markdownlint, TOC, link
conventions, prose style) bind every committed .md file.
See [docs/rules/markdown-writing.md](docs/rules/markdown-writing.md)
for the full text.

### When editing files under scripts/ or .github/workflows/

CI and workflow conventions (commit-message format, pre-push
checklist, action pinning) apply to scripts and workflow files.
See [docs/rules/ci-and-workflow.md](docs/rules/ci-and-workflow.md)
for the full text.

## References

- [CONTRIBUTING.md](CONTRIBUTING.md) — universal contributor
  rules.
- [docs/rules/](docs/rules/) — path-scoped rule files binding
  every contributor for the file globs in each rule's `paths:`
  frontmatter.
- [docs/process.md](docs/process.md) — rationale for every rule.
- [CLAUDE.md](CLAUDE.md) — Claude-specific additions on top of
  this file.
