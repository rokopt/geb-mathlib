# AGENTS.md

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Audience](#audience)
- [Agent-specific rules](#agent-specific-rules)
  - [No `jj git push` without user line-by-line review](#no-jj-git-push-without-user-line-by-line-review)
  - [Adversarial review of specs and plans](#adversarial-review-of-specs-and-plans)
  - [Verify agent claims](#verify-agent-claims)
  - [No LLM-drafted text in mathlib-facing channels (enforcement)](#no-llm-drafted-text-in-mathlib-facing-channels-enforcement)
  - [AI authoring (upstream-eligible work)](#ai-authoring-upstream-eligible-work)
  - [Aristotle (external LLM prover)](#aristotle-external-llm-prover)
- [Skills and MCP servers](#skills-and-mcp-servers)
- [Path-scoped rules](#path-scoped-rules)
  - [When editing .lean files](#when-editing-lean-files)
  - [When editing files under Geb/Mathlib/, Geb/Cslib/ or GebLang/](#when-editing-files-under-gebmathlib-gebcslib-or-geblang)
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
governs LLM-generated code (mandatory disclosure and line-by-line
understanding).

### No `jj git push` without user line-by-line review

This includes first-creation pushes, force-pushes,
branch-deletes, tag-pushes.

### Adversarial review of specs and plans

Specs and plans go through fresh-context adversarial review
rounds until convergence — no blocker and no serious findings —
before the user reviews the artifact and before execution
begins. Each round is a new general-purpose `Agent` invocation,
never a `SendMessage` to a continuing agent, so no round
inherits the previous reviewer's conclusions. Findings are
categorised blocker / serious / minor / cosmetic-taste; the
author responds in writing to every finding: fix, defer with
rationale, or reject as cosmetic-taste. Re-fetch the upstream
guides on every round; they are subject to upstream revision.
See [docs/process.md](docs/process.md) § Adversarial review.

### Verify agent claims

Verify agent claims against authoritative sources before
committing them to artifacts; include citations. When the claim
is the attribution of a mathematical definition or theorem,
locate and verify it against the primary source using available
paper-search tooling (e.g. an arXiv search) before recording the
citation identifier required by
[CONTRIBUTING.md § Cite the literature when transcribing](CONTRIBUTING.md).
Where installed, the `theoremsearch` MCP (`theorem_search`) locates
published statements and their searchable identifiers across the informal
literature (arXiv, the Stacks Project, ProofWiki, and others); see
[docs/references.md](docs/references.md) § Searchable.

### No LLM-drafted text in mathlib-facing channels (enforcement)

Do not draft PR descriptions, Zulip messages, or GitHub
issue/PR comments. These are user-authored per
[CONTRIBUTING.md § Submission policy](CONTRIBUTING.md).

### AI authoring (upstream-eligible work)

An AI agent may draft code for upstream-eligible locations. Before
the user commits it to `Geb/Mathlib/`, `Geb/Cslib/` or `GebLang/`,
the user understands every line, can justify each design decision to
reviewers without AI assistance, and discloses which tools were
used and how (per
[CONTRIBUTING.md § Submission policy](CONTRIBUTING.md)). There is
no human-only authoring track and no requirement to rewrite
AI-drafted code that already meets that bar.

### Aristotle (external LLM prover)

If Harmonic's Aristotle is available in the environment (the
`aristotle` CLI plus an API key), an agent may use it to formalize
and prove Lean. Consider it when a task exceeds the in-editor
tooling: to formalize a definition or theorem available only in a
published paper, or when a goal resists the `lean4` skill's
`autoprove` and `sorry-filler-deep` passes.

For mathematics available only in published sources, locate the
reference with the `theoremsearch` (`theorem_search`) or
`arxiv-mcp-server` (`search_papers`, `read_paper`) MCP where
installed — see
[CONTRIBUTING.md § Cite the literature when transcribing](CONTRIBUTING.md)
— then draft the Lean with the `lean4` skill's `autoformalize`
workflow (end-to-end formalization from the informal source) or
`formalize` (interactive drafting plus proving); see
[docs/rules/lean-coding.md](docs/rules/lean-coding.md) § Lean 4
skill workflows. Escalate formalizations or proofs that exceed
the in-editor tooling to Aristotle (below).

It is a metered hosted service,
so the agent asks the contributor whether to use it before
invoking it, even when it is available. Its output is
LLM-generated code, governed by the
same policy as any other AI tool
([CONTRIBUTING.md § Submission policy](CONTRIBUTING.md)): it may
enter any subtree, upstream-eligible included, provided the user
understands every line, can justify each decision to reviewers
without AI, and discloses its use. Returned proofs are re-verified
under the repository's toolchain and constructive discipline
before use. See [docs/aristotle.md](docs/aristotle.md) for
invocations and operational notes.

## Skills and MCP servers

Nothing in this repository assumes a skill or MCP server is
installed. Every mention of one, in this file and in the files it
references, reads: if it is installed, consider using it in the
situations named and in any others where it applies. Where one is
not installed, work with the tooling that is, and do not report
its absence to the user. The one exception is the `lean4` skill:
it is the one skill known to target Lean, the project's primary
language, so an agent that finds it absent says so once, as a
suggestion, and then proceeds.

The invocation form is host-dependent. Select by activity.

- Lean code work and mathlib search: the `lean4` skill's workflows
  ([docs/rules/lean-coding.md](docs/rules/lean-coding.md) § Lean 4
  skill workflows), the `lean-lsp` MCP's search and proof tools
  (§ `lean-lsp` MCP search and proof tools), and the `serena` MCP
  for symbol-level navigation and editing.
- Literature search and citation: the `theoremsearch` MCP
  (`theorem_search`), the `arxiv-mcp-server` MCP (`search_papers`,
  `read_paper`), and the `deep-research` skill for multi-source
  cited surveys. See § Verify agent claims.
- Brainstorming, writing a plan, executing a plan: the
  `brainstorming`, `writing-plans` and `executing-plans` (or
  `subagent-driven-development`) skills. The `sequential-thinking`
  MCP complements them where a task benefits from explicit
  multi-step reasoning: hypothesis generation and verification,
  branching exploration, or revision of earlier steps.
- Independent tasks, bugs, and new features: the
  `dispatching-parallel-agents`, `systematic-debugging` and
  `test-driven-development` skills.
- Pre-commit: the `verification-before-completion` skill. Code
  review: the `pr-review-toolkit` skill. Receiving review: the
  `receiving-code-review` skill.

Skills that write spec and plan files under `docs/superpowers/`
leave them in the working tree. Those files are spec and plan
documents like any other: the lifespan rules in
[CONTRIBUTING.md](CONTRIBUTING.md) § Concern shape apply, so remove
them in the final commits of the topic branch.

## Path-scoped rules

### When editing .lean files

Lean style, naming, docstring, and module-system rules bind
every .lean file in this repository.
See [docs/rules/lean-coding.md](docs/rules/lean-coding.md) for
the full text.

### When editing files under Geb/Mathlib/, Geb/Cslib/ or GebLang/

Additional upstream-eligibility rules apply (import rules,
authoring, subtree boundaries).
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
- [docs/aristotle.md](docs/aristotle.md) — Aristotle CLI usage
  and contribution-policy constraints.
- [CLAUDE.md](CLAUDE.md) — Claude-specific additions on top of
  this file.
