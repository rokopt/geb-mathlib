# AGENTS.md

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Audience](#audience)
- [Agent-specific rules](#agent-specific-rules)
  - [Version control follows the checkout](#version-control-follows-the-checkout)
  - [Session-start checks](#session-start-checks)
  - [No push without user line-by-line review](#no-push-without-user-line-by-line-review)
  - [Verify agent claims](#verify-agent-claims)
  - [No LLM-drafted text in mathlib-facing channels (enforcement)](#no-llm-drafted-text-in-mathlib-facing-channels-enforcement)
  - [AI authoring (upstream-eligible work)](#ai-authoring-upstream-eligible-work)
  - [Aristotle (external LLM prover)](#aristotle-external-llm-prover)
- [Modes of operation](#modes-of-operation)
  - [Prototyping](#prototyping)
  - [Code review](#code-review)
  - [Pair programming](#pair-programming)
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

### Version control follows the checkout

With its git backend, `jj` leaves no metadata that distinguishes
its commits from git's, so the repository does not mandate either.
An agent uses whichever the checkout it is working in was created
with. The test: `jj` is in use when `jj root` succeeds and names
the directory `git rev-parse --show-toplevel` names, or git names
none; otherwise `git` is in use. The two agree at the root of a
colocated repository, and a workspace added with `jj workspace add`
carries its own `.jj/` and no `.git`; a git worktree of a colocated
repository carries `.git` and no `.jj/`, so `jj root` fails there
or, for a worktree nested inside the repository, names the parent
instead. Where `jj` is in use, every state-mutating operation goes
through it, since a colocated checkout's git index is an export of
jj's state that a raw mutating `git` command desynchronises.
`scripts/hooks/block-mutating-git.sh` is a Claude Code hook a
contributor may install locally to enforce that (see its header);
the repository does not install it.

### Session-start checks

Before a task that builds, run `scripts/toolchain-watch.sh`, which
reports whether the toolchain pin matches mathlib's; a mismatch is
a bump branch's concern rather than the task's. Before a task that
may commit, check whether commit signing is configured and, if so,
whether its key is cached (`scripts/hooks/check-signing-key.sh`
shows the checks for gpg and ssh), and tell the user when it is
not, since a commit would then block on a passphrase prompt. Under
Claude Code, `.claude/settings.json` runs both at session start.

### No push without user line-by-line review

Neither `git push` nor `jj git push`. This includes first-creation
pushes, force-pushes, branch-deletes, tag-pushes.

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
published paper, or when a goal resists the `lean4` skill's `prove`
and `autoprove` workflows.

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

It is a metered, rate-limited hosted service whose calls add
latency, so before embarking on a project the agent asks the user
whether to use it in that project, even when it is available, and
does not invoke it otherwise. Its output is
LLM-generated code, governed by the
same policy as any other AI tool
([CONTRIBUTING.md § Submission policy](CONTRIBUTING.md)): it may
enter any subtree, upstream-eligible included, provided the user
understands every line, can justify each decision to reviewers
without AI, and discloses its use. Returned proofs are re-verified
under the repository's toolchain and constructive discipline
before use. See [docs/aristotle.md](docs/aristotle.md) for
invocations and operational notes.

## Modes of operation

The user directs an agent in one of the modes below, or in any
other mode the user describes. No mode begins with a written
specification or plan: a mathematical development is settled by
writing and compiling Lean, so planning what code to write is done
in the session, with a `brainstorming` skill and the
`sequential-thinking` MCP where installed (§ Skills and MCP
servers). See [docs/process.md](docs/process.md) § Modes of
operation for the rationale.

### Prototyping

The agent resolves a programming or mathematical question by
writing and compiling Lean under `Geb/Prototypes/`, continuing
through an extended development until it has a proven-correct
implementation of the concept in question. The code is committed
whatever its fate: it may be discarded later, or polished and
ported to another subtree
([docs/rules/upstream-eligible.md](docs/rules/upstream-eligible.md)
§ Two-track development), and either way it is versioned for
future reference. Experimental Lean of any kind, in any mode, is
written inside the codebase rather than under a temporary
directory, so that it compiles against the project's build and can
be versioned.

The agent stops short of that only on coming to suspect that the
concept cannot be implemented, or not practically: it may be
ill-specified or contradictory, or require infrastructure that
neither mathlib, Cslib nor this repository has, such as the
formalization of a large mathematical theory. It then explains to
the user why it suspects so, leaves the code in place for the user
to examine, and lets the user decide how to proceed.

### Code review

The agent examines changes the user has made, one or more
changesets, and proposes changes from many angles, which may be
apportioned among subagents (the `pr-review-toolkit` skill's
agents where installed), each a fresh context that inherits no
other reviewer's conclusions. Mathematical and implementation
correctness come first; every other property the coding rules
demand is also checked: mathlib, CSLib and local style compliance
([docs/rules/lean-coding.md](docs/rules/lean-coding.md), including
its reviewer instructions), higher-order constructions over
piece-by-piece ones, refactoring of duplication, the constructive
discipline, and the rest. A finding states what kind of problem it
is rather than a severity grade: that a proof or definition is
mathematically incorrect says everything a grade would; and where
a concept has more than one standard name, the finding says so
and says which name the reviewer judges to have the better
connotations in that context, which makes it a matter of taste
without a label. The user decides on each finding.

### Pair programming

The agent and the user alternate in a live session. As the user
requests, the agent reviews a short chunk of the user's code and
then waits for the next, or writes a short chunk the user asks for
and proposes it for the user's review. The user is attending, so
the agent writes a small amount of code per turn, in contrast to
prototyping, where it may work unattended for a long time.

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

The invocation form is host-dependent, and a skill's command set
changes between versions, so before using a skill, list the
commands it currently provides and select from that list; the
names below are indicative. Select by activity.

- Lean code work, proving, and mathlib search: the `lean4` skill's
  workflows ([docs/rules/lean-coding.md](docs/rules/lean-coding.md)
  § Lean 4 skill workflows) and the `lean-lsp` MCP's search and
  proof tools (§ `lean-lsp` MCP search and proof tools).
- A finite combinatorial question — whether a bounded instance has
  a satisfying assignment, a counterexample, or an optimum — before
  attempting a Lean proof of it or after the `lean4` skill's
  `disprove` finds no refutation: the `MCP Solver` MCP
  (`MCP_Solver`), which states the question as a constraint model
  and solves it.
- A fact about the project or the user's preferences that should
  survive the session: the `memory` MCP, a knowledge graph read at
  the start of a session and written when the user asks that
  something be remembered.
- A defect or missing workflow in the `lean4` skill, or an insight
  its maintainers would want: the `lean4-contribute` skill drafts
  a GitHub issue for the `lean4-skills` repository. On producing
  the draft, the agent reminds the user that the text is a summary
  for the user, and recommends that they rewrite it in their own
  words before filing, so that it complies with mathlib's
  own-words standard (§ No LLM-drafted text in mathlib-facing
  channels) whichever channel it reaches.
- Reviewing changes: the `pr-review-toolkit` skill, whose agents
  each review from one angle.
- Writing or reviewing any code: the `ponytail` skill, which holds
  to the minimal solution that works, the discipline
  [CONTRIBUTING.md](CONTRIBUTING.md) § Code is cost states.
- Literature search and citation: the `theoremsearch` MCP
  (`theorem_search`) and the `arxiv-mcp-server` MCP
  (`search_papers`, `read_paper`). See § Verify agent claims.
- Planning what code to write: a `brainstorming` skill, and the
  `sequential-thinking` MCP where a task benefits from explicit
  multi-step reasoning: hypothesis generation and verification,
  branching exploration, or revision of earlier steps.

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
