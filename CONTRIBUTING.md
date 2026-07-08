# Contributing to geb-mathlib

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Audience](#audience)
- [Project status](#project-status)
- [Setup](#setup)
- [Working](#working)
- [Rules](#rules)
  - [Concern shape](#concern-shape)
  - [Code is cost](#code-is-cost)
  - [Submission policy](#submission-policy)
  - [Style and references](#style-and-references)
  - [Constructive-only](#constructive-only)
  - [Floodgate test](#floodgate-test)
  - [Each phase produces an artifact](#each-phase-produces-an-artifact)
- [Repo structure](#repo-structure)
- [Tooling](#tooling)
- [References](#references)

<!-- END doctoc -->

## Audience

This file binds every contributor (human or AI). It is the
top-level contributor document; the rules in `docs/rules/`
also bind every contributor for the file globs documented
in each rule's `paths:` frontmatter. `AGENTS.md` and
`CLAUDE.md` add further rules for AI-assisted contribution
and for Claude Code specifically.

All participants are also expected to follow the project's
[Code of Conduct](CODE_OF_CONDUCT.md).

## Project status

Underway; initial language bootstrap.
Active development happens on topic branches; `main` is the
append-only public-facing trunk; `integration` is the regenerated
fan-in view of `main` plus active topic branches.

## Setup

Suggested steps to run after cloning the repository. The jj
configuration below is recommended local config; the project
does not run config commands on a contributor's behalf.

1. Install `jj` via your preferred package manager.
2. Initialise jj's colocated mode:
   `jj git init --colocate`.
3. Apply the recommended local jj configuration:

   ```bash
   jj config set --repo git.private-commits 'conflicts()'
   jj config set --repo remotes.origin.auto-track-bookmarks 'glob:*'
   jj config set --repo revsets.bookmark-advance-from 'heads(::@ & mutable())'
   jj config set --repo revsets.bookmark-advance-to '@'
   ```

   `git.private-commits = 'conflicts()'` makes `jj git push -b
   <name>` fail on a conflict commit (which would be rejected
   in a submitted PR).
4. Configure your per-developer `~/.config/jj/config.toml`
   `[signing]` block (`behavior = "own"`,
   `backend = "gpg"` or `"ssh"`, `key = "..."`) so commits are
   signed.
5. Install the Lean toolchain via `elan` (the toolchain version
   is read from `lean-toolchain`).
6. Run `lake exe cache get` then `lake build` to verify the
   build chain.
7. Install `doctoc` to enable pre-push TOC regeneration of
   committed Markdown:
   `npm install -g doctoc` (or your preferred install path).
   The pre-push checklist skips the TOC check when `doctoc` is
   missing rather than failing, so this step is recommended but
   not blocking.

## Working

1. Read this file from top to bottom; the rules here bind every
   contribution. If you use an AI agent, also read `AGENTS.md`;
   if you use Claude Code, also read `CLAUDE.md`.
2. Pick a workstream from `TODO.md` (or propose a new one and
   brainstorm a spec following the process described in
   `docs/process.md`).
3. Develop on a topic branch (`feat/<topic>`, `fix/<topic>`, etc.);
   use `jj` (the working VCS).
4. Run `scripts/pre-push.sh` and have a contributor (or yourself)
   review the diff line-by-line before pushing.

## Rules

### Concern shape

- **One concern per branch.** Refactoring is encouraged; when you
  find code worth refactoring outside the current branch's scope,
  create a separate branch for it rather than bundling it with
  unrelated work.

Each feature's spec, plan, and code co-evolve on the same topic
branch, but only the code and its persistent documentation are
permanent. Specs and plans are transient: they record how the
current state was reached, not what it is, so they belong in
history, not on an active branch. The branch is ordered
accordingly:

1. Commits adding the spec and plan (and their adversarial-review
   iterations).
2. Commits implementing the change, including its persistent
   documentation under `docs/` and any `TODO.md` notes on
   follow-on work.
3. Commits removing the spec and plan.

After merge to `main`, the spec and plan remain reachable in
history but are absent from the working tree, so no active branch
presents superseded decisions as current. See `docs/process.md`
§ Specs and plans are transient.

### Code is cost

- **Code is cost.** Every committed byte must be justified by a
  return greater than its overhead (reader time, AI context, build
  time, freezing surrounding code in place). Code that meets the
  bar is written in small, reusable chunks so its cost is paid
  once. See `docs/process.md` § Code is cost.
- **Reuse existing process code.** We do not invent build,
  version-control, or CI machinery: anything we need is assumed
  to already exist somewhere. Find code to reuse; if none exists,
  find a concept to reuse. See `docs/process.md` § Code is cost.
- **Reuse existing abstractions.** Before defining a new
  mathematical concept, check whether it already exists in
  mathlib, CSLib, or elsewhere in this repository. Instantiate
  the existing abstraction rather than defining a parallel
  concept. See `docs/process.md` § Code is cost.
- **Avoid the ad-hoc.** Geb is built entirely out of precise,
  universal mathematics. Any data structure should correspond to
  a known formal concept; innovation proceeds in single steps,
  each composed from two concepts already established (in formal
  mathematics or built in Geb by this discipline). See
  `docs/process.md` § Code is cost.
- **Document only the persistent.** Comments and committed text
  describe what is enduring about the code as it is — its purpose,
  its contracts, non-obvious external constraints. They do not
  describe transient process artifacts: how the code used to be,
  what testing iteration discovered an issue, which task in our
  plan produced a file, or similar. Specs and plans are themselves
  transient process artifacts in this sense (see § Concern shape).
  See `docs/process.md` § Document only the persistent.

### Submission policy

- **LLM-contribution policy** binds any work in `Geb/Mathlib/`
  or `Geb/Cslib/`. mathlib and CSLib permit LLM-generated code,
  with no per-contributor or first-PR exception, provided the
  contributor understands every line and can justify each design
  decision to reviewers without AI assistance. Disclosure of
  which tools were used and how is mandatory, and a pull request
  containing a substantial amount of LLM-generated code carries
  the `LLM-generated` label. We apply this bar to both subtrees.
  Source pages (re-check periodically; subject to upstream
  revision):
  [mathlib § Use of AI](https://leanprover-community.github.io/contribute/index.html#use-of-ai),
  [mathlib PR lifecycle (`LLM-generated` label)](https://leanprover-community.github.io/contribute/how-to-contribute.html#lifecycle-of-a-pr),
  [CSLib § The role of AI](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md#the-role-of-ai).
- **No LLM-drafted text in mathlib-facing channels.** PR
  descriptions, Zulip messages, GitHub issue/PR comments are
  user-authored ("use your own words"). This is unconditional in
  mathlib's policy and unchanged by the code policy above.
- **Cite the literature when transcribing.** Every definition or
  theorem taken from published mathematics carries a literature
  reference with a searchable identifier in its plan, spec, and
  Lean source. Each workstream's brainstorming-phase spec marks
  each definition as transcription or novel. (Comments, however,
  do not. Comments only cite literary context, either stating
  what is being transcribed, or known context for what is being
  defined if it is not itself a transcription.) In `.lean` files,
  citations live in the module docstring's `## References`
  section or inside the declaration's `/-- ... -/` docstring. The
  bibliographic detail for each cited work lives once in
  `docs/references.bib`, keyed by a citation key; docstrings refer
  to a work by that key in `[Key]` form (mathlib's convention), so
  a work cited from several modules is described in one place.
  `docs/references.md` is the complementary catalogue of library
  and URL pointers, not citable literature.

### Style and references

- **Generic user references in committed text.** "the user" /
  "they" / "them"; no first names, email, or autobiographical
  detail. The exception is a designated project point of contact
  (e.g. the maintainer named for Code-of-Conduct or security
  reporting): a specific name and email are appropriate there,
  since they identify a project role rather than a contributor.

Formal, precise, mathematical, dry, unopinionated.
Cite known mathematics where applicable; reference standard
notation. No emojis. No all-caps words unless they are acronyms.
Be wary of value-laden adjectives ("key" / "important" / "core"
/ "elegant" etc.), state-judgment words ("blocked" / "issue" /
"challenge" etc.), and conversational fillers ("yes" / "wait" /
"hmm" / "careful" / "actually"). Avoid markup for emphasis;
save it for delineation (e.g. of book names, links, and words
being defined).  See also `docs/rules/markdown-writing.md`.

**Avoid colloquialisms and metaphors.** Only standard technical
terms are precise and universal enough for our purposes.
See `docs/process.md` § Avoid colloquialisms and metaphors.

### Constructive-only

- **No `noncomputable` anywhere; minimise `Classical`.** See
  `docs/rules/lean-coding.md` § Constructive-only Lean code.

Lean placeholder syntax: see
[docs/rules/lean-coding.md § sorry, admit, and underscores](docs/rules/lean-coding.md).

### Floodgate test

At all times, the repo is ready to ship dependency-ordered PRs on
short notice with no source-code changes. `scripts/lint-imports.sh`
enforces this by rejecting forbidden imports in `Geb/Mathlib/`
and `Geb/Cslib/` files, and the `Geb.Mathlib.` / `Geb.Cslib.`
prefixes outside import lines in their respective subtrees.

### Each phase produces an artifact

Every phase of a workstream leaves a durable artifact: brainstorming
produces a spec, planning produces a plan, and implementation
produces the code and its `docs/` entries. The spec and plan are
transient (see § Concern shape); the code and its documentation
persist. A phase is not complete until its artifact exists.

## Repo structure

`Geb/Mathlib/*` and `Geb/Cslib/*` upstream-eligible |
`Geb/Internal/*` downstream-only. Narrow-and-deep dirs with one
indexing file per directory. `main` = append-only stable;
`integration` = regenerated fan-in view; topic branches per
PR-candidate.

## Tooling

- VCS: `jj` v0.41+ in colocated mode; lease-protected pushes.
- Build: `lake` (the mathlib `rev` pin is bumped by the
  `update.yml` cron).
- CI: GitHub Actions via `leanprover/lean-action@v1`; mathlib bumps
  run `scripts/mathlib-bump-detect.sh` (reusing
  `mathlib-update-action`'s tag-selection algorithm) plus
  `leanprover-community/lean-update`.
  (`upstreaming-dashboard-action` deferred until `Geb/Mathlib/`
  has substantive content for it to dashboard.)
- Linters: `markdownlint-cli2`, `scripts/lint-imports.sh`,
  `lake lint` (drives `batteries/runLinter`).

## References

- [docs/rules/](docs/rules/) — path-scoped rule files binding
  every contributor for the file globs in each rule's `paths:`
  frontmatter.
- [docs/process.md](docs/process.md) — rationale for every rule.
- [docs/references.md](docs/references.md) — Lean library and
  mathematical reference catalog.
- [docs/index.md](docs/index.md) — implemented mathematical
  content in topological order.
- [AGENTS.md](AGENTS.md), [CLAUDE.md](CLAUDE.md) — additional
  rules for AI-assisted contribution.
