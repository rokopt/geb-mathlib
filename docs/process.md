# Development process — rationale

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Sections](#sections)
- [Repository structure](#repository-structure)
- [Code is cost](#code-is-cost)
- [Document only the persistent](#document-only-the-persistent)
- [Specs and plans are transient](#specs-and-plans-are-transient)
- [Illustrate only with the archetypal](#illustrate-only-with-the-archetypal)
- [Avoid colloquialisms and metaphors](#avoid-colloquialisms-and-metaphors)
- [Documentation under `docs/`](#documentation-under-docs)
- [Adversarial review](#adversarial-review)
- [Verify agent claims](#verify-agent-claims)
- [Two-track development](#two-track-development)
- [Floodgate test](#floodgate-test)
- [Alternative formalization targets](#alternative-formalization-targets)
- [main and integration](#main-and-integration)
- [Mathlib bump procedure](#mathlib-bump-procedure)
- [jj bump procedure](#jj-bump-procedure)
- [Markdownlint discipline](#markdownlint-discipline)
- [Use of AI in upstream-eligible code](#use-of-ai-in-upstream-eligible-code)
- [No LLM-drafted user-facing text](#no-llm-drafted-user-facing-text)
- [Generic user references](#generic-user-references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document records *why* each rule in `CONTRIBUTING.md`,
`AGENTS.md`, `CLAUDE.md`, `docs/rules/*.md`, and
`.claude/rules/*.md` exists. The rules themselves live in
those files; this document explains the motivation behind each.
Read it when you need to understand the reason for a rule,
propose a change, or weigh how to apply a rule in an
unfamiliar situation.

## Sections

- [Development process — rationale](#development-process--rationale)
  - [Sections](#sections)
  - [Repository structure](#repository-structure)
  - [Code is cost](#code-is-cost)
  - [Document only the persistent](#document-only-the-persistent)
  - [Specs and plans are transient](#specs-and-plans-are-transient)
  - [Illustrate only with the archetypal](#illustrate-only-with-the-archetypal)
  - [Avoid colloquialisms and metaphors](#avoid-colloquialisms-and-metaphors)
  - [Documentation under `docs/`](#documentation-under-docs)
  - [Adversarial review](#adversarial-review)
  - [Verify agent claims](#verify-agent-claims)
  - [Two-track development](#two-track-development)
  - [Floodgate test](#floodgate-test)
  - [Alternative formalization targets](#alternative-formalization-targets)
  - [main and integration](#main-and-integration)
  - [Mathlib bump procedure](#mathlib-bump-procedure)
  - [jj bump procedure](#jj-bump-procedure)
  - [Markdownlint discipline](#markdownlint-discipline)
  - [Use of AI in upstream-eligible code](#use-of-ai-in-upstream-eligible-code)
  - [No LLM-drafted user-facing text](#no-llm-drafted-user-facing-text)
  - [Generic user references](#generic-user-references)

## Repository structure

The repo is laid out narrow-and-deep: every directory has either a
small number of subdirectories or a small number of source modules,
with one indexing `.lean` file per directory. The path is itself
documentation. This policy resembles mathlib's.

## Code is cost

Every committed byte must be justified by a return greater than
its cost. Cost has several components:

- **Reader time and cognitive capacity.** Anyone reading the
  codebase — human or AI — pays attention to every file, every
  line, every comment.
- **Drift and obsolescence.** Code falls out of sync with the
  rest of the codebase as surrounding things change. Comments
  are particularly susceptible, being unverified by compilation.
- **Dependence pressure.** Code that depends on something else
  freezes that thing in place: changing the dependency requires
  changing the dependent. The more code depends on a given thing,
  the harder that thing is to change.
- **Process overhead.** Every line lengthens build time, commit
  diffs, code-review time, search results, and AI-context
  consumption.

## Document only the persistent

A direct corollary of "Code is cost". Comments and committed text
should describe what is enduring about the code as it is — its
purpose, contracts, and non-obvious external constraints.
They should not describe transient process artifacts such as:

- **History.** "Previously this used X; now it uses Y."
  "Refactored from a different shape." How the code arrived at
  its current form belongs in commit messages, not in the code.
- **Testing process.** "Verified by testing." "This caused a
  build failure that was fixed by...." How something was
  discovered belongs in the project-internal findings log,
  not in the code.
- **Project-management artifacts.** "Required by spec § X.Y."
  Tasks and plan numbers are ephemeral — they exist during a
  discrete project phase and lose meaning afterward; readers of
  the code should not need to consult an external document just
  to understand the comments.
- **In-progress notes.** "TODO: rewrite this when we have time."
  "Try this approach if X fails." Active work belongs in
  `TODO.md` or the workstream's spec/plan, not in code comments.

What's persistent and worth documenting:

- The code's purpose at the namespace / module / declaration
  level (its contract).
- Non-obvious external constraints.
- Cross-references to specific external documentation (mathlib's
  contribute pages, jj's documentation), where the cross-reference
  saves a reader from re-deriving the constraint.

The principle is: when this codebase is years old, the comments
should still read as useful context. Anything that won't survive
that test belongs elsewhere.

## Specs and plans are transient

The file-level corollary of "Document only the persistent". A spec
is a worked-out route to a target state; a plan is the task
sequence that reaches it. Once the change is complete, everything
persistent has moved into the live code, its `docs/` entries, and
any `TODO.md` notes on follow-on work; the spec and plan retain
only the record of how that state was reached. They are therefore
removed in the final commits of the topic branch (`CONTRIBUTING.md`
§ Concern shape gives the branch ordering), leaving no spec or plan
file on an active branch.

Two costs motivate the removal. A spec or plan left in the working
tree presents superseded intentions as if current — later work may
have changed direction without rewriting the original plan. And it
forces every reader to reconcile the plan against the code, an
obligation that grows as the code evolves away from it. The git
history preserves the spec and plan in full for anyone tracing how
a decision was reached; the active branch carries only what the
code currently is.

## Illustrate only with the archetypal

A corollary of "Document only the persistent". When a rule or
explanation needs an illustration, the example should be
archetypal — a timeless mathematical or physical concept that
cannot become obsolete. Incidental examples (a particular task,
test artifact, or transient project state) consume reader
attention with trivialities and rot as the codebase evolves; an
archetypal example continues to teach the rule years later.

## Avoid colloquialisms and metaphors

Only standard technical terms are precise and universal enough
for our purposes. The rule binds all committed text; the rule
statement lives in `CONTRIBUTING.md` § Rules § Style and
references.  Examples (where not specific technical terms)
include "land", "gap", and "gate".

## Documentation under `docs/`

`docs/index.md` is the project's reader-facing description: the
directory layout and a topological narrative of the implemented
content. Each entry covers the source-tree paths it touches, the
central concepts it introduces, and its dependencies (other
entries here, or specific external modules). Documentation is
updated in concert with any code change that introduces new
content appropriate to document, such as the formalisation of a
new mathematical concept.

`docs/process.md` (this file) contains the rationale for each
rule that binds development; `docs/references.md` catalogues
external library and mathematical references organised by topic.
Both are reader-facing alongside `docs/index.md`.

## Adversarial review

Specs and plans go through fresh-context adversarial review until
convergence (no blockers, no serious findings). The reviewer is a
NEW general-purpose `Agent` invocation per round (not
`SendMessage` to a continuing agent), reading only the artifact at
the given path. Findings are categorised blocker / serious / minor
/ cosmetic-taste; the author responds in writing to every finding
(fix / defer with rationale / reject as cosmetic-taste). The
discipline catches bugs the author cannot see; the fresh context
ensures the reviewer is not subject to the author's blind spots.

## Verify agent claims

Any factual claim about an external system (mathlib, Lean,
third-party tools, jj, GitHub conventions, library APIs) is
provisional until verified against authoritative sources.
Committed artifacts include the citation alongside the claim.
Adversarial reviewers explicitly check for unverified claims. AI-agent memory
is unreliable for facts about external systems; verification at
use time keeps committed content trustworthy.

## Two-track development

`Geb/Internal/` holds code that is not (yet) upstream-eligible:
work in progress, explorations that build on upstream-quality
code without themselves meeting that bar, and code too
specialized to this project for mathlib or CSLib. Code is ported
into `Geb/Mathlib/` or `Geb/Cslib/` when it reaches upstream
quality, with dependents migrated via `jj rebase` after the
upstream PR is accepted. The split lets velocity and upstream-
readiness each get the discipline that suits them, without one
blocking the other. It is driven by quality, scope, and
dependency-readiness, not by authorship: AI-drafted and
human-written code follow the same rules in every subtree (see
`docs/rules/upstream-eligible.md` § Two-track development).

## Floodgate test

At all times, the repo is ready to ship dependency-ordered PRs on
short notice with no source-code changes.
`scripts/lint-imports.sh` enforces the import-direction and
no-prefix-leakage rules. The test is what makes
"upstream-eligible" a binding property of `Geb/Mathlib/` and
`Geb/Cslib/` rather than an aspiration: at any moment, every
file in either subtree can be extracted to a PR upstream.

## Alternative formalization targets

mathlib and CSLib apply a scope-and-significance bar enforced by
human review, and require that any LLM-generated code be
understood line-by-line by a contributor who can justify each
decision to reviewers without AI. When a sound, `sorry`-free
result is not a practical fit for either — because it falls
outside their scope, because no contributor is prepared to take
that line-by-line ownership for upstream submission, or because
an upstream PR is blocked or slow — two repositories admit it on
looser terms (catalogued in `docs/references.md` § Alternative
formalization targets):

- lean-pool, for results meeting mathlib's rigor and linting but
  not its scope.
- merely-true, for results below lean-pool's quality gate that
  still build `sorry`-free and `axiom`-free.

Both relax the human-review bar that mathlib and CSLib enforce
(lean-pool substitutes automated linting plus LLM evaluation;
merely-true merges on CI pass without human review); neither
requires changes to source layout, the floodgate test, or the
build, so submitting to them is a copy-out of an already-sound
file, not a restructuring. Code produced here already satisfies
this project's stricter discipline (constructive, no
`noncomputable`, minimised `Classical`), which exceeds both
targets' requirements; that discipline is not relaxed to match a
looser target. These remain fallbacks: mathlib and CSLib are the
primary targets, and the two-track workflow
(§ Two-track development) is unchanged.

## main and integration

`main` is append-only stable history; never force-pushed. Topic
branches are merged without force-pushing.
`integration` is the regenerated fan-in merge view of `main` plus
active topic branches; force-pushed (lease-protected by default)
as topic-branch tips move. The split keeps `main` fork-friendly
(clones never see force-pushed history) while giving us a single
working view of all in-flight work.

## Mathlib bump procedure

`update.yml` (daily cron plus manual dispatch) self-detects the
newest mathlib release tag against the project's pin via
`scripts/mathlib-bump-detect.sh`, which reuses
`mathlib-update-action`'s tag-selection (`git ls-remote --tags` +
npm `semver`) but baselines against the `lakefile.toml` pin. It
emits a target only when the tag is newer, exists on `cslib` and
`doc-gen4` (the version-locked dependencies bump in lockstep), and
no bump is in flight. The apply job sets all three `rev` fields to
the target and runs `leanprover-community/lean-update`, which does
an in-tree `lake update`, builds via `leanprover/lean-action`, and
opens a pull request on success or an issue on failure; nothing
merges automatically. The bump pull request is created with
`GITHUB_TOKEN`, whose events do not trigger workflow runs, so the
apply job dispatches `ci.yml` on the bump branch
(`workflow_dispatch`, which is exempt from that suppression). The
dispatched run records its result on the bump commit and the
Actions tab — not in the pull request's merge-box checks (a
`workflow_dispatch` suite is not associated with the pull request),
so the reviewer checks the commit's checks (via the pull request's
Commits list) or the Actions run before merging. A
contributor reviews the diff line-by-line
and merges. After merge to `main`, the contributor mass-rebases
active topic branches with `scripts/rebase-topics.sh main` and
regenerates `integration` with `scripts/regenerate-integration.sh`.
The detector tracks release tags, not `master`.

## jj bump procedure

`jj-bump.yml` (weekly cron `0 17 * * 1` plus manual dispatch)
parallels the mathlib bump pipeline for the jj binary pin. A
read-only detect job runs `scripts/jj-bump-detect.sh`; the apply
job runs only when detect emits a nonempty `target`.

Detection reads the bare pinned version from `scripts/jj-version`
and queries `GET /releases/latest` (which excludes drafts and
prereleases server-side). The semver comparison reuses the shared
`scripts/lib/select-newest-tag.cjs` helper as a guard against the
endpoint surfacing an older release (e.g. after a yanked release).
The release must carry `jj-v<version>-x86_64-unknown-linux-musl.tar.gz`
— the asset `scripts/install-jj.sh` downloads — before a target is
emitted; a tag whose binaries are still uploading waits for the
next run. The in-flight guard checks for an open PR on
`auto-update-jj/patch` or an open issue labelled `jj-bump-fail`;
either suppresses a new bump. Fail-loudly: any `gh` or network
failure exits 1, so outages never read as "already current".

The apply job writes the pin, installs the bumped binary via
`scripts/install-jj.sh`, and runs
`scripts/tests/test-regenerate-integration.sh` under that binary
before opening the pull request. A would-be red-CI PR is instead
converted into a labelled-issue failure artifact. These pre-PR
checks do not exercise the fetch/push surfaces of
`scripts/regenerate-integration.sh`; a jj CLI change there surfaces
in the first regeneration run after merge, covered by contributor
review of the upstream release notes on the bump PR.

The pull request is opened via the SHA-pinned
`peter-evans/create-pull-request` (dependabot maintains the pin).
Because `GITHUB_TOKEN`-created PRs do not trigger `pull_request`
workflows, the apply job dispatches `ci.yml` on the bump branch via
`gh workflow run ci.yml --ref auto-update-jj/patch`.

Any apply-step failure opens an issue labelled `jj-bump-fail`
naming the target version and per-step outcomes. A failure issue
can coexist with a successfully opened PR (e.g. only the CI
dispatch failed). The open issue suppresses scheduled bumps until
closed; closing the bump PR without merging does not suppress
re-opening — the labelled issue is the suppression mechanism.
The `jj-bump-fail` label is a one-time repository side effect.

The weekly cadence matches the dependabot interval for other
CI-tooling pins; jj releases roughly monthly, so the schedule
detects a new release within a week of publication.

A contributor reviews the bump PR diff and merges. After merge
to `main`, the contributor mass-rebases active topic branches and
regenerates `integration` as in the mathlib bump procedure.

## Markdownlint discipline

Every Markdown document passes `markdownlint-cli2` against
`.markdownlint-cli2.jsonc` (shared with VSCode extension).
`.remember/` is intentionally not excluded; non-compliant remember
output is edited locally. The discipline keeps documentation
uniformly readable; sharing the config with VSCode means the
editor catches violations as we type.

## Use of AI in upstream-eligible code

mathlib and CSLib permit LLM-generated code under mandatory
disclosure and line-by-line human understanding; there is no
first-PR or new-contributor exception and no requirement to
rewrite AI-drafted code that already meets the bar. The binding
rule and its source links live in `CONTRIBUTING.md`
§ Submission policy; the agent-facing form is `AGENTS.md`
§ AI authoring (upstream-eligible work).

This policy is set upstream and has changed before: mathlib
briefly prohibited new-contributor LLM code (PR #827,
2026-04-20), removed that prohibition (PR #840, 2026-05-09), and
reworded the section (PR #850, 2026-05-27). The linked source
pages are the authority; re-check them periodically (the
adversarial-review re-fetch in `AGENTS.md` § Adversarial review
is one such checkpoint), and when they change, update
`CONTRIBUTING.md`, `AGENTS.md`, and this file together.

## No LLM-drafted user-facing text

PR descriptions, Zulip messages, GitHub issue/PR comments are
user-authored. Mathlib's policy is unconditional ("use your own
words"). Multi-layered enforcement: hard rule in
`CONTRIBUTING.md` § Rules § Submission policy,
pre-push reminder in `scripts/pre-push.sh`, PR template checkbox,
user-review-before-push gate. The redundancy is intentional.

## Generic user references

"the user" / "they" / "them" generically in committed text. No
first names, email, or autobiographical detail. Committed content
should make sense to any contributor; specific identities make it
read as a single author's project.

The rule exists so that no contributor is singled out and the
project does not read as one author's. A designated project point
of contact is different: naming the maintainer for Code-of-Conduct
or security reporting identifies a project role, not a
contribution. A specific name and email are therefore appropriate
for such a contact.
