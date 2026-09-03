# Development process — rationale

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Repository structure](#repository-structure)
- [Code is cost](#code-is-cost)
- [Document only the persistent](#document-only-the-persistent)
- [Modes of operation](#modes-of-operation)
- [Literate Lean by default](#literate-lean-by-default)
- [Illustrate only with the archetypal](#illustrate-only-with-the-archetypal)
- [Constructive-only discipline](#constructive-only-discipline)
- [Avoid colloquialisms and metaphors](#avoid-colloquialisms-and-metaphors)
- [Documentation under `docs/`](#documentation-under-docs)
- [Verify agent claims](#verify-agent-claims)
- [Two-track development](#two-track-development)
- [Floodgate test](#floodgate-test)
- [Alternative formalization targets](#alternative-formalization-targets)
- [Version control follows the checkout](#version-control-follows-the-checkout)
- [main and integration](#main-and-integration)
- [Mathlib bump procedure](#mathlib-bump-procedure)
- [jj bump procedure](#jj-bump-procedure)
- [LKG/FKB pipeline](#lkgfkb-pipeline)
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
  `TODO.md`, not in code comments.
- **Counts of occurrences.** "Of the module's 54 theorems, 13
  depend on no axioms." "209 anonymous `example`s remain."
  A count over a population the project keeps adding to is
  transient by construction: every branch that adds one member
  falsifies it, and no reader acts differently at 54 than at 55.
  Name the members, or state the property the population has.

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

## Modes of operation

`AGENTS.md` § Modes of operation names prototyping, code review and
pair programming, and no mode begins with a written specification
or plan. A mathematical development is not foreseeable in prose:
the questions a construction raises are settled by writing and
compiling Lean, so a specification detailed enough to follow is
the implementation restated in a form that does not type-check,
and the remainder of such a document restates the process rules
that bind every workstream, which `CONTRIBUTING.md`, `AGENTS.md`
and `docs/rules/` state once. Prototyping puts the exploration
where it is checked, under `Geb/Prototypes/`, and the versioned
prototype is the record of how a question was settled.

The prototyping mode's stopping rule, and its instruction to leave
the code in place, exist because the judgement that a concept is
ill-specified, contradictory or out of practical reach is the
user's to make, and the agent's evidence for it is the code that
reached the difficulty.

Code review apportions angles among fresh-context reviewers because
a reviewer that inherits another's conclusions inherits its blind
spots; the discipline catches what the author cannot see. A finding
states its kind rather than a grade on a scale because a scale's
distinctions are too vague to act on, whereas the kind of problem
determines the action: an incorrect proof is repaired, a choice
between standard names is the author's to make.

Pair programming bounds the size of each turn because the user is
attending: a long unattended development is reviewed all at once,
which is the prototyping mode's shape, not this one's.

## Literate Lean by default

Every new module of `Geb/` and `GebLang/` is written so that Verso's
literate pipeline renders it as a manual page, and a chapter of the
manual under `manual/` includes such a module by name
(`docs/rules/lean-coding.md` § Literate modules). The rule separates
readiness from linking. A module is renderable from the moment it is
written, and the rendering is checked whenever the literate site is
built, which CI does for every pull request; whether a chapter
includes it is decided by the manual's narrative, so a prototype
kept for reference need never appear in the manual, and a settled
development is linked without being rewritten. One source serves the
library, the API reference and the manual, so exposition and code
cannot drift apart, and a reference in prose to a constant is
checked at elaboration as the code is. Citations follow the same
principle: `docs/references.bib` is the one record of the
bibliographic detail, a literate module's `{cite}` role resolves a
key in it at elaboration, and the manual's citable entries are
generated from it rather than transcribed.

The checked markup is enabled per module rather than per library
because a library-wide option would reach every module written
before the rule, whose Markdown docstrings are not converted.
`GebLang` is the exception, taking the option from `lakefile.toml`:
its umbrella imports its modules directly, where mathlib's header
linter rejects any command before the module docstring. Verso
renders a Markdown docstring as well, but the path by which the
manual includes such a module loses a paragraph's line breaks and
nests sibling headings, so the checked markup is what makes a module
manual-ready rather than only site-ready.

mathlib's linters reach every module through Lake's `moreLeanArgs`
rather than its `leanOptions` because Verso's literate facet forwards
a module's `leanOptions` to an executable that rejects an option it
does not register; the arrangement keeps every module of every
library renderable without a per-module command. The manual is
linted for axioms like any library, and every chapter module is
listed in `GebMeta.classicalAllowedModules`, because a Verso document
object depends on `Classical.choice` through Verso's own definitions;
the list names exact modules, so a literate module kept under
`manual/` stays held to the strict set.

## Illustrate only with the archetypal

A corollary of "Document only the persistent". When a rule or
explanation needs an illustration, the example should be
archetypal — a timeless mathematical or physical concept that
cannot become obsolete. Incidental examples (a particular task,
test artifact, or transient project state) consume reader
attention with trivialities and rot as the codebase evolves; an
archetypal example continues to teach the rule years later.

## Constructive-only discipline

The rules in `docs/rules/lean-coding.md` § Constructive-only Lean code
exist because axiom cleanliness is not a property of a name. `#print
axioms` on a polymorphic constant reports that constant, not any
instantiation of it, so a constant whose hypothesis is a class can measure
clean while every use of it at a concrete type collects `Classical.choice`.
Instance search compounds this: which instance is selected depends on the
import closure, so the same measurement taken in a narrow closure and in
the consuming one can disagree.

That is why the rules are stated as obligations on the author rather than
as facts about named declarations. Naming the term, pinning the instance
and splitting modules by what can be stated choice-free all remove the
dependence on what search selects. The module split also bounds the
allowlist. The boundary is drawn at what can be stated, not at how much a
module contains: a module reaches `GebMeta.classicalAllowedModules` when it
has no choice-free content of its own left to state, either because its
content is packaging or because its subject is the correspondence
between a concept developed here and a concept of an external Lean
library — Batteries, mathlib, CSLib — that is itself
`Classical`-dependent. A module with choice-free content of its own
is held to the strict set, so the constructive core cannot widen by
accident. The remaining admissions follow from that reading rather than
extending it: a test parallel inherits the dependence of the module it
exercises, the linter's own fixture exists to establish that the allowlist
has effect at all, and a wrapper may carry content that cannot be stated
choice-free — a bridge through a `Classical`-dependent mathlib construct,
say. Where a rule rests on a measurement, a lemma's axioms follow its
proof, so it is re-taken on a toolchain bump.

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
Both are reader-facing alongside `docs/index.md`. The manual under
`manual/` presents the implemented content itself, chapter by
chapter, including the literate modules it discusses
(§ Literate Lean by default).

## Verify agent claims

Any factual claim about an external system (mathlib, Lean,
third-party tools, jj, GitHub conventions, library APIs) is
provisional until verified against authoritative sources.
Committed artifacts include the citation alongside the claim.
Reviewers explicitly check for unverified claims. AI-agent memory
is unreliable for facts about external systems; verification at
use time keeps committed content trustworthy.

## Two-track development

`Geb/Prototypes/` holds prototypes: code that works out a
construction the language is to have, established far enough to
show how the construction goes, while the expression written so
far is not yet settled as the one to keep. The directory is named
for that state rather than for its consequence: a prototype is
not upstream-eligible because its form is still open, and it
stops being a prototype when the form closes. Code is ported into
`Geb/Mathlib/`, `Geb/Cslib/` or `GebLang/` when its expression is
settled and it reaches upstream quality, with dependents migrated
by rebasing after the upstream PR is accepted. The split lets
velocity and upstream-readiness each get the discipline that
suits them, without one blocking the other. It is driven by
whether a module's expression is settled, and by
dependency-readiness, not by authorship: AI-drafted and
human-written code follow the same rules in every subtree (see
`docs/rules/upstream-eligible.md` § Two-track development).

The upstream target is not a mathlib-or-Cslib binary. The subtree
import rules restrict `Geb/Mathlib/` modules to `Mathlib.*`,
`Batteries.*`, `Geb.Mathlib.*` and `GebLang.*` imports, so a
dependency of such a module cannot live in `Geb/Prototypes/`; a module
restating Lean core or Batteries API therefore sits in `Geb/Mathlib/`
while its upstream is neither mathlib4 nor Cslib. That destination is
open, per `TODO.md` § Upstream destination of core- and
Batteries-targeted content.

## Floodgate test

At all times, the repository is ready to ship dependency-ordered PRs
on short notice with no source-code changes.
`scripts/lint-imports.sh` enforces the import-direction and
no-prefix-leakage rules, and
`scripts/check-transitive-imports.sh` enforces the closure rules the
direct-import lists cannot see. The test is what makes
"upstream-eligible" a binding property of `Geb/Mathlib/`,
`Geb/Cslib/` and `GebLang/` rather than an aspiration: at any
moment, every file in any of them can be extracted to a PR
upstream.

The three locations are not independent of one another. A `GebLang`
module is retargeted by its own import closure, mathlib-track when
the closure reaches no `Cslib.*` and Cslib-track otherwise, so
extraction is dependency-ordered through `GebLang` rather than
independent per subtree: a module's within-repository dependencies
ship first, each to the upstream its own closure selects.

Cross-track dependency is uniform policy in one direction.
Cslib-destined content may depend on mathlib-destined content,
shipping after its dependencies merge and Cslib's mathlib pin
advances, exactly as Cslib itself depends on mathlib. Three cadences
the project does not set stand between the two PRs, which is the cost
the floodgate test's "on short notice" weighs; the ordering is
nevertheless available, whereas the reverse is not. Mathlib-destined
content depends on no Cslib-destined content: mathlib does not depend
on Cslib, so no ordering makes such a PR extractable, and
`Geb/Mathlib/`'s allowed lists bar it directly while
`scripts/check-transitive-imports.sh` bars it through `GebLang`.

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

## Version control follows the checkout

`jj` with its git backend writes ordinary git commits and leaves no
metadata that tells a `jj` user's work from a `git` user's, so a
contributor's choice between them is invisible to the repository
and is not the repository's to make. `AGENTS.md` § Version control
follows the checkout therefore has an agent detect the choice from
the checkout rather than assume one. The detection compares
`jj root` with `git rev-parse --show-toplevel` because a git
worktree nested inside a colocated repository is the case a bare
`.jj/` lookup gets wrong: `jj root` walks up to the parent's
`.jj/`, while the worktree itself is git's. The mutating-git hook
is opt-in for the same reason: installed unconditionally, it would
prompt a `git` user on every commit.

## main and integration

`main` is append-only stable history; never force-pushed. Topic
branches are merged without force-pushing.
`integration` is the regenerated fan-in merge view of `main` plus
active topic branches; force-pushed (lease-protected by default)
as topic-branch tips move. The split keeps `main` fork-friendly
(clones never see force-pushed history) while giving us a single
working view of all in-flight work. A regeneration that hits a
fan-in conflict refuses to publish and opens a deduplicated
`integration-regen-fail` tracking issue rather than leaving
`integration` silently stale.

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
and merges. The procedure runs on GitHub, on `update.yml`'s
schedule or by its manual dispatch; a bump is not run locally.
After the merge to `main`, `regenerate-integration.yml` regenerates
`integration` with `scripts/regenerate-integration.sh`. Topic
branches are not rebased by CI: each is rebased onto the new `main`
by whoever next works on it, or all at once with
`scripts/rebase-topics.sh main`, a `jj` script.
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

A contributor reviews the bump PR diff and merges. The procedure
runs on GitHub, and after the merge `integration` is regenerated and
topic branches are rebased as in the mathlib bump procedure.

## LKG/FKB pipeline

The mathlib bump procedure above follows the newest release tag
blindly: if that tag is the first to break this repository, the
bump PR fails CI and waits for a human. The
`leanprover-community/downstream-reports` pipeline replaces blind
tag-following with regression-gating. Its `hopscotch` tool walks
mathlib commits to record, per registered downstream, the
Last-Known-Good (LKG) commit that still builds and the
First-Known-Bad (FKB) commit that does not, and bumps only as far
as the LKG. Fermat's Last Theorem uses it (`update.yml` →
`hopscotch/lkg-bump`); registration is an entry in the pipeline's
`ci/inventory/downstreams.json`.

This repository has not adopted it. Registration triggers daily
Zulip notifications, a community-visible cost that is only worth
paying once the repository carries enough substantive content that
its breakage signal is informative to mathlib. The trigger for
revisiting is recorded in `TODO.md`; adopting the pipeline replaces
the `update.yml` detect-and-apply flow above with the
`downstream-reports` actions and is a deliberate, separately
reviewed change rather than an incremental tweak.

## Markdownlint discipline

Every Markdown document passes `markdownlint-cli2` against
`.markdownlint-cli2.jsonc` (shared with VSCode extension). The
discipline keeps documentation uniformly readable; sharing the
config with VSCode means the editor catches violations as we
type. Machine-emitted logs that are not authored documentation
are excluded from the lint via the ignore list in
`.markdownlint-cli2.jsonc` rather than held to the prose rules.

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
2026-04-20), removed that prohibition (PR #840, 2026-05-09),
reworded the section (PR #850, 2026-05-27), and added the
label-by-comment mechanism for the `LLM-generated` label (PR #855,
2026-05-28). The linked source
pages are the authority; re-check them periodically (the re-fetch
at each review of upstream-eligible content,
`docs/rules/lean-coding.md` § Authoritative upstream guides
(mathlib), is one such checkpoint), and when they change, update
`CONTRIBUTING.md`, `AGENTS.md`, and this file together.

## No LLM-drafted user-facing text

PR descriptions, Zulip messages, GitHub issue/PR comments are
user-authored. Mathlib's policy is unconditional ("use your own
words"). Two enforcement layers: the rule in `CONTRIBUTING.md`
§ Rules § Submission policy and the user-review-before-push gate.
The redundancy is intentional. Build output is not one of the
layers: `scripts/`
reports what the checks found, and restating a project rule there
would address the reader who runs the checklist as though they
were the agent the rule binds.

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

`.lean` copyright headers are a second exception: mathlib's
style guide prescribes named authors in the copyright and
`Authors:` lines, and upstream-eligible files keep that form.
The header names identify authorship for upstream submission,
not autobiographical detail.
