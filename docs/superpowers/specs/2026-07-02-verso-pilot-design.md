# Verso pilot design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Goal](#goal)
- [Background: three scopes](#background-three-scopes)
- [Pilot subject and deliverable](#pilot-subject-and-deliverable)
- [Success criteria](#success-criteria)
- [Build setup](#build-setup)
- [Interaction with the transient-artifact lifecycle](#interaction-with-the-transient-artifact-lifecycle)
- [Build versus CI](#build-versus-ci)
- [Markdown fallback](#markdown-fallback)
- [Escalation path](#escalation-path)
- [Out of scope](#out-of-scope)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This spec is a transient process artifact. Per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape, it is
removed in the final commits of its topic branch and does not
reach `main`'s working tree.

## Goal

Evaluate, with a reversible local experiment, whether Verso is
worth adopting for any of this project's documentation. The
experiment answers two questions against a single small document:

1. Does Verso's build-time type-checking of embedded Lean catch
   real drift between prose and code?
2. Is a Verso-rendered document more readable, to the user, than
   the Markdown equivalent — enough to justify Verso's authoring
   friction?

The experiment commits no dependency, touches no CI, and modifies
no upstream-eligible content. If it fails either question, the
current doc-gen4 plus Markdown strategy stands unchanged.

## Background: three scopes

A prior evaluation corrected a flat four-condition trigger into
three scopes with distinct gates. doc-gen4 (an automatic
API-reference generator) and Verso (a hand-written prose and book
authoring tool) are complementary, not alternatives; the question
is never whether to switch from one to the other, only whether to
add a Verso prose layer alongside doc-gen4.

- **Docstrings** in `.lean` files: gated on doc-gen4 gaining
  Verso-aware rendering and on mathlib migrating to Verso.
  Hard-blocked, and contraindicated for `Geb/Mathlib/` and
  `Geb/Cslib/`. Out of scope for this pilot.
- **Persistent prose** (`docs/`, a future Geb-language
  exposition): gated on the prose growing substantial and
  describing stable, existing code. The pilot's escalation target.
- **Transient design docs** on feature branches: no external gate.
  The pilot exercises this scope's authoring path.

The full trigger record lives in
[TODO.md](../../../TODO.md) § Triggers.

## Pilot subject and deliverable

One Verso document rendering a write-up of
`Geb/Mathlib/Data/PFunctor/Slice/W.lean` to local HTML. The
document:

- embeds that module's real declaration signatures via Verso's
  docstring and Lean-code roles, so the embedded code elaborates
  against the current `Slice/W.lean`;
- includes at least one within-document reference role (a
  declaration reference or a section reference), to exercise
  Verso's linking roles on a concrete case. Verso's experimental
  cross-references are cross-document semantic links and require
  two or more documents; they are not fully testable in a
  single-document pilot and are deferred to the escalation step;
- is paired with the equivalent content authored in Markdown, for
  the readability comparison.

The subject is an already-implemented module deliberately: its
declarations exist, so embedded Lean and cross-references are
testable immediately, and drift can be induced under controlled
conditions (see Success criteria) rather than awaited.

The exact Verso genre and rendering API follow the
`leanprover/reference-manual` template; the precise wiring is
settled in the implementation plan.

## Success criteria

- **Builds green.** The document builds against the current
  `Slice/W.lean`.
- **Catches induced drift.** Renaming or retyping one real
  declaration in a scratch copy makes the Verso build fail with a
  locatable error; reverting restores the green build.
- **Reference role resolves.** The within-document reference role
  resolves in the rendered HTML. A precise record of how it fails,
  if it does, is also an acceptable result.
- **Readability verdict.** The user renders the Verso HTML and the
  Markdown side by side and records a plain verdict on relative
  readability.

## Build setup

A throwaway lake project in a git-ignored in-repo directory
(`.verso-pilot/`, added to `.gitignore`). It:

- requires Verso, pinned to `v4.32.0-rc1` to match
  `lean-toolchain`;
- path-requires this repository so embedded Lean can import
  `Geb.*`.

The committed `lakefile.toml` and `lake-manifest.json` are not
modified: no new committed dependency, and the floodgate test is
preserved. The one-time cost is building Verso's dependency tree
once (cached thereafter); the Geb and mathlib builds already
exist.

## Interaction with the transient-artifact lifecycle

The pilot's working artifacts — `.verso-pilot/` and the rendered
HTML — are never committed. Being git-ignored scratch, they sit
outside the create-implement-remove lifecycle of specs and plans
and cannot leak onto `main`.

The one committed artifact is this spec, under
`docs/superpowers/specs/`, which follows the normal transient rule
and is removed in the final commits of its topic branch. A durable
finding (the readability verdict and the drift-test result) is
recorded outside the repository, in the docs-strategy reference
note, not in the committed tree.

## Build versus CI

Local only. No CI target, no committed lake target, no Pages
publication. The CI-runner sizing question is deferred entirely to
the escalation step, if it fires.

## Markdown fallback

Unconditional. If the pilot fails either question, nothing
changes: the doc-gen4 plus Markdown strategy stands, and the
recorded rationale already explains why. Because nothing was
committed, there is no partial-migration state to unwind.

## Escalation path

A pilot that passes both questions does not lead to an immediate
migration. The next step is a second, larger pilot: a persistent
Geb-language exposition seed chapter (the persistent-prose scope),
at which point the questions this pilot defers are brainstormed —
a committed lake target, a CI build, Pages publication, runner
sizing, and how a Verso book coexists with doc-gen4's API site.
The transient-design-doc scope can be exercised opportunistically
on a live feature branch once the authoring path is known to suit
the user.

## Out of scope

- Docstring migration (the hard-blocked scope).
- Any CI target or Pages publication.
- Any committed dependency or `lakefile.toml` change.
- Any change under `Geb/Mathlib/` or `Geb/Cslib/`.
- Conversion of process or rules documents, which remain Markdown.
