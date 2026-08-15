# Verso manual design: adversarial review, round 3

Reviewer: fresh-context agent, 2026-08-14. Verification sources:
this repository's binding documents, lakefile, workflows, and
scripts; Lake sources at `lean4@v4.34.0-rc1`; verso at
`v4.34.0-rc1`; verso-templates; batteries `runLinter` and Cslib
as pinned; `anoma/geb` directly (its manual PRs, lakefile,
nolints, CI, and rules files); `docs/index.md`,
`docs/references.bib`, `README.md`; the topic branch's `jj` log.
The round confirmed every prior-round fix it spot-checked, from
primary sources (the pin-precedence direction from Lake's
resolver, the axiom-linter boundary from `runLinter`'s
per-module import behavior, the generator invocation, the
`srcDir` fields, the precedent's defect history). It also
confirmed § Content's coherence (the framing matches
`README.md`'s own first sentence; the works the initial chapters
would cite are keyed in `docs/references.bib`) and the fit of
§ CI with `doc-build.yml` as written.

Verdict: **converged**, with no blocker and no serious findings.
Six
minor and three cosmetic-taste findings were left to the author;
all are fixed below, in this round's commit.

## Findings and responses

Minor.

1. The bibliography `def`s, keyed as in `docs/references.bib`,
   are UpperCamelCase terms, departing from the lowerCamelCase
   term-naming rule, and the spec recorded no exemption. Fixed:
   § Content records the exemption and its justification
   (cross-artifact key identity), to be recorded in
   `docs/rules/lean-coding.md`.
2. `update.yml`'s step name enumerates the requires its `sed`
   rewrites; after this workstream the enumeration would be
   falsified. Fixed: § Dependency states the step name gains the
   new member.
3. `scripts/manual.sh` needs repository-root resolution
   (`scripts/nolints.json` and `--output manual/_out` are
   cwd-relative), which the spec omitted. Fixed: § Build, serve,
   reload states the script resolves the repository root and runs
   from it, as the existing scripts do.
4. § Layout's claim that `lake build`, `lake test`, and the
   default `lake lint` are unaffected held for compilation only;
   the manifest change materializes new checkouts once and
   invalidates the pre-push cache stamp once. Fixed: the claim is
   scoped to compilation and the one-time effects are stated.
5. § Generator executable understated the `module` evidence: the
   precedent recorded the old obstruction (`#doc` emitting a
   non-`public` `def`), and at `v4.34.0-rc1` that mechanism is
   gone (`#doc` emits a `public def`). Fixed: the paragraph
   carries both facts; the deferral and fallback stand.
6. The `doc-build.yml` paths filter omitted
   `scripts/nolints.json`, so a nolints change would not trigger
   the manual lint that consumes it. Fixed: § CI adds it with the
   rationale.

Cosmetic-taste.

1. The port-fallback description was imprecise (`verso-serve`
   scans upward, bounded, and binds `127.0.0.1`). Fixed in
   § Build, serve, reload.
2. The precedent merge date was timezone-dependent. Fixed: the
   spec dates the merges in UTC.
3. Case drift between the project and package spellings of the
   Verso name. Fixed: Verso in prose names the project; `verso`
   in code spans names the package or require.
