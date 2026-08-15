# Verso manual design: adversarial review, round 1

Reviewer: fresh-context agent, 2026-08-14. Verification sources:
this repository's binding documents and scripts; Lake at
`lean4@v4.34.0-rc1`; verso at `v4.34.0-rc1` (lakefile,
`VersoManual.lean`, `VersoServe`, `InlineLean`); verso-templates;
batteries `runLinter`; Cslib as pinned; Reservoir. Verdict: not
converged (no blocker; five serious findings). Every finding is
addressed below; the spec edits land in this round's commit.

## Findings and responses

Serious.

1. `lake exe geb-manual -- --output manual/_out` fails: Lake's
   `exe` handler forwards trailing arguments verbatim, so the
   program receives `--` and `manualMain` rejects it. Fixed: the
   `--` is dropped in § Build, serve, reload, with the mechanism
   noted.
2. Verso's dependency set was mis-stated as `subverso` and
   `MD4Lean`; at the tag it also requires `plausible` and
   `illuminate`, all four at branch `main`, and `plausible` and
   `MD4Lean` overlap pins the repository already carries (mathlib
   transitives, `doc-gen4`). Fixed: § Dependency analyzes the
   overlap, places verso first among the git requires, and adds
   transitive branch-head drift as a second bump-time failure
   mode; § Ecosystem lists all four.
3. The axiom linter (`GebMeta.detectNonstandardAxiom`) under
   `lake lint -- GebManual` was unaddressed. Fixed: § Linting
   states the intended scope boundary (the manual imports specific
   `Geb` modules, not `GebMeta`, so the linter does not register
   in its lint environment; the constructive discipline governs
   the formalization, not Verso's rendering data), records it in
   `docs/rules/lean-coding.md`, and § Verification checks the
   boundary during implementation.
4. The `test-lint-driver.sh` extension was mis-described (the
   script has no table) and its natural reading would compile
   Verso in `pre-push.sh` and `ci.yml`, contradicting the spec's
   own exclusions. Fixed: § Linting specifies a static-only
   extension (reachability over `manual/`, presence of the
   `doc-build.yml` step) and states why the executed-lint check is
   not extended.
5. Package `leanOptions` inheritance (`mathlibStandardSet`,
   `flexible`, `style.header`, `warningAsError`) onto the manual
   library was not analyzed. Fixed: § Linting states the
   inheritance,
   the known-in-advance accommodations, the candidates for
   further ones, and the rule that `warningAsError` stays on so
   the accommodation set is exactly what a clean build requires.

Minor.

1. `topNamespace` nolints would be dead configuration: under this
   repository's pins the Cslib linter carries no `env_linter`
   attribute. Fixed: dropped; `docBlame` covers the bibliography
   entries.
2. "`lake lint` loads `.olean` files but does not compile them"
   is contradicted by `runLinter`'s build fallback. Fixed: the
   precedent's defect is now described by its observed behavior,
   without the mechanism claim.
3. teorth/analysis was mis-cited as an instance of the
   document-library pattern; it uses Verso's literate docstring
   flow. Fixed in § Ecosystem and § References.
4. The serve verb printed a fixed URL, but `verso-serve` falls
   back from port 8000 to the next free port and prints the URL
   it serves. Fixed: the script defers to `verso-serve`'s output.
5. `Bibliography.lean` duplicates bibliographic detail that
   `CONTRIBUTING.md` locates once in `docs/references.bib`.
   Fixed: § Content names the `.bib` as authoritative and the
   Lean entries as a rendering transcription corrected against it.
6. The `Main.lean` snippet omitted the copyright header and
   module discipline `docs/rules/lean-coding.md` requires. Fixed:
   the snippet is marked abbreviated and the requirement stated.
7. Later reviewers cannot consult the experimental repository,
   so precedent-only details rested on the author's
   report. Fixed: § Precedents says so and § Verification
   re-verifies those details during implementation; the universal
   no-watch-mechanism claim is narrowed to the surveyed projects.
8. CI cost (from-source Verso builds inside the 60-minute job;
   `lintDriverArgs` prepending `Geb` to the manual lint) was not
   assessed. Fixed: § CI records both and the fallback of a
   separate job.
9. `docs/index.md`'s charter (implemented content) does not cover
   build commands. Fixed: the commands live in `README.md`;
   `docs/index.md` gains only a pointer.

Cosmetic-taste.

1. Colloquial phrasing (the layout described as a complaint, an
   executable root described as loose). Fixed in § Precedents and
   § Alternatives.
