# Verso Pilot Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Determine, with a reversible local-only experiment, whether Verso's
build-time type-checking of embedded Lean catches drift and whether a
Verso-rendered document reads better than the Markdown equivalent.

**Architecture:** A throwaway lake project in a git-ignored directory
(`.verso-pilot/`) built from Verso's `basic-book` template (Manual genre),
pinned to `v4.32.0-rc1`. It path-requires this repository so a Book chapter can
`import` a real module and embed type-checked Lean referring to `SlicePFunctor`
declarations from `Geb/Mathlib/Data/PFunctor/Slice/W.lean`. Rendering is `lake
exe generate-book` to `_out/html-multi/`. A Markdown twin of the same content
is written for the readability comparison. The only committed change in the
whole plan is one line in `.gitignore`.

**Tech Stack:** Lean 4 (`v4.32.0-rc1`), Lake, Verso (`VersoManual`,
`Verso.Genre.Manual.InlineLean`), the `basic-book` template from
`leanprover/verso-templates`, `jj` for the single commit.

## Global Constraints

- Verso is pinned to `rev = "v4.32.0-rc1"` (matches `lean-toolchain`); the
  `basic-book` template already pins this exact value.
- Do not modify the committed `lakefile.toml` or `lake-manifest.json` at the
  repository root.
- Do not modify any file under `Geb/Mathlib/` or `Geb/Cslib/` (including the
  drift test, which is performed doc-side).
- No CI target, no committed lake target, no Pages publication.
- Nothing under `.verso-pilot/` or any rendered HTML is committed;
  `.verso-pilot/` is added to `.gitignore`.
- The single committed change (the `.gitignore` line) is made through `jj`,
  not raw mutating `git`.
- The durable finding (readability verdict plus drift result) is recorded in
  the docs-strategy memory note, not in the repository.
- The spec this implements is
  `docs/superpowers/specs/2026-07-02-verso-pilot-design.md`.

---

### Task 1: Ignore the pilot directory

The one committed change. It keeps every subsequent artifact out of the
repository, satisfying the floodgate test.

**Files:**

- Modify: `.gitignore` (append one entry)

**Interfaces:**

- Produces: a git-ignored `.verso-pilot/` path that all later tasks write into
  without affecting `jj status`.

- [ ] **Step 1: Inspect the current ignore file**

Run: `cat .gitignore`
Expected: existing entries such as `.lake/`; confirm there is no
`.verso-pilot/` entry yet.

- [ ] **Step 2: Append the ignore entry**

Add this line to the end of `.gitignore`:

```gitignore
.verso-pilot/
```

- [ ] **Step 3: Verify the path is ignored**

Run: `mkdir -p .verso-pilot && touch .verso-pilot/probe && jj status`
Expected: `jj status` lists `.gitignore` as modified and does NOT list
`.verso-pilot/probe`. Then remove the probe: `rm .verso-pilot/probe`.

- [ ] **Step 4: Commit the ignore change through jj**

Run:

```bash
jj commit -m "chore: ignore local Verso pilot directory" .gitignore
```

Expected: a new commit on `doc/verso-pilot` containing only `.gitignore`;
`jj log -r '::@' --limit 3` shows it.

---

### Task 2: Scaffold the minimal Verso book and prove it renders

Isolates the Verso toolchain from mathlib. This task depends only on Verso, so
it builds fast and confirms the Verso side works before any integration.

**Files:**

- Create: `.verso-pilot/lakefile.toml`
- Create: `.verso-pilot/lean-toolchain`
- Create: `.verso-pilot/Main.lean`
- Create: `.verso-pilot/Book.lean`
- Create: `.verso-pilot/Book/Slice.lean`

**Interfaces:**

- Produces: a buildable Manual-genre document whose entry point is
  `generate-book` and whose single chapter is `Book.Slice`; later tasks add
  content to `Book/Slice.lean`.

- [ ] **Step 1: Write the lake configuration**

Create `.verso-pilot/lakefile.toml`:

```toml
name = "verso-pilot"
defaultTargets = ["Book", "generate-book"]

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"
rev = "v4.32.0-rc1"

[[lean_lib]]
name = "Book"

[[lean_exe]]
name = "generate-book"
root = "Main"
```

- [ ] **Step 2: Write the toolchain file**

Create `.verso-pilot/lean-toolchain` with exactly:

```text
leanprover/lean4:v4.32.0-rc1
```

- [ ] **Step 3: Write the entry point**

Create `.verso-pilot/Main.lean`:

```lean
import VersoManual
import Book

open Verso.Genre Manual

def main := manualMain (%doc Book)
```

- [ ] **Step 4: Write the book root**

Create `.verso-pilot/Book.lean`:

```lean
import VersoManual
import Book.Slice

open Verso.Genre Manual

#doc (Manual) "Verso Pilot" =>
%%%
authors := ["The geb-mathlib contributors"]
%%%

A local-only experiment rendering a write-up of the slice W-type module.

{include 1 Book.Slice}
```

- [ ] **Step 5: Write a placeholder chapter**

Create `.verso-pilot/Book/Slice.lean`:

```lean
import VersoManual

open Verso.Genre Manual

#doc (Manual) "Slice W-types" =>

Placeholder chapter. Content is added in Task 4.
```

- [ ] **Step 6: Resolve dependencies and build**

Run:

```bash
cd .verso-pilot && lake update && lake build
```

Expected: Verso and its dependencies are fetched (writing
`.verso-pilot/lake-manifest.json`, which is git-ignored) and the build
succeeds with no errors.

- [ ] **Step 7: Render to HTML**

Run:

```bash
cd .verso-pilot && lake exe generate-book
```

Expected: an `_out/html-multi/` directory is produced under `.verso-pilot/`.

- [ ] **Step 8: View the output**

Run:

```bash
cd .verso-pilot && python3 -m http.server 8000 -d _out/html-multi
```

Expected: opening `http://localhost:8000` shows the "Verso Pilot" book with
the placeholder chapter. Stop the server with Ctrl-C. No commit — everything
here is git-ignored.

---

### Task 3: Wire in the repository and prove one real declaration type-checks

The integration step and the highest-risk task. It adds the path dependency on
this repository and confirms the combined dependency graph resolves and a real
`SlicePFunctor` declaration elaborates inside the Verso build.

**Files:**

- Modify: `.verso-pilot/lakefile.toml` (add the path require)
- Modify: `.verso-pilot/Book/Slice.lean` (import the module, add one
  type-checked reference)

**Interfaces:**

- Consumes: `SlicePFunctor.W.elim` from
  `Geb/Mathlib/Data/PFunctor/Slice/W.lean` (all referenced declarations are
  `@[expose]`).
- Produces: a chapter whose build fails if the referenced declaration is
  absent or mistyped.

- [ ] **Step 1: Add the path dependency**

Append to `.verso-pilot/lakefile.toml`:

```toml
[[require]]
name = "geb-mathlib"
path = ".."
```

- [ ] **Step 2: Reference a real declaration in the chapter**

Replace the contents of `.verso-pilot/Book/Slice.lean` with (the source itself
contains an inner `lean` code block, so it is shown here inside a four-backtick
fence):

````lean
import VersoManual
import Geb.Mathlib.Data.PFunctor.Slice.W

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Slice W-types" =>

The eliminator of the slice W-type is the morphism into any slice algebra.

```lean
#check @SlicePFunctor.W.elim
```
````

- [ ] **Step 3: Resolve the combined graph and fetch the mathlib cache**

Run:

```bash
cd .verso-pilot && lake update && lake exe cache get
```

Expected: dependency resolution succeeds and the mathlib build cache is
fetched.

DECISION POINT: if `lake update` fails with a dependency-version conflict
between Verso's transitive dependencies and mathlib's, stop. Do not hand-edit
the graph. Record the exact conflict and switch to the contingency: decouple
the graphs using Verso's external example-project mechanism (`set_option
verso.exampleProject ".."`, per the `package-docs` template in
`leanprover/verso-templates`), which does not import mathlib into the Verso
process. Re-scope with the user before proceeding.

- [ ] **Step 4: Build with the real reference**

Run:

```bash
cd .verso-pilot && lake build
```

Expected: the build succeeds; the `#check @SlicePFunctor.W.elim` block
elaborates against the repository's `Geb` library.

- [ ] **Step 5: Render and confirm the signature appears**

Run:

```bash
cd .verso-pilot && lake exe generate-book && python3 -m http.server 8000 -d _out/html-multi
```

Expected: the chapter renders and shows the elaborated `#check` output for
`SlicePFunctor.W.elim`. Stop the server with Ctrl-C. No commit.

---

### Task 4: Author the write-up and its Markdown twin

Produces the paired documents for the readability comparison. Content is a
short write-up of the module embedding several real declaration signatures and
one within-document reference.

**Files:**

- Modify: `.verso-pilot/Book/Slice.lean` (full write-up)
- Create: `.verso-pilot/Slice.md` (Markdown twin)

**Interfaces:**

- Consumes: `SlicePFunctor.W`, `SlicePFunctor.windex`, `SlicePFunctor.W.mk`,
  `SlicePFunctor.W.dest`, `SlicePFunctor.W.elim`, `SlicePFunctor.W.dest_mk`
  (all `@[expose]`).
- Produces: the rendered Verso HTML and the Markdown twin, the inputs to the
  readability verdict.

- [ ] **Step 1: Write the full Verso chapter**

Replace the contents of `.verso-pilot/Book/Slice.lean` with (shown inside a
four-backtick fence because the source contains inner `lean` code blocks):

````lean
import VersoManual
import Geb.Mathlib.Data.PFunctor.Slice.W

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Slice W-types" =>

When the domain and codomain indices coincide, a slice polynomial functor
is an endofunctor, and its W-type is the admissible subtype of the underlying
`PFunctor` W-type.

# The carrier and its structure map
%%%
tag := "carrier"
%%%

The carrier is the admissible trees, with a structure map into the index type.

```lean
#check @SlicePFunctor.W
#check @SlicePFunctor.windex
```

# Constructor and destructor

The constructor and destructor are mutually inverse, so the carrier is a fixed
point of the slice endofunctor.

```lean
#check @SlicePFunctor.W.mk
#check @SlicePFunctor.W.dest
#check @SlicePFunctor.W.dest_mk
```

# The eliminator

The eliminator is the morphism from the carrier defined in {ref "carrier"}[the
carrier section] into any slice algebra.

```lean
#check @SlicePFunctor.W.elim
```
````

- [ ] **Step 2: Write the Markdown twin**

The twin must present identical content to the Verso chapter, so its
signatures are the exact `#check` outputs the Verso build already printed in
Task 4 Step 3 (read them from the `lake build` output or the rendered HTML; do
not hand-write them). Reproduce the four sections with the same prose, and
under each, place the corresponding `#check` output lines verbatim as an
indented (four-space) code block. Create `.verso-pilot/Slice.md`:

```markdown
# Slice W-types

When the domain and codomain indices coincide, a slice polynomial functor is an
endofunctor, and its W-type is the admissible subtype of the underlying
`PFunctor` W-type.

## The carrier and its structure map

The carrier is the admissible trees, with a structure map into the index type.

[indented code block: the verbatim #check output lines for
SlicePFunctor.W and SlicePFunctor.windex]

## Constructor and destructor

The constructor and destructor are mutually inverse, so the carrier is a fixed
point of the slice endofunctor.

[indented code block: the verbatim #check output lines for
SlicePFunctor.W.mk, SlicePFunctor.W.dest, and SlicePFunctor.W.dest_mk]

## The eliminator

The eliminator is the morphism from the carrier (see the carrier section) into
any slice algebra.

[indented code block: the verbatim #check output line for
SlicePFunctor.W.elim]
```

- [ ] **Step 3: Build and render the Verso document**

Run:

```bash
cd .verso-pilot && lake build && lake exe generate-book
```

Expected: the build succeeds and `_out/html-multi/` is regenerated.

- [ ] **Step 4: View both documents side by side**

Run:

```bash
cd .verso-pilot && python3 -m http.server 8000 -d _out/html-multi
```

Expected: the multi-page book renders with the four sections and the
signatures. Open `.verso-pilot/Slice.md` in the Markdown preview alongside it.
Stop the server with Ctrl-C. No commit.

---

### Task 5: Confirm the within-document reference resolves

Checks success criterion "reference role resolves" on the concrete
`{ref "carrier"}` link authored in Task 4.

**Files:**

- No file changes (verification only)

- [ ] **Step 1: Locate the reference in the rendered HTML**

Run:

```bash
cd .verso-pilot && grep -rl "carrier" _out/html-multi | head
```

Expected: the eliminator section's HTML contains an anchor link whose target
is the carrier section's permalink.

- [ ] **Step 2: Click through in the browser**

Run:

```bash
cd .verso-pilot && python3 -m http.server 8000 -d _out/html-multi
```

Expected: the link rendered from `{ref "carrier"}[the carrier section]`
navigates to the tagged carrier section. Record the result: resolved, or the
precise failure mode. Stop the server with Ctrl-C.

---

### Task 6: Run the drift test

Demonstrates success criterion "catches induced drift" doc-side, touching no
committed file. A mismatch introduced in the pilot doc is, to the
type-checker, indistinguishable from the library renaming the declaration.

**Files:**

- Temporarily modify then revert: `.verso-pilot/Book/Slice.lean` (git-ignored)

- [ ] **Step 1: Introduce a drift by mismatching one reference**

In `.verso-pilot/Book/Slice.lean`, change the eliminator block from
`#check @SlicePFunctor.W.elim` to a name the library does not provide:

```lean
#check @SlicePFunctor.W.eliminate
```

- [ ] **Step 2: Build and confirm a locatable failure**

Run:

```bash
cd .verso-pilot && lake build
```

Expected: FAIL with an "unknown identifier" (or "unknown constant") error
naming `SlicePFunctor.W.eliminate`, located in `Book/Slice.lean`.

- [ ] **Step 3: Revert the drift and confirm green**

Restore the block to `#check @SlicePFunctor.W.elim`, then run:

```bash
cd .verso-pilot && lake build
```

Expected: PASS. Record that the drift was caught and reverting restored the
green build.

---

### Task 7: Record the finding and clean up

Captures the durable result outside the repository and confirms the working
tree is clean of pilot artifacts.

**Files:**

- No repository file changes (the memory note lives outside the repo)

- [ ] **Step 1: Record the verdict in the docs-strategy memory**

Append to the docs-strategy memory note a dated pilot result: whether the
Verso build caught the induced drift, whether the within-document reference
resolved, and the user's readability verdict (Verso HTML versus the Markdown
twin), with a one-line recommendation on whether to proceed to the persistent
Geb-language exposition pilot.

- [ ] **Step 2: Confirm the repository is unaffected**

Run:

```bash
jj status
```

Expected: no changes other than what Task 1 already committed; nothing under
`.verso-pilot/` appears (it is git-ignored). The `.verso-pilot/` directory may
be left in place for further local exploration or removed with
`rm -rf .verso-pilot`.
