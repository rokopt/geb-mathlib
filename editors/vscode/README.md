# Geb for VS Code

The `geb` language supports the Geb authoring profile: parentheses,
semicolon line comments, quoted atoms with escapes and embedded line
breaks, numerals, and named holes. The extension registers the language,
its TextMate grammar and its editing configuration, and runs the Geb host
commands for a selected program. It does not change the compiler's grammar.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Installation](#installation)
- [Editing and formatting](#editing-and-formatting)
- [Diagnostics](#diagnostics)
- [Navigation](#navigation)
- [Programs and commands](#programs-and-commands)
- [Validation](#validation)
- [Structural editing acceptance](#structural-editing-acceptance)
- [References](#references)

<!-- END doctoc -->

## Installation

From the repository root, with Node.js 22 or later:

```sh
npm ci --prefix editors/vscode
npm run package --prefix editors/vscode
code --install-extension editors/vscode/geb-language.vsix
```

The package is local; these commands do not publish it. Open a `.geb`
file and select the `Geb` language if a previous file association
overrides its extension. In a remote workspace, install the extension
in the VS Code instance displaying the file.

The extension runs the host executables of the Geb checkout that
`geb.toolchainDirectory` names (§ Programs and commands). The default
`lake build` builds the `Geb` library alone, and no executable; build
them ahead of the first command with

```sh
lake build geb-author geb-kernel geb-fmt geb-compile geb-defs
```

`geb-author` compiles programs, checks their examples, proves and
replays proof documents, and answers the editor's navigation, formatting
and hole requests; `geb-kernel` lists a manifest's sources, reports
kernel holes and runs an image's definition on a file; `geb-fmt` formats
files; `geb-compile` and `geb-defs` are run by `scripts/preserve.py` for
records. The extension uses Python 3 to check the selected checkout's
host sources, dependency sources, build configuration, toolchain and
executable. On first use or after a change it asks Lake to build the
requested tools. Subsequent commands run those executables directly.
The checkout keeps the successful build stamps in `.lake/geb-editor/tools/`.
Editing a client or library Geb document requires no host rebuild.

The structural editor is Mike's Paredit, built from the upstream commit
and [patch](patches/README.md) that `package.json` pins under
`editorTest.paredit`. The build requires `git`, `patch` and network
access:

```sh
npm run build:paredit --prefix editors/vscode
code --install-extension 'editors/vscode/paredit-0.2.1+geb.1.vsix' --force
```

The build keeps upstream's identifier, `MikeDelmonaco.paredit`, so its
commands and keybindings are upstream's, and it replaces an installed
Marketplace release. Its version, `0.2.1+geb.1`, has the precedence of
the release it patches, so VS Code offers no update to that release. A
later upstream release would be offered; disabling Auto Update for the
extension in the Extensions view keeps the build installed.

## Editing and formatting

The language configuration supplies `;` for Toggle Line Comment,
parenthesis matching, and closing pairs for parentheses and quoted
atoms. The grammar distinguishes comments and quoted atoms so that
parentheses inside them do not participate in bracket matching.
Brackets and braces are not Geb grouping delimiters.

Format Document formats the current buffer, including untitled Geb
documents. One undo restores the original text.
The formatter retains comments and annotations. In CRLF buffers it spells
newlines within quoted atoms as escapes, preserving their bytes when the
editor normalizes inserted line endings. Malformed input leaves
the buffer unchanged. Atoms containing non-UTF-8 bytes use hexadecimal
escapes. It uses the selected program's toolchain, or the
workspace's `geb.toolchainDirectory` when no program is selected.
Formatting on save is disabled by default for Geb.

The extension also contributes the task `Geb: format saved file`, which
invokes `geb-fmt` on the active file and writes its layout.

The formatter and the document type are described in the
[bootstrap chapter](../../manual/GebManual/Bootstrap.lean).

## Diagnostics

The extension contributes, for each workspace folder, the task
`Geb: check saved file`, which runs `geb-author check` on the
active file in the folder's `geb.toolchainDirectory`, and the command
writes nothing. Both file tasks are listed under Tasks: Run Task, and a
`tasks.json` may refer to them as
`{"type": "geb", "task": "check saved file"}`. For a source of a program it
compiles the sources of the nearest manifest that lists the file, up to
that file, or the file alone where no manifest lists it. It reports what
rejects the program as `FILE:LINE:COLUMN: error: MESSAGE`, at the name of
the first failing declaration, at an atom the implementation reserves, or
at the character or parenthesis at which the text does not read. For a
proof document, a file holding a form `(proofs V …)`, it proves the
document, after the documents it imports, against the program the
document names by `(program NAME)`, and reports a theorem whose statement
or script does not read at the theorem's name, and a hole that a script
leaves open, or a step of a script that does not prove its goal, at the
hole or the step, with the goal on the diagnostic's line (the manual's
chapter Writing a first Geb development, § Holes and goals). The task
passes `--cache` with the folder's `.lake/geb-proof-cache`, so that a
proof document is resumed from the cache its last check left there and
searched only where it changed (§ The cache of a development). The
extension contributes the problem matcher `$geb`,
which the task names, so that the report appears in the Problems view and
at its position in the file that holds it, which may be an earlier source
of the program or an imported document.

For an editor with a language-server client,
[`editors/efm-langserver/config.yaml`](../efm-langserver/config.yaml)
configures [efm-langserver](https://github.com/mattn/efm-langserver) to
run the same command when a buffer is saved.

## Navigation

After selecting a program, Go to Definition
resolves references to that program's declarations, including imports,
aliases and module instances. An instance's declaration opens its
template's source. Hover displays the source signature and its preceding
documentation; comments before a declaration's note are included.
The Outline view lists the current file's declarations, and Go to Symbol
in Workspace searches the selected program.

Local references navigate to their binders, respecting shadowing, sequential
bindings and pattern branches. The selected program's `proofs` entry and
its imports contribute theorem outlines, statement and script hover,
references to earlier theorems, quantified variables, named hypotheses and
script binders. Identifier completion uses those scopes and the module
elaborator's visible names, retaining import aliases and quoting names
when the authoring profile requires it. Type positions offer type names.
Comments, quoted data and hole names offer no identifier completions.
Completion insertions escape embedded line breaks; a name already spanning
several source lines supports navigation but not completion replacement.

Navigation reads snapshots of open file buffers without saving them or
compiling the program. The extension translates byte columns into editor
positions, including Unicode names. Cancelled requests and results whose
input buffers changed are discarded. During incomplete edits the host
recovers readable prefixes and completed children of open forms. Outlines
also retain missing entries from the previous successful parse, labelled
as such; those entries supply no definition, hover or completion result.
Recovery never changes the compiler's input. Strict-encoded sources have
no editor navigation interface. Navigation requires workspace trust.

The extension keeps `geb-author navigation-server MANIFEST` running for
the selected program. It accepts one JSON request and returns one JSON
response per line. Each query checks the manifest and the contents of
its sources and proof imports, including unsaved snapshots. The host
reuses parsed documents and resumes indexing at the first changed file.
A change to the module nesting bound requires indexing from the start.
The extension restarts the process when the host executable changes.
For a project pinned to a checkout that provides only the single-request
interface, it uses that interface.

The single-request interface `geb-author navigation MANIFEST` reads a JSON
object from standard input with `file`, one-based byte `line` and
`column`, and `documents`, an array of `{path, text}` buffer snapshots
under absolute paths. Optional `proofs` names the entry proof document;
`recover: true` enables editor recovery. A zero line and column requests
the declaration index alone. The optional `operation` selects `target`,
`completion`, `document` or `workspace`. Omitting it returns the full
single-request result. The result contains `symbols`, an optional
`target`, `completions`, an optional `atomSpan` for completion replacement,
`incomplete` file paths and `errors`. Each symbol names its file, full
span, name selection, signature, documentation and completion `insertText`
in the full result. Operation-specific responses omit unused symbol fields.
Names and source text are arrays of bytes, decoded as UTF-8; file paths
and kinds are JSON strings. Spans are
`[startLine, startColumn, endLine, endColumn]`, with inclusive endpoints.
The interface uses the existing document lexer and module renamer.

The Explorer's Geb Kernel Obligations view is populated by
`Geb: Refresh Kernel Obligations`. It displays each hole's expected type,
its context and links to every source occurrence. After the first refresh,
edits refresh the view automatically from unsaved snapshots. Changed
inputs invalidate the previous report; rejected input is shown as not
checked. A completed check with no holes is distinguished from a report
of open obligations. This view uses the existing kernel hole checker and
accepts its kernel forms; datatype holes and proof synthesis are separate
work. The terminal command `Geb: Show Kernel Holes` remains available.

`geb-author format-buffer` accepts `{text}` and an optional `crlf: true`,
and returns formatted byte text. `geb-author editor-holes MANIFEST` accepts
`{documents}` and returns
`complete` and `holes`, each with `name`, `target`, `context` and
`occurrences`. These interfaces write no files. Hole checking requires
complete syntax and never consumes recovery results.

## Programs and commands

The workspace settings list the programs available to the editor. This
repository configures the Pair and Roundtrip examples, the shared
library under `library/` and the Tree cases proof development. The
template under [`examples/client/`](../../examples/client/README.md) is a
client kept in a repository of its own, with the Geb checkout as a
submodule that its settings name as the toolchain directory. For another
program, add an entry to `geb.programs` in the workspace folder's
settings:

```json
{
  "geb.toolchainDirectory": ".",
  "geb.programs": [{
    "name": "Pair",
    "manifest": "examples/authoring/pair.manifest",
    "proofs": "examples/authoring/Pair.proofs.geb"
  }]
}
```

Paths are absolute or relative to that workspace folder, including when
the editor has several folders open. `geb.toolchainDirectory` names the
Geb repository containing `lakefile.toml` and `scripts/preserve.py`; set
it to that repository's path when the development lives elsewhere.
The host reads source order and entry points from the manifest. The
editor does not infer a program from the active source file.

Run `Geb: Select Program` or click the Geb status-bar item. The selection
is remembered for the workspace and shown in the status bar and task
title. A command selects the sole configured program automatically, or
offers a selection when needed. Commands run as process tasks, with
arguments passed separately and paths with spaces supported. The task
terminal displays the host's output. Use `Tasks: Terminate Task` to stop
a running command; another Geb command can start after the task ends.

| Command | Host operation |
| --- | --- |
| `Geb: Compile Program` | `geb-author compile`: compile the manifest and check its examples |
| `Geb: Prove Statements` | `geb-author prove`: run proof scripts, check and save the certificate |
| `Geb: Replay Certificate` | `geb-author replay`: check the saved certificate against current statements without search |
| `Geb: Show Kernel Holes` | `geb-kernel holes --manifest`: display the context and type of each kernel-language hole |
| `Geb: Record Development` | `preserve.py record --certificate`: retain the development using its saved proof |
| `Geb: Verify Record Integrity` | `preserve.py verify`: check the record's inventory and hashes |
| `Geb: Check Recorded Development` | `preserve.py check`: compile archived sources and replay the saved certificate |
| `Geb: Compare Sources with Record` | `preserve.py compare`: compare current sources with the record and replay its certificate |

Compilation, proof commands, terminal hole reporting, recording and comparison
save modified file-backed documents in the selected workspace folder
before running, and documents below the manifest's and entry proof
document's directories, including proof imports opened elsewhere.
A failed save prevents execution. Untitled buffers are not program
inputs. Integrity verification and checking an archived development do
not save buffers. Commands require a trusted, local-filesystem workspace;
syntax highlighting remains available in Restricted Mode. A remote
workspace runs the tools on its extension host.

The `proofs` field selects one entry proof document and is required by
proof, record and comparison commands. The host resolves its imports;
recording retains those documents with the entry document. These commands
use the selected manifest explicitly, including when a proof document
names its default program. The task `Geb: check saved file` instead uses
the proof document's program, independently of the editor's selection.
The optional `image` and `certificate` fields choose output paths. Their
defaults are
`.lake/geb-editor/program-NAME/program.img` and
`.lake/geb-editor/program-NAME/proof.cert`, with the display name encoded
as a URI component. Parent directories are created for those outputs.
Prove Statements shares the folder's `.lake/geb-proof-cache` with the
saved-file check. Its terminal reports how many theorems it took from
the cache and how many it proved. It replays the resulting certificate
before writing it. Integrity verification needs only Python.
A rejected program or failed proof leaves an existing output in place.
Hole reporting is limited to the kernel forms accepted by the current
host: exit status `2` means open obligations, `0` means complete, and `1`
means rejection. Open obligations are displayed without being reported
as a completed program.

A development can be compiled, proved and replayed with those commands,
then retained by `Geb: Record Development`. Recording asks for a new
directory and replays the selected certificate without proof search.
The dialog proposes `records/program-NAME` under the workspace folder;
keep retained records with the development's versioned files.
An existing record is rejected rather than replaced. The new record is
selected after successful creation; `Geb: Select Development Record`
selects another directory. An optional `record` field supplies an initial
selection, as the Roundtrip example's settings do. Integrity verification
checks no theorem; use checking or comparison for compilation and replay.
The [authoring chapter](../../manual/GebManual/Authoring.lean) describes
the records' contents and migration limits.

Commands use the public CLI and leave diagnostic text in the task
terminal. Compilation, proving and replay also publish located errors
in the Problems panel, including errors in imported proof documents.
For command keybindings, `geb.selectProgram` accepts the program's name
when unique across workspace folders, and `geb.record` accepts a new
directory path in place of the directory dialog.

## Validation

The editor suite includes unsaved imports, local and proof navigation,
scoped completion, Unicode names, recovery, outlines, workspace symbols,
buffer formatting and navigable kernel obligations. To run only that fixture,
pass `--navigation` to `node editors/vscode/test/run.cjs` after building
`geb-author`.

```sh
lake build geb-fmt geb-kernel geb-author geb-compile geb-defs
npm test --prefix editors/vscode
npm run test:editor --prefix editors/vscode
npm run test:paredit --prefix editors/vscode
```

On Linux without a graphical session, run the last two commands under
`xvfb-run -a`. The integration runner downloads the VS Code version
pinned in `package.json`, and uses separate extension and user-data
directories under `editors/vscode/node_modules/.cache/editor`. It does
not install extensions into the user's editor. The first run requires
network access.

`scripts/tests/client-acceptance.sh WORKDIR [REVISION]` accepts a client
of the shared library from a fresh clone. `WORKDIR` lies below no
`lean-toolchain`, since elan would select that file's toolchain for the
clone in place of the client's own. The script makes a client repository
from [the template](../../examples/client/README.md) with its submodule
at a revision of this repository, clones it from a bare repository,
follows the template README's build and packaging steps in the clone,
and runs `node editors/vscode/test/run.cjs --client DIRECTORY`. That
mode installs the clone's packaged Geb and patched Paredit extensions
into VS Code Insiders and runs `test/client.cjs` in the clone's folder.
The tests follow an import into the library, compile after edits of the
library's module, prove, replay and check saved files. From an empty
Lake directory the run builds the host executables, which takes an hour
or more, and it is not part of CI.

The grammar tests use VS Code's TextMate and Oniguruma libraries. The
integration tests invoke the formatter task, the check task and its
problem matcher, bracket matching and pair completion in VS Code. Their
fixtures include nested bindings, parentheses in comments, quoted
parentheses and semicolons, escaped quotes, Unicode names, multiline
atoms, CRLF and incomplete buffers.

Formatting is compared through the document formatter: equality of its
output implies equality of the parsed documents by its retraction law.
The kernel also checks the formatted programs against their originals.

The repository's tooling tests run these checks and package the extension
when its dependencies are installed. A graphical session or `xvfb-run`
is required for the integration tests. CI installs the dependencies and
runs the integration tests under Xvfb.

The command fixture uses a separate workspace folder whose path contains
spaces and Unicode. It compiles saved editor buffers, proves and replays
statements with imported proofs outside that folder, checks located
diagnostics, preserves a certificate after failed search, records without
search, checks and compares the record and its imports, rejects replacement
of a record, and distinguishes open kernel holes from a complete program.
It uses the real host commands and an isolated copy of the authoring example.

## Structural editing acceptance

The pinned build of Mike's Paredit passes the authoring profile's
[acceptance fixture](test/editor.cjs). `test:paredit` rebuilds it when
its pinned inputs have changed, installs it in a fresh extension
directory of the test instance, and tests navigation, selection,
wrapping, slurping, barfing and undo, exiting unsuccessfully if any
fixture fails. `scripts/tests/test-editor.sh` runs it, in continuous
integration among other places.

Structural edits are compared with the intended document through the
formatter; the kernel checks the resulting programs and their expected
forms. Undo must restore the original buffer exactly.

The Marketplace release 0.2.1 fails the fixture: navigation treats a
semicolon in a quoted atom as a comment and misplaces cursor offsets in
CRLF input. The following command installs the release that
`editorTest.paredit.release` names and reproduces its failures, so that
a later release, once named there, is tested against the fixture before
it replaces the patch:

```sh
npm run test:paredit-release --prefix editors/vscode
```

## References

- [VS Code process tasks](https://code.visualstudio.com/api/references/vscode-api#ProcessExecution)
- [VS Code workspace trust](https://code.visualstudio.com/api/extension-guides/workspace-trust)
- [VS Code language configuration](https://code.visualstudio.com/api/language-extensions/language-configuration-guide)
- [VS Code extension testing](https://code.visualstudio.com/api/working-with-extensions/testing-extension)
- [Mike's Paredit](https://github.com/quasarbright/vscode-paredit)
- [The authoring profile and editor decisions](../../manual/GebManual/Bootstrap.lean)
