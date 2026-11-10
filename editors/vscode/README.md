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

In this repository, save the buffer and run the VS Code task
`Geb: format saved file`. It invokes `lake exe geb-fmt` with the active
file as a process argument, including when its path contains spaces.
The formatter keeps the parsed document, including comments, and writes
its chosen layout. Malformed input leaves the file unchanged. The task
requires the project's Lean toolchain and dependencies. Formatting on
save is disabled for Geb.

The formatter and the document type are described in the
[bootstrap chapter](../../manual/GebManual/Bootstrap.lean).

## Diagnostics

The task `Geb: check saved file` runs `lake exe geb-author check` on the
active file, and the command writes nothing. For a source of a program it
compiles the sources of the nearest manifest that lists the file, up to
that file, or the file alone where no manifest lists it. It reports what
rejects the program as `FILE:LINE:COLUMN: error: MESSAGE`, at the name of
the first failing declaration, at an atom the implementation reserves, or
at the character or parenthesis at which the text does not read. For a
proof document, a file holding a form `(proofs V …)`, it proves the
document, after the documents it imports, against the program the
document names by `(program NAME)`, and reports a theorem whose statement
or script does not read, or whose script does not prove it, at the
theorem's name. The extension contributes the problem matcher `$geb`,
which the task names, so that the report appears in the Problems view and
at its position in the file that holds it, which may be an earlier source
of the program or an imported document.

For an editor with a language-server client,
[`editors/efm-langserver/config.yaml`](../efm-langserver/config.yaml)
configures [efm-langserver](https://github.com/mattn/efm-langserver) to
run the same command when a buffer is saved.

## Programs and commands

The workspace settings list the programs available to the editor. This
repository configures the Pair and Roundtrip examples and the Tree cases
proof development. For another program, add an entry to `geb.programs`
in the workspace folder's settings:

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

Compilation, proof commands, hole reporting, recording and comparison
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
Commands that compile or check proofs build their host tools through
Lake before using them; integrity verification needs only Python.
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
