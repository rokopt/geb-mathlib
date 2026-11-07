# Geb for VS Code

The `geb` language supports the Geb authoring profile: parentheses,
semicolon line comments, quoted atoms with escapes and embedded line
breaks, numerals, and named holes. The extension is declarative; it
registers the language, its TextMate grammar and its editing configuration.
It does not change the compiler's grammar.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Installation](#installation)
- [Editing and formatting](#editing-and-formatting)
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

## Validation

```sh
lake build geb-fmt geb-kernel
npm test --prefix editors/vscode
npm run test:editor --prefix editors/vscode
```

On Linux without a graphical session, run the last command under
`xvfb-run -a`. The integration runner downloads the VS Code version
pinned in `package.json`, and uses separate extension and user-data
directories under `editors/vscode/node_modules/.cache/editor`. It does
not install extensions into the user's editor. The first run requires
network access.

The grammar tests use VS Code's TextMate and Oniguruma libraries. The
integration tests invoke the formatter task, bracket matching and pair
completion in VS Code. Their fixtures include nested bindings,
parentheses in comments, quoted parentheses and semicolons, escaped
quotes, Unicode names, multiline atoms, CRLF and incomplete buffers.

Formatting is compared through the document formatter: equality of its
output implies equality of the parsed documents by its retraction law.
The kernel also checks the formatted programs against their originals.

The repository's tooling tests run these checks and package the extension
when its dependencies are installed. A graphical session or `xvfb-run`
is required for the integration tests. CI installs the dependencies and
runs the integration tests under Xvfb.

## Structural editing acceptance

Mike's Paredit 0.2.1 does not pass the authoring profile's
[acceptance fixture](test/editor.cjs). Navigation treats a semicolon
in a quoted atom as a comment and
misplaces cursor offsets in CRLF input. The extension therefore does not
install or recommend Paredit, and structural editing remains pending.

A [source patch and reproduction instructions](patches/README.md) are
available for review. A supplied VSIX can be tested in a fresh extension
directory by setting `GEB_PAREDIT_VSIX` to its absolute path when running
`test:paredit`. The choice of a supported distribution remains separate
from these tests.

The failing examples and the other structural commands can be tested
with the pinned release in an isolated VS Code instance:

```sh
npm run test:paredit --prefix editors/vscode
```

This command installs the Paredit version pinned in `package.json` into
the test instance. It tests navigation, selection, wrapping, slurping,
barfing and undo, and exits unsuccessfully while any fixture fails.
Structural edits are compared with the intended document through the
formatter; the kernel checks the resulting programs and their expected
forms. Undo must restore the original buffer exactly.

## References

- [VS Code language configuration](https://code.visualstudio.com/api/language-extensions/language-configuration-guide)
- [VS Code extension testing](https://code.visualstudio.com/api/working-with-extensions/testing-extension)
- [Mike's Paredit](https://github.com/quasarbright/vscode-paredit)
- [The authoring profile and editor decisions](../../manual/GebManual/Bootstrap.lean)
