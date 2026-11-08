# Paredit compatibility patch

[paredit-0.2.1.patch](paredit-0.2.1.patch) applies to Mike's Paredit
[commit dcc13c5](https://github.com/quasarbright/vscode-paredit/commit/dcc13c5cf5438ca3236e1c7b46f3bbd089337817),
whose package version is 0.2.1. The patch and its upstream context are
under the [MIT license](paredit-LICENSE.txt).

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Changes](#changes)
- [Build and test](#build-and-test)

<!-- END doctoc -->

## Changes

- Comment detection uses the lexer's string tokens to exclude comment
  markers in quoted atoms, including escaped quotes and multiline
  strings. Scanning the prefix before a comment preserves an adjacent
  atom and the string state at the comment's start.
- The document model retains each line's terminator and the original
  text. Model and token-cursor offsets count CRLF as two UTF-16 code
  units; text moved by an edit retains its original line endings.
- Slurp and barf skip comments when locating expressions, and traverse
  quoted atoms as whole expressions. This keeps a moved delimiter out
  of a comment or quoted atom.

The patch includes unit regressions in upstream's Jest test format. The
Geb [editor acceptance suite](../test/editor.cjs) also checks navigation,
selection, wrap, slurp, barf and undo in VS Code, with LF and CRLF input.
It compares edits with the intended parsed documents and checks their
resulting programs with `geb-kernel`.

## Build and test

[`build.sh`](build.sh), which `npm run build:paredit --prefix
editors/vscode` runs, fetches the commit that `package.json` pins under
`editorTest.paredit` into a temporary checkout, applies the patch
without fuzz, runs upstream's unit tests, sets the version that
`package.json` names, and packages
`editors/vscode/paredit-<version>.vsix`. It records the build's inputs,
the repository, the commit, the version and the patch's digest, beside
the VSIX, and builds again only when they change. `npm run test:paredit
--prefix editors/vscode` builds and then tests the VSIX; the
[editor README](../README.md) describes the tests and the installation.

To inspect the patched source, apply the patch to a checkout of the
pinned commit:

```sh
git clone https://github.com/quasarbright/vscode-paredit.git vscode-paredit
git -C vscode-paredit checkout --detach dcc13c5cf5438ca3236e1c7b46f3bbd089337817
patch --batch --fuzz=0 -d vscode-paredit -p1 < editors/vscode/patches/paredit-0.2.1.patch
```

The version, `0.2.1+geb.1`, adds build metadata to the release's, so it
has the precedence of 0.2.1 and the release is not offered as its
update. A change to the patch increments its final number.
