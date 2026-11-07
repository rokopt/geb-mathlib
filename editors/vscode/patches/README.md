# Paredit compatibility patch

[paredit-0.2.1.patch](paredit-0.2.1.patch) applies to Mike's Paredit
[commit dcc13c5](https://github.com/quasarbright/vscode-paredit/commit/dcc13c5cf5438ca3236e1c7b46f3bbd089337817),
whose package version is 0.2.1. The patch and its upstream context are
under the [MIT license](paredit-LICENSE.txt).

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Changes](#changes)
- [Build and test](#build-and-test)
- [Local installation](#local-installation)

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

Start at the Geb repository root, with the prerequisites in the
[editor README](../README.md#validation) installed. The commands below
make a separate checkout of the pinned upstream source, apply the patch,
run its unit tests and build a local VSIX. The checkout remains available
for inspection at `paredit_work_dir`.

```sh
geb_root_dir="$PWD"
paredit_work_dir="$(mktemp -d)"
git clone https://github.com/quasarbright/vscode-paredit.git "$paredit_work_dir"
git -C "$paredit_work_dir" checkout --detach dcc13c5cf5438ca3236e1c7b46f3bbd089337817
patch --batch --fuzz=0 -d "$paredit_work_dir" -p1 \
  < editors/vscode/patches/paredit-0.2.1.patch
npm ci --ignore-scripts --prefix "$paredit_work_dir"
npm test --prefix "$paredit_work_dir" -- --runInBand
(
  cd "$paredit_work_dir"
  "$geb_root_dir/editors/vscode/node_modules/.bin/vsce" package \
    --no-dependencies --allow-star-activation \
    --out "$geb_root_dir/editors/vscode/paredit-0.2.1-geb.vsix"
)
GEB_PAREDIT_VSIX="$PWD/editors/vscode/paredit-0.2.1-geb.vsix" \
  npm run test:paredit --prefix editors/vscode
```

On Linux without a graphical session, put `xvfb-run -a` before `npm run`
in the last command. The runner installs the supplied VSIX in a fresh
test profile and disables automatic updates. Without `GEB_PAREDIT_VSIX`,
`test:paredit` tests the unmodified Marketplace release and reproduces
its failures.

The VSIX retains upstream's extension identifier and version. Its
filename distinguishes the local build. The Geb extension's normal
package and CI checks do not install this build; selecting a supported
distribution and submitting changes upstream remain separate decisions.

## Local installation

To try the build in a personal editor after reviewing the patch:

```sh
code --install-extension editors/vscode/paredit-0.2.1-geb.vsix --force
```

It replaces an installed Mike's Paredit 0.2.1 under the same identifier.
Disable automatic updates for that extension while trying this build,
so the installed version remains the one being evaluated. The Geb
language extension must also be installed as described in its README.
