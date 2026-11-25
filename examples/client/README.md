# A Geb client

This directory is the template of a client of the shared Geb library,
laid out as the root of a repository of its own. Its program,
`client.manifest`, names `geb/library/library.manifest` as its library
layer. The library supplies its sources in order before the client's.
`Client.geb` imports the library's module `Lists` and uses its generic
functions at the trees. `Copy.geb` imports the library's module
`Requests` and copies the file that an index names by requests of the
host, writing a line of its own where that file is missing.
`Settings.geb` saves a datatype of the client's, the order in which it
writes a file's bytes, in the envelope of the library's module `Saved`,
which names the datatype and the version of its encoding. `Upgrade.geb`
migrates an order that the client's previous revision saved at version 1,
before `Settings.Order` declared `reversed`; the Geb repository's
`examples/client-upgrade/` keeps that revision.
`Client.proofs.geb` imports the library's proof document, so that the
library's theorems are proved again against the client's program, and
adds a theorem of the client's.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The pinned dependencies](#the-pinned-dependencies)
- [Creating the repository](#creating-the-repository)
- [Pinning a release](#pinning-a-release)
- [From a fresh clone](#from-a-fresh-clone)
- [In the editor](#in-the-editor)
- [Continuous integration](#continuous-integration)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## The pinned dependencies

The Geb repository is a Git submodule at `geb/`. The submodule's commit
pins the Geb revision, which supplies the toolchain, the host
executables and the editor extensions, and the library revision, since
the library is the directory `library/` of the same repository. A
manifest's sources lie below its directory, and the submodule places the
library's sources below the client's manifest without copying them.

A release of Geb can take the submodule's place (§ Pinning a release).
It holds the host executables, built, and the library's sources, so that
a client that does not change the library needs neither Lake nor the
build of the executables.

## Creating the repository

Copy this directory to the new repository's root and add the submodule
at the Geb revision to pin:

```sh
git init
git submodule add https://github.com/rokopt/geb-mathlib geb
git -C geb checkout REVISION
git add .
```

Changing the pinned revision is `git -C geb checkout REVISION` followed
by `git add geb`, then a check of the client (§ Continuous integration).

## Pinning a release

A release holds the host tools and library in
`geb-TAG-PLATFORM.tar.gz` for Linux x86-64, Linux Arm64 and macOS
on Apple silicon. To create a release-based client, copy this template
into the new repository. If converting a submodule-based client,
remove the submodule with `git rm geb` first. Set `tag` to the chosen
release tag and pin the published archive checksums in the client.

```sh
tag=TAG
assets=$(mktemp -d)
gh release download "$tag" --repo rokopt/geb-mathlib --pattern '*.tar.gz.sha256' --dir "$assets"
cat "$assets"/*.tar.gz.sha256 > geb-release.sha256
printf '/geb/\n' >> .gitignore
git add geb-release.sha256 .gitignore
```

Commit the pin with the client. On each machine, `fetch-geb.sh` downloads
that platform's archive, checks its digest and extracts it at `geb/`.
Development records need a checkout, and an edit of the library is an
edit of the checkout, so a client that does either keeps the submodule.

## From a fresh clone

For a release pin, clone the client and run these commands from its
root. The first command installs the host executables and library.
`check.sh` runs the same manifest, examples and proofs as the client's CI.
The two VSIX files come from the tag recorded in the installed archive.

```sh
bash fetch-geb.sh
bash check.sh
tag=$(python3 -c 'import json; print(json.load(open("geb/geb-release.json"))["version"])')
assets=$(mktemp -d)
gh release download "$tag" --repo rokopt/geb-mathlib --pattern '*.vsix' --dir "$assets"
code-insiders --install-extension "$assets/geb-language.vsix" --force
code-insiders --install-extension "$assets/geb-paredit.vsix" --force
code-insiders .
```

For a submodule pin, use Lean's `elan` and Node.js 22 or later.

```sh
git clone --recurse-submodules URL client
cd client
(cd geb && lake exe cache get)
lake -d geb build geb-author geb-kernel geb-fmt geb-compile geb-defs
```

The default `lake build` of the Geb checkout builds its Lean library and
no executable; the second command builds the host executables the
editor runs ([the extension's README](../../editors/vscode/README.md)
§ Installation). Install the Geb extension and the patched build of
Mike's Paredit into VS Code Insiders:

```sh
npm ci --prefix geb/editors/vscode
npm run package --prefix geb/editors/vscode
npm run build:paredit --prefix geb/editors/vscode
code-insiders --install-extension geb/editors/vscode/geb-language.vsix
code-insiders --install-extension 'geb/editors/vscode/paredit-0.2.1+geb.1.vsix' --force
```

## In the editor

Open the client's directory as the workspace folder. Its settings name
`geb` as the toolchain directory and select the program `Client`, so
that editor commands use the pinned host tools and read the client's
files where they are. With a release the editor runs the packaged
executables directly. With a submodule the first use checks the tools
through Lake and later commands reuse them until their inputs change.

- Go to Definition on `reverse` in `Client.geb` opens its definition in
  `geb/library/Lists.geb`, and Hover shows its documentation.
- `Geb: Compile Program` compiles the program and checks the examples of
  its notes, the library's and the client's.
- `Geb: Run Program on a File` compiles the program and applies the entry
  point `Client.run`, a definition from trees to trees, to a file it asks
  for, writing the output file it asks for.
- `Geb: Run Program with Requests` compiles the program and runs the
  entry point `Copy.step` with the arguments it asks for, the path of an
  index and the path of an output, relative to the client's directory.
  With the entry point `Settings.choose` and the arguments `m` and a
  path it saves the order `mirrored` there, with `Settings.apply` and
  that path, an input's and an output's it writes the input mirrored, and
  with `Upgrade.migrate` it writes at the current version an order saved
  at version 1.
- `Geb: Prove Statements` uses the client's `.lake/geb-proof-cache`
  to prove `Client.proofs.geb` and the library's
  document it imports and saves the certificate;
  `Geb: Replay Certificate` replays it without search.
- The task `Geb: check saved file` checks the active file against the
  program that lists it, the client's for `Client.geb` and the library's
  for a source under `geb/library/`.

An edit of a library module is an edit of the submodule's working tree,
which the client's checks read at once. It is kept by a commit of the
Geb repository and a new pin of the submodule.

The Geb repository's `scripts/tests/client-acceptance.sh` follows these
steps from a fresh clone of a repository made from this template, in
VS Code Insiders.

## Continuous integration

`check.sh` compiles the program and checks its examples, proves its
theorems and replays their certificate, with the manifest and proof
document the editor's settings select, runs `Copy.step` where the
file its index names exists and where it is missing, and saves, applies
and migrates an order of `Settings.Order`.
`.github/workflows/check.yml` runs it after building the host
executables of the submodule, or after fetching the pinned release where
`geb-release.sha256` exists. The Geb repository's
`scripts/tests/test-client.sh` runs it on this template, with that
repository's checkout in place of the submodule.

## References

- [Writing a Geb program](https://rokopt.github.io/geb-mathlib/Writing-a-Geb-program/)
- [The Geb extension for VS Code](../../editors/vscode/README.md)
- [Writing a first Geb development](../../manual/GebManual/Authoring.lean)
- [Git submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules)
