# A Geb client

This directory is the template of a client of the shared Geb library,
laid out as the root of a repository of its own. Its program,
`client.manifest`, lists the library's sources, `library/seq.geb` and
`library/Bytes.geb` of a Geb checkout at `geb/`, in the order of the
library's manifest, before its own source `Client.geb`, which imports
the library's module `Bytes` and the instance `(Seq T)` of its
parameterized module `Seq`. `Client.proofs.geb` imports the library's
proof document, so that the library's theorems are proved again against
the client's program, and adds a theorem of the client's.

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

A release of the Geb repository, made by its workflow
`.github/workflows/release.yml` at a tag, holds an archive
`geb-VERSION-PLATFORM.tar.gz` for each platform it is built on, beside
the archive's SHA-256 sum, and the two editor extensions. Write the
lines of the sums of the platforms the client is built on into
`geb-release.sha256`, in place of the submodule:

```sh
git rm geb
printf '/geb/\n' >> .gitignore
cat geb-VERSION-*.tar.gz.sha256 > geb-release.sha256
bash fetch-geb.sh
```

`fetch-geb.sh` downloads the archive of the machine's platform, checks it
against the pinned sum and extracts it at `geb/`, where the editor's
settings and `check.sh` read it as they read a checkout. It refuses a
`geb/` that is not a release. Install the editor extensions from the
release's `.vsix` files with `code-insiders --install-extension`.
Development records need a checkout, and an edit of the library is an
edit of the checkout, so a client that does either keeps the submodule.

## From a fresh clone

With Lean's `elan` and Node.js 22 or later installed:

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
that editor commands use the submodule's host tools and read the client's
files where they are. The first use checks the tools through Lake. Later
commands reuse them until their build inputs or executables change.

- Go to Definition on `Bytes.reverse` in `Client.geb` opens its
  definition in `geb/library/Bytes.geb`, and Hover shows its
  documentation.
- `Geb: Compile Program` compiles the program and checks the examples of
  its notes, the library's and the client's.
- `Geb: Run Program on a File` compiles the program and applies the entry
  point `Client.run`, a definition from trees to trees, to a file it asks
  for, writing the output file it asks for.
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
document the editor's settings select.
`.github/workflows/check.yml` runs it after building the host
executables of the submodule, or after fetching the pinned release where
`geb-release.sha256` exists. The Geb repository's
`scripts/tests/test-client.sh` runs it on this template, with that
repository's checkout in place of the submodule.

## References

- [The Geb extension for VS Code](../../editors/vscode/README.md)
- [Writing a first Geb development](../../manual/GebManual/Authoring.lean)
- [Git submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules)
