#!/usr/bin/env bash
#
# scripts/manual.sh
#
# Build or serve the Verso manual (the GebManual library and the
# geb-manual generator). Runs from the repository root regardless
# of the invoking directory: the lint's nolints path
# (scripts/nolints.json) and the generator's --output path are
# both resolved against the working directory.
#
# CI (doc-build.yml) and scripts/pre-push-full.sh run the build
# verb; the manual is otherwise outside every default build, test,
# and lint path. A chapter that includes a literate module runs
# `lake query +Mod:literate` in a subprocess while it elaborates,
# which builds that module's literate facet on demand.

set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

case "${1:-}" in
  build)
    lake build GebManual
    lake lint -- GebManual
    # The generator links a dependency's C sources (leansqlite's
    # bundled SQLite), whose compiler warnings Lake logs, and replays
    # on every later run, at its informational level. Warnings and
    # errors, the levels a Lean message of this repository reaches,
    # stay visible; the two steps above compile the manual's own Lean
    # at the default level.
    lake exe --log-level=warning geb-manual --output manual/_out
    ;;
  serve)
    # verso-serve.toml mounts the manual and the literate site
    # together, as pages.yml deploys them.
    exec lake exe verso-serve
    ;;
  *)
    cat >&2 <<'EOF'
usage: scripts/manual.sh {build|serve}

  build  Build the GebManual library, lint it, and generate the
         HTML into manual/_out/html-multi.
  serve  Serve the manual at / and the literate site (built by
         scripts/literate.sh build) at /literate, the layout
         GitHub Pages serves, with verso-serve, which prints the
         URL it binds (port 8000, or a higher free port when 8000
         is taken).

There is no watch mode: after editing, re-run 'build' and refresh
the browser. Lake rebuilds only the changed modules.
EOF
    exit 2
    ;;
esac
