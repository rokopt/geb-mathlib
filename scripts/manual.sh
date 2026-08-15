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
# CI (doc-build.yml) runs the build verb; the manual is otherwise
# outside every default build, test, and lint path.

set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

case "${1:-}" in
  build)
    lake build GebManual
    lake lint -- GebManual
    lake exe geb-manual --output manual/_out
    ;;
  serve)
    exec lake exe verso-serve manual/_out/html-multi
    ;;
  *)
    cat >&2 <<'EOF'
usage: scripts/manual.sh {build|serve}

  build  Build the GebManual library, lint it, and generate the
         HTML into manual/_out/html-multi.
  serve  Serve manual/_out/html-multi with verso-serve, which
         prints the URL it binds (port 8000, or a higher free
         port when 8000 is taken).

There is no watch mode: after editing, re-run 'build' and refresh
the browser. Lake rebuilds only the changed modules.
EOF
    exit 2
    ;;
esac
