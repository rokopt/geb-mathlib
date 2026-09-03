#!/usr/bin/env bash
#
# scripts/literate.sh
#
# Build or serve the Verso literate site for the Geb and GebLang
# libraries: every module of both rendered as a page, which is the
# check that each is literate (docs/rules/lean-coding.md § Literate
# modules). Runs from the repository root regardless of the invoking
# directory: the lint's nolints path (scripts/nolints.json) is
# resolved against the working directory. literate.toml and the
# site's output path are resolved against the package root by the
# literateHtml facet, so they are unaffected either way.
#
# CI (doc-build.yml) and scripts/pre-push-full.sh run the build verb.
# The libraries themselves are the defaultTargets, so an ordinary lake
# build compiles them; only the rendering is confined to this script.

set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

case "${1:-}" in
  build)
    lake build
    # The driver argument (lakefile.toml lintDriverArgs) is prepended,
    # so this lints Geb and GebLang both.
    lake lint -- GebLang
    lake build :literateHtml
    ;;
  serve)
    site="$(lake query :literateHtml)"
    exec lake exe verso-serve "$site"
    ;;
  *)
    cat >&2 <<'EOF'
usage: scripts/literate.sh {build|serve}

  build  Build the Geb and GebLang libraries, lint them, and render
         the literate site. The first run compiles Verso's literate
         executables from source, which takes minutes; later runs
         are incremental.
  serve  Serve the rendered site with verso-serve, which prints the
         URL it binds (port 8000, or a higher free port when 8000 is
         taken). Its first run compiles verso-serve, one more
         executable than 'build' needs.

There is no watch mode: after editing a docstring, re-run 'build' and
refresh the browser. Lake rebuilds only the changed modules.
EOF
    exit 2
    ;;
esac
