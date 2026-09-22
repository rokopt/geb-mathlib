#!/usr/bin/env bash
#
# scripts/pre-push-full.sh
#
# Run the whole pre-push checklist: the content checks in
# scripts/pre-push.sh, including the Verso builds of the manual and
# the literate site, and the tooling self-tests in
# scripts/test-tooling.sh. Use it for a change that touches the build
# system itself. A change confined to the Lean sources and Markdown
# that the build system acts on is covered by scripts/pre-push.sh
# alone.
#
# pre-push.sh runs first because several tooling tests drive `lake`
# against the live project, and so need the built tree and populated
# olean cache that pre-push.sh's `lake exe cache get` and `lake build`
# steps leave behind.
#
# Exits non-zero on any failure.

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lint_log="$(mktemp)"
trap 'rm -f "$lint_log"' EXIT
export GEB_LINT_LOG="$lint_log"

bash scripts/pre-push.sh
bash scripts/test-tooling.sh
