#!/usr/bin/env bash
#
# scripts/shake.sh
#
# The minimised-imports check, run by scripts/pre-push.sh and by CI:
# `lake shake` over Geb and GebTests. A failing report passes when
# each of its suggestions stems from a matcher congruence lemma that
# `lake shake` attributes to a module the reported module does not
# import (scripts/lib/shake-congr-eq.py). Requires built oleans for
# both libraries.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

report="$(lake shake --add-public --keep-implied --keep-prefix --explain \
  Geb GebTests 2>&1)" \
  || python3 scripts/lib/shake-congr-eq.py <<<"$report"
