#!/usr/bin/env bash
#
# scripts/tests/test-extract-pr.sh
#
# Tests scripts/extract-pr.sh: destination-path mapping per subtree
# and the import-line prefix rewrite (Geb.<Subtree>. -> <Subtree>.).
# Offline and deterministic.

set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SCRIPT="$here/../extract-pr.sh"

failed=0
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cd "$tmp" || exit 1

has() { # name needle file
  if grep -qF "$2" "$3"; then echo "PASS: $1"; else
    echo "FAIL: $1 (missing '$2' in $3)"; failed=1; fi
}
lacks() { # name needle file
  if grep -qF "$2" "$3"; then
    echo "FAIL: $1 (unexpected '$2' in $3)"; failed=1; else echo "PASS: $1"; fi
}
exists() { # name path
  if [ -f "$2" ]; then echo "PASS: $1"; else echo "FAIL: $1 (no $2)"; failed=1; fi
}

# Geb/Mathlib -> Mathlib/, import and public import rewritten.
mkdir -p Geb/Mathlib/Foo fork1
cat > Geb/Mathlib/Foo/Bar.lean <<'EOF'
module
public import Geb.Mathlib.Foo.Baz
import Geb.Mathlib.Other
import Mathlib.Tactic
EOF
bash "$SCRIPT" Geb/Mathlib/Foo/Bar.lean fork1 >/dev/null
out=fork1/Mathlib/Foo/Bar.lean
exists "Geb/Mathlib -> Mathlib path" "$out"
has   "public import rewritten" "public import Mathlib.Foo.Baz" "$out"
has   "import rewritten"        "import Mathlib.Other" "$out"
has   "foreign mathlib import preserved" "import Mathlib.Tactic" "$out"
lacks "no Geb.Mathlib. prefix remains"  "Geb.Mathlib." "$out"

# GebTests/Mathlib -> MathlibTest/.
mkdir -p GebTests/Mathlib fork2
printf 'module\nimport Geb.Mathlib.X\n' > GebTests/Mathlib/Y.lean
bash "$SCRIPT" GebTests/Mathlib/Y.lean fork2 >/dev/null
exists "GebTests/Mathlib -> MathlibTest path" "fork2/MathlibTest/Y.lean"

# Geb/Cslib -> Cslib/; a prefix embedded in a non-import line is left
# alone (import-anchored rewrite).
mkdir -p Geb/Cslib fork3
cat > Geb/Cslib/Z.lean <<'EOF'
module
import Geb.Cslib.A
-- mentions XGeb.Cslib.embedded in a comment
EOF
bash "$SCRIPT" Geb/Cslib/Z.lean fork3 >/dev/null
has   "cslib import rewritten" "import Cslib.A" "fork3/Cslib/Z.lean"
has   "embedded non-import ref untouched" "XGeb.Cslib.embedded" "fork3/Cslib/Z.lean"

if [ "$failed" -ne 0 ]; then
  echo "test-extract-pr.sh: failures"
  exit 1
fi
echo "test-extract-pr.sh: all checks passed"
