#!/usr/bin/env bash
#
# scripts/tests/test-axiom-linter.sh
#
# Smoke test for the GebMeta.detectNonstandardAxiom env_linter.
# Stages throwaway fixtures in a temp directory: a violating one
# (a theorem proved via a custom axiom) that the linter must reject,
# and a clean one that it must accept. Nothing axiom-violating is
# committed to the repository.
#
# Exit 0 if both scenarios behave; non-zero otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
failed=0

# The `#lint` command is provided by `Batteries.Tactic.Lint`; the
# linter itself is registered via `import GebMeta`. The env_linter
# is selected by its base name `detectNonstandardAxiom`.
cat > "$tmp/Bad.lean" <<'EOF'
import GebMeta
import Batteries.Tactic.Lint
axiom badAx : (1 : Nat) = 2
theorem usesBad : (1 : Nat) = 2 := badAx
#lint only detectNonstandardAxiom
EOF

cat > "$tmp/Good.lean" <<'EOF'
import GebMeta
import Batteries.Tactic.Lint
theorem fine : True := True.intro
#lint only detectNonstandardAxiom
EOF

out_bad="$(lake env lean "$tmp/Bad.lean" 2>&1)"
rc_bad=$?
if [[ "$rc_bad" -eq 0 ]]; then
  echo "FAIL: linter accepted a declaration using a non-standard axiom" >&2
  echo "  output: $out_bad" >&2
  failed=1
fi
if ! grep -qF 'badAx' <<<"$out_bad"; then
  echo "FAIL: violation output did not name the offending axiom 'badAx'" >&2
  echo "  output: $out_bad" >&2
  failed=1
fi

out_good="$(lake env lean "$tmp/Good.lean" 2>&1)"
rc_good=$?
if [[ "$rc_good" -ne 0 ]]; then
  echo "FAIL: linter rejected clean code" >&2
  echo "  output: $out_good" >&2
  failed=1
fi

if [[ "$failed" -ne 0 ]]; then
  echo "test-axiom-linter: FAIL" >&2
  exit 1
fi
echo "test-axiom-linter: ok"
exit 0
