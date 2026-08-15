#!/usr/bin/env bash
#
# scripts/test-tooling.sh
#
# Run the self-tests of the repository's own tooling: the scripts
# under scripts/ and the Claude Code hooks under scripts/hooks/.
# Checks over repository content are a separate concern and live in
# scripts/pre-push.sh; scripts/pre-push-full.sh runs both.
#
# Tests are discovered by glob, so a new scripts/tests/test-*.sh or
# scripts/hooks/tests/test-*.sh runs by virtue of existing.
#
# Several tests drive `lake` (`lake shake`, `lake env lean`,
# `lake lint`) against the live project and so require a built tree
# with the mathlib olean cache populated. pre-push-full.sh satisfies
# that by running pre-push.sh first; a standalone run needs a prior
# `lake build`.
#
# Exits non-zero if any test fails.

set -uo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

failed=0
checked=0

for test_script in scripts/tests/test-*.sh scripts/hooks/tests/test-*.sh; do
  checked=$((checked + 1))
  if ! bash "$test_script"; then
    echo "FAIL: $test_script" >&2
    failed=$((failed + 1))
  fi
done

if [ "$failed" -ne 0 ]; then
  echo "test-tooling: $failed of $checked tooling test(s) failed" >&2
  exit 1
fi
echo "test-tooling: $checked tooling test(s) passed"
