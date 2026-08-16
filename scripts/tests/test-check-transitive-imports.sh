#!/usr/bin/env bash
#
# scripts/tests/test-check-transitive-imports.sh
#
# Smoke test for scripts/check-transitive-imports.sh. Stages synthetic
# Geb/, GebTests/ and GebLang/ trees under a temp directory and runs
# the checker against a clean state and against induced failures from
# both root kinds and from the second pass.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
checker="$repo_root/scripts/check-transitive-imports.sh"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

failed=0
checked=0

setup_empty() {
  rm -rf "$test_dir"
  mkdir -p "$test_dir/Geb/Mathlib" "$test_dir/Geb/Cslib" \
           "$test_dir/GebTests/Mathlib" "$test_dir/GebTests/Cslib" \
           "$test_dir/GebTests/Lang" "$test_dir/GebLang"
}

assert_case() {
  local name="$1" expected_exit="$2" expected_substr="$3"
  checked=$((checked + 1))
  local output exit_code
  output="$(cd "$test_dir" && bash "$checker" 2>&1)"
  exit_code=$?
  if [[ "$exit_code" -ne "$expected_exit" ]]; then
    echo "FAIL: $name: expected exit $expected_exit, got $exit_code" >&2
    echo "  output: $output" >&2
    failed=$((failed + 1))
    return
  fi
  if [[ -n "$expected_substr" ]] && ! grep -qF "$expected_substr" <<<"$output"; then
    echo "FAIL: $name: expected substring '$expected_substr' not in output" >&2
    echo "  output: $output" >&2
    failed=$((failed + 1))
    return
  fi
}

# A mathlib-track GebLang dependency: clean.
setup_empty
printf 'module\nimport Mathlib.Tactic\n' > "$test_dir/GebLang/Base.lean"
printf 'module\nimport GebLang.Base\n' > "$test_dir/Geb/Mathlib/Foo.lean"
assert_case "mathlib-track GebLang dependency" 0 "clean"

# A Geb/Mathlib/ root whose GebLang dependency reaches Cslib.
setup_empty
printf 'module\nimport Cslib.Init\n' > "$test_dir/GebLang/Cs.lean"
printf 'module\nimport GebLang.Cs\n' > "$test_dir/Geb/Mathlib/Foo.lean"
assert_case "Geb/Mathlib root reaching Cslib" 1 \
  "Geb/Mathlib/Foo.lean: its import closure reaches Cslib.*"

# The same failure from the test mirror's root kind, and through one
# more hop, so the walk's transitivity is exercised.
setup_empty
printf 'module\nimport Cslib.Init\n' > "$test_dir/GebLang/Cs.lean"
printf 'module\nimport GebLang.Cs\n' > "$test_dir/GebLang/Mid.lean"
printf 'module\nimport GebLang.Mid\n' > "$test_dir/GebTests/Mathlib/Foo.lean"
assert_case "GebTests/Mathlib root reaching Cslib transitively" 1 \
  "GebTests/Mathlib/Foo.lean: its import closure reaches Cslib.*"

# Pass 2: a Cslib-track test importing a mathlib-track sibling.
setup_empty
printf 'module\nimport Mathlib.Tactic\n' > "$test_dir/GebLang/Base.lean"
printf 'module\nimport GebLang.Base\n' > "$test_dir/GebTests/Lang/MSib.lean"
printf 'module\nimport Cslib.Init\nimport GebTests.Lang.MSib\n' \
  > "$test_dir/GebTests/Lang/CsMain.lean"
assert_case "cslib-track test importing a mathlib-track sibling" 1 \
  "Cslib-track test imports the mathlib-track sibling GebTests.Lang.MSib"

# Pass 2: a Cslib-track test importing a Cslib-track sibling is clean.
setup_empty
printf 'module\nimport Cslib.Init\n' > "$test_dir/GebTests/Lang/CsSib.lean"
printf 'module\nimport Cslib.Init\nimport GebTests.Lang.CsSib\n' \
  > "$test_dir/GebTests/Lang/CsMain.lean"
assert_case "cslib-track test importing a cslib-track sibling" 0 "clean"

echo "test-check-transitive-imports.sh: $checked case(s) checked, $failed failure(s)"
exit "$failed"
