#!/usr/bin/env bash
#
# scripts/tests/test-check-md-links.sh
#
# Smoke test for scripts/check-md-links.sh. Stages synthetic Markdown
# files under a temp directory and runs the checker against them by
# explicit path, covering resolving and dangling targets, the forms the
# checker ignores, and the code-span exclusion.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
checker="$repo_root/scripts/check-md-links.sh"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

failed=0
checked=0

# Run the checker from $test_dir on the named files; assert the exit
# code, and (when non-empty) that the output contains the substring.
assert_case() {
  local name="$1" expected_exit="$2" expected_substr="$3"
  shift 3
  checked=$((checked + 1))
  local output exit_code
  output="$(cd "$test_dir" && bash "$checker" "$@" 2>&1)"
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
  echo "PASS [$name]"
}

mkdir -p "$test_dir/docs/rules"
: >"$test_dir/target.md"
: >"$test_dir/docs/sibling.md"
: >"$test_dir/docs/rules/nested.md"

printf '[a](target.md)\n' >"$test_dir/root-ok.md"
printf '[a](missing.md)\n' >"$test_dir/root-dangling.md"
printf '[a](sibling.md)\n' >"$test_dir/docs/rel-ok.md"
printf '[a](../target.md)\n[b](rules/nested.md)\n' >"$test_dir/docs/updir-ok.md"
printf '[a](target.md#heading)\n' >"$test_dir/frag-ok.md"
printf '[a](target.md#no-such-heading)\n' >"$test_dir/frag-unchecked.md"
printf '[a](#local-section)\n' >"$test_dir/anchor-only.md"
printf '[a](https://example.invalid/x.md)\n[b](mailto:x@example.invalid)\n' \
  >"$test_dir/external.md"
printf 'Internal links look like `[name](docs/foo.md)` in prose.\n' \
  >"$test_dir/code-span.md"
printf '[a](target.md)\n[b](gone.md)\n[c](also-gone.md)\n' >"$test_dir/multi.md"

assert_case "resolving target at root" 0 "all Markdown link targets resolve" root-ok.md
assert_case "dangling target reported" 1 "root-dangling.md: link target does not exist: missing.md" \
  root-dangling.md
assert_case "sibling resolved relative to file" 0 "" docs/rel-ok.md
assert_case "parent and subdirectory targets" 0 "" docs/updir-ok.md
assert_case "fragment stripped before check" 0 "" frag-ok.md
assert_case "fragment itself not checked" 0 "" frag-unchecked.md
assert_case "pure anchor ignored" 0 "" anchor-only.md
assert_case "external targets ignored" 0 "" external.md
assert_case "link inside code span ignored" 0 "" code-span.md
assert_case "every dangling target reported" 1 "2 unresolved link target(s)" multi.md
assert_case "clean and dangling files together" 1 "gone.md" root-ok.md multi.md

# The regression this checker exists for: a document that outlives the
# transient file it links (CONTRIBUTING.md § Concern shape removes specs
# and plans in a branch's final commits).
printf '[spec](docs/superpowers/specs/design.md)\n' >"$test_dir/outlived-spec.md"
assert_case "link to removed transient spec" 1 "docs/superpowers/specs/design.md" outlived-spec.md

if [[ "$failed" -ne 0 ]]; then
  echo "test-check-md-links: $failed of $checked checks failed" >&2
  exit 1
fi

echo "test-check-md-links: all $checked checks passed"
