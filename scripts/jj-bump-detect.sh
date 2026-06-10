#!/usr/bin/env bash
#
# scripts/jj-bump-detect.sh
#
# Decide whether a jj release-binary bump should proceed, and to
# which version. Writes `target=<version>` (empty when no bump)
# to stdout and, when set, to $GITHUB_OUTPUT. Versions are bare
# (e.g. 0.43.0), matching scripts/jj-version; the GitHub release
# tag and asset name add the `v` prefix (scripts/install-jj.sh
# prepends it, so an unstripped emission would build a
# jj-vv<version> asset URL).
#
# A version is emitted only when all hold:
#   1. the latest jj release is semver-greater than the pin in
#      scripts/jj-version. `GET /releases/latest` excludes drafts
#      and prereleases server-side; the semver comparison guards
#      against the endpoint surfacing an older release (e.g.
#      after a yanked release);
#   2. the release carries the x86_64 musl asset that
#      scripts/install-jj.sh downloads (a published tag whose
#      binaries are still uploading must not produce a broken
#      bump PR);
#   3. no bump is in flight (no open PR on auto-update-jj/patch,
#      no open issue labelled jj-bump-fail).
#
# Detection needs network (gh, `npx` fetching semver). Failures
# fail loudly (exit 1) rather than emitting an empty target, so
# an outage is never mistaken for "already current".

set -uo pipefail
# -e is intentionally omitted: bump_in_flight returns 1 on the
# common "not in flight" success path, which set -e would treat
# as fatal. All real failures are handled explicitly (if ! ...,
# || return 2, and the flight=$? capture in main).

JJ_REPO="jj-vcs/jj"
BUMP_BRANCH="auto-update-jj/patch"
FAIL_LABEL="jj-bump-fail"

# Read the bare pinned version, whitespace-stripped (same read as
# scripts/install-jj.sh).
read_jj_pin() {
  tr -d '[:space:]' < "$1"
}

# Print the latest-release JSON for jj.
fetch_latest_release() {
  gh api "repos/${JJ_REPO}/releases/latest"
}

# Print the release's tag name (e.g. v0.43.0); release JSON on
# stdin.
release_tag() {
  jq -r '.tag_name // empty'
}

# True iff the release JSON on stdin carries the asset
# scripts/install-jj.sh downloads for the bare version $1.
release_has_asset() {
  local asset="jj-v$1-x86_64-unknown-linux-musl.tar.gz"
  jq -e --arg name "$asset" \
    '[.assets[].name] | index($name) != null' >/dev/null
}

# Given the current pin ($1) and candidate tags (newline-separated
# on stdin), print the newest tag semver-greater than the pin, or
# nothing. Same npx/NODE_PATH arrangement as
# mathlib-bump-detect.sh; the helper emits the tag as given
# (v-prefixed), so callers strip the v afterwards.
select_target() {
  local pin="$1" helper
  helper="$(dirname "${BASH_SOURCE[0]}")/lib/select-newest-tag.cjs"
  # _ becomes $0 inside the -c script; $1=helper, $2=pin.
  npx --yes -p semver@7 bash -c '
    node_modules="$(cd "$(dirname "$(command -v semver)")/.." && pwd)"
    NODE_PATH="$node_modules" node "$1" "$2"
  ' _ "$helper" "$pin"
}

# Strip a leading v, passing bare versions through.
strip_v() {
  printf '%s\n' "${1#v}"
}

# Return 0 if a bump is in flight, 1 if not, 2 on error. Fails
# closed: a `gh` failure or non-numeric count is treated as an
# error (return 2), never as "not in flight" — otherwise a
# transient `gh` outage would let the apply job clobber an open,
# under-review pull request.
bump_in_flight() {
  local open_pr open_issue
  open_pr=$(gh pr list --state open --head "$BUMP_BRANCH" \
    --json number --jq 'length') || return 2
  open_issue=$(gh issue list --state open --label "$FAIL_LABEL" \
    --json number --jq 'length') || return 2
  [[ "$open_pr" =~ ^[0-9]+$ ]] || return 2
  [[ "$open_issue" =~ ^[0-9]+$ ]] || return 2
  [[ "$open_pr" != "0" || "$open_issue" != "0" ]]
}

# Emitting an empty target= is intentional protocol: the
# downstream workflow gates on `if: ... outputs.target != ''`, so
# the key must always be written (present-but-empty vs absent are
# different).
emit() {
  echo "target=$1"
  if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
    echo "target=$1" >> "$GITHUB_OUTPUT"
  fi
}

main() {
  local pin_file="${1:-$(dirname "${BASH_SOURCE[0]}")/jj-version}"
  local pin release_json tag target version flight
  pin=$(read_jj_pin "$pin_file")
  if [[ -z "$pin" ]]; then
    echo "error: no jj version pin in $pin_file" >&2
    exit 1
  fi

  if ! release_json=$(fetch_latest_release); then
    echo "error: failed to fetch the latest jj release" >&2
    exit 1
  fi
  tag=$(release_tag <<<"$release_json")
  if [[ -z "$tag" ]]; then
    echo "error: no tag_name in the latest-release response" >&2
    exit 1
  fi

  if ! target=$(printf '%s\n' "$tag" | select_target "$pin"); then
    echo "error: version selection failed" >&2
    exit 1
  fi
  if [[ -z "$target" ]]; then
    echo "No jj release newer than $pin." >&2
    emit ""
    return 0
  fi
  version=$(strip_v "$target")

  if ! release_has_asset "$version" <<<"$release_json"; then
    echo "Release $tag lacks the x86_64 musl asset; waiting." >&2
    emit ""
    return 0
  fi

  bump_in_flight
  flight=$?
  if [[ "$flight" -eq 2 ]]; then
    echo "error: in-flight check failed (gh)" >&2
    exit 1
  fi
  if [[ "$flight" -eq 0 ]]; then
    echo "Bump in flight (open PR or $FAIL_LABEL issue); skipping." >&2
    emit ""
    return 0
  fi

  echo "Target jj bump: $version (from $pin)." >&2
  emit "$version"
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  main "$@"
fi
