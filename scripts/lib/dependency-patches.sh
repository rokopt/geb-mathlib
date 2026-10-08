#!/usr/bin/env bash
#
# scripts/lib/dependency-patches.sh
#
# Shared helper for the document build scripts: applies each
# scripts/patches/<package>/*.patch to the checkout Lake materializes
# for that dependency, .lake/packages/<package>. A patch carries an
# upstream fix the pinned revision lacks, and its header names the
# upstream defect; it is deleted once the pin includes a fix. Source
# this file from the repository root; it defines
# apply_dependency_patches.
#
# Applying is idempotent: a patch that already applies in reverse is
# skipped. A patch that applies in neither direction fails the run,
# which is the signal that upstream has changed the patched code and
# the patch is to be dropped or rebased. Lake keeps a dependency's
# local changes across builds, warning that the repository has local
# changes, and `lake update` carries them to the new revision unless
# that revision changes the patched lines, in which case
# `git -C .lake/packages/<package> checkout -- .` before the update
# discards them.
#
# Not meant to be executed directly.

apply_dependency_patches() {
  local patch pkg dir
  for patch in scripts/patches/*/*.patch; do
    [ -e "$patch" ] || continue
    pkg="$(basename "$(dirname "$patch")")"
    dir=".lake/packages/$pkg"
    # Loading the workspace materializes its dependencies.
    [ -d "$dir" ] || lake script list >/dev/null
    if git -C "$dir" apply --reverse --check "$PWD/$patch" 2>/dev/null; then
      continue
    fi
    if ! git -C "$dir" apply "$PWD/$patch"; then
      echo "error: $patch does not apply to $dir;" \
        "upstream has changed the patched code" >&2
      return 1
    fi
  done
}
