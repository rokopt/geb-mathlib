#!/usr/bin/env bash
#
# scripts/bootstrap.sh regen|check
#
# Regenerate or check the bootstrap's committed build artifacts: the
# stage-1 compiler's image, bootstrap/compiler.img, and the Lean it emits
# from its own source, bootstrap/lean/GebBoot.lean (the manual's
# Bootstrap chapter, Speed and a second host and What self-compilation
# establishes); and the Lean it emits from the programs whose agreement
# with a Lean function is proved, each under bootstrap/lean/GebMirror/ in
# a namespace of its own.
#
# The stage-1 compiler's source S is the files of STAGE1 joined as the
# host driver joins sources, each followed by a newline.
#
#   regen  The seed builds the stage-0 compiler from its sources in the
#          kernel's syntax; the stage-0 compiler compiles S to the image;
#          the image's mainLean compiles S to the Lean.
#   check  Regenerates both into a temporary directory and compares their
#          bytes with the committed ones; checks that the stage-0 compiler
#          and the committed image each reproduce themselves; builds
#          geb-compile, the committed Lean, and checks that it compiles S
#          to the committed Lean and the committed image.
#
# Exit 0 when every comparison holds; exit 1 naming the first that does
# not.

set -euo pipefail
cd "$(dirname "$0")/.."

b=bootstrap
stage0=("$b/prelude.geb" "$b/serialize.geb" "$b/reader.geb" "$b/check.geb" "$b/datatype.geb"
        "$b/compile.geb")
stage1=("$b/prelude.geb" "$b/serialize.geb" "$b/reader.geb" "$b/check.geb" "$b/stage1/datatype.geb"
        "$b/compile.geb" "$b/stage1/lean.geb")
img=$b/compiler.img
lean=$b/lean/GebBoot.lean
# each mirror: its name, then its sources
f=$b/free-topos
metalogic="$b/prelude.geb $f/base.geb $f/partial-horn.geb $f/theory.geb $f/infer.geb"
metalogic+=" $f/language.geb $f/derivation.geb $b/reader.geb $b/check.geb $f/translation.geb"
metalogic+=" $f/prove.geb $f/tactics.geb"
mirrors=("GoedelT $b/prelude.geb $b/reader.geb $b/check.geb $b/goedel-t/equations.geb"
         "Metalogic $metalogic")
kernel=.lake/build/bin/geb-kernel

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fail() { echo "bootstrap: $1" >&2; exit 1; }
same() { cmp -s "$1" "$2" || fail "$3"; }
join() { local f; for f in "$@"; do cat "$f"; echo; done; }

# The stage-0 compiler, S and the two artifacts, written into the directory $1.
generate() {
  "$kernel" build "${stage0[@]}" "$1/stage0.img"
  join "${stage1[@]}" > "$1/S.geb"
  "$kernel" run "$1/stage0.img" main "$1/S.geb" "$1/compiler.img"
  [ -s "$1/compiler.img" ] || fail "the stage-0 compiler rejects S"
  "$kernel" run "$1/compiler.img" mainLean "$1/S.geb" "$1/GebBoot.lean"
  [ -s "$1/GebBoot.lean" ] || fail "the image's mainLean rejects S"
}

# The Lean the committed image emits from a mirror's sources, in the namespace GebMirror.<name>,
# written to $2.
mirror() {
  local name=$1; shift
  local out=$1; shift
  join "$@" > "$tmp/$name.geb"
  "$kernel" run "$img" mainLean "$tmp/$name.geb" "$tmp/$name.raw"
  [ -s "$tmp/$name.raw" ] || fail "the image's mainLean rejects the mirror $name"
  sed "s/^namespace GebBoot$/namespace GebMirror.$name/; s/^end GebBoot$/end GebMirror.$name/" \
    "$tmp/$name.raw" > "$out"
}

lake build geb-kernel
case "${1:-}" in
  regen)
    generate "$tmp"
    cp "$tmp/compiler.img" "$img"
    cp "$tmp/GebBoot.lean" "$lean"
    for m in "${mirrors[@]}"; do
      read -r -a a <<< "$m"
      mirror "${a[0]}" "$b/lean/GebMirror/${a[0]}.lean" "${a[@]:1}"
    done
    ;;
  check)
    generate "$tmp"
    same "$tmp/compiler.img" "$img" "the committed image is not the stage-0 compiler's image of S"
    same "$tmp/GebBoot.lean" "$lean" "the committed Lean is not the image's Lean of S"
    join "${stage0[@]}" > "$tmp/S0.geb"
    "$kernel" run "$tmp/stage0.img" main "$tmp/S0.geb" "$tmp/stage0-self.img"
    same "$tmp/stage0-self.img" "$tmp/stage0.img" "the stage-0 compiler does not reproduce its image"
    "$kernel" run "$img" main "$tmp/S.geb" "$tmp/self.img"
    same "$tmp/self.img" "$img" "the committed image does not reproduce itself"
    lake build geb-compile
    .lake/build/bin/geb-compile lean "$tmp/S.geb" "$tmp/C1.lean"
    same "$tmp/C1.lean" "$lean" "the compiled compiler does not reproduce the committed Lean"
    .lake/build/bin/geb-compile image "$tmp/S.geb" "$tmp/C1.img"
    same "$tmp/C1.img" "$img" "the compiled compiler does not reproduce the committed image"
    for m in "${mirrors[@]}"; do
      read -r -a a <<< "$m"
      mirror "${a[0]}" "$tmp/mirror.lean" "${a[@]:1}"
      same "$tmp/mirror.lean" "$b/lean/GebMirror/${a[0]}.lean" \
        "the committed mirror ${a[0]} is not the image's Lean of its sources"
    done
    echo "bootstrap: every fixed point holds"
    ;;
  *)
    echo "usage: scripts/bootstrap.sh regen|check" >&2
    exit 2
    ;;
esac
