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
# a namespace of its own; the metalogic's, a module per layer, beside the
# loading of its program through each layer, checked by the kernel.
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
#          to the committed Lean and the committed image. Checks that every
#          source under bootstrap/ is a fixed point of geb-fmt and, where
#          the parinfer release pinned in scripts/parinfer/ is installed
#          (npm ci --prefix scripts/parinfer), of both of its modes.
#
# Exit 0 when every comparison holds; exit 1 naming the first that does
# not.

set -euo pipefail
cd "$(dirname "$0")/.."

b=bootstrap
stage0=("$b/prelude.geb" "$b/serialize.geb" "$b/reader.geb" "$b/check.geb" "$b/datatype.geb"
        "$b/modules.geb" "$b/recognize.geb" "$b/compile.geb")
stage1=("$b/prelude.geb" "$b/serialize.geb" "$b/reader.geb" "$b/check.geb" "$b/seq.geb"
        "$b/stage1/typing.geb"
        "$b/stage1/datatype.geb"
        "$b/modules.geb" "$b/recognize.geb" "$b/compile.geb" "$b/stage1/lean.geb")
img=$b/compiler.img
lean=$b/lean/GebBoot.lean
# each mirror emitted as one module: its name, then its sources
mirrors=("GoedelT $b/prelude.geb $b/reader.geb $b/check.geb $b/goedel-t/equations.geb")
# the metalogic's layers, each its name, then its sources: its mirror and the loading of its
# program are emitted a module per layer, each importing the layer before it, so that a change to
# a layer's sources changes only the modules of that layer and the layers after it
f=$b/free-topos
checker="$b/prelude.geb $f/base.geb $f/partial-horn.geb $f/theory.geb $f/infer.geb"
checker+=" $f/language.geb $f/derivation.geb $b/reader.geb $b/check.geb"
layers=("Checker $checker" "Translation $f/translation.geb" "Prover $f/prove.geb"
        "Tactics $f/tactics.geb" "Combinator $f/combinator.geb"
        "Printer $b/datatype.geb $b/printer.geb")
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

# The metalogic's modules, written under the directory $1: for each layer,
# GebMirror/Metalogic/<name>.lean, the Lean the committed image emits from its definitions, and
# GebMirror/Metalogic/Load/<name>.lean, the loading of the program's definitions through the
# layer from the image of its sources; GebMirror/Metalogic.lean and GebMirror/Metalogic/Load.lean
# import them.
layered() {
  local out=$1 sources=() prev="" count=0 name layer imports=()
  mkdir -p "$out/GebMirror/Metalogic/Load"
  for layer in "${layers[@]}"; do
    read -r -a a <<< "$layer"
    name=${a[0]}
    sources+=("${a[@]:1}")
    join "${sources[@]}" > "$tmp/layer.geb"
    "$kernel" run "$img" mainLean "$tmp/layer.geb" "$tmp/layer.raw"
    [ -s "$tmp/layer.raw" ] || fail "the image's mainLean rejects the layer $name"
    "$kernel" run "$img" main "$tmp/layer.geb" "$tmp/layer.img"
    [ -s "$tmp/layer.img" ] || fail "the image rejects the layer $name"
    awk -v skip="$count" -v prev="$prev" '
      /^def «/ { n++ }
      n == 0 {
        if ($0 ~ /^public import / && prev != "") print "public import GebMirror.Metalogic." prev
        else if ($0 == "namespace GebBoot") print "namespace GebMirror.Metalogic"
        else print
        next
      }
      /^end GebBoot$/ { print "end GebMirror.Metalogic"; tail = 1; next }
      tail || n > skip { print }' "$tmp/layer.raw" > "$out/GebMirror/Metalogic/$name.lean"
    count=$(grep -c '^def «' "$tmp/layer.raw")
    {
      printf 'module\n\npublic import GebMirror.Metalogic.%s\n' "$name"
      if [ -n "$prev" ]; then printf 'public import GebMirror.Metalogic.Load.%s\n' "$prev"
      else printf 'public import Geb.Prototypes.Kernel.LoadCommand\n'; fi
      printf '\n/-! Generated by `scripts/bootstrap.sh`: the loading of the metalogic'"'"'s program'
      printf ' through the\nlayer %s, each step checked by the kernel. -/\n\n' "$name"
      printf 'set_option maxHeartbeats 20000000 in\nset_option Elab.async false in\n'
      printf 'geb_load GebMirror.metalogic mirror GebMirror.Metalogic image "%s"\n' \
        "$(od -An -v -tx1 "$tmp/layer.img" | tr -d ' \n')"
    } > "$out/GebMirror/Metalogic/Load/$name.lean"
    imports+=("public import GebMirror.Metalogic.$name")
    prev=$name
  done
  {
    printf 'module\n\n'
    printf '%s\n' "${imports[@]}"
    printf '\n/-! Generated by `scripts/bootstrap.sh`: the metalogic'"'"'s mirror, a module per'
    printf ' layer. -/\n'
  } > "$out/GebMirror/Metalogic.lean"
  {
    printf 'module\n\npublic import GebMirror.Metalogic.Load.%s\n' "$prev"
    printf '\n/-! Generated by `scripts/bootstrap.sh`: the loading of the metalogic'"'"'s program,'
    printf '\na module per layer. -/\n'
  } > "$out/GebMirror/Metalogic/Load.lean"
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
    rm -rf "$b/lean/GebMirror/Metalogic"
    layered "$b/lean"
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
    layered "$tmp/lean"
    same "$tmp/lean/GebMirror/Metalogic.lean" "$b/lean/GebMirror/Metalogic.lean" \
      "the committed index of the metalogic's layers is not the generated one"
    diff -rq "$tmp/lean/GebMirror/Metalogic" "$b/lean/GebMirror/Metalogic" > /dev/null \
      || fail "the committed layers of the metalogic are not the image's Lean of their sources"
    lake build geb-fmt
    mapfile -t sources < <(find "$b" -name '*.geb' | sort)
    .lake/build/bin/geb-fmt --check "${sources[@]}" \
      || fail "a source is not formatted: run lake exe geb-fmt on it"
    if [ -d scripts/parinfer/node_modules/parinfer ]; then
      node scripts/parinfer/check.mjs "${sources[@]}" \
        || fail "a source is not a fixed point of parinfer"
    else
      echo "bootstrap: parinfer not installed (npm ci --prefix scripts/parinfer); skipped"
    fi
    echo "bootstrap: every fixed point holds"
    ;;
  *)
    echo "usage: scripts/bootstrap.sh regen|check" >&2
    exit 2
    ;;
esac
