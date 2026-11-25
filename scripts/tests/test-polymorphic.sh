#!/usr/bin/env bash
#
# scripts/tests/test-polymorphic.sh
#
# Test of declarations with type parameters on the program of
# examples/polymorphic/, whose library layer is the shared library under
# library/, which declares optional values, lists and the composition of
# functions generic in their types, and whose application layer uses them.
# Asserts that the program compiles from its
# manifest, by geb-compile and by geb-author, which checks its examples;
# that the image compiled a layer at a time with a directory of kept states
# is the same image, when no state is kept and when the library's is; that
# an entry run on a file writes the expected bytes; that the image defines
# one instance for each list of type arguments a declaration is used at,
# named by its use, the optional values of the trees that one module
# returns and another consumes among them, and no instance of a module with
# parameters; and that geb-doc resolves the references of the sources'
# comments. Asserts of the library's text followed by a further module that a
# declaration inspecting the trees of its type parameter is rejected at the
# term that does so though nothing uses it, and that a use at a term where a
# type stands is rejected at the declaration that writes the use.
#
# Exit 0 if all scenarios pass; exit non-zero with the failure count
# otherwise.

set -uo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
test_dir="$(mktemp -d)"
trap 'rm -rf "$test_dir"' EXIT

(cd "$repo_root" && lake build geb-compile geb-author geb-kernel geb-defs geb-doc \
  > "$test_dir/build.log" 2>&1) || {
  cat "$test_dir/build.log" >&2
  echo "FAIL: the host executables do not build" >&2
  exit 1
}
bin="$repo_root/.lake/build/bin"
example="$repo_root/examples/polymorphic"
manifest="$example/polymorphic.manifest"

failed=0
checked=0

fail_case() {
  echo "FAIL: $1: $2" >&2
  failed=$((failed + 1))
}

# expect NAME STATUS COMMAND...: the command exits with STATUS.
expect() {
  local name=$1 status=$2
  shift 2
  checked=$((checked + 1))
  "$@" > "$test_dir/$name.out" 2> "$test_dir/$name.err"
  local actual=$?
  [ "$actual" -eq "$status" ] || fail_case "$name" "exit $actual, expected $status"
}

# same NAME FILE EXPECTED: FILE holds the bytes EXPECTED.
same() {
  checked=$((checked + 1))
  cmp -s "$2" "$3" || fail_case "$1" "$2 differs from $3"
}

# reports NAME TEXT: the standard error of the command NAME has a line holding TEXT.
reports() {
  checked=$((checked + 1))
  grep -qF -- "$2" "$test_dir/$1.err" ||
    fail_case "$1" "the diagnostics lack '$2': $(cat "$test_dir/$1.err")"
}

cd "$test_dir" || exit 1

# The program compiles, its examples hold, and the layered compilation gives the same image.
expect check 0 "$bin/geb-compile" check --manifest "$manifest"
expect image 0 "$bin/geb-compile" image --manifest "$manifest" plain.img
expect examples 0 "$bin/geb-author" compile "$manifest" author.img
same examples author.img plain.img
expect cold 0 "$bin/geb-compile" image --cache cache --manifest "$manifest" cold.img
same cold cold.img plain.img
expect warm 0 "$bin/geb-compile" image --cache cache --manifest "$manifest" warm.img
same warm warm.img plain.img

# An entry runs on a file.
printf '\001\003\000\005' > input
printf '\003\004\006\002\002\001\002' > expected
expect run 0 "$bin/geb-kernel" run plain.img Client.run input output
same run output expected

# The instances the image defines: one for each list of type arguments, named by its use.
expect defs 0 "$bin/geb-defs" plain.img defs
cut -f1 defs | grep -F '(' | sort > instances
cat > instances.expected <<'EOF'
(Functions.compose (List Client.Light) T T)
(Functions.compose T Client.Light T)
(Lists.find T)
(Lists.length Client.Light)
(Lists.length T)
(Lists.map T Client.Light)
(Lists.map T T)
(Optional.none T)
(Optional.orElse T)
(Optional.some T)
EOF
same instances instances instances.expected
checked=$((checked + 1))
if cut -f1 defs | grep -qF '/'; then
  fail_case instances "the image defines an instance of a module with parameters"
fi

# The references of the comments resolve.
expect doc 0 env -C "$repo_root" lake env "$bin/geb-doc" --check "$manifest"

# A declaration that inspects the trees of its type parameter is rejected though nothing uses it,
# at the term that does so. The module that declares it follows the text of the library layer.
expect join 0 "$bin/geb-kernel" join "$manifest" library.geb library
cp library.geb opaque.geb
printf '%s\n' '(module Peek (export peek)' '  (defn (peek A) ((x A)) T (label x)))' >> opaque.geb
expect opaque 1 "$bin/geb-compile" check opaque.geb
line=$(($(wc -l < library.geb) + 2))
reports opaque "opaque.geb:$line:35: error: Peek.peek does not check at its opaque type parameters: expected T, got A"

# A use at a term where a type stands is rejected at the declaration that writes the use.
cp library.geb use.geb
printf '%s\n' '(module Use (import Lists)' '  (defn count ((xs (List T))) T (length xs)))' >> use.geb
expect use 1 "$bin/geb-compile" check use.geb
reports use "use.geb:$line:9: error: Use.count does not check: the instance (Lists.length xs) it requires does not check: the type is not declared before"

# A use at a number of types other than that of the parameters is rejected.
cp library.geb arity.geb
printf '%s\n' '(module Arity (import Optional)' '  (defn none2 ((t T)) (Option T T) (none T)))' >> arity.geb
expect arity 1 "$bin/geb-compile" check arity.geb
reports arity "Optional.Option is used at 2 types and takes 1"

if [ "$failed" -ne 0 ]; then
  echo "test-polymorphic: $failed of $checked checks failed" >&2
  exit "$failed"
fi
echo "test-polymorphic: $checked checks passed"
