#!/usr/bin/env bash
# Compile the client and check its examples, prove its theorems and replay their certificate, run
# Copy.step where the file its index names exists and where it is missing, and save, apply and
# migrate a setting, with the host executables of the Geb checkout or release at geb/. The manifest
# and proof document are those the editor's settings select.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
mkdir -p .lake
if [ -f geb/geb-release.json ]; then author=(geb/bin/geb-author)
else author=(lake -d geb exe geb-author); fi
cache=(--cache .lake/geb-proof-cache)
"${author[@]}" compile "${cache[@]}" client.manifest .lake/client.img
"${author[@]}" prove "${cache[@]}" client.manifest Client.proofs.geb .lake/client.cert
"${author[@]}" replay "${cache[@]}" client.manifest Client.proofs.geb .lake/client.cert
# The copy of the file the index names, and the line written where that file is missing.
printf '.lake/copy.source\n' > .lake/copy.index
printf 'the source\n' > .lake/copy.source
"${author[@]}" interact "${cache[@]}" client.manifest Copy.step .lake/copy.index .lake/copy.found
cmp .lake/copy.source .lake/copy.found
rm .lake/copy.source
"${author[@]}" interact "${cache[@]}" client.manifest Copy.step .lake/copy.index .lake/copy.missing
printf 'missing\n' | cmp - .lake/copy.missing
# The order that a letter names, saved and applied to a file, and the same order saved by the
# previous revision at version 1 of its encoding and migrated.
printf 'abc' > .lake/settings.input
"${author[@]}" interact "${cache[@]}" client.manifest Settings.choose m .lake/settings.saved
"${author[@]}" interact "${cache[@]}" client.manifest Settings.apply .lake/settings.saved \
  .lake/settings.input .lake/settings.output
printf 'abccba' | cmp - .lake/settings.output
printf 'O\001\001' > .lake/settings.v1
"${author[@]}" interact "${cache[@]}" client.manifest Upgrade.migrate .lake/settings.v1 \
  .lake/settings.migrated
cmp .lake/settings.saved .lake/settings.migrated
