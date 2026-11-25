#!/usr/bin/env bash
# Compile the client and check its examples, prove its theorems and replay their certificate, and
# run Copy.step where the file its index names exists and where it is missing, with the host
# executables of the Geb checkout or release at geb/. The manifest and proof document are those
# the editor's settings select.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
mkdir -p .lake
if [ -f geb/geb-release.json ]; then author=(geb/bin/geb-author)
else author=(lake -d geb exe geb-author); fi
"${author[@]}" compile client.manifest .lake/client.img
"${author[@]}" prove client.manifest Client.proofs.geb .lake/client.cert
"${author[@]}" replay client.manifest Client.proofs.geb .lake/client.cert
# The copy of the file the index names, and the line written where that file is missing.
printf '.lake/copy.source\n' > .lake/copy.index
printf 'the source\n' > .lake/copy.source
"${author[@]}" interact client.manifest Copy.step .lake/copy.index .lake/copy.found
cmp .lake/copy.source .lake/copy.found
rm .lake/copy.source
"${author[@]}" interact client.manifest Copy.step .lake/copy.index .lake/copy.missing
printf 'missing\n' | cmp - .lake/copy.missing
