#!/usr/bin/env bash
# Compile the client and check its examples, prove its theorems and replay their certificate,
# with the host executables of the Geb checkout or release at geb/. The manifest and proof document
# are those the editor's settings select.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
mkdir -p .lake
if [ -f geb/geb-release.json ]; then author=(geb/bin/geb-author)
else author=(lake -d geb exe geb-author); fi
"${author[@]}" compile client.manifest .lake/client.img
"${author[@]}" prove client.manifest Client.proofs.geb .lake/client.cert
"${author[@]}" replay client.manifest Client.proofs.geb .lake/client.cert
