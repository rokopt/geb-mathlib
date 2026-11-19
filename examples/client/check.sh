#!/usr/bin/env bash
# Compile the client and check its examples, prove its theorems and replay their certificate,
# with the host executables of the Geb checkout at geb/. The manifest and proof document are those
# the editor's settings select.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
mkdir -p .lake
lake -d geb exe geb-author compile client.manifest .lake/client.img
lake -d geb exe geb-author prove client.manifest Client.proofs.geb .lake/client.cert
lake -d geb exe geb-author replay client.manifest Client.proofs.geb .lake/client.cert
