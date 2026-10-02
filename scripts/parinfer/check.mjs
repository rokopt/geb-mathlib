// scripts/parinfer/check.mjs
//
// Usage: node scripts/parinfer/check.mjs FILE...
//
// Checks that each file is a fixed point of both of parinfer's modes,
// parenMode(x).text === x && indentMode(x).text === x, at the release
// pinned in scripts/parinfer/package.json, so that the output of geb-fmt
// stays usable under parinfer. A file is read one character per byte, as
// Geb's readers read it. Exits 1 naming each file that is not a fixed point.

import { readFileSync } from "node:fs";
import parinfer from "parinfer";

let failed = 0;
for (const file of process.argv.slice(2)) {
  const text = readFileSync(file, "latin1");
  for (const mode of ["parenMode", "indentMode"]) {
    const result = parinfer[mode](text);
    if (!result.success || result.text !== text) {
      console.log(`${file}: not a fixed point of parinfer's ${mode}`);
      failed = 1;
    }
  }
}
process.exit(failed);
