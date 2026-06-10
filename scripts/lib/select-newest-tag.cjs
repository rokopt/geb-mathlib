// scripts/lib/select-newest-tag.cjs
//
// Reads candidate tags (newline-separated) from stdin and the
// current pin from argv[2]; prints the newest tag strictly greater
// than the pin by semver order, or nothing. Requires the `semver`
// package to be resolvable (the caller sets NODE_PATH). Tags are
// parsed v-stripped without coercion so prerelease components
// (e.g. -rc1) are preserved and ordered correctly.
const semver = require("semver");
const fs = require("fs");
const clean = (t) => t.replace(/^v/, "");
const pin = clean(process.argv[2] || "");
const tags = fs.readFileSync(0, "utf8").split("\n")
  .map((s) => s.trim()).filter(Boolean)
  .filter((t) => semver.valid(clean(t)));
const newer = tags
  .filter((t) => semver.gt(clean(t), pin))
  .sort((a, b) => semver.compare(clean(a), clean(b)));
process.stdout.write(newer.length ? newer[newer.length - 1] : "");
