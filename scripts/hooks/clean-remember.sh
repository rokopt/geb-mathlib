#!/usr/bin/env bash
# clean-remember.sh — Claude Code Stop hook.  Normalizes the `remember`
# plugin's .remember/*.md logs so the repository-wide markdownlint run stays
# clean (the plugin emits non-conforming markdown).  Claude-specific: wired
# only via .claude/settings.json, never by CI or pre-push.  No-ops — and
# never blocks — when .remember/ is absent (Claude without the remember
# feature) or python3 is unavailable, so it imposes no requirement on anyone.
set -u

root="${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
remember="$root/.remember"

[ -d "$remember" ] || exit 0
command -v python3 >/dev/null 2>&1 || exit 0

python3 "$(dirname "${BASH_SOURCE[0]}")/clean-remember.py" "$remember" || true
exit 0
