#!/usr/bin/env bash
# Regression checks for signing-cache diagnostics. Mock the commands so no
# personal keys, running agent, or signing configuration are needed.

set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
hook="$here/../check-signing-key.sh"

git() { return 1; }
jj() {
  case "$*" in
    'config get signing.behavior') echo own ;;
    'config get signing.backend') echo gpg ;;
    'config get signing.key') echo test-key ;;
    *) return 1 ;;
  esac
}
gpg() {
  printf '%s\n' "$TEST_KEYS"
  return "$TEST_GPG_STATUS"
}
gpg-connect-agent() {
  printf '%s\n' "$TEST_KEYINFO"
  return "$TEST_AGENT_STATUS"
}
export -f git jj gpg gpg-connect-agent

export TEST_GPG_STATUS=0 TEST_AGENT_STATUS=0
export TEST_KEYS='sec:u:255:22:TEST:0:0::u:::scESC:
grp:::::::::SIGNING_GRIP:
ssb:u:255:18:TEST:0:0:::::e:
grp:::::::::ENCRYPTION_GRIP:'
export TEST_KEYINFO='S KEYINFO SIGNING_GRIP D - - 1 P - - -
OK'

check() {
  local name="$1" expected="$2" out
  out=$(bash "$hook")
  if [[ -z "$expected" ]]; then
    [[ -z "$out" ]] || { echo "FAIL [$name]: $out" >&2; exit 1; }
  else
    if ! jq -e --arg expected "$expected" '
      (.systemMessage | contains($expected)) and
      .hookSpecificOutput.hookEventName == "SessionStart" and
      .hookSpecificOutput.additionalContext == .systemMessage
    ' <<<"$out" >/dev/null; then
      echo "FAIL [$name]: expected '$expected', got: $out" >&2
      exit 1
    fi
  fi
}

check 'cached signing key' ''

TEST_KEYINFO='S KEYINFO SIGNING_GRIP D - - - P - - -
S KEYINFO ENCRYPTION_GRIP D - - 1 P - - -
OK'
check 'only encryption key cached' 'signing key is not cached'

TEST_KEYINFO=OK
check 'successful empty cache query' 'signing key is not cached'

TEST_KEYINFO=''
TEST_AGENT_STATUS=1
check 'agent connection failure' 'signing readiness is unknown'

TEST_AGENT_STATUS=0
check 'agent unavailable with exit zero' 'signing readiness is unknown'

TEST_KEYINFO='ERR 67109133 IPC call has been forbidden <GPG Agent>'
check 'protocol error with exit zero' 'signing readiness is unknown'

TEST_KEYINFO='S KEYINFO SIGNING_GRIP D - - 1 P - - -'
check 'incomplete agent response' 'signing readiness is unknown'

TEST_KEYINFO='S KEYINFO SIGNING_GRIP D - - 1 P - - -
OK'
TEST_GPG_STATUS=2
check 'failed key listing with partial output' 'signing readiness is unknown'

TEST_KEYS=''
check 'failed key listing without output' 'signing readiness is unknown'

TEST_GPG_STATUS=0
check 'successful listing without signing keys' 'no sign-capable secret key'

echo 'test-check-signing-key.sh: all checks passed'
