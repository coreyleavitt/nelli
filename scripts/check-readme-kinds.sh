#!/usr/bin/env bash
# RFC-0016 W1-z. docs/symex/README.md's decline catalogue must name every
# `fe*` member of `SymexErrorKind` and every `ub*` member (the `UbKind` range)
# declared in src/nelli/smt/types.nim. That is the whole scope: it does NOT
# check the other kinds a consumer can see (the `sx*` / `sf*` statuses, the
# `sc*` taints, `rs*` replay states, `gap*` causes, or any kind declared outside
# `SymexErrorKind` / `UbKind`). The list is derived from types.nim, not
# hard-coded, so an `fe*` / `ub*` kind added later fails this check until the
# README names it. A member whose declaration line says "retired" (never
# emitted, ordinal kept for cache-key stability) is exempt. Pure grep/awk: no
# toolchain, runs on the host.
#
# Usage: scripts/check-readme-kinds.sh [readme] [types.nim]
#        scripts/check-readme-kinds.sh --self-test
# Exit:  0 = every kind is named; 1 = some are missing (listed); 2 = misuse.
# --self-test copies the README to a temp file with one kind removed and
# requires the check to fail on it (and to pass on an untouched copy).
set -uo pipefail
cd "$(dirname "$0")/.."
if [ "${1:-}" = "--self-test" ]; then
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
  src=docs/symex/README.md
  bash "$0" "$src" >/dev/null || { echo "self-test: the real README does not pass" >&2; exit 1; }
  cp "$src" "$tmp/ok.md"
  bash "$0" "$tmp/ok.md" >/dev/null || { echo "self-test: an untouched copy fails" >&2; exit 1; }
  # Remove every occurrence of one kind (an fe* and a ub* in turn).
  for k in feLocalPragma ubIndeterminateRead; do
    sed "s/\b$k\b/REMOVED/g" "$src" > "$tmp/bad.md"
    if bash "$0" "$tmp/bad.md" >"$tmp/out" 2>&1; then
      echo "self-test: the check passed with $k removed" >&2; exit 1
    fi
    command grep -q "MISSING from .*: $k" "$tmp/out" \
      || { echo "self-test: the failure did not name $k" >&2; exit 1; }
  done
  echo "check-readme-kinds: self-test ok (a removed kind fails the check)"
  exit 0
fi
readme="${1:-docs/symex/README.md}"
types="${2:-src/nelli/smt/types.nim}"
[ -f "$readme" ] || { echo "no such file: $readme" >&2; exit 2; }
[ -f "$types" ] || { echo "no such file: $types" >&2; exit 2; }

kinds=$(awk '
  /^  SymexErrorKind\*[ ]*=[ ]*enum/ { on = 1; next }
  on && /^  UbKind\*/               { exit }
  on {
    code = $0
    sub(/#.*/, "", code)
    retired = ($0 ~ /[Rr][Ee][Tt][Ii][Rr][Ee][Dd]/)
    code = " " code
    while (match(code, /[^A-Za-z0-9_](fe|ub)[A-Z][A-Za-z0-9]*/)) {
      if (!retired) print substr(code, RSTART + 1, RLENGTH - 1)
      code = substr(code, RSTART + RLENGTH)
    }
  }' "$types" | sort -u)

if [ -z "$kinds" ]; then
  echo "check-readme-kinds: derived no kinds from $types (parser out of date)" >&2
  exit 2
fi
if ! printf '%s\n' "$kinds" | command grep -qx 'ubIndeterminateRead'; then
  echo "check-readme-kinds: the derived list lacks the ub* kinds (parser out of date)" >&2
  exit 2
fi

missing=0
total=0
for k in $kinds; do
  total=$((total + 1))
  if ! command grep -qE "(^|[^A-Za-z0-9_])${k}([^A-Za-z0-9_]|$)" "$readme"; then
    echo "MISSING from $readme: $k"
    missing=$((missing + 1))
  fi
done
if [ "$missing" -ne 0 ]; then
  echo "check-readme-kinds: $missing of $total kinds are not named in $readme" >&2
  exit 1
fi
echo "check-readme-kinds: all $total fe*/ub* kinds are named in $readme"
