#!/usr/bin/env bash
# Closure gate — Series 3 is the live series.
#
# The project moved to a new foundation (a quantaloid / allegory with relations as the primitive arrow).
# Series 2 is closed and frozen under `archive/`; only `series-3/` is live. Its one library is the
# `Series3` skeleton (registered in lake/lakefile.toml) — the closure rule is that series-3 imports
# resolve only to series-3's own roots (+ mathlib). The Series 3 charter grows it.
set -u
cd "$(dirname "$0")/.." || exit 2
fail=0

check () { # <root> <allowed-egrep>
  local root="$1" allowed="$2"
  local bad
  bad=$(grep -rhE "^import " "$root/formal" 2>/dev/null | grep -vE "Mathlib" \
        | grep -vE "$allowed" || true)
  if [ -n "$bad" ]; then
    echo "LEAK in $root/:"; echo "$bad" | sed 's/^/   /'; fail=1
  else
    echo "OK   $root/ — imports resolve only to allowed roots"
  fi
}

# series-3 is the live library: its `Series3` root (and any it grows) may import each other
# (+ mathlib); nothing outside them is allowed.
check series-3 "^import (Series3(\.[A-Za-z0-9_]+)*|Spec[0-9]{2}[a-z])$"

exit $fail
