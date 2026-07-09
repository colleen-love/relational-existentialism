#!/usr/bin/env bash
# Closure gate — Series 5 is the live series.
#
# The project moved to the stratification arena (a doubly-unbounded tower of faced carriers).
# Series 3 is closed and frozen under `archive/`; Series 4 is complete under `series-4/`; only
# `series-5/` is live. Its one library is the `Series5` skeleton (registered in lake/lakefile.toml)
# — the closure rule is that series-5 imports resolve only to series-5's own roots (+ mathlib).
# Series 5 is wholly standalone: nothing is imported from `series-4/` or `archive/`. The Series 5
# charter grows it.
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

# series-5 is the live library: its roots (`Series5`, the per-workstream `wsN`, and
# `AxiomCheck`) may import each other (+ mathlib); nothing outside them is allowed.
check series-5 "^import (Series5(\.[A-Za-z0-9_]+)*|AxiomCheck|ws[0-9]+)$"

exit $fail
