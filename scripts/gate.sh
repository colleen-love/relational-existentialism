#!/usr/bin/env bash
# Closure gate — Series 6 is the live series.
#
# Series 3 is closed and frozen under `archive/`; Series 4 and Series 5 are complete under
# `series-4/` and `series-5/`; only `series-6/` is live. Its one library is `Series6`
# (registered in lake/lakefile.toml) — the closure rule is that series-6 imports resolve only
# to series-6's own roots (+ mathlib). Series 6 is wholly standalone: nothing is imported from
# `series-5/`, `series-4/`, or `archive/`.
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

# series-6 is the live library: its roots (`Series6`, the per-workstream `wsN`, and
# `AxiomCheck`) may import each other (+ mathlib); nothing outside them is allowed.
check series-6 "^import (Series6(\.[A-Za-z0-9_]+)*|AxiomCheck|ws[0-9]+)$"

exit $fail
