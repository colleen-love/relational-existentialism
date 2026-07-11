#!/usr/bin/env bash
# Closure gate — each series is standalone.
#
# Series 3, 4, 5, and 6 are closed and frozen under `archive/` (`archive/series-3/`…
# `archive/series-6/`); Series 7 is complete and Series 8 is live under `series-7/` and
# `series-8/`. Both are registered in lake/lakefile.toml, each in its own module namespace
# (`Series7.*` / `Series8.*`) so the flat `wsN` module names coexist across series. The
# closure rule is that each series' imports resolve only to that series' own roots (+ mathlib):
# Series 8 imports nothing from `series-7/`, `archive/` (Series 3–6), or any other series.
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

# Each series' roots (the aggregator `SeriesN`, the per-workstream `SeriesN.wsX`, and
# `SeriesN.AxiomCheck`) may import each other (+ mathlib); nothing outside the namespace is allowed.
check series-7 "^import Series7(\.[A-Za-z0-9_]+)*$"
check series-8 "^import Series8(\.[A-Za-z0-9_]+)*$"

exit $fail
