#!/usr/bin/env bash
# Closure gate — each series is standalone.
#
# Series 03, 04, 05, and 06 are closed and frozen under `archive/` (`archive/series-03/`…
# `archive/series-06/`); Series 07 is complete and Series 08 is live under `series-07/` and
# `series-08/`. Both are registered in lake/lakefile.toml, each in its own module namespace
# (`Series07.*` / `Series08.*`) so the flat `wsN` module names coexist across series. The
# closure rule is that each series' imports resolve only to that series' own roots (+ mathlib):
# Series 08 imports nothing from `series-07/`, `archive/` (Series 03–06), or any other series.
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
check series-07 "^import Series07(\.[A-Za-z0-9_]+)*$"
check series-08 "^import Series08(\.[A-Za-z0-9_]+)*$"

exit $fail
