#!/usr/bin/env bash
# Closure gate — each series is standalone.
#
# The project moved to the stratification arena (a doubly-unbounded tower of faced carriers).
# Series 3 is closed and frozen under `archive/`; Series 4 is complete under `series-4/`; Series 5
# is live under `series-5/`. Both libraries are registered in lake/lakefile.toml, each in its own
# module namespace (`Series4.*` / `Series5.*`) so the flat `wsN` module names can coexist. The
# closure rule is that each series' imports resolve only to that series' own roots (+ mathlib):
# Series 5 imports nothing from `series-4/` or `archive/`, and Series 4 imports nothing from
# `series-5/` or `archive/`.
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
check series-4 "^import Series4(\.[A-Za-z0-9_]+)*$"
check series-5 "^import Series5(\.[A-Za-z0-9_]+)*$"

exit $fail
