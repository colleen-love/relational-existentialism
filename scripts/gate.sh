#!/usr/bin/env bash
# Closure gate — each series is standalone.
#
# Series 03, 04, 05, 06, and 08–11 are closed and frozen under `archive/` (`archive/series-03/`…
# `archive/series-11/`); Series 07 is complete under `series-07/` and registered in
# lake/lakefile.toml, in its own module namespace (`Series07.*`) so the flat `wsN` module names
# coexist across series. The closure rule is that each series' imports resolve only to that
# series' own roots (+ mathlib): each imports nothing from another series' tree or from `archive/`.
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
check series-12 "^import Series12(\.[A-Za-z0-9_]+)*$"

exit $fail
