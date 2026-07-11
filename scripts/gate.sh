#!/usr/bin/env bash
# Closure gate — each series is standalone.
#
# Series 3, 4, 5, and 6 are closed and frozen under `archive/` (`archive/series-3/`…
# `archive/series-6/`); Series 7 is live under `series-7/`. Only Series 7 is registered
# in lake/lakefile.toml, in its own module namespace (`Series7.*`) so the flat `wsN`
# module names can coexist across series. The closure rule is that each series' imports
# resolve only to that series' own roots (+ mathlib): Series 7 imports nothing from
# `archive/` (Series 3–6) or any other series.
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

# Series 7's roots (the aggregator `Series7`, the per-workstream `Series7.wsX`, and
# `Series7.AxiomCheck`) may import each other (+ mathlib); nothing outside the namespace is allowed.
check series-7 "^import Series7(\.[A-Za-z0-9_]+)*$"

exit $fail
