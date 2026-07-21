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
check program-1/series-07 "^import Series07(\.[A-Za-z0-9_]+)*$"
check program-1/series-12 "^import Series12(\.[A-Za-z0-9_]+)*$"
check program-1/series-13 "^import Series13(\.[A-Za-z0-9_]+)*$"

# Program 2 foundation (`program-2/formal/`): the `P1` library imports only its own `P1.*` roots (+ mathlib);
# it must not reach into any series tree or `archive/`. Program 2 series (added later under
# `program-2/series-NN/formal/`) get their own checks when registered.
check program-2 "^import P1(\.[A-Za-z0-9_]+)*$"

# Program 2 Series 0 (`program-2/series-0/formal/`): the `P2S0` library may import the `P1` foundation
# (Program 2 permits it) and its own `P2S0.*` roots (+ mathlib); any other series' tree is forbidden.
check program-2/series-0 "^import (P1|P2S0)(\.[A-Za-z0-9_]+)*$"

# Program 2 Series 1 (`program-2/series-1/formal/`): the `P2S1` library imports its predecessor `P2S0` and its
# own `P2S1.*` roots (+ mathlib); the `P1` prior art is reached transitively through S0, not imported directly;
# any other series' tree is forbidden.
check program-2/series-1 "^import (P2S0|P2S1)(\.[A-Za-z0-9_]+)*$"

# Program 2 Series 2 (`program-2/series-2/formal/`): the `P2S2` library imports its predecessor `P2S1` and its
# own `P2S2.*` roots (+ mathlib); the `P2S0` ground and `P1` prior art are reached transitively through S1, not
# imported directly; any other series' tree is forbidden.
check program-2/series-2 "^import (P2S1|P2S2)(\.[A-Za-z0-9_]+)*$"

# Program 2 Series 3 (`program-2/series-3/formal/`): the `P2S3` library imports its predecessor `P2S2` and its
# own `P2S3.*` roots (+ mathlib); the `P2S1` / `P2S0` ground and `P1` prior art are reached transitively through
# S2, not imported directly; any other series' tree is forbidden. The convergence machinery is built fresh in
# `P2S3.*`, never imported from Series 12.
check program-2/series-3 "^import (P2S2|P2S3)(\.[A-Za-z0-9_]+)*$"

# Program 2 Series 4 (`program-2/series-4/formal/`): the `P2S4` library imports its predecessor `P2S3` and its
# own `P2S4.*` roots (+ mathlib); the `P2S2` / `P2S1` / `P2S0` ground and `P1` prior art are reached transitively
# through S3, not imported directly; any other series' tree is forbidden. The world and the two gradings are
# built fresh in `P2S4.*`.
check program-2/series-4 "^import (P2S3|P2S4)(\.[A-Za-z0-9_]+)*$"

exit $fail
