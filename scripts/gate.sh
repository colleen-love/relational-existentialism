#!/usr/bin/env bash
# Closure gate — reset to series-2 only (handoff I.II, the arena change).
#
# The project moved to a new foundation (a quantaloid / allegory with relations as the primitive arrow).
# Only `series-2/` is live. Its one library has grown from the empty `Series2` skeleton into the `Spec2xx`
# roots (all registered in lake/lakefile.toml), which import one another freely — the closure rule is that
# series-2 imports resolve only to series-2's own roots (+ mathlib). (Updated post-Spec203b: the original
# skeleton-era rule allowed only `Series2.*` and flagged the intended Spec cross-imports as leaks.)
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

# series-2 is the live library: its roots (`Series2`, `Spec200`, `Spec201`–`Spec201d`, `Spec202`,
# `Spec203`, `Spec203b`, ...) may import each other (+ mathlib); nothing outside them is allowed.
check series-2 "^import (Series2(\.[A-Za-z0-9_]+)*|Spec[0-9]{3}[a-z]?)$"

exit $fail
