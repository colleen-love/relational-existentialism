#!/usr/bin/env bash
# Closure gate — reset to scratch only (handoff I.II, the arena change).
#
# The project moved to a new foundation (a quantaloid / allegory with relations as the primitive arrow). The
# prior edifice (paper-2/paper-3/scratch/foundation/theory) is archived under `archive/traceable-smt/` as
# structural reference; archived code is **not** gated. Only `scratch/` is live. Its one library has grown
# from the empty `Paper1` skeleton into the `Spec2xx` roots (all registered in lake/lakefile.toml), which
# import one another freely — the closure rule is that scratch imports resolve only to scratch's own roots
# (+ mathlib), never to `archive/`. (Updated post-Spec203b: the original skeleton-era rule allowed only
# `Paper1.*` and flagged the intended Spec cross-imports as leaks.)
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

# scratch is the live library: its roots (`Paper1`, `Spec200`, `Spec201`–`Spec201d`, `Spec202`,
# `Spec203`, `Spec203b`, ...) may import each other (+ mathlib); nothing outside them is allowed.
check scratch "^import (Paper1(\.[A-Za-z0-9_]+)*|Spec[0-9]{3}[a-z]?)$"

# archive/ — NOT gated (structural reference, not built).
echo "EXEMPT archive/traceable-smt/ — prior edifice kept as structural reference, not built or gated"

exit $fail
