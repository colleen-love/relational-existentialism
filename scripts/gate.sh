#!/usr/bin/env bash
# Closure gate — reset to paper-1 only (handoff I.II, the arena change).
#
# The project moved to a new foundation (a quantaloid / allegory with relations as the primitive arrow). The
# prior edifice (paper-2/paper-3/scratch/foundation/theory) is archived under `archive/archived/` as
# structural reference; archived code is **not** gated. Only `paper-1/` is live, and while it is a skeleton
# the check is trivial: its (empty) `Paper1` root imports nothing outside itself. The cross-root closure
# rules will grow back here with the new arena (spec II.1+).
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

# paper-1 is the new relational skeleton: it may import only its own `Paper1.*` root (+ mathlib).
check paper-1 "^import Paper1\."

# archive/ — NOT gated (structural reference, not built).
echo "EXEMPT archive/archived/ — prior edifice kept as structural reference, not built or gated"

exit $fail
