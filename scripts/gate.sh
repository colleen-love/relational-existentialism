#!/usr/bin/env bash
# Closure gates for the six-root layout (handoff XIII).
# A paper imports only itself + foundation; theory imports only theory + foundation;
# foundation imports only mathlib. Resolution is by file location (module names are
# stable in paper-1 as Scratch.*/RelExist.*, root-prefixed in theory as Theory.*).
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
check paper-1   "^import (Scratch|RelExist|Foundation)\."
check paper-2   "^import (Paper2|Foundation)\."
check theory    "^import (Theory|Foundation)\."
check foundation "^import Foundation\."
exit $fail
