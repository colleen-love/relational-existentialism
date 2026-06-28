#!/usr/bin/env bash
# Closure gates for the six-root layout (handoff XIII), as amended by handoff XX.
#
# Original closure (XIII): a paper imports only itself + foundation; theory imports only
# theory + foundation; foundation imports only mathlib. Resolution is by file location
# (module names are stable in paper-1 as Scratch.*/RelExist.*, root-prefixed in theory as
# Theory.*).
#
# Amendment (XX) — the canonical axiom layer is a STABLE SHARED layer, like foundation/.
# Handoff XX collapsed the per-paper A3 *divergence* (A3 reframed as a process; the eigenform,
# the generative engine, and the modular self all derived as theorems of the one process —
# Theory.Axioms). With the divergence gone, the axioms are one canonical, version-pinned layer.
# So a paper may now ALSO import the canonical layer `Theory.Axioms` (not arbitrary `Theory.*`,
# only the canonical module) — and pins the layer it was proved against in
# `<paper>/spec/AXIOM-PROVENANCE.md`. The freeze shifts from *duplication* to *version-pinning*.
#
#   * NAMESPACE EXCEPTION (paper-1). The XIII fork-and-freeze gave paper-1's `theory/` forks
#     paper-one's own `RelExist.*` namespace so they would stay byte-identical. That same choice
#     *blocks* a literal `import Theory.Axioms` into paper-1: pulling in the transitively-required
#     `Theory.*` forks collides with paper-1's `Scratch.*` (`environment already contains
#     'RelExist.RotatingSpectrum.Ucoh'`). So paper-1 keeps its byte-identical forks as the
#     version-pinned copy and consumes the canonical layer by CITATION + PIN (the same mechanism
#     by which paper two cites paper one's arrow). The `Theory.Axioms` allowance below is therefore
#     latent for paper-1 (available, structurally unused) until the forks are unified.
set -u
cd "$(dirname "$0")/.." || exit 2
fail=0

# The canonical axiom layer a paper may import (handoff XX). Exactly `Theory.Axioms`, not any
# other `Theory.*` fork.
CANON='(^import Theory\.Axioms\b)'

check () { # <root> <allowed-egrep>
  local root="$1" allowed="$2"
  local bad
  bad=$(grep -rhE "^import " "$root/formal" 2>/dev/null | grep -vE "Mathlib" \
        | grep -vE "$allowed" || true)
  if [ -n "$bad" ]; then
    echo "LEAK in $root/:"; echo "$bad" | sed 's/^/   /'; fail=1
  else
    echo "OK   $root/ — imports resolve only to allowed roots (+ canonical axiom layer)"
  fi
}

pin () { # <root> — a paper must pin the canonical axiom layer it was proved against
  local root="$1"
  local f="$root/spec/AXIOM-PROVENANCE.md"
  if grep -qiE "canonical axiom|Theory\.Axioms" "$f" 2>/dev/null; then
    echo "OK   $root/ — pins the canonical axiom layer ($f)"
  else
    echo "UNPINNED $root/ — no canonical-axiom pin in $f"; fail=1
  fi
}

# Closure (XIII) + canonical-layer allowance (XX). A paper imports itself + foundation +
# the canonical axiom layer; theory imports only theory + foundation; foundation only mathlib.
check paper-1   "(^import (Scratch|RelExist|Foundation)\.)|$CANON"
check paper-2   "(^import (Paper2|Foundation)\.)|$CANON"
check theory    "^import (Theory|Foundation)\."
check foundation "^import Foundation\."

# Version-pinning (XX): each paper pins the canonical layer commit in its AXIOM-PROVENANCE.md.
pin paper-1
pin paper-2

exit $fail
