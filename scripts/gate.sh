#!/usr/bin/env bash
# Closure gates for the six-root layout (handoff XIII → XXI → XXII).
#
# Closure: a paper imports only itself + theory + foundation; theory imports only theory +
# foundation; foundation imports only mathlib. Resolution is by file location (paper-1 is
# Scratch.*/RelExist.*, paper-2 Paper2.*, theory uniformly Theory.* since XXI).
#
# Stable shared layer (XX/XXI): the canonical axioms + the T.x theorems live in `theory/` and
# change only backward-compatibly. A paper is a THIN layer importing the `Theory.*` it uses +
# foundation + its own `P*.x`, and pins the `theory/` commit in `<paper>/spec/AXIOM-PROVENANCE.md`.
# The spec-XX namespace collision is gone (XXI normalized theory to clean `Theory.*`), so papers
# import the shared nodes directly.
#
# SCRATCH IS A FREE WORKBENCH (XXII). `scratch/` is the living frontier (pre-paper-three). It is
# *intentionally exempt* from the closure check: it may import freely from `paper-1/` and
# `paper-2/` as well as `theory/`/`foundation/`. The cite-don't-import / hoist-to-theory convention
# is enforced ONLY at the promotion event — when scratch *becomes* paper three. (E.g. paper three's
# `Conservation` importing paper one's `Scratch.Decoherence` is a recorded hoist-item, not a
# violation; it resolves at promotion. See scratch/README.md and theory/spec/NODES.md P3.)
set -u
cd "$(dirname "$0")/.." || exit 2
fail=0

# The stable shared theory layer a paper may import (handoff XXI): any `Theory.*` node. The
# proof-DAG reorg promoted the double-imported nodes (the band layer, etc.) into clean `Theory.*`
# names, so a paper is now a THIN layer importing the `T.x` it uses + foundation + its own `P*.x`.
CANON='(^import Theory\.)'

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
  local f="$root/spec/04-provenance.md"
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

# scratch/ — intentionally NOT checked (free workbench until the paper-three promotion, XXII).
echo "EXEMPT scratch/ — free workbench (cross-paper imports allowed until promotion to paper three)"

# Version-pinning (XX): each paper pins the canonical layer commit in its AXIOM-PROVENANCE.md.
pin paper-1
pin paper-2

exit $fail
