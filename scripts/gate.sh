#!/usr/bin/env bash
# Closure gates for the rotated layout (handoff XIII → XXI → XXII → I.O).
#
# Closure: a paper imports only itself + theory + foundation; theory imports only theory +
# foundation; foundation imports only mathlib. Resolution is by file location. The I.O rotation
# moved the papers back one slot WITHOUT touching module names, so the resolver is unchanged for
# the rotated content: paper-2 is the old paper-1 (Scratch.*/RelExist.*), paper-3 is the old
# paper-2 (Paper3.* — renamed from Paper2.* in lockstep with the folder), theory is uniformly
# Theory.*. paper-1 is the new foundational skeleton (empty Paper1 root, no theorems yet).
#
# Stable shared layer (XX/XXI): the canonical axioms + the T0.x theorems live in `theory/` and
# change only backward-compatibly. A content paper is a THIN layer importing the `Theory.*` it
# uses + foundation + its own roots, and pins the `theory/` commit in `<paper>/spec/04-provenance.md`.
#
# SCRATCH IS A FREE WORKBENCH (XXII). `scratch/` is the living frontier (pre-paper-four). It is
# *intentionally exempt* from the closure check: it may import freely from `paper-2/`/`paper-3/` as
# well as `theory/`/`foundation/`. The cite-don't-import / hoist-to-theory convention is enforced
# ONLY at the promotion event — when scratch *becomes* paper four.
set -u
cd "$(dirname "$0")/.." || exit 2
fail=0

# The stable shared theory layer a paper may import (handoff XXI): any `Theory.*` node.
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

pin () { # <root> — a content paper must pin the canonical axiom layer it was proved against
  local root="$1"
  local f="$root/spec/04-provenance.md"
  if grep -qiE "canonical axiom|Theory\.Axioms" "$f" 2>/dev/null; then
    echo "OK   $root/ — pins the canonical axiom layer ($f)"
  else
    echo "UNPINNED $root/ — no canonical-axiom pin in $f"; fail=1
  fi
}

# Closure (XIII) + canonical-layer allowance (XX). A content paper imports itself + foundation +
# the canonical axiom layer; theory imports only theory + foundation; foundation only mathlib.
# paper-1 is the new skeleton (no formal content yet) — its empty root trivially closes.
check paper-1   "(^import (Paper1|Foundation)\.)|$CANON"
check paper-2   "(^import (Scratch|RelExist|Foundation)\.)|$CANON"
check paper-3   "(^import (Paper3|Foundation)\.)|$CANON"
check theory    "^import (Theory|Foundation)\."
check foundation "^import Foundation\."

# scratch/ — intentionally NOT checked (free workbench until the paper-four promotion, XXII).
echo "EXEMPT scratch/ — free workbench (cross-paper imports allowed until promotion to paper four)"

# Version-pinning (XX): each content paper pins the canonical layer commit in its 04-provenance.md.
# paper-1 is a skeleton (no theorems), so it is not yet pinned.
pin paper-2
pin paper-3

exit $fail
