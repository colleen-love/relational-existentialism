#!/usr/bin/env bash
#
# Environment Setup script for Claude Code on the web.
#
#   Environment → edit → Setup script:   bash scripts/setup-environment.sh
#
# Runs ONCE per environment; Anthropic then snapshots the filesystem and reuses
# it for every later session, skipping this step. That snapshot is what makes
# the toolchain install + mathlib fetch persist, instead of being redone each
# session (which is what happened when this lived in the SessionStart hook).
# It delegates to the existing idempotent layer bootstraps, so re-runs — after
# you edit this script or the allowlist, or after the ~7-day cache expiry — are
# cheap, each step skipping work already on disk.
set -euo pipefail

LOG="/tmp/relexist-setup.log"
PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# --- Lean 4 + mathlib (fatal: the formal development depends on it) -----------
echo "[setup] bootstrapping Lean + mathlib (this is the slow, one-time step)..."
if "$PROJECT_DIR/formal/scripts/bootstrap.sh" > "$LOG" 2>&1; then
  echo "[setup] Lean ready: $("$HOME/.elan/bin/lean" --version 2>/dev/null | head -1)"
else
  echo "[setup] Lean bootstrap FAILED — tail of $LOG:"; tail -30 "$LOG"; exit 1
fi

# --- Agda, Layer 5 (non-fatal: a session without it still has the Lean dev) ---
echo "[setup] bootstrapping Agda..."
if "$PROJECT_DIR/agda/scripts/bootstrap.sh" >> "$LOG" 2>&1; then
  echo "[setup] Agda ready: $(agda --version 2>/dev/null | head -1)"
else
  echo "[setup] Agda bootstrap skipped/failed (non-fatal); see $LOG"
fi

echo "[setup] done — filesystem will be snapshotted from here."
