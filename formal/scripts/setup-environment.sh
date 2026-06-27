#!/usr/bin/env bash
#
# Environment Setup script for Claude Code on the web. Lives in formal/scripts/.
# Set the environment's "Setup script" field to:
#     cd "$(git rev-parse --show-toplevel)" && bash formal/scripts/setup-environment.sh
#
# Runs once per environment; the filesystem is then snapshotted and reused, so
# the toolchain + mathlib warm persists instead of being redone each session.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"   # -> formal/scripts
REPO_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"                  # -> repo root
LOG="/tmp/relexist-setup.log"

# --- Lean 4 + mathlib (fatal: the formal development depends on it) -----------
echo "[setup] bootstrapping Lean + mathlib (slow, one-time)..."
if "$SCRIPT_DIR/bootstrap.sh" > "$LOG" 2>&1; then
  echo "[setup] Lean ready: $("$HOME/.elan/bin/lean" --version 2>/dev/null | head -1)"
else
  echo "[setup] Lean bootstrap FAILED — tail of $LOG:"; tail -30 "$LOG"; exit 1
fi

# --- Agda, Layer 5 (non-fatal) ------------------------------------------------
echo "[setup] bootstrapping Agda..."
if "$REPO_DIR/agda/scripts/bootstrap.sh" >> "$LOG" 2>&1; then
  echo "[setup] Agda ready: $(agda --version 2>/dev/null | head -1)"
else
  echo "[setup] Agda bootstrap skipped/failed (non-fatal); see $LOG"
fi

echo "[setup] done — filesystem snapshotted from here."
