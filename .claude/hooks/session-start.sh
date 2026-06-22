#!/bin/bash
#
# SessionStart hook for Claude Code on the web.
#
# Bootstraps the Lean 4 (+ mathlib) environment for formal/ so the formal
# development builds and checks immediately, and so later sessions reuse the cached
# container state instead of redoing the work. Synchronous: the session starts only
# after this completes, which guarantees the toolchain is ready before any build.
#
# All heavy lifting (idempotent, network-policy-aware) lives in
# formal/scripts/bootstrap.sh; this hook just gates on the remote environment,
# persists PATH, and keeps the verbose build log out of the agent's context.
set -euo pipefail

# Local (non-remote) sessions: do nothing — developers manage their own toolchain.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

# Persist the Lean toolchain on PATH for the whole session.
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$CLAUDE_ENV_FILE"

LOG="/tmp/relexist-bootstrap.log"
if "$CLAUDE_PROJECT_DIR/formal/scripts/bootstrap.sh" > "$LOG" 2>&1; then
  echo "[session-start] Lean env ready: $("$HOME/.elan/bin/lean" --version 2>/dev/null | head -1)"
else
  echo "[session-start] bootstrap FAILED — tail of $LOG:"
  tail -25 "$LOG"
  exit 1
fi
