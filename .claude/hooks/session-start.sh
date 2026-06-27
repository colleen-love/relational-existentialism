#!/bin/bash
#
# SessionStart hook. Runs every session and is NOT covered by the environment
# snapshot, so it must stay cheap. The heavy Lean/Agda bootstrap now lives in
# scripts/setup-environment.sh (the environment Setup script), whose output IS
# snapshotted and reused. All this does is expose the planted toolchain and set
# a UTF-8 locale (Agda needs it to read its unicode sources) for the session.
set -euo pipefail

[ "${CLAUDE_CODE_REMOTE:-}" != "true" ] && exit 0

echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$CLAUDE_ENV_FILE"
echo 'export LC_ALL=C.UTF-8'              >> "$CLAUDE_ENV_FILE"
