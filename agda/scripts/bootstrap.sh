#!/bin/bash
#
# Idempotent, network-policy-aware bootstrap for the Agda coinductive layer
# (agda/RelExist/Coinductive.agda). Installs Agda + the standard library from the
# Ubuntu archive and registers the library so `agda` finds it by default.
#
# Kept separate from the Lean bootstrap and invoked non-fatally by the
# SessionStart hook: a session without Agda still has the full Lean development.
set -euo pipefail

# Already set up? (binary present and stdlib registered.)
if command -v agda >/dev/null 2>&1 && [ -f "$HOME/.agda/libraries" ]; then
  exit 0
fi

export DEBIAN_FRONTEND=noninteractive

# Install agda + agda-stdlib (--no-install-recommends avoids an unrelated, often
# stale mysql/mailutils dependency chain). Retry once behind `apt-get update`.
if ! apt-get install -y --no-install-recommends agda agda-stdlib >/dev/null 2>&1; then
  apt-get update >/dev/null 2>&1 || true
  apt-get install -y --no-install-recommends agda agda-stdlib
fi

# Register the standard library (the Ubuntu package ships sources but no .agda-lib).
LIB=/usr/share/agda-stdlib/standard-library.agda-lib
if [ ! -f "$LIB" ]; then
  printf 'name: standard-library\ninclude: .\n' > "$LIB"
fi
mkdir -p "$HOME/.agda"
echo "$LIB" > "$HOME/.agda/libraries"
echo "standard-library" > "$HOME/.agda/defaults"
