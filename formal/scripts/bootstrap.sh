#!/usr/bin/env bash
#
# Bootstrap the Lean 4 (+ mathlib) environment for formal/.
#
# Idempotent and non-interactive. Designed for the network policy in our remote
# sessions, which allows github.com + pypi.org but blocks release.lean-lang.org /
# api.github.com (so `elan` can't auto-resolve toolchains) and the mathlib cache
# blob (so mathlib must compile from source). It therefore:
#   1. installs `elan` from its GitHub release,
#   2. plants the Lean toolchain by direct download (decompressing .tar.zst via the
#      `zstandard` PyPI module, since there is no `zstd` binary), registered under
#      the name `elan` derives from the pin so `lean-toolchain` resolves offline,
#   3. builds the dependency-free core (fast), and
#   4. builds the mathlib-backed target (slow the first time, cached afterwards).
#
# Re-running is cheap: each step is skipped when its result is already present, so
# once a container's state is cached this returns in seconds.
#
# Env knobs:
#   SKIP_MATHLIB=1   skip step 4 (toolchain + core only)
set -euo pipefail

LEAN_VER="4.15.0"
ELAN_BIN="$HOME/.elan/bin"
TC_LINK="$HOME/.elan/toolchains/leanprover--lean4---v${LEAN_VER}"
TC_CACHE="$HOME/.cache/lean-toolchains"
REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # the formal/ directory
export PATH="$ELAN_BIN:$PATH"

log() { echo "[bootstrap] $*"; }

# --- 1. elan (Lean toolchain manager) ----------------------------------------
if ! command -v elan >/dev/null 2>&1; then
  log "installing elan from GitHub release..."
  tmp="$(mktemp -d)"
  curl -fL --retry 3 --max-time 180 -o "$tmp/elan.tar.gz" \
    https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz
  tar -xzf "$tmp/elan.tar.gz" -C "$tmp"
  "$tmp/elan-init" -y --default-toolchain none
  rm -rf "$tmp"
  export PATH="$ELAN_BIN:$PATH"
else
  log "elan already present"
fi

# --- 2. Lean toolchain (planted manually; elan can't auto-resolve under policy) --
if [ -x "$TC_LINK/bin/lean" ]; then
  log "Lean ${LEAN_VER} toolchain already present"
else
  log "downloading Lean ${LEAN_VER} toolchain (direct asset)..."
  python3 -m pip install --quiet zstandard
  tmp="$(mktemp -d)"
  curl -fL --retry 3 --max-time 600 -o "$tmp/lean.tar.zst" \
    "https://github.com/leanprover/lean4/releases/download/v${LEAN_VER}/lean-${LEAN_VER}-linux.tar.zst"
  log "decompressing (.tar.zst -> .tar via python zstandard)..."
  python3 - "$tmp/lean.tar.zst" "$tmp/lean.tar" <<'PY'
import sys, zstandard
with open(sys.argv[1], "rb") as fi, open(sys.argv[2], "wb") as fo:
    zstandard.ZstdDecompressor().copy_stream(fi, fo, read_size=1 << 20, write_size=1 << 20)
PY
  mkdir -p "$TC_CACHE"
  tar -xf "$tmp/lean.tar" -C "$TC_CACHE"
  rm -rf "$tmp"
  mkdir -p "$HOME/.elan/toolchains"
  ln -sfn "$TC_CACHE/lean-${LEAN_VER}-linux" "$TC_LINK"
fi
# A stable default so `lean`/`lake` work outside the project dir too.
elan default "leanprover/lean4:v${LEAN_VER}" >/dev/null 2>&1 || true
log "lean: $(lean --version 2>&1 | head -1)"

# --- 3. Build the dependency-free core (always; fast) -------------------------
cd "$REPO_DIR"
log "building core target RelExist..."
lake build RelExist
log "core built."

# --- 4. Build the mathlib-backed target (slow first time, cached after) -------
if [ "${SKIP_MATHLIB:-0}" = "1" ]; then
  log "SKIP_MATHLIB=1 set — skipping mathlib build."
else
  log "building mathlib-backed target Scratch (fetches pinned deps; compiles mathlib"
  log "from source the first time because the prebuilt cache is unreachable)..."
  lake build Scratch
  log "mathlib-backed target built."
fi

log "done."
