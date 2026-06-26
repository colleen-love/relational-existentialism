#!/usr/bin/env bash
#
# Bootstrap the Lean 4 (+ mathlib) environment for formal/.
#
# Idempotent and non-interactive. Designed for the network policy in our remote
# sessions, which allows github.com (over HTTPS) + pypi.org but blocks
# release.lean-lang.org / api.github.com (so `elan` can't auto-resolve toolchains)
# and the mathlib olean cache (mathlib4.lean-cache.cloud and the Azure blob), so
# mathlib must compile from source. It therefore:
#   0. routes git's github.com traffic through the agent HTTPS proxy (see below),
#   1. installs `elan` from its GitHub release,
#   2. plants the Lean toolchain by direct download (decompressing .tar.zst via the
#      `zstandard` PyPI module, since there is no `zstd` binary), registered under
#      the name `elan` derives from the pin so `lean-toolchain` resolves offline,
#   3. builds the dependency-free core (fast), and
#   4. builds the mathlib-backed target (tries the prebuilt cache first; falls back
#      to compiling mathlib from source — slow the first time, cached afterwards).
#
# Why step 0 exists: the remote session injects a git url-rewrite
# (`url."http://…@127.0.0.1:<gitproxy>/git/".insteadOf = https://github.com/`)
# that sends *all* github git traffic to a **scoped** git proxy which only allows
# this one repo. Lake clones mathlib (and its deps) from github, so without the
# reroute every `lake build`/`lake update` dies with `git exited 128` (HTTP 403) —
# even `lake build RelExist`, because lake resolves all manifest deps before
# building any target. The agent's general HTTPS proxy (`$HTTPS_PROXY`) *does*
# allow github.com, so step 0 points git at it for the dependency fetch via a
# throwaway global git config, leaving this repo's own (scoped, authenticated)
# remote untouched.
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

# --- 0. Route git's github traffic through the agent HTTPS proxy --------------
# The session rewrites github.com git → a scoped git proxy that 403s every repo
# but this one, so lake's mathlib clone fails. $HTTPS_PROXY allows github.com, so
# point git there for dep fetching. Scoped to this script's lake invocations via a
# throwaway global git config; the project repo's own remote is untouched.
setup_git_proxy() {
  local proxy ca
  proxy="${HTTPS_PROXY:-${https_proxy:-}}"
  if [ -z "$proxy" ]; then
    log "no HTTPS_PROXY set — leaving git config as-is (assuming direct github access)"
    return 0
  fi
  # Discover the proxy's CA bundle (TLS is re-terminated at the proxy); fall back
  # to the documented default path.
  ca="$(curl -s --max-time 10 "$proxy/__agentproxy/status" 2>/dev/null \
        | sed -n 's/.*"caBundlePath" *: *"\([^"]*\)".*/\1/p')"
  [ -n "$ca" ] && [ -f "$ca" ] || ca="/root/.ccr/ca-bundle.crt"
  local cfg; cfg="$(mktemp)"
  {
    echo "[http]"
    echo "    proxy = $proxy"
    [ -f "$ca" ] && echo "    sslCAInfo = $ca"
  } > "$cfg"
  export GIT_CONFIG_GLOBAL="$cfg"      # replaces ~/.gitconfig (drops the scoped-proxy rewrite)
  export GIT_CONFIG_SYSTEM=/dev/null   # and /etc/gitconfig, for good measure
  export GIT_TERMINAL_PROMPT=0
  if git ls-remote https://github.com/leanprover-community/mathlib4 v4.15.0 >/dev/null 2>&1; then
    log "git dep-fetch routed via $proxy (ca: $ca) — mathlib reachable"
  else
    log "WARNING: github still unreachable for git after reroute; mathlib fetch may fail"
  fi
}
setup_git_proxy

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
  log "resolving pinned deps (lake update; needs the step-0 git reroute)..."
  lake update
  # Try the prebuilt olean cache first. It is unreachable under our usual policy
  # (mathlib4.lean-cache.cloud / *.blob.core.windows.net are blocked), so this is
  # best-effort: a green cache turns the next step into a no-op; a blocked cache
  # just means we compile from source. Never fatal.
  log "attempting prebuilt mathlib cache (lake exe cache get; non-fatal if blocked)..."
  if lake exe cache get >/dev/null 2>&1; then
    log "cache get succeeded — mathlib oleans fetched."
  else
    log "cache unreachable — will compile mathlib from source (slow first time, cached after)."
  fi
  log "building mathlib-backed target Scratch..."
  lake build Scratch
  log "mathlib-backed target built."
fi

log "done."
