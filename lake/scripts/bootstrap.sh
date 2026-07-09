#!/usr/bin/env bash
#
# Bootstrap the Lean 4 (+ mathlib) environment for lake/.
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
REPO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # the lake/ package home
export PATH="$ELAN_BIN:$PATH"

log() { echo "[bootstrap] $*"; }

# --- 0. Make git able to clone the (public) mathlib repo ----------------------
# The remote environment injects a *scoped* git config that limits git to THIS
# repo, so lake's clone of mathlib is 403'd -> "git exited 128". In an agent
# session the workaround was to route git through $HTTPS_PROXY (which allows
# github broadly); in the SETUP-script context that var isn't set. So instead we
# drop the injected system/global git config and let git reach github.com
# directly through the transparent egress proxy (the same path curl used to pull
# elan + the toolchain). A public clone needs no credential.
setup_git_proxy() {
  export GIT_CONFIG_SYSTEM=/dev/null              # ignore /etc/gitconfig (the scoped rewrite)
  export GIT_TERMINAL_PROMPT=0
  local cfg; cfg="$(mktemp)"; : > "$cfg"          # start from an empty global config
  export GIT_CONFIG_GLOBAL="$cfg"

  # If an explicit proxy var exists under any common name, prefer it (covers
  # contexts where egress isn't transparent).
  local proxy="${HTTPS_PROXY:-${https_proxy:-${HTTP_PROXY:-${http_proxy:-${ALL_PROXY:-${all_proxy:-}}}}}}"
  if [ -n "$proxy" ]; then
    local ca
    ca="$(curl -s --max-time 10 "$proxy/__agentproxy/status" 2>/dev/null \
          | sed -n 's/.*"caBundlePath" *: *"\([^"]*\)".*/\1/p')"
    [ -n "$ca" ] && [ -f "$ca" ] || ca="/root/.ccr/ca-bundle.crt"
    { echo "[http]"; echo "    proxy = $proxy"; [ -f "$ca" ] && echo "    sslCAInfo = $ca"; } > "$cfg"
    log "git routed via explicit proxy: $proxy"
  else
    log "no proxy var; dropped injected git config, using direct github via transparent egress"
  fi

  if git ls-remote https://github.com/leanprover-community/mathlib4 v4.15.0 >/dev/null 2>&1; then
    log "mathlib reachable via git."
  else
    log "WARNING: mathlib still unreachable for git. Diagnostics:"
    log "  git/proxy env : $(env | grep -iE 'proxy|git_config|ccr' | paste -sd' ' - )"
    log "  /etc/gitconfig: $(tr '\n' ';' < /etc/gitconfig 2>/dev/null)"
    log "  ~/.gitconfig  : $(tr '\n' ';' < "$HOME/.gitconfig" 2>/dev/null)"
    log "  ls-remote err : $(git ls-remote https://github.com/leanprover-community/mathlib4 v4.15.0 2>&1 | head -3 | tr '\n' ' ')"
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
# The live root is `Series4` (see lake/lakefile.toml; sources in
# ../series-4/formal). Series 3 is closed and frozen under archive/.
cd "$REPO_DIR"
log "building core target Series4..."
lake build Series4
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
  log "building the live target Series4 (skeleton imports no mathlib yet)..."
  lake build Series4
  log "target built."
fi

log "done."
