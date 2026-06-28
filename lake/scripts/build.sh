#!/usr/bin/env bash
#
# Everyday build for lake/. Assumes the environment Setup script already
# planted the toolchain and warmed mathlib (snapshotted), so this NEVER builds
# mathlib from source:
#
#   * it does not run `lake update` — that re-resolves deps and is the usual way
#     the cache gets invalidated; it belongs in setup only;
#   * `lake exe cache get` only unpacks/downloads prebuilt oleans, never compiles
#     them — a no-op on a snapshot hit, a few-second re-unpack from
#     ~/.cache/mathlib if .lake was wiped;
#   * if the mathlib oleans still aren't present, it aborts loudly rather than
#     silently grind through a from-source mathlib build.
#
# Usage:
#   scripts/build.sh                 # RelExist (core) + Scratch (mathlib-backed)
#   scripts/build.sh RelExist        # core only — no mathlib needed
#   NO_CACHE_GET=1 scripts/build.sh  # skip the cache refresh (offline / fast)
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."          # -> lake/
export PATH="$HOME/.elan/bin:$PATH"

TARGETS=("$@"); [ ${#TARGETS[@]} -eq 0 ] && TARGETS=(RelExist Scratch)

needs_mathlib=0
for t in "${TARGETS[@]}"; do [ "$t" = "Scratch" ] && needs_mathlib=1; done

MATHLIB_LIB=".lake/packages/mathlib/.lake/build/lib"

# Re-materialize prebuilt oleans only when a mathlib target is requested.
if [ "$needs_mathlib" = "1" ] && [ "${NO_CACHE_GET:-0}" != "1" ]; then
  echo "[build] refreshing prebuilt mathlib cache (lake exe cache get)..."
  lake exe cache get || echo "[build] cache get reported issues; continuing to guard"
fi

# Guard: refuse to kick off a from-source mathlib build.
if [ "$needs_mathlib" = "1" ] \
   && ! find "$MATHLIB_LIB" -name '*.olean' -print -quit 2>/dev/null | grep -q .; then
  echo "[build] ERROR: no mathlib oleans under $MATHLIB_LIB." >&2
  echo "[build] Building Scratch now would recompile mathlib from source." >&2
  echo "[build] Re-run the environment Setup script (and confirm the cache host" >&2
  echo "[build] is in allowedDomains) to warm the cache first." >&2
  echo "[build] To build just the core meanwhile:  scripts/build.sh RelExist" >&2
  exit 1
fi

echo "[build] building: ${TARGETS[*]}"
lake build "${TARGETS[@]}"
echo "[build] done."
