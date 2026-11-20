#!/usr/bin/env bash
# fetch_frozen.sh — sha-pinned fetch of the frozen per-cell mass payload.
#
# The full per-cell frozen masses (p^frozen_c) ship ONLY in the upstream
# release archive (the local fine_coarse_inner_sources payload carries the D3
# affine-prefix suprema, not the masses). This script fetches the release
# asset + its sha256 pin, verifies, and extracts into frozen/extracted/.
#
# The blob is NOT committed (repo must not bloat); only this script and the
# hash manifest are. Never read the archive or its contents as text — parse
# data files with Python (json/npz libraries) only.
set -euo pipefail
DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$DIR"
RELEASE_TAG="external-numerics-20260909"
REPO="romyar1/prime-gaps-lean"
ZIP="prime-gaps-external-182-verified-20260909.zip"

if [ ! -f "$ZIP" ]; then
  # asset id 554239243 (pinned from the release page 2026-11-07)
  gh api "repos/$REPO/releases/assets/554239243" -H "Accept: application/octet-stream" > "$ZIP"
fi
if [ ! -f "$ZIP.sha256" ]; then
  gh release download "$RELEASE_TAG" -R "$REPO" -p "*.sha256" -O "$ZIP.sha256"
fi

echo "actual:  $(shasum -a 256 "$ZIP")"
echo "pinned:  $(cat "$ZIP.sha256")"
echo "$ZIP" | shasum -a 256 -c <(sed 's|  .*|  '"$ZIP"'|' "$ZIP.sha256")

if [ ! -d extracted ]; then
  mkdir -p extracted
  unzip -q "$ZIP" -d extracted
  (cd extracted && find . -type f -exec shasum -a 256 {} \; ) > ../EXTRACTED_MANIFEST.sha256
fi
echo "OK: extracted to extracted/ ; manifest at EXTRACTED_MANIFEST.sha256"
