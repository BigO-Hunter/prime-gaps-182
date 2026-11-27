#!/bin/bash
# Compile the kloosterman-sheaf receipts against the already-built Weil+Stacks+Mathlib
# oleans, without creating a new lake package (no rebuild of mathlib, no new toolchain).
#
# The Lean search path is taken from the Weil package's own lake environment, so this script
# only works while "$WEIL_VERIFY" (the Weil checkout) has its dependency oleans in place.
set -euo pipefail

KS="$(cd "$(dirname "$0")" && pwd)"
WEIL="${WEIL_VERIFY:?Set WEIL_VERIFY to the Weil checkout containing .lake/packages}"
export PATH="/opt/homebrew/bin:$PATH"
export LEAN_NUM_THREADS=1

if [ ! -f "$KS/build/lean_path.txt" ]; then
  mkdir -p "$KS/build"
  (cd "$WEIL" && lake env printenv LEAN_PATH > "$KS/build/lean_path.txt")
fi
LEAN_PATH="$(cat "$KS/build/lean_path.txt")"
export LEAN_PATH="$LEAN_PATH:$KS/build"

cd "$KS"
LEAN_BIN="$HOME/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean"
for f in "$@"; do
  mod="$(basename "$f" .lean)"
  echo "== $mod"
  "$LEAN_BIN" -o "build/$mod.olean" -i "build/$mod.ilean" "$f"
done
echo "== ok"
