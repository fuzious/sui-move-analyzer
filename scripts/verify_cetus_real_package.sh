#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CACHE_DIR="$ROOT_DIR/target/security_cetus"
REPO_DIR="$CACHE_DIR/cetus-clmm-vuln"
PACKAGE_DIR="$REPO_DIR/sui/cetus_clmm"
REV="74e98b69334ecc84fc419d10a59d3d4e1f832d32"
REPO="https://github.com/CetusProtocol/cetus-clmm-interface.git"

mkdir -p "$CACHE_DIR"

if [[ ! -d "$REPO_DIR/.git" ]]; then
  git clone --no-checkout "$REPO" "$REPO_DIR"
fi

git -C "$REPO_DIR" fetch --depth 1 origin "$REV"
git -C "$REPO_DIR" checkout --force "$REV"

echo "[verify_cetus] building real Cetus package with sui move build"
(cd "$PACKAGE_DIR" && sui move build)

echo "[verify_cetus] running scoped analyzer with framework auto-retry"
OUTPUT="$(cargo run --quiet --bin security_demo -- --dependency-mode auto --scope direct "$PACKAGE_DIR")"
echo "$OUTPUT"

if grep -qi "address 'std'" <<<"$OUTPUT"; then
  echo "[verify_cetus] analyzer still failed with missing framework addresses" >&2
  exit 1
fi

if grep -qi "unbound module" <<<"$OUTPUT"; then
  echo "[verify_cetus] analyzer still failed with unresolved framework modules" >&2
  exit 1
fi

if ! grep -q "security/" <<<"$OUTPUT"; then
  echo "[verify_cetus] expected at least one security finding from the real Cetus checkout" >&2
  exit 1
fi
