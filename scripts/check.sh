#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/palomar_static_check.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'error: lake is not on PATH. Load $HOME/.elan/env, or use the GitHub Actions checks.' >&2
  exit 1
fi
lake build Sqrt6KissingBound Solution Challenge
lake env lean Axioms.lean
sha256sum --check SOURCE_SHA256SUMS
echo 'Lean, source-integrity, and Palomar packaging checks passed.'
echo 'Full independent verification additionally requires: bash scripts/verify-comparator.sh'
