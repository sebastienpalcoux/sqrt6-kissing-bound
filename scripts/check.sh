#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
pattern='(^|[[:space:]])(sorry|admit|native_decide)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]'
if grep -R -n -E --include='*.lean' "$pattern" \
    Sqrt6KissingBound Sqrt6KissingBound.lean Axioms.lean; then
  echo 'forbidden proof hole, project-defined axiom, or unsafe evaluation shortcut found' >&2
  exit 1
fi
lake build
lake env lean Axioms.lean
