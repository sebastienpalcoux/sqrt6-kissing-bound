#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

# Palomar's verifier pins, checked against its published workflow on 2026-09-05.
# lean4export is pinned to the matching Lean 4.33.0 exporter.
comparator_commit=575674928e239f5bc452aab72d1dd7b0f1326494
lean4export_commit=15f6055e299ad5b89345e533cc2192f4cc00f659
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for command in cargo git go lake python3; do
  if ! command -v "$command" >/dev/null 2>&1; then
    echo "error: $command is required for Comparator; alternatively use GitHub Actions." >&2
    exit 1
  fi
done
python3 "$repository_root/scripts/palomar_static_check.py" --online
mkdir -p "$cache_root" "$bin_dir"
checkout_exact() {
  local repository=$1 destination=$2 commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
  test "$(git -C "$destination" rev-parse HEAD)" = "$commit"
}
checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"
project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$export_toolchain" ]; then
  echo "error: project/exporter toolchain mismatch: $project_toolchain versus $export_toolchain" >&2
  exit 1
fi
checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"
CGO_ENABLED=0 GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"
(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)
cd "$repository_root"
lake exe cache get
PALOMAR_LANDRUN_BIN="$bin_dir/landrun" \
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
  lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json
echo 'Comparator and independent NanoDa replay passed for the selected statements.'
