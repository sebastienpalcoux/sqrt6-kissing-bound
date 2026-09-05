# Archived development workflows

The previous workflow directory is preserved intact in `legacy-workflows/` for provenance. Those files are outside `.github/workflows/` and are not active GitHub Actions workflows.

The sole active workflow on this branch is **Full Lean certificate**, retained without changes at `.github/workflows/dev-check-quiet.yml`. It has read-only repository permissions and performs the clean build and 16-theorem axiom whitelist audit. It does not commit source changes or diagnostic logs back to the repository.

The permanent source set passed this workflow in run `33933962286`, at commit `dea00ea3862c1a2dc7773a1afb71e9f4a42e67ac`, on September 5, 2026. The complete certificate artifact is named `sqrt6-complete-lean-certificate`.

This archival change does not alter any certified source, source hash, build configuration, manuscript, or active verification workflow. It prevents obsolete one-off development checks from firing on future source changes.
