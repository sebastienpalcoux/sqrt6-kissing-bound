# Certification status

## Existing successful certification

- Original repository: `sebastienpalcoux/Fusion-Categories`
- Temporary branch: `gpt-pro/sqrt6-kissing-certificate`
- Certified commit: `90edce0218112c39a163410d4b7eb66dee5ebc41`
- GitHub Actions run: `33720108355`
- Result: **success**
- Lean: `v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- `lake build`: successful (`8708` jobs)
- Axiom audit: successful (`49` declarations; only `propext`, `Classical.choice`, and `Quot.sound`)
- Source scan: no `sorry`, `admit`, project-defined `axiom`, or `native_decide`

The principal Lean sources and pinned dependency files in this repository are copied from that certified project. The workflow in this dedicated layout reruns the same checks from the repository root.

See [`FORMALIZATION_SCOPE.md`](FORMALIZATION_SCOPE.md) for the exact mathematical scope.
