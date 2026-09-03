# Certification status

## Dedicated repository

- Repository: `sebastienpalcoux/sqrt6-kissing-bound`
- Lean: `v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Initial dedicated Lean workflow run: `33726121717`
- Result: **success**
- `lake build`: successful (`8708` jobs)
- Axiom audit: successful (`49` declarations; only `propext`, `Classical.choice`, and `Quot.sound`)
- Source scan: no `sorry`, `admit`, project-defined `axiom`, or `native_decide`

The manuscript source is in `manuscript/sqrt6-kissing-bound.tex`. The reproducible PDF workflow run `33731585406` compiled it successfully and committed `manuscript/sqrt6-kissing-bound.pdf` to the repository.

## Original certification

The same principal Lean sources were first certified at:

- Original repository: `sebastienpalcoux/Fusion-Categories`
- Temporary branch: `gpt-pro/sqrt6-kissing-certificate`
- Certified commit: `90edce0218112c39a163410d4b7eb66dee5ebc41`
- GitHub Actions run: `33720108355`
- Result: **success**

See [`FORMALIZATION_SCOPE.md`](FORMALIZATION_SCOPE.md) for the exact mathematical scope. The present certificate is conditional and does not yet formalize the complete geometric and analytic bridge to the kissing-number theorem.
