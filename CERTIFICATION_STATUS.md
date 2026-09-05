# Verification

The certificate includes every step of the Euclidean-volume proof presented in the manuscript, the existence of an attained kissing number, the value τ₂ = 6, and optimality of the universal base.

## Reproduce the checks

```bash
lake exe cache get
bash scripts/check.sh
sha256sum --check SOURCE_SHA256SUMS
```

`check.sh` builds the root and all its dependencies, rejects proof holes and project-defined axioms, and checks the public conclusions with exactly their dimension and configuration hypotheses. `Axioms.lean` audits all project declarations, including private ones. It accepts only the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Dependency revisions: `lake-manifest.json`.
- Proof-source fingerprints: `SOURCE_SHA256SUMS`.

The read-only GitHub workflows build the Lean certificate and the manuscript PDF on pull requests and `main`. Their check results identify the exact source commit verified.

## Checked source set — 5 September 2026

The complete local check passed with 8,728 build jobs and an axiom audit of **274 project declarations**. The root imports all 21 project modules. The audit includes the exact supremum statement for the actual kissing numbers and the characterization of their universal exponential bases.

The six-page manuscript PDF was rebuilt from the included LaTeX source and visually reviewed. Both GitHub workflows check the published source with read-only permissions.
