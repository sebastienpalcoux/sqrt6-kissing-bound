# Certification status: complete geometric formalization

The complete proof source set passed a clean Lean build, source scan, and an enforced 16-theorem axiom audit on September 5, 2026, in GitHub Actions run `33933318109`, staging commit `449ebb9b62419d9d90eceef444f09a9fdde2e48e`.

These exact sources have been promoted to the ordinary Lean project. The permanent **Full Lean certificate** workflow independently rebuilds them directly from the repository, with no dependency on a development checkpoint artifact. Its successful downloadable artifact records the permanent commit and run in `certification/VERIFICATION.json`.

## What is complete

The formalization proves the all-positive-dimensional bound for actual normalized kissing configurations; realization and maximality of the kissing number; the universal kissing-number bound; the exact values in dimensions one and two; the least-universal-base characterization; the equivalent supremum statement; and the strict recurrence for the actual sine-integral cap fractions.

The proof supplies its own disjointness, measurability, volume calculation, rotation invariance, packing, and low-dimensional estimates. None of these are assumed in the final public theorems.

## Trusted foundations and reproducibility

The source dependency closure contains 32 Lean files, counting the root import file and `Axioms.lean`. Sixteen public theorems have their transitive axiom dependencies checked against the whitelist:

```text
propext
Classical.choice
Quot.sound
```

There are no proof holes, new project axioms, or native-decision shortcuts. `scripts/check_axioms.py` rejects missing or duplicate reports as well as every non-whitelisted axiom.

The toolchain is Lean 4.33.1, with Mathlib pinned to `0df444a360eaa60ab8c11dca51a86af692955474`. `SOURCE_SHA256SUMS` identifies the proof and build files. Reproduce with:

```bash
lake exe cache get
bash scripts/check.sh
```

A green development workflow alone is not a certificate. For the permanent workflow, verification is enforced by nonzero exit status on failure, source hashes, the clean build, and the complete axiom whitelist. The final artifact contains explicit verification records and compiler output.

## Scope qualification

This is an unconditional formal proof of the specified mathematical results relative to the standard Lean foundations and pinned Mathlib. It is not an assertion of human peer review, a literature-priority assessment, or a line-by-line translation of every informal proof. The principal geometric theorem is proved by an alternative volume-packing argument described in `PROOF_GUIDE.md`.

The original manuscript is preserved unchanged, including its historical disclosure concerning the earlier conditional certificate. That disclosure does not describe the later complete formalization.
