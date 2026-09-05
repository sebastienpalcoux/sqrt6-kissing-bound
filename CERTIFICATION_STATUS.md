# Verification record

## Complete local certificate — 5 September 2026

The complete proof passed `bash scripts/check.sh`, including:

- `lake build`: successful, 8,735 jobs in the pinned dependency graph;
- 28 project modules and their root module imported;
- explicit checks that the final bound has only its dimension and geometric hypotheses;
- axiom audit: **410 project declarations**, permitting only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, `native_decide`, or project-defined axioms in the delivered proof sources.

The main audited conclusions are the universal finite-configuration bound, the genuine greatest-cardinality property, the kissing-number bound, the explicit value `kissingNumber 2 = 6`, the least uniform base, and the supremum formulation. `Axioms.lean` prints their transitive axiom dependencies and enforces the allowlist over all imported project declarations, including private ones.

The audit itself was also tested separately on a valid sample and on a deliberately added test axiom: it accepted the former and rejected the latter. Those scratch tests are not part of the certificate.

## Reproducibility

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- All dependency revisions: `lake-manifest.json`.
- Exact proof-source fingerprints: `SOURCE_SHA256SUMS`.
- Verification command: `bash scripts/check.sh`.

A separate publication checkout also passed the full check, rebuilding the project modules from source while reusing only the pinned external dependency cache. Normal read-only GitHub CI supplies a further check on the published commit. Consult that commit's check result; this record does not turn an earlier diagnostic run into a certificate.

## Scope and history

The conclusion is now unconditional, but Lean uses a Euclidean-volume proof different from the manuscript's cap-integral argument. The general cap-area identity remains outside the formalization. See `FORMALIZATION_SCOPE.md` for the precise distinction.

The initial dedicated repository run `33726121717` verified the earlier conditional algebraic core. The development branch and its diagnostic runs are historical working material. They are not the verification evidence for the complete source set presented here.
