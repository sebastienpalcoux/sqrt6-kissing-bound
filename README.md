# The sharp universal square-root-of-six kissing-number bound

This branch contains a complete Lean formalization of the bound

    tau_n <= (sqrt(6))^n  for every integer n >= 1,

and of the optimality of sqrt(6) as a universal exponential base. The certificate is no longer conditional on a geometric packing inequality or on exceptional-dimensional bounds.

## Verification

The exact proof sources were successfully compiled and audited in GitHub Actions run 33933318109, staging commit `449ebb9b62419d9d90eceef444f09a9fdde2e48e`, on September 5, 2026. They are now ordinary project files, not generated development candidates. `SOURCE_SHA256SUMS` identifies their exact bytes.

The **Full Lean certificate** workflow verifies those hashes, checks the pinned dependency, performs a clean project build, and audits 16 public theorems. It fails if any audit is missing or if a theorem uses an axiom other than `propext`, `Classical.choice`, or `Quot.sound`. The downloadable certificate artifact includes the final run's `certification/VERIFICATION.json`, exact commit identifier, build logs, and axiom reports.

Pinned environment:

- Lean: `leanprover/lean4:v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`

No project proof uses `sorry`, `admit`, a newly declared axiom, `unsafe`, or `native_decide`. The source scan supplements, rather than replaces, the kernel-checked theorem dependency audit.

## Reproduce the certificate

With Elan/Lean installed, run these commands from the directory containing `lakefile.lean`:

```bash
lake exe cache get
bash scripts/check.sh
```

To check source identity first:

```bash
sha256sum -c SOURCE_SHA256SUMS
```

The last line of a successful check is:

```text
Full Lean build, source scan, and public-theorem axiom audit passed.
```

The small certificate ZIP contains source, configuration, and verification records, not the multi-gigabyte `.lake` dependency cache. Rechecking will obtain dependencies as needed.

## Public results

| Result | Formal declaration in namespace `Sqrt6KissingBound` |
| --- | --- |
| Unit-vector configurations with pairwise distance at least one have at most `(sqrt(6))^n` points | `kissingConfiguration_card_le_sqrt6_pow_of_dist` |
| The kissing number is realized and is the greatest realizable cardinality | `kissingNumber_realized`, `kissingNumber_isGreatest` |
| Universal kissing-number bound | `kissingNumber_le_sqrt6_pow` |
| Exact one- and two-dimensional values | `kissingNumber_one_eq_two`, `kissingNumber_two_eq_six` |
| Least universal exponential base | `sqrt6_isLeast_universalKissingBase` |
| For nonnegative alpha, the universal bound holds exactly when `sqrt(6) <= alpha` | `universal_kissingNumber_bound_iff` |
| Supremum of positive-dimensional kissing-number roots equals `sqrt(6)` | `supremum_kissingNumber_roots_eq_sqrt6` |
| Strict recurrence for the actual sine-integral cap fractions | `capFraction_step_strict` |

See `Axioms.lean` for exact statements and all 16 audited theorem dependencies, `FORMALIZATION_SCOPE.md` for the manuscript correspondence, and `PROOF_GUIDE.md` for the geometric argument.

## Provenance and scope

The formalization was developed by AI with repeated compiler feedback. It is not a one-shot formalization and this repository does not assert independent human peer review. Formal checking verifies the stated Lean theorems under the listed standard foundations; mathematical interpretation and exposition remain open to human review.

The end-to-end formal proof uses an alternative ambient-volume packing argument with explicitly integrated cone bodies. It proves the principal mathematical statements of the manuscript; it does not claim to translate every line of the manuscript's spherical-cap proof.

The original `manuscript/` files and `main` branch were not changed. Earlier files such as `MATHOVERFLOW_ANSWER.md`, `PROOF_README.md`, `readme.md`, historical checklists, and older submission archives describe earlier stages and are not the current certification record. Their conditional-certification language is historical. Current status is recorded in this README, `CERTIFICATION_STATUS.md`, the **Full Lean certificate** workflow, and its verification artifact. Development material under `.ci/` is not needed to build the permanent certificate.
