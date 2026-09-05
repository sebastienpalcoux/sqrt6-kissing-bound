# Palomar registration and submission record

## Registered version

This result was registered on 5 September 2026 as
[PALOMAR-2026-09-05-000002, version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-05-000002&version=1),
at repository commit `cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9`.
Palomar's mechanical verification passed and its automated editorial review
identified no problems. The submitter authorized publication and the permanent
record is now public.

The fields below document the original submission. Do not resubmit that
already registered commit. A future version of this same result must use the
new tested commit and existing ID `PALOMAR-2026-09-05-000002`.

## Submission fields

| Field | Value |
| --- | --- |
| Repository | `sebastienpalcoux/sqrt6-kissing-bound` |
| Project directory | repository root (leave empty, or `.` if requested) |
| Comparator configuration | `comparator.json` |
| Commit | `cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9` |
| Existing Palomar ID | left empty for the initial registration |

The title and abstract come from `project.name` and `project.description` in
`formalization.yaml`; there is no need to search for a separate title field.
This was a new result, not a new version of the group-theory registration.
Do not enter `PALOMAR-2026-09-03-000005` here.

**Do not use the Mathlib commit as the submission commit.** The Mathlib pin is
`db584cd6d46c92f209a44c0f1c829460d327499d`. It identifies a dependency, not this
repository's source snapshot. From a checked-out, clean source tree, the
submission commit is printed by `git rev-parse HEAD`. Branch names and short
commit abbreviations are not substitutes for the full commit.

## Gate before submitting

Use the [repository Actions page](https://github.com/sebastienpalcoux/sqrt6-kissing-bound/actions).
For the exact proposed commit, require successful results from **preflight**,
**lean-check**, and **comparator-and-nanoda**, as well as the manuscript build.
The first two alone are not enough: the group-theory project previously built
in Lean but failed Comparator because its exported statements differed.
Do not submit a running, failed, or merely statically checked snapshot.

The workflow is read-only. Intermediate pushes to a development branch do not
start it until a pull request is opened; related edits should be batched before
that point. A passing revision may then be merged, and the exact merged commit
should be checked before using its SHA for registration. No local Lean install,
repeated Mathlib download, or deletion of a multi-gigabyte directory is needed
when using the GitHub checks.

## What is being registered?

All names below have prefix `Sqrt6KissingBound.`.

| Declaration | Mathematical statement |
| --- | --- |
| `kissingConfiguration_card_le_sqrt6_pow` | Every finite configuration in dimension n >= 1 has at most (sqrt(6))^n points. |
| `sqrt6_isLeast_universalKissingBase` | sqrt(6) is the least universal exponential base without a prefactor. |
| `isUniversalKissingBase_iff` | The admissible nonnegative bases are exactly alpha >= sqrt(6). |
| `supremum_kissing_roots_eq_sqrt6` | The supremum of all configuration cardinality roots is sqrt(6). |
| `Palomar.kissingNumber_exists` | In each positive dimension a greatest cardinality exists, is attained, and satisfies the bound. |
| `Palomar.planar_kissingNumber` | The genuine maximum cardinality in dimension two is six. |
| `Palomar.kissingNumber_roots` | For the actual kissing numbers, sup tau_n^(1/n) = sqrt(6). |
| `Palomar.kissingNumber_universal_base` | The same exact characterization of bases holds for the actual kissing numbers. |

The Challenge imports only Mathlib and has three explicit definitions. Its set
of realizable cardinalities has **no upper cutoff**. `IsGreatest` asserts both
attainment and an upper bound on every realizable cardinality. The existence
theorem ensures that the later statements about an arbitrary function of
maxima are not vacuous. The four adapters are proved from the existing
manuscript-facing results in `Solution.lean`.

The configuration uses unit vectors with distinct inner products at most 1/2.
Their doubles are precisely centers of equal unit balls touching the unit ball
at the origin, with nonoverlapping interiors. All dimensions are positive;
there is no asymptotic-optimality claim and no hidden prefactor.

## Safeguards against the previous registration failures

The project uses the canonical Mathlib ancestor and matching Lean 4.33.0,
not a noncanonical toolchain-only Mathlib patch. Online preflight checks actual
canonical ancestry, the upstream toolchain, and all eight inherited dependency
revisions. `Finset.card` avoids the separately elaborated local `Fintype.card`
instances that caused the group-theory Comparator mismatch. The definitions
and signatures are also compared at source level, and the full exported
statements are checked by Comparator and NanoDa before submission.

The verifier revisions are fixed in `scripts/verify-comparator.sh`:

| Tool | Commit |
| --- | --- |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| lean4export for Lean 4.33.0 | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |

The Landrun wrapper retains sandbox restrictions and supplies exactly one
command delimiter. The standard Apache-2.0 root license matches the metadata.
Lean build output and verifier caches are ignored, not committed.

The manuscript's reproducibility paragraph records the registered environment:
the committed `lean-toolchain`, Lakefile, and manifest listed above. The later
disclosure and registration revision leaves the mathematical argument and Lean
source unchanged; the archived Palomar version retains the submitted snapshot.

## Submission and registration are distinct

For a future version, open [Palomar's submission service](https://submit.palomar-registry.org/)
and submit a new tested repository snapshot with the existing kissing-number
ID above. Read the returned review before choosing registration. Passing this
repository's checks does not guarantee that Palomar's separate automated
review will find no blocking issue.

Registration permanently records an immutable source snapshot and publishes
the mathematical statements, dependency and verification records, and the
review's public comments. It is neither human peer review, validation of the
informal prose, a novelty certificate, nor journal acceptance. Record a Palomar
ID only after registration has actually completed.

Policy checked on 5 September 2026:
[Palomar submission requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
