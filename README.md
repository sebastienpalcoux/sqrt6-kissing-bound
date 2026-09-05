# The universal square-root-of-six bound for kissing numbers

This project proves in Lean 4 / Mathlib that

\[
\tau_n \le (\sqrt6)^n \qquad(n\ge1),
\]

and that **sqrt(6) is the least universal exponential base** with no prefactor.
The kissing number is an attained maximum, an explicit planar hexagon gives
\(\tau_2=6\), and \(\sup_{n\ge1}\tau_n^{1/n}=\sqrt6\). This is not a claim
of asymptotic optimality.

The manuscript and substantive Lean development present the same
Euclidean-volume proof: cone separation, disjoint packing, the volumes of the
explicit bodies, and every dimension case.

## Read the result

- [Manuscript PDF](manuscript/sqrt6-kissing-bound.pdf) and [LaTeX source](manuscript/sqrt6-kissing-bound.tex).
- [Formal statements and proof map](FORMALIZATION_SCOPE.md).
- [Verification and its limits](CERTIFICATION_STATUS.md).
- [Palomar submission instructions and statement map](PALOMAR_SUBMISSION.md).

## Palomar interface

[Challenge.lean](Challenge.lean) imports only Mathlib and states eight principal
claims. [Solution.lean](Solution.lean) supplies their proofs from this repository;
it never imports the Challenge. The three public definitions describe ordinary
kissing configurations, all attainable cardinalities, and universal bases.
No claimed bound is built into those definitions.

Four proved adapters expose genuine greatest cardinalities without the
implementation-specific bounded search. The interface uses `Finset.card`, not
`Fintype.card` with independently elaborated local instances. Comparator checks
the exported statements and their definition dependencies, not just their
printed text. The full project axiom audit also includes the adapters.

[formalization.yaml](formalization.yaml) records the public title and abstract,
mathematical sources, human responsibility, AI contributions, scope, and review
status. The repository is licensed under [Apache-2.0](LICENSE).
**Repository preparation and a green CI run are not Palomar registration.**

## Verify

The registration environment pins Lean `v4.33.0` and canonical Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`; all inherited dependency revisions are
fixed in `lake-manifest.json`.

```bash
lake exe cache get
bash scripts/check.sh
bash scripts/verify-comparator.sh
```

The first check builds the complete proof and both interface modules, checks
source fingerprints, and audits every project declaration against exactly
`propext`, `Classical.choice`, and `Quot.sound`. The second runs pinned Comparator
and independent NanoDa replay, retaining downloaded tools in an ignored cache.
The only statement placeholders are in the isolated Challenge file.

The read-only [verification workflow](.github/workflows/lean.yml) first runs a
fast preflight, then Lean and the axiom audit, then Comparator and NanoDa. Its
preflight verifies canonical Mathlib ancestry and the exact inherited dependency
lock before spending time on compilation. The read-only
[PDF workflow](.github/workflows/manuscript.yml) compiles the manuscript as an
artifact. Both workflows run on pull requests and `main`, not on every
intermediate branch push. No local Lean installation is needed to inspect
these GitHub checks.

## AI provenance and review

The proof, manuscript, and formalization were developed with OpenAI's GPT-5.6 Pro
and further AI assistance in ChatGPT Work, from prompts supplied by Sébastien
Palcoux. GPT-6 Pro assisted with Palomar packaging. No independent human
mathematical review or human audit of the informal-to-formal alignment is
recorded. Mechanical verification does not establish novelty, assess research
importance, or certify the prose as a human referee would.
