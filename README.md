# The universal square-root-of-six bound for kissing numbers

The Euclidean kissing number $\tau_n$ is an attained maximum, and the
Lean 4 / Mathlib development proves

$$
\tau_n\le 6^{n/2}\qquad(n\ge 1),\qquad \tau_2=6.
$$

Consequently, $\sqrt6$ is the least base $\alpha$ for which $\tau_n\le\alpha^n$
in every positive dimension.

## Published estimates and the proofs in the manuscript

Section 1 deduces the sharp bound from results available before the 2017
MathOverflow question. The cap-area estimate of Böröczky and Wintsche gives
$\tau_n\le 2^{n-1}\sqrt{2\pi n}<6^{n/2}$ for $n\ge6$ by packing disjoint caps
of radius $\pi/6$. Bachoc and Vallentin's Table 5.1 supplies the upper bounds
12, 24, and 45 in dimensions 3, 4, and 5. The values 2 and 6 in dimensions 1
and 2 complete the deduction, with equality only in dimension 2. The
introduction also explains the motivating subfactor problem and credits
Henry Cohn's prediction of the optimal base.
[Böröczky–Wintsche, Corollary 3.2(i)](https://doi.org/10.1007/978-3-642-55566-4_10) ·
[Bachoc–Vallentin, Table 5.1](https://doi.org/10.1090/S0894-0347-07-00589-9) ·
[Cohn's 2017 answer](https://mathoverflow.net/a/282685/)

The manuscript gives two self-contained elementary proofs that derive their
own low-dimensional estimates:

- **Spherical caps.** A recurrence for cap areas proves the bound and shows
  that dimension two is the unique equality case. This is an informal proof.
- **Euclidean volumes.** Explicit bodies pack into disjoint sectors of the
  unit ball. The revised paper explains the choice of the four-dimensional
  profile and gives a short lower bound for its volume. Lean checks the volume
  construction and exact integrals through to the sharp universal bound.

## Read the result

- [Manuscript PDF](manuscript/sqrt6-kissing-bound.pdf) and [LaTeX source](manuscript/sqrt6-kissing-bound.tex), dated 18 November 2026.
- [Palomar registration, PALOMAR-2026-09-05-000002, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000002&version=1).
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

Palomar registered all eight selected declarations on 5 September 2026 at
repository commit `cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9`. Comparator, Lean's
kernel, and NanoDa passed; the automated editorial review identified no
problems. Palomar preserves the exact registered snapshot. The November
manuscript describes the same volume construction and identifies the scope of
the certificate in Section 5.

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

OpenAI's GPT-6 Astra developed the original argument, manuscript, formalization,
and Palomar packaging from prompts supplied by Sébastien Palcoux, the author
and responsible maintainer. GPT-6.2 Astra assisted with the November manuscript
revision. Section 5 of the manuscript links to the dated provenance correction
for the archived metadata. Palomar registration records mechanical verification
and automated editorial review. Independent human mathematical review has yet
to be recorded.
