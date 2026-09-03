# The universal square-root-of-six bound for kissing numbers

This repository contains a proposed proof that

\[
\tau_n \le (\sqrt 6)^n \qquad (n\ge 1),
\]

where \(\tau_n\) is the kissing number in Euclidean dimension \(n\), together with a Lean 4 / Mathlib certificate for the proof's algebraic and inductive core.

## Manuscript

- [`manuscript/sqrt6-kissing-bound.pdf`](manuscript/sqrt6-kissing-bound.pdf) is the four-page manuscript.
- [`manuscript/sqrt6-kissing-bound.tex`](manuscript/sqrt6-kissing-bound.tex) is its LaTeX source.
- [`.github/workflows/manuscript.yml`](.github/workflows/manuscript.yml) rebuilds the PDF and commits it to the repository whenever the source changes.

The earlier MathOverflow-formatted draft remains in [`MATHOVERFLOW_ANSWER.md`](MATHOVERFLOW_ANSWER.md).

## Lean certificate

- [`FORMALIZATION_SCOPE.md`](FORMALIZATION_SCOPE.md) states exactly what Lean does and does not yet verify.
- [`Sqrt6KissingBound/Core.lean`](Sqrt6KissingBound/Core.lean) contains the formalized lemmas.
- [`CERTIFICATION_STATUS.md`](CERTIFICATION_STATUS.md) records the certification details.

The project pins Lean `v4.33.1` and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

```bash
lake build
bash scripts/check.sh
```

The Lean CI workflow additionally runs an axiom audit and scans the project sources for proof holes.

## Provenance

The formal source was first certified on the temporary branch
`gpt-pro/sqrt6-kissing-certificate` of
`sebastienpalcoux/Fusion-Categories`, at commit
`90edce0218112c39a163410d4b7eb66dee5ebc41`. GitHub Actions run
`33720108355` succeeded. The project now lives in this dedicated repository, whose own Lean and manuscript workflows also pass.
