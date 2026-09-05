# The universal square-root-of-six bound for kissing numbers

This project proves in Lean 4 / Mathlib that

\[
\tau_n \le (\sqrt6)^n \qquad(n\ge1),
\]

and that **√6 is the least universal exponential base**: it is the least positive real number α for which τₙ ≤ αⁿ holds in every positive dimension, with no prefactor.

The manuscript and Lean development present the same Euclidean-volume proof. It establishes cone separation, the packing inequalities, the volumes of the explicit bodies, and every dimension case. The kissing number is an attained maximum; an explicit regular hexagon proves τ₂ = 6 and optimality of the base.

## Read the result

- [Manuscript PDF](manuscript/sqrt6-kissing-bound.pdf) and [LaTeX source](manuscript/sqrt6-kissing-bound.tex).
- [Formal statements and proof map](FORMALIZATION_SCOPE.md).
- [Verification record](CERTIFICATION_STATUS.md).
- [MathOverflow answer draft](MATHOVERFLOW_ANSWER.md).

## Verify

The project pins Lean `v4.33.1` and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.
With Lean's `elan` installer available, run:

```bash
lake exe cache get
bash scripts/check.sh
sha256sum --check SOURCE_SHA256SUMS
```

The checks build the complete proof, exclude proof holes and project-defined axioms, verify the public theorem contracts, and audit the transitive axiom dependencies of all project declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

The [Lean certificate](.github/workflows/lean.yml) and [manuscript PDF](.github/workflows/manuscript.yml) workflows run on pull requests and `main` with read-only repository permissions. The PDF workflow compiles and uploads the manuscript without changing repository files.

## Main declarations

All names are in the `Sqrt6KissingBound` namespace.

| Statement | Declaration |
| --- | --- |
| Every finite kissing configuration obeys the bound | `kissingConfiguration_card_le_sqrt6_pow` |
| The kissing number is an attained maximum | `kissingNumber_realized`, `kissingNumber_isGreatest` |
| The kissing number obeys the bound | `kissingNumber_le_sqrt6_pow` |
| The planar kissing number equals six | `kissingNumber_two_eq_six` |
| √6 is the least universal base | `sqrt6_isLeast_universalKissingBase` |
| All admissible universal bases are characterized | `kissingNumber_universal_base_iff` |
| The supremum of τₙ¹⁄ⁿ equals √6 | `supremum_kissingNumber_roots_eq_sqrt6` |

## AI provenance

The proof, manuscript, and formalization were developed with OpenAI's GPT-5.6 Pro and further AI assistance in ChatGPT Work, from prompts supplied by Sébastien Palcoux. The manuscript has not undergone independent human mathematical review.
