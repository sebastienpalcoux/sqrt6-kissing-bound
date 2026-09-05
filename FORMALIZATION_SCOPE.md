# Formalization scope and manuscript correspondence

## Geometric objects

`IsKissingConfiguration X` means that X is a finite subset of real Euclidean n-space, all its members have norm one, and the inner product of distinct members is at most one half. `isKissingConfiguration_iff_norm_dist` proves equivalence with the usual distance condition: distinct unit vectors have distance at least one.

`RealizableKissingCard n m` means that such a configuration of cardinality m exists. Although `kissingNumber n` is implemented by a finite greatest-element search using an independently proved ceiling, its realization and maximality are theorems. For every positive n, `kissingNumber_isGreatest` states that it is the greatest element of the set of *all* realizable cardinalities. Thus the certified invariant is not merely a bounded proxy.

## Results and exact locations

| Mathematical assertion | File | Public theorem |
| --- | --- | --- |
| Configuration cardinality is at most `(sqrt(6))^n` for n >= 1 | `KissingBound.lean` | `kissingConfiguration_card_le_sqrt6_pow` |
| Same assertion from unit-norm and pairwise-distance assumptions | `KissingBound.lean` | `kissingConfiguration_card_le_sqrt6_pow_of_dist` |
| Integer floor version | `KissingBound.lean` | `kissingConfiguration_card_le_floor_sqrt6_pow` |
| Kissing number is attained and greatest | `KissingNumber.lean` | `kissingNumber_realized`, `kissingNumber_isGreatest` |
| `tau_n <= (sqrt(6))^n` | `KissingNumber.lean` | `kissingNumber_le_sqrt6_pow` |
| `tau_1 = 2` and `tau_2 = 6` | `KissingNumber.lean` | `kissingNumber_one_eq_two`, `kissingNumber_two_eq_six` |
| `sqrt(6)` is the least universal exponential base | `Optimality.lean` | `sqrt6_isLeast_universalKissingBase` |
| A nonnegative alpha bounds all kissing numbers by alpha^n iff alpha >= sqrt(6) | `KissingNumber.lean` | `universal_kissingNumber_bound_iff` |
| Supremum of `tau_n^(1/n)` over positive n is `sqrt(6)` | `Supremum.lean` | `supremum_kissingNumber_roots_eq_sqrt6` |
| The supremum is attained at n = 2 | `Supremum.lean` | `sqrt6_isGreatest_kissingNumberRoots` |
| For the actual integral-defined cap fractions, `capFraction n / 6 < capFraction (n+2)` when n >= 2 | `ManuscriptLemmas.lean` | `capFraction_step_strict` |

All listed files are under `Sqrt6KissingBound/`. `Axioms.lean` checks the exact public signatures and prints 16 transitive axiom reports. `scripts/check_axioms.py` enforces the allowed list and rejects missing results.

## What was proved rather than assumed

The complete geometric dependency chain proves disjointness of the relevant open cones; measurability and Fubini formulas for rotational-profile bodies; volume preservation under coordinate isometries and reflections; finite volume additivity; the resulting packing inequality; exact unit-ball volumes and their recurrence; the large-dimensional numerical induction; and separate estimates in dimensions one through five. The regular hexagon is built from explicit coordinates, with cardinality and separation verified in Lean.

## Relationship with the written proof

The principal bounds, optimality, supremum formula, and strict cap-fraction recurrence match the manuscript's mathematical statements. The final geometric proof uses ambient Euclidean volume and explicit inscribed bodies rather than relying on an unformalized spherical-cap area formula. This is an alternative proof of the principal theorem, not a claim that every sentence or intermediate formula in the manuscript's argument was translated into Lean.

No exact value of the kissing number in dimension three or four is assumed. The proved estimates `tau_3 <= 14`, `tau_4 <= 36`, and `tau_5 <= 85` suffice for the universal bound.

The earlier conditional `Core.lean` lemmas are retained for comparison, but their hypotheses do not remain as unproved assumptions in the final geometric theorems. Unimported experimental modules have been preserved under `.ci/archive/unimported/`, outside the permanent proof tree.

The original manuscript and prior MathOverflow draft are unchanged. This certificate makes no claim of independent human peer review, novelty, or exact values in other dimensions.
