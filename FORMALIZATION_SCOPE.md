# Formal statements and proof map

The manuscript and Lean development use the same Euclidean-volume argument. The proof's geometric and analytic dependencies are proved in the project or supplied by the pinned Mathlib library; the final theorem has no additional packing or volume hypotheses.

## Statements

`IsKissingConfiguration X` means that `X` is a finite set in `EuclideanSpace ℝ (Fin n)`, all its vectors have norm one, and distinct members have inner product at most `1/2`. For unit vectors, the latter condition is equivalent to pairwise distance at least one.

`kissingConfiguration_card_le_sqrt6_pow` proves

\[
 n\ge1,\quad \operatorname{IsKissingConfiguration}(X)
 \quad\Longrightarrow\quad |X|\le(\sqrt6)^n.
\]

The resulting finite ceiling permits the definition of `kissingNumber n` as a greatest realizable cardinality. Its realization and maximality are both proved; the definition does not assume the bound it is used to state. `kissingNumber_le_sqrt6_pow` yields the theorem in the usual notation.

The explicit regular hexagon gives `kissingNumber_two_eq_six`. Together with the universal bound, it establishes `sqrt6_isLeast_universalKissingBase` and `kissingNumber_universal_base_iff`. The theorem `supremum_kissingNumber_roots_eq_sqrt6` states directly that supₙ≥₁ τₙ¹⁄ⁿ = √6. This is optimality among bounds valid in every positive dimension without a prefactor.

## Proof map

Write Vₙ for the volume of the unit ball in dimension n and a = √3/2.

| Mathematical step | Lean files |
| --- | --- |
| Disjoint open cones and orthogonal transport | `Geometry.lean`, `StandardGeometry.lean` |
| Coordinate measure preservation and Fubini integration | `CoordinateVolume.lean`, `ProfileVolume.lean`, `ProfileIntegral.lean`, `ProfileIntegralReal.lean` |
| Finite volume packing | `VolumePacking.lean`, `BodyVolumeAdditivity.lean` |
| Bicone containment and volume Vₙ₋₁/(n·2ⁿ⁻¹) | `BiconeGeometry.lean`, `LinearProfileIntegral.lean`, `BiconeVolume.lean`, `CenteredBicone.lean` |
| Unit-ball volumes, recurrence, and descent for n ≥ 6 | `BallVolumes.lean` |
| Dimensions 2 and 5, and the numerical induction for n ≥ 6 | `BiconeBounds.lean` |
| Dimension 1 | `DimensionOne.lean` |
| Dimensions 3 and 4, including exact profile integrals | `CenteredBody.lean`, `DimensionThree.lean`, `DimensionFour.lean` |
| Universal configuration bound | `KissingBound.lean` |
| Explicit hexagon and least universal base | `Optimality.lean` |
| Attained maximum and kissing-number statements | `KissingNumber.lean` |

For dimension three, the upper profile is √(1−t²), producing body volume π(2−√3)/3 and the bound 14. For dimension four, the upper profile is (1−t)(14t+2−6√3), producing volume V₃(265352−153195√3)/320 and the bound 36. The containment inequalities and both exact integrals are proved in the indicated files.

`Axioms.lean` checks the theorem contracts and audits every imported project declaration, including private declarations, against the allowlist `propext`, `Classical.choice`, and `Quot.sound`. See [verification instructions](CERTIFICATION_STATUS.md).
