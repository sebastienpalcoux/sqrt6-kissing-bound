import Mathlib

/-!
# The universal square-root-of-six bound for kissing numbers

For every positive integer n the Euclidean kissing number tau_n exists and
satisfies tau_n <= (sqrt 6)^n. Moreover tau_2 = 6, sqrt 6 is the least
universal exponential base without a prefactor, and sup_{n>=1} tau_n^(1/n)
is sqrt 6. This is not a claim of asymptotic optimality.

This statement file imports only Mathlib. The three definitions below have
their ordinary geometric meanings; in particular the attainable cardinalities
are NOT truncated at the claimed bound. IsGreatest asserts both attainment
and the upper-bound property. The existence theorem prevents the later
statements about an arbitrary choice of maxima from being vacuous.

Solution.lean supplies the proofs from the complete Euclidean-volume
development in this repository. See formalization.yaml for sources, AI
provenance, review status, and the precise scope of the submission.
-/

namespace Sqrt6KissingBound

noncomputable section

/-- Unit vectors whose distinct pairwise inner products are at most 1/2.
After scaling by two, these are the centers of equal unit balls touching the
unit ball at the origin, with disjoint interiors. -/
def IsKissingConfiguration {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ x ∈ X, ‖x‖ = 1) ∧
    (∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2)

/-- The set of all attainable cardinalities, with no imposed upper cutoff. -/
def RealizableKissingCard (n m : ℕ) : Prop :=
  ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
    IsKissingConfiguration X ∧ X.card = m

/-- A nonnegative base bounds every configuration in every positive dimension,
with no additional multiplicative constant. -/
def IsUniversalKissingBase (α : ℝ) : Prop :=
  0 ≤ α ∧ ∀ {n : ℕ}, 1 ≤ n →
    ∀ X : Finset (EuclideanSpace ℝ (Fin n)),
      IsKissingConfiguration X → (X.card : ℝ) ≤ α ^ n

/-- Every finite kissing configuration in dimension n >= 1 has at most (sqrt 6)^n points. -/
theorem kissingConfiguration_card_le_sqrt6_pow {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : IsKissingConfiguration X) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ n := by
  sorry

/-- The least universal exponential base is sqrt 6. -/
theorem sqrt6_isLeast_universalKissingBase :
    IsLeast {α : ℝ | IsUniversalKissingBase α} (Real.sqrt 6) := by
  sorry

/-- The admissible universal bases are exactly the real numbers at least sqrt 6. -/
theorem isUniversalKissingBase_iff (α : ℝ) :
    IsUniversalKissingBase α ↔ Real.sqrt 6 ≤ α := by
  sorry

/-- The supremum of all positive-dimensional configuration roots is sqrt 6. -/
theorem supremum_kissing_roots_eq_sqrt6 :
    sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
      IsKissingConfiguration X ∧ x = (X.card : ℝ) ^ ((n : ℝ)⁻¹)} =
      Real.sqrt 6 := by
  sorry

namespace Palomar

/-- The usual kissing number exists as an attained maximum and satisfies the bound. -/
theorem kissingNumber_exists {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℕ, IsGreatest {m : ℕ | RealizableKissingCard n m} k ∧
      (k : ℝ) ≤ (Real.sqrt 6) ^ n := by
  sorry

/-- The maximum cardinality in the plane is exactly six. -/
theorem planar_kissingNumber :
    IsGreatest {m : ℕ | RealizableKissingCard 2 m} 6 := by
  sorry

/-- For the actual maximum cardinalities, the supremum of the dimensional roots is sqrt 6. -/
theorem kissingNumber_roots (τ : ℕ → ℕ)
    (hτ : ∀ n : ℕ, 1 ≤ n →
      IsGreatest {m : ℕ | RealizableKissingCard n m} (τ n)) :
    sSup {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (τ n : ℝ) ^ ((n : ℝ)⁻¹)} = Real.sqrt 6 := by
  sorry

/-- The same complete characterization of bases holds for the actual kissing numbers. -/
theorem kissingNumber_universal_base (τ : ℕ → ℕ)
    (hτ : ∀ n : ℕ, 1 ≤ n →
      IsGreatest {m : ℕ | RealizableKissingCard n m} (τ n)) (α : ℝ) :
    (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (τ n : ℝ) ≤ α ^ n) ↔
      Real.sqrt 6 ≤ α := by
  sorry

end Palomar

end

end Sqrt6KissingBound
