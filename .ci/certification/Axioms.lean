import Sqrt6KissingBound

/-! Public theorem audit. This file introduces no assumptions or new axioms. -/
open Sqrt6KissingBound

-- These examples check that no hidden geometric assumption has been added.
example {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hu : ∀ x ∈ X, ‖x‖ = 1)
    (hs : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ n :=
  kissingConfiguration_card_le_sqrt6_pow_of_dist hn X hu hs

example {n : ℕ} (hn : 1 ≤ n) :
    IsGreatest {m : ℕ | RealizableKissingCard n m} (kissingNumber n) :=
  kissingNumber_isGreatest hn

example {n : ℕ} (hn : 1 ≤ n) :
    (kissingNumber n : ℝ) ≤ (Real.sqrt 6) ^ n := kissingNumber_le_sqrt6_pow hn

example : kissingNumber 1 = 2 := kissingNumber_one_eq_two
example : kissingNumber 2 = 6 := kissingNumber_two_eq_six

example (α : ℝ) (hα : 0 ≤ α) :
    (∀ n : ℕ, 1 ≤ n → (kissingNumber n : ℝ) ≤ α ^ n) ↔ Real.sqrt 6 ≤ α :=
  universal_kissingNumber_bound_iff α hα

example : sSup kissingNumberRoots = Real.sqrt 6 := supremum_kissingNumber_roots_eq_sqrt6
example (n : ℕ) (hn : 2 ≤ n) : capFraction n / 6 < capFraction (n + 2) :=
  capFraction_step_strict n hn

#print Sqrt6KissingBound.IsKissingConfiguration
#print Sqrt6KissingBound.RealizableKissingCard
#print Sqrt6KissingBound.kissingNumber
#print Sqrt6KissingBound.IsUniversalKissingBase
#print Sqrt6KissingBound.kissingNumberRoots

#check Sqrt6KissingBound.kissingConfiguration_card_le_sqrt6_pow
#check Sqrt6KissingBound.kissingConfiguration_card_le_floor_sqrt6_pow
#check Sqrt6KissingBound.kissingConfiguration_card_le_sqrt6_pow_of_dist
#check Sqrt6KissingBound.kissingNumber_realized
#check Sqrt6KissingBound.kissingNumber_isGreatest
#check Sqrt6KissingBound.kissingNumber_le_sqrt6_pow
#check Sqrt6KissingBound.kissingNumber_one_eq_two
#check Sqrt6KissingBound.kissingNumber_two_eq_six
#check Sqrt6KissingBound.sqrt6_isLeast_universalKissingBase
#check Sqrt6KissingBound.universal_kissingNumber_bound_iff
#check Sqrt6KissingBound.supremum_kissingNumber_roots_eq_sqrt6
#check Sqrt6KissingBound.capFraction_step_strict

#print axioms Sqrt6KissingBound.isKissingConfiguration_iff_norm_dist
#print axioms Sqrt6KissingBound.kissingConfiguration_card_le_sqrt6_pow
#print axioms Sqrt6KissingBound.kissingConfiguration_card_le_floor_sqrt6_pow
#print axioms Sqrt6KissingBound.kissingConfiguration_card_le_sqrt6_pow_of_dist
#print axioms Sqrt6KissingBound.kissingNumber_realized
#print axioms Sqrt6KissingBound.kissingNumber_isGreatest
#print axioms Sqrt6KissingBound.kissingNumber_le_sqrt6_pow
#print axioms Sqrt6KissingBound.kissingNumber_one_eq_two
#print axioms Sqrt6KissingBound.kissingNumber_two_eq_six
#print axioms Sqrt6KissingBound.sqrt6_isLeast_universalKissingBase
#print axioms Sqrt6KissingBound.isUniversalKissingBase_iff
#print axioms Sqrt6KissingBound.universal_kissingNumber_bound_iff
#print axioms Sqrt6KissingBound.kissingNumber_root_le_sqrt6
#print axioms Sqrt6KissingBound.sqrt6_isGreatest_kissingNumberRoots
#print axioms Sqrt6KissingBound.supremum_kissingNumber_roots_eq_sqrt6
#print axioms Sqrt6KissingBound.capFraction_step_strict
