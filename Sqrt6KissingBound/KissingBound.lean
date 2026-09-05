import Sqrt6KissingBound.DimensionOne
import Sqrt6KissingBound.DimensionThree
import Sqrt6KissingBound.DimensionFour
import Sqrt6KissingBound.BiconeBounds

/-! Development candidate: the dimension-uniform theorem. -/
namespace Sqrt6KissingBound
noncomputable section

/-- A normalized kissing configuration, equivalently a unit spherical code
whose distinct points have Euclidean distance at least one. -/
def IsKissingConfiguration {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  (∀ x ∈ X, ‖x‖ = 1) ∧
    (∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2)

lemma unit_inner_le_half_iff_dist_ge_one {n : ℕ}
    {x y : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    inner ℝ x y ≤ (1 : ℝ) / 2 ↔ 1 ≤ dist x y := by
  have hsq : dist x y ^ 2 = 2 - 2 * inner ℝ x y := by
    rw [dist_eq_norm, norm_sub_sq_real, hx, hy]
    ring
  have hd0 : 0 ≤ dist x y := dist_nonneg
  constructor <;> intro h <;> nlinarith

lemma isKissingConfiguration_iff_norm_dist {n : ℕ}
    (X : Finset (EuclideanSpace ℝ (Fin n))) :
    IsKissingConfiguration X ↔
      (∀ x ∈ X, ‖x‖ = 1) ∧
        (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y) := by
  constructor
  · rintro ⟨hu, hi⟩
    refine ⟨hu, ?_⟩
    intro x hx y hy hxy
    exact (unit_inner_le_half_iff_dist_ge_one (hu x hx) (hu y hy)).mp (hi x hx y hy hxy)
  · rintro ⟨hu, hd⟩
    refine ⟨hu, ?_⟩
    intro x hx y hy hxy
    exact (unit_inner_le_half_iff_dist_ge_one (hu x hx) (hu y hy)).mpr (hd x hx y hy hxy)

theorem kissingConfiguration_card_le_sqrt6_pow {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n))) (hX : IsKissingConfiguration X) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ n := by
  rcases hX with ⟨hunit, hsep⟩
  by_cases hn5 : n ≤ 5
  · have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · simpa using code_card_le_sqrt6_dim_one X hunit
    · simpa using code_card_le_sqrt6_sq X hunit hsep
    · simpa using code_card_le_sqrt6_cube X hunit hsep
    · simpa using code_card_le_sqrt6_fourth X hunit hsep
    · simpa using code_card_le_sqrt6_fifth X hunit hsep
  · have hn6 : 6 ≤ n := by omega
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2, by omega⟩
    exact code_card_le_sqrt6_high (by omega) X hunit hsep

theorem kissingConfiguration_card_le_floor_sqrt6_pow {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n))) (hX : IsKissingConfiguration X) :
    X.card ≤ ⌊(Real.sqrt 6) ^ n⌋₊ := by
  exact Nat.le_floor (kissingConfiguration_card_le_sqrt6_pow hn X hX)

theorem kissingConfiguration_card_le_sqrt6_pow_of_dist {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ n :=
  kissingConfiguration_card_le_sqrt6_pow hn X
    ((isKissingConfiguration_iff_norm_dist X).mpr ⟨hunit, hsep⟩)

end
end Sqrt6KissingBound
