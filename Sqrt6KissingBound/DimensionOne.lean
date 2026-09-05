import Sqrt6KissingBound.StandardGeometry

/-! The unit sphere in one dimension consists of two points. -/

namespace Sqrt6KissingBound
noncomputable section

lemma unit_vector_dim_one_eq_axis_or_neg
    (x : EuclideanSpace ℝ (Fin 1)) (hx : ‖x‖ = 1) :
    x = standardAxis 0 ∨ x = -standardAxis 0 := by
  have hs : (x 0) ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hx
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] using h
  have hf : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hcoord : x 0 = 1 := by linarith
    ext i
    fin_cases i
    simpa [standardAxis, standardCoordinates] using hcoord
  · right
    have hcoord : x 0 = -1 := by linarith
    ext i
    fin_cases i
    simpa [standardAxis, standardCoordinates] using hcoord

lemma code_card_le_two_dim_one
    (X : Finset (EuclideanSpace ℝ (Fin 1)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1) : X.card ≤ 2 := by
  classical
  have hsub : X ⊆ ({standardAxis 0, -standardAxis 0} :
      Finset (EuclideanSpace ℝ (Fin 1))) := by
    intro x hx
    rcases unit_vector_dim_one_eq_axis_or_neg x (hunit x hx) with h | h
    · simp [h]
    · simp [h]
  exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_insert_le (standardAxis 0) ({-standardAxis 0} : Finset (EuclideanSpace ℝ (Fin 1))))

lemma code_card_le_sqrt6_dim_one
    (X : Finset (EuclideanSpace ℝ (Fin 1)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1) :
    (X.card : ℝ) ≤ Real.sqrt 6 := by
  have hc : (X.card : ℝ) ≤ 2 := by
    exact_mod_cast code_card_le_two_dim_one X hunit
  have hs0 := Real.sqrt_nonneg (6 : ℝ)
  have hs2 : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  nlinarith

end
end Sqrt6KissingBound
