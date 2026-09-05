import Sqrt6KissingBound.CoordinateVolume
import Sqrt6KissingBound.Geometry
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Geometry in standard first-coordinate form
-/

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory

/-- The first standard unit vector in dimension `d+1`. -/
def standardAxis (d : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  standardCoordinates d (1, 0)

lemma norm_sq_standardCoordinates (d : ℕ) (t : ℝ) (v : Fin d → ℝ) :
    ‖standardCoordinates d (t, v)‖ ^ 2 =
      t ^ 2 + ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [standardCoordinates, Fin.sum_univ_succ]

@[simp] lemma norm_standardAxis (d : ℕ) : ‖standardAxis d‖ = 1 := by
  have hsq : ‖standardAxis d‖ ^ 2 = 1 := by
    simpa [standardAxis] using
      norm_sq_standardCoordinates d 1 (0 : Fin d → ℝ)
  have hn : 0 ≤ ‖standardAxis d‖ := norm_nonneg _
  nlinarith

@[simp] lemma inner_standardAxis_standardCoordinates (d : ℕ)
    (t : ℝ) (v : Fin d → ℝ) :
    inner ℝ (standardAxis d) (standardCoordinates d (t, v)) = t := by
  simp [standardAxis, standardCoordinates, PiLp.inner_apply,
    Fin.sum_univ_succ] <;> simp

lemma standardCoordinates_mem_ball_iff (d : ℕ) (t : ℝ) (v : Fin d → ℝ) :
    standardCoordinates d (t, v) ∈ ball 0 1 ↔
      t ^ 2 + ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 < 1 := by
  rw [mem_ball, dist_zero_right]
  constructor
  · intro h
    let N : ℝ := ‖standardCoordinates d (t, v)‖
    have hN0 : 0 ≤ N := norm_nonneg _
    have hpos : 0 < (1 - N) * (1 + N) :=
      mul_pos (sub_pos.mpr h) (by linarith)
    have hsq : N ^ 2 < 1 := by nlinarith
    simpa [N, norm_sq_standardCoordinates] using hsq
  · intro h
    let N : ℝ := ‖standardCoordinates d (t, v)‖
    have hN0 : 0 ≤ N := norm_nonneg _
    have hsq : N ^ 2 < 1 := by
      simpa [N, norm_sq_standardCoordinates] using h
    by_contra hnot
    have hge : 1 ≤ N := le_of_not_gt hnot
    nlinarith [sq_nonneg (N - 1)]

lemma standardCoordinates_mem_strictCone_iff (d : ℕ) (t : ℝ)
    (v : Fin d → ℝ) :
    standardCoordinates d (t, v) ∈ strictCone (standardAxis d) ↔
      (Real.sqrt 3 / 2) *
          Real.sqrt (t ^ 2 +
            ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2) < t := by
  change (Real.sqrt 3 / 2) * ‖standardCoordinates d (t, v)‖ <
    inner ℝ (standardAxis d) (standardCoordinates d (t, v)) ↔ _
  rw [inner_standardAxis_standardCoordinates]
  congr 2
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_standardCoordinates]

end

end Sqrt6KissingBound
