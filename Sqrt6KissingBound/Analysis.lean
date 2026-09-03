import Mathlib

/-!
# One-dimensional estimates for the square-root-of-six kissing bound

This file formalizes the sine-integral part of the proof.
-/

namespace Sqrt6KissingBound

noncomputable section

open scoped Interval Real
open intervalIntegral

private abbrev s3 : ℝ := Real.sqrt 3

/-- The numerator in the normalized measure of a spherical cap of angular radius `π / 6`. -/
def capNumerator (m : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi / 6, Real.sin t ^ m

/-- The denominator in the normalized measure of a spherical cap. -/
def capDenominator (m : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.pi, Real.sin t ^ m

lemma capNumerator_recurrence (m : ℕ) :
    capNumerator (m + 2) =
      ((m + 1 : ℝ) / (m + 2)) * capNumerator m -
        (((1 : ℝ) / 2) ^ (m + 1) * (s3 / 2)) / (m + 2) := by
  rw [capNumerator, capNumerator, integral_sin_pow]
  simp [Real.sin_pi_div_six, Real.cos_pi_div_six]
  ring

lemma capDenominator_recurrence (m : ℕ) :
    capDenominator (m + 2) =
      ((m + 1 : ℝ) / (m + 2)) * capDenominator m := by
  rw [capDenominator, capDenominator, integral_sin_pow]
  simp

lemma capDenominator_pos (m : ℕ) : 0 < capDenominator m := by
  simpa [capDenominator] using integral_sin_pow_pos m

lemma capNumerator_zero : capNumerator 0 = Real.pi / 6 := by
  simp [capNumerator]

lemma capDenominator_zero : capDenominator 0 = Real.pi := by
  simp [capDenominator]

lemma capNumerator_one : capNumerator 1 = 1 - s3 / 2 := by
  norm_num [capNumerator, integral_sin]

lemma capDenominator_one : capDenominator 1 = 2 := by
  norm_num [capDenominator, integral_sin]

lemma capNumerator_three : capNumerator 3 = (2 : ℝ) / 3 - 3 * s3 / 8 := by
  have h := capNumerator_recurrence 1
  norm_num at h ⊢
  rw [capNumerator_one] at h
  nlinarith

lemma capDenominator_three : capDenominator 3 = (4 : ℝ) / 3 := by
  have h := capDenominator_recurrence 1
  norm_num at h ⊢
  rw [capDenominator_one] at h
  norm_num at h ⊢
  exact h

/-- The chord from `(0,0)` to `(π/6,1/2)` lies below sine. -/
lemma three_mul_div_pi_le_sin {t : ℝ} (ht0 : 0 ≤ t) (ht6 : t ≤ Real.pi / 6) :
    3 * t / Real.pi ≤ Real.sin t := by
  have hpi : 0 < Real.pi := Real.pi_pos
  let x : ℝ := 6 * t / Real.pi
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_one hpi).2
    nlinarith
  have h := Real.strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, hpi.le⟩)
    (show Real.pi / 6 ∈ Set.Icc 0 Real.pi by constructor <;> nlinarith)
    (sub_nonneg.2 hx1) hx0
  dsimp [x] at h
  simp [Real.sin_pi_div_six, hpi.ne'] at h
  convert h using 1 <;> field_simp [hpi.ne'] <;> ring

end

end Sqrt6KissingBound
