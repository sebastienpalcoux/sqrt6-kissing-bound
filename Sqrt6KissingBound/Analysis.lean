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
        s3 / ((m + 2 : ℝ) * 2 ^ (m + 2)) := by
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
  simp [capNumerator, integral_sin]

lemma capDenominator_one : capDenominator 1 = 2 := by
  simp [capDenominator, integral_sin]

lemma capNumerator_three : capNumerator 3 = (2 : ℝ) / 3 - 3 * s3 / 8 := by
  rw [show (3 : ℕ) = 1 + 2 by norm_num, capNumerator_recurrence]
  rw [capNumerator_one]
  norm_num
  ring

lemma capDenominator_three : capDenominator 3 = (4 : ℝ) / 3 := by
  rw [show (3 : ℕ) = 1 + 2 by norm_num, capDenominator_recurrence]
  rw [capDenominator_one]
  norm_num

end

end Sqrt6KissingBound
