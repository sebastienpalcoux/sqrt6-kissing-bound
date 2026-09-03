import Sqrt6KissingBound.Core

/-!
# One-dimensional estimates for the square-root-of-six kissing bound

This file formalizes the sine-integral part of the spherical-cap proof. No
geometric or analytic statement in this file is assumed.
-/

namespace Sqrt6KissingBound

noncomputable section

open Set
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
  field_simp
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

/-- The chord from `(0,0)` to `(π/6,1/2)` lies below sine. -/
lemma three_mul_div_pi_le_sin {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi / 6) :
    3 * t / Real.pi ≤ Real.sin t := by
  let x : ℝ := 6 * t / Real.pi
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one Real.pi_pos]
    linarith
  have hcap : Real.pi / 6 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · positivity
    · nlinarith [Real.pi_pos]
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi by simp [Real.pi_pos.le]) hcap
    (sub_nonneg.2 hx1) hx0
  dsimp [x] at h
  simpa [Real.sin_pi_div_six, Real.pi_ne_zero] using h

/-- The chord estimate integrated after taking a natural power. -/
lemma chord_integral_le_capNumerator (m : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) ≤ capNumerator m := by
  rw [capNumerator]
  apply intervalIntegral.integral_mono_on (by positivity)
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro t ht
    have hnonneg : 0 ≤ 3 * t / Real.pi := by
      have : 0 ≤ t := ht.1
      positivity
    exact pow_le_pow_left₀ hnonneg (three_mul_div_pi_le_sin ht.1 ht.2) m

/-- Evaluation of the elementary integral appearing in the chord estimate. -/
lemma chord_integral (m : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) =
      Real.pi / (6 * (m + 1) * 2 ^ m) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hfun : (fun t : ℝ => (3 * t / Real.pi) ^ m) =
      fun t : ℝ => ((3 : ℝ) / Real.pi) ^ m * t ^ m := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
  simp
  field_simp
  ring

lemma pi_div_six_gt_three_sqrt3_div_ten :
    3 * s3 / 10 < Real.pi / 6 := by
  have hpi := Real.pi_gt_d2
  norm_num at hpi
  have hs3 : s3 < (26 : ℝ) / 15 := sqrt3_lt_26_div_15
  nlinarith

/-- The quantitative lower estimate that drives the two-step cap recurrence. -/
lemma capNumerator_lower (m : ℕ) :
    3 * s3 / (10 * (m + 1) * 2 ^ m) < capNumerator m := by
  have hD : 0 < (m + 1 : ℝ) * 2 ^ m := by positivity
  have hDne : (m + 1 : ℝ) * 2 ^ m ≠ 0 := ne_of_gt hD
  have hconst := pi_div_six_gt_three_sqrt3_div_ten
  calc
    3 * s3 / (10 * (m + 1) * 2 ^ m)
        = (3 * s3 / 10) / ((m + 1 : ℝ) * 2 ^ m) := by
          field_simp [hDne]
    _ < (Real.pi / 6) / ((m + 1 : ℝ) * 2 ^ m) :=
      div_lt_div_of_pos_right hconst hD
    _ = Real.pi / (6 * (m + 1) * 2 ^ m) := by
      field_simp [hDne]
    _ = (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) :=
      (chord_integral m).symm
    _ ≤ capNumerator m := chord_integral_le_capNumerator m

end

end Sqrt6KissingBound
