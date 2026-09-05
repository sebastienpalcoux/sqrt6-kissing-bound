import Sqrt6KissingBound.AnalysisEstimate

/-!
# The analytic spherical-cap data

This file packages the sine-integral calculation as the concrete `CapData`
used by the algebraic core.
-/

namespace Sqrt6KissingBound

noncomputable section

private abbrev s3 : ℝ := Real.sqrt 3

/-- The normalized sine-integral fraction of a cap of angular radius `π/6`. -/
def capFraction (n : ℕ) : ℝ :=
  capNumerator (n - 2) / capDenominator (n - 2)

lemma capNumerator_three :
    capNumerator 3 = (2 : ℝ) / 3 - 3 * s3 / 8 := by
  rw [show (3 : ℕ) = 1 + 2 by norm_num, capNumerator_recurrence, capNumerator_one]
  norm_num
  ring

lemma capDenominator_three : capDenominator 3 = (4 : ℝ) / 3 := by
  have h := capDenominator_recurrence 1
  norm_num [capDenominator_one] at h
  exact h

lemma capFraction_two : capFraction 2 = (1 : ℝ) / 6 := by
  simp only [capFraction, Nat.reduceSub, capNumerator_zero, capDenominator_zero]
  field_simp [Real.pi_ne_zero]

lemma capFraction_five :
    capFraction 5 = (1 : ℝ) / 2 - 9 * s3 / 32 := by
  norm_num [capFraction, capNumerator_three, capDenominator_three]
  ring

private lemma six_boundary_eq_scaled_lower (m : ℕ) :
    6 * (((1 : ℝ) / 2) ^ (m + 1) * (s3 / 2)) =
      (5 * (m + 1 : ℝ)) *
        (3 * s3 / (10 * (m + 1) * 2 ^ m)) := by
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  have hpow : ((1 : ℝ) / 2) ^ m * 2 ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  rw [pow_succ]
  field_simp [hm]
  calc
    6 * ((1 : ℝ) / 2) ^ m * 10 * 2 ^ m
        = 60 * (((1 : ℝ) / 2) ^ m * 2 ^ m) := by ring
    _ = 2 ^ 2 * 5 * 3 := by rw [hpow]; norm_num

private lemma boundary_term_lt (m : ℕ) :
    6 * (((1 : ℝ) / 2) ^ (m + 1) * (s3 / 2)) <
      5 * (m + 1 : ℝ) * capNumerator m := by
  rw [six_boundary_eq_scaled_lower]
  exact mul_lt_mul_of_pos_left (capNumerator_lower m) (by positivity)

/-- The numerator recurrence retains more than one sixth of the scaled preceding numerator. -/
lemma capNumerator_step (m : ℕ) :
    (((m + 1 : ℝ) / (m + 2)) / 6) * capNumerator m <
      capNumerator (m + 2) := by
  rw [capNumerator_recurrence]
  have hm2 : 0 < (m + 2 : ℝ) := by positivity
  have hleft :
      (((m + 1 : ℝ) / (m + 2)) / 6) * capNumerator m =
        (((m + 1 : ℝ) * capNumerator m / 6) / (m + 2)) := by
    field_simp [hm2.ne']
  have hright :
      ((m + 1 : ℝ) / (m + 2)) * capNumerator m -
          (((1 : ℝ) / 2) ^ (m + 1) * (s3 / 2)) / (m + 2) =
        (((m + 1 : ℝ) * capNumerator m -
          ((1 : ℝ) / 2) ^ (m + 1) * (s3 / 2)) / (m + 2)) := by
    field_simp [hm2.ne']
  rw [hleft, hright, div_lt_div_iff_of_pos_right hm2]
  have hboundary := boundary_term_lt m
  nlinarith

/-- The normalized cap fractions satisfy the two-step estimate used in the proof. -/
lemma capFraction_step_aux (m : ℕ) :
    capNumerator m / capDenominator m / 6 <
      capNumerator (m + 2) / capDenominator (m + 2) := by
  rw [capDenominator_recurrence]
  have hm1 : (m + 1 : ℝ) ≠ 0 := by positivity
  have hm2 : (m + 2 : ℝ) ≠ 0 := by positivity
  have hJ : 0 < capDenominator m := capDenominator_pos m
  have ha : 0 < (m + 1 : ℝ) / (m + 2) := by positivity
  have hden : 0 < ((m + 1 : ℝ) / (m + 2)) * capDenominator m :=
    mul_pos ha hJ
  have hleft :
      capNumerator m / capDenominator m / 6 =
        ((((m + 1 : ℝ) / (m + 2)) / 6) * capNumerator m) /
          (((m + 1 : ℝ) / (m + 2)) * capDenominator m) := by
    field_simp [hm1, hm2, hJ.ne']
  rw [hleft, div_lt_div_iff_of_pos_right hden]
  exact capNumerator_step m

lemma capFraction_step (n : ℕ) (hn : 2 ≤ n) :
    capFraction n / 6 ≤ capFraction (n + 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := (capFraction_step_aux m).le
  simpa [capFraction, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The actual sine-integral cap fractions instantiate the abstract data of `Core.lean`. -/
def analyticCapData : CapData where
  cap := capFraction
  cap_two := capFraction_two
  cap_five := by simpa [s3] using capFraction_five
  step := capFraction_step

end

end Sqrt6KissingBound
