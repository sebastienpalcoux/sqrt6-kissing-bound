import Sqrt6KissingBound.AnalysisChord
import Sqrt6KissingBound.LinearProfileIntegral

/-! A chord estimate for the sine integral. -/
namespace Sqrt6KissingBound
noncomputable section
open Set intervalIntegral
open scoped Interval Real

lemma chord_integral_le_capNumerator (m : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) ≤ capNumerator m := by
  rw [capNumerator]
  apply intervalIntegral.integral_mono_on (by positivity)
  · exact (by fun_prop : Continuous (fun t : ℝ => (3 * t / Real.pi) ^ m)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun t : ℝ => Real.sin t ^ m)).intervalIntegrable _ _
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    exact pow_le_pow_left₀ (by positivity) (three_mul_div_pi_le_sin ht.1 ht.2) m

lemma chord_integral (m : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) =
      Real.pi / (6 * (m + 1) * 2 ^ m) := by
  have hbase : (Real.pi / 6) / (Real.pi / 3) = (1 : ℝ) / 2 := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  have halg (u v w : ℝ) : u ^ (m + 1) / (v ^ m * w) =
      (u / v) ^ m * u / w := by
    simp only [div_pow, pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring
  calc
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) =
        ∫ t in (0 : ℝ)..Real.pi / 6, (t / (Real.pi / 3)) ^ m := by
      apply intervalIntegral.integral_congr
      intro t ht
      congr 1
      field_simp [Real.pi_ne_zero]
      <;> ring
    _ = (Real.pi / 6) ^ (m + 1) / ((Real.pi / 3) ^ m * (m + 1)) :=
      integral_div_mul_pow m (by positivity)
    _ = ((Real.pi / 6) / (Real.pi / 3)) ^ m * (Real.pi / 6) / (m + 1) :=
      halg (Real.pi / 6) (Real.pi / 3) (m + 1)
    _ = Real.pi / (6 * (m + 1) * 2 ^ m) := by
      rw [hbase]
      simp only [div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
      ring_nf <;> norm_num

lemma pi_div_six_gt_three_sqrt3_div_ten :
    3 * Real.sqrt 3 / 10 < Real.pi / 6 := by
  have hpi := Real.pi_gt_d2
  have hs3 := sqrt3_lt_26_div_15
  norm_num at hpi
  nlinarith

lemma capNumerator_lower (m : ℕ) :
    3 * Real.sqrt 3 / (10 * (m + 1) * 2 ^ m) < capNumerator m := by
  have hD : 0 < (m + 1 : ℝ) * 2 ^ m := by positivity
  calc
    3 * Real.sqrt 3 / (10 * (m + 1) * 2 ^ m) =
        (3 * Real.sqrt 3 / 10) / ((m + 1 : ℝ) * 2 ^ m) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ < (Real.pi / 6) / ((m + 1 : ℝ) * 2 ^ m) :=
      div_lt_div_of_pos_right pi_div_six_gt_three_sqrt3_div_ten hD
    _ = Real.pi / (6 * (m + 1) * 2 ^ m) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) := (chord_integral m).symm
    _ ≤ capNumerator m := chord_integral_le_capNumerator m

end
end Sqrt6KissingBound
