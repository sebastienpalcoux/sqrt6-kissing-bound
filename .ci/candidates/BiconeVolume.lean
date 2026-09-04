import Sqrt6KissingBound.BodyVolumeAdditivity
import Sqrt6KissingBound.BiconeGeometry
import Sqrt6KissingBound.LinearProfileIntegral
import Sqrt6KissingBound.ProfileIntegralReal

/-! Development candidate: exact volume of the standard inscribed bicone. -/
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real

private abbrev s3 : ℝ := Real.sqrt 3
private abbrev a : ℝ := s3 / 2
private abbrev upperSlope : ℝ := 2 + s3
private lemma s3_pos : 0 < s3 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_ne : s3 ≠ 0 := s3_pos.ne'
private lemma s3_sq : s3 ^ 2 = 3 := by norm_num [s3]

private lemma lower_power_value (k : ℕ) :
    a ^ (k + 2) / (s3 ^ (k + 1) * (k + 2)) =
      s3 / ((k + 2) * 2 ^ (k + 2)) := by
  have hk : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  dsimp [a]
  rw [div_pow]
  field_simp [s3_ne, hk]
  ring

private lemma upper_product : upperSlope * (1 - a) = (1 : ℝ) / 2 := by
  dsimp [upperSlope, a]
  nlinarith [s3_sq]

private lemma two_power_step (k : ℕ) :
    (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]

private lemma upper_power_value (k : ℕ) :
    upperSlope ^ (k + 1) * (1 - a) ^ (k + 2) / (k + 2) =
      (2 - s3) / ((k + 2) * 2 ^ (k + 2)) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  calc
    upperSlope ^ (k + 1) * ((1 - a) ^ (k + 1) * (1 - a)) / (k + 2) =
        (upperSlope * (1 - a)) ^ (k + 1) * (1 - a) / (k + 2) := by
      rw [mul_pow]
      ring
    _ = ((1 : ℝ) / 2) ^ (k + 1) * (1 - a) / (k + 2) := by rw [upper_product]
    _ = (2 - s3) / ((k + 2) * 2 ^ (k + 2)) := by
      dsimp [a]
      simp only [two_power_step, div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
      norm_num <;> ring

lemma lower_profile_integral (k : ℕ) :
    (∫ t in (0 : ℝ)..a, (t / s3) ^ (k + 1)) =
      s3 / ((k + 2) * 2 ^ (k + 2)) := by
  rw [integral_div_mul_pow (k + 1) s3_ne]
  convert lower_power_value k using 1 <;> norm_num [Nat.cast_add, add_assoc]

lemma upper_profile_integral (k : ℕ) :
    (∫ t in a..1, (upperSlope * (1 - t)) ^ (k + 1)) =
      (2 - s3) / ((k + 2) * 2 ^ (k + 2)) := by
  rw [integral_const_mul_sub_pow (k + 1)]
  convert upper_power_value k using 1 <;> norm_num [Nat.cast_add, add_assoc]

lemma bicone_profile_integral (k : ℕ) :
    (∫ t in (0 : ℝ)..a, (t / s3) ^ (k + 1)) +
        (∫ t in a..1, (upperSlope * (1 - t)) ^ (k + 1)) =
      1 / ((k + 2) * 2 ^ (k + 1)) := by
  rw [lower_profile_integral, upper_profile_integral]
  simp only [two_power_step, div_eq_mul_inv, mul_inv_rev]
  ring

lemma measurableSet_lowerBicone (k : ℕ) : MeasurableSet (lowerBicone k) := by
  exact measurableSet_rotationalProfile (k + 1) measurableSet_Ioo
    (continuous_id.div_const _).measurable

lemma measurableSet_upperBicone (k : ℕ) : MeasurableSet (upperBicone k) := by
  exact measurableSet_rotationalProfile (k + 1) measurableSet_Ioo
    (continuous_const.mul (continuous_const.sub continuous_id)).measurable

lemma volumeReal_lowerBicone (k : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real (lowerBicone k) =
      (s3 / ((k + 2) * 2 ^ (k + 2))) * unitBallVolumeReal (k + 1) := by
  have h := volumeReal_rotationalProfile_Ioo k
    (a := (0 : ℝ)) (b := a) (g := fun t => t / s3)
    (by positivity) (continuous_id.div_const _)
    (by intro t ht; exact div_nonneg ht.1 s3_pos.le)
  simpa [lowerBicone, lower_profile_integral] using h

lemma volumeReal_upperBicone (k : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real (upperBicone k) =
      ((2 - s3) / ((k + 2) * 2 ^ (k + 2))) * unitBallVolumeReal (k + 1) := by
  have h := volumeReal_rotationalProfile_Ioo k
    (a := a) (b := (1 : ℝ)) (g := fun t => upperSlope * (1 - t))
    (by
      have hs : s3 < 2 := by nlinarith [s3_sq, s3_pos]
      dsimp [a]
      linarith)
    (continuous_const.mul (continuous_const.sub continuous_id))
    (by
      intro t ht
      have : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      positivity)
  simpa [upperBicone, upper_profile_integral] using h

lemma volumeReal_standardBicone (k : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real (standardBicone k) =
      (1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1) := by
  rw [standardBicone, volumeReal_union_of_subsets_ball
    (lowerBicone_disjoint_upperBicone k) (measurableSet_upperBicone k)
    (fun y hy => (lowerBicone_subset k hy).2)
    (fun y hy => (upperBicone_subset k hy).2)]
  rw [volumeReal_lowerBicone, volumeReal_upperBicone]
  simp only [two_power_step, div_eq_mul_inv, mul_inv_rev]
  ring

end
end Sqrt6KissingBound
