import Sqrt6KissingBound.ProfileIntegralReal
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Development candidate: volumes of Euclidean unit balls. -/
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Real

lemma pi_lt_22_div_7 : Real.pi < (22 : ℝ) / 7 := by
  have h := Real.pi_lt_d4
  norm_num at h
  linarith

lemma unitBallVolumeReal_formula (d : ℕ) :
    unitBallVolumeReal (d + 1) =
      Real.sqrt Real.pi ^ (d + 1) /
        Real.Gamma (((d + 1 : ℕ) : ℝ) / 2 + 1) := by
  rw [unitBallVolumeReal, Measure.real, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal]
  positivity

lemma unitBallVolumeReal_add_two (d : ℕ) :
    unitBallVolumeReal (d + 3) =
      (2 * Real.pi / (d + 3)) * unitBallVolumeReal (d + 1) := by
  rw [unitBallVolumeReal_formula (d + 2), unitBallVolumeReal_formula d]
  have hz : 0 < (((d + 1 : ℕ) : ℝ) / 2 + 1) := by positivity
  have hG : Real.Gamma (((d + 1 : ℕ) : ℝ) / 2 + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos hz).ne'
  have harg : (((d + 3 : ℕ) : ℝ) / 2 + 1) =
      (((d + 1 : ℕ) : ℝ) / 2 + 1) + 1 := by
    push_cast
    ring
  rw [harg, Real.Gamma_add_one (ne_of_gt hz)]
  rw [show d + 3 = (d + 1) + 2 by omega, pow_add, Real.sq_sqrt Real.pi_nonneg]
  field_simp [hG]
  push_cast
  ring

lemma unitBallVolumeReal_two : unitBallVolumeReal 2 = Real.pi := by
  rw [unitBallVolumeReal, Measure.real, EuclideanSpace.volume_ball_fin_two]
  simp [Real.pi_pos.le]

lemma unitBallVolumeReal_three : unitBallVolumeReal 3 = 4 * Real.pi / 3 := by
  rw [unitBallVolumeReal, Measure.real, EuclideanSpace.volume_ball_fin_three]
  simp [Real.pi_pos.le]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

lemma unitBallVolumeReal_four : unitBallVolumeReal 4 = Real.pi ^ 2 / 2 := by
  rw [unitBallVolumeReal_add_two 1, unitBallVolumeReal_two]
  ring

lemma unitBallVolumeReal_five : unitBallVolumeReal 5 = 8 * Real.pi ^ 2 / 15 := by
  rw [unitBallVolumeReal_add_two 2, unitBallVolumeReal_three]
  ring

lemma unitBallVolumeReal_six : unitBallVolumeReal 6 = Real.pi ^ 3 / 6 := by
  rw [unitBallVolumeReal_add_two 3, unitBallVolumeReal_four]
  ring

lemma unitBallVolumeReal_seven : unitBallVolumeReal 7 = 16 * Real.pi ^ 3 / 105 := by
  rw [unitBallVolumeReal_add_two 4, unitBallVolumeReal_five]
  ring

lemma unitBallVolumeReal_five_gt_six : unitBallVolumeReal 6 < unitBallVolumeReal 5 := by
  rw [unitBallVolumeReal_five, unitBallVolumeReal_six]
  have hpi : Real.pi < (16 : ℝ) / 5 := lt_trans pi_lt_22_div_7 (by norm_num)
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hmul := mul_lt_mul_of_pos_right hpi (sq_pos_of_pos hpipos)
  nlinarith

lemma unitBallVolumeReal_six_gt_seven : unitBallVolumeReal 7 < unitBallVolumeReal 6 := by
  rw [unitBallVolumeReal_six, unitBallVolumeReal_seven]
  have hpipos : 0 < Real.pi := Real.pi_pos
  nlinarith [pow_pos hpipos 3]

private lemma volume_descent_step {n : ℕ} (hn : 8 ≤ n)
    (hprev : unitBallVolumeReal (n - 2) ≤ unitBallVolumeReal (n - 3)) :
    unitBallVolumeReal n ≤ unitBallVolumeReal (n - 1) := by
  have hcast : ((n - 3 : ℕ) : ℝ) + 3 = (n : ℝ) := by
    exact_mod_cast (show n - 3 + 3 = n by omega)
  have hcast' : ((n - 4 : ℕ) : ℝ) + 3 = ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n - 4 + 3 = n - 1 by omega)
  have hvn : unitBallVolumeReal n =
      (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 2) := by
    simpa only [show n - 3 + 3 = n by omega,
      show n - 3 + 1 = n - 2 by omega, hcast]
      using unitBallVolumeReal_add_two (n - 3)
  have hvn1 : unitBallVolumeReal (n - 1) =
      (2 * Real.pi / ((n - 1 : ℕ) : ℝ)) * unitBallVolumeReal (n - 3) := by
    simpa only [show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 1 = n - 3 by omega, hcast']
      using unitBallVolumeReal_add_two (n - 4)
  rw [hvn, hvn1]
  have hn1pos : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hcoef : 2 * Real.pi / (n : ℝ) ≤ 2 * Real.pi / (n - 1 : ℕ) := by
    exact div_le_div_of_nonneg_left (by positivity) hn1pos
      (by exact_mod_cast Nat.sub_le n 1)
  have hV : 0 ≤ unitBallVolumeReal (n - 3) := measureReal_nonneg
  calc
    (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 2) ≤
        (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 3) :=
      mul_le_mul_of_nonneg_left hprev (by positivity)
    _ ≤ (2 * Real.pi / (n - 1 : ℕ)) * unitBallVolumeReal (n - 3) :=
      mul_le_mul_of_nonneg_right hcoef hV

lemma unitBallVolumeReal_antitone_from_six (n : ℕ) (hn : 6 ≤ n) :
    unitBallVolumeReal n ≤ unitBallVolumeReal (n - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h6 : n = 6
    · subst n
      simpa using unitBallVolumeReal_five_gt_six.le
    by_cases h7 : n = 7
    · subst n
      simpa using unitBallVolumeReal_six_gt_seven.le
    have hn8 : 8 ≤ n := by omega
    exact volume_descent_step hn8 (ih (n - 2) (by omega) (by omega))

end
end Sqrt6KissingBound
