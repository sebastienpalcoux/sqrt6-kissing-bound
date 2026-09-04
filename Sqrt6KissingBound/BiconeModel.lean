import Sqrt6KissingBound.CapMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volumes of model cones

This file computes the volume of a right circular cone by slicing it
orthogonally to its axis.  It is the measure-theoretic input for the bicone
proof of the universal square-root-of-six bound.
-/

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- A model open cone of height `h` and base radius `r` in `ℝ × V`. -/
def lowerConeModel (h r : ℝ) : Set (ℝ × V) :=
  {p | 0 < p.1 ∧ p.1 < h ∧ ‖p.2‖ < p.1 / h * r}

lemma isOpen_lowerConeModel (h r : ℝ) : IsOpen (lowerConeModel (V := V) h r) := by
  change IsOpen {p : ℝ × V | 0 < p.1 ∧ p.1 < h ∧ ‖p.2‖ < p.1 / h * r}
  exact ((isOpen_lt (by fun_prop) (by fun_prop)).inter
    (isOpen_lt (by fun_prop) (by fun_prop))).inter
      (isOpen_lt (by fun_prop) (by fun_prop))

lemma measurableSet_lowerConeModel (h r : ℝ) :
    MeasurableSet (lowerConeModel (V := V) h r) :=
  (isOpen_lowerConeModel h r).measurableSet

lemma lowerConeModel_fiber (h r t : ℝ) :
    Prod.mk t ⁻¹' lowerConeModel (V := V) h r =
      if t ∈ Set.Ioo (0 : ℝ) h then ball 0 (t / h * r) else ∅ := by
  ext v
  simp [lowerConeModel, mem_ball, dist_zero_right]

lemma lintegral_Ioo_pow (m : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ t in Set.Ioo (0 : ℝ) h, ENNReal.ofReal (t ^ m) =
      ENNReal.ofReal (h ^ (m + 1) / (m + 1)) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ENNReal.ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_pow m).1,
    ← intervalIntegral.integral_of_le hh]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg ht.1.le _

/-- The volume of a right circular cone is height times base volume divided by
one plus the base dimension. -/
lemma volume_lowerConeModel [Nontrivial V]
    {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    volume (lowerConeModel (V := V) h r) =
      ENNReal.ofReal (h / (Module.finrank ℝ V + 1)) *
        ENNReal.ofReal r ^ Module.finrank ℝ V * volume (ball (0 : V) 1) := by
  let d : ℕ := Module.finrank ℝ V
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_lowerConeModel h r)]
  simp_rw [lowerConeModel_fiber]
  rw [lintegral_ite measurableSet_Ioo]
  simp only [measure_empty, lintegral_zero, add_zero]
  have hrad : ∀ t ∈ Set.Ioo (0 : ℝ) h, 0 < t / h * r := by
    intro t ht
    positivity
  simp_rw [Measure.restrict_apply_univ]
  have hball : ∀ t ∈ Set.Ioo (0 : ℝ) h,
      volume (ball (0 : V) (t / h * r)) =
        ENNReal.ofReal (t / h * r) ^ d * volume (ball (0 : V) 1) := by
    intro t ht
    simpa [d] using
      (Measure.addHaar_ball_of_pos (volume : Measure V) (0 : V) (hrad t ht))
  rw [setLIntegral_congr_fun measurableSet_Ioo hball]
  rw [lintegral_mul_const]
  have hscale : ∀ t ∈ Set.Ioo (0 : ℝ) h,
      ENNReal.ofReal (t / h * r) ^ d =
        (ENNReal.ofReal r ^ d / ENNReal.ofReal h ^ d) *
          ENNReal.ofReal (t ^ d) := by
    intro t ht
    have ht : 0 ≤ t := ht.1.le
    have hh0 : 0 ≤ h := hh.le
    have hr0 : 0 ≤ r := hr.le
    rw [ENNReal.ofReal_mul hr0]
    rw [ENNReal.ofReal_div_of_pos _ hh]
    rw [div_pow, mul_pow]
    rw [ENNReal.ofReal_pow ht, ENNReal.ofReal_pow hh0]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioo hscale]
  rw [lintegral_const_mul]
  rw [lintegral_Ioo_pow d hh.le]
  dsimp [d]
  rw [ENNReal.ofReal_div_of_pos _ hh]
  rw [ENNReal.ofReal_div_of_pos _ (by positivity : (0 : ℝ) < Module.finrank ℝ V + 1)]
  rw [ENNReal.ofReal_pow hh.le]
  field_simp
  ring

end

end Sqrt6KissingBound
