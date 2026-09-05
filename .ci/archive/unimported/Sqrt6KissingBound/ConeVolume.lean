import Sqrt6KissingBound.CapMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Volume of a Euclidean right cone

This file proves the elementary cone-volume formula needed for a completely
formalized lower bound on the spherical cap sector.
-/

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- An open right cone in `ℝ × F`, of height `h` and base radius `r`. -/
def rightCone (h r : ℝ) : Set (ℝ × F) :=
  {p | p.1 ∈ Ioo 0 h ∧ ‖p.2‖ < (p.1 / h) * r}

lemma isOpen_rightCone (h r : ℝ) : IsOpen (rightCone (F := F) h r) := by
  change IsOpen ({p : ℝ × F | p.1 ∈ Ioo 0 h} ∩
    {p : ℝ × F | ‖p.2‖ < (p.1 / h) * r})
  exact (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt (by fun_prop) (by fun_prop))

lemma measurableSet_rightCone (h r : ℝ) :
    MeasurableSet (rightCone (F := F) h r) :=
  (isOpen_rightCone h r).measurableSet

lemma rightCone_section (h r t : ℝ) :
    Prod.mk t ⁻¹' rightCone (F := F) h r =
      if t ∈ Ioo 0 h then ball (0 : F) ((t / h) * r) else ∅ := by
  ext z
  by_cases ht : t ∈ Ioo (0 : ℝ) h
  · simp [rightCone, ht, mem_ball, dist_zero_right]
  · simp [rightCone, ht]

/-- The elementary integral used in the cone-volume formula. -/
lemma lintegral_Ioo_div_pow (d : ℕ) {h : ℝ} (hh : 0 < h) :
    ∫⁻ t in Ioo (0 : ℝ) h, ENNReal.ofReal ((t / h) ^ d) =
      ENNReal.ofReal (h / (d + 1)) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hh.le]
    have hpi : h ≠ 0 := hh.ne'
    simp_rw [div_pow]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_pow]
    simp
    congr 1
    field_simp [hpi]
    ring
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact pow_nonneg (div_nonneg ht.1.le hh.le) d

/-- Volume of a right cone equals height times base volume divided by the
ambient dimension. -/
theorem volume_rightCone [Nontrivial F] {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    volume (rightCone (F := F) h r) =
      ENNReal.ofReal (h / (Module.finrank ℝ F + 1)) *
        volume (ball (0 : F) r) := by
  let d : ℕ := Module.finrank ℝ F
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_apply (measurableSet_rightCone h r)]
  simp_rw [rightCone_section]
  have hfun :
      (fun t : ℝ => volume (if t ∈ Ioo (0 : ℝ) h
        then ball (0 : F) ((t / h) * r) else ∅)) =
      (Ioo (0 : ℝ) h).indicator
        (fun t : ℝ => ENNReal.ofReal ((t / h) ^ d) * volume (ball (0 : F) r)) := by
    funext t
    by_cases ht : t ∈ Ioo (0 : ℝ) h
    · have htdiv : 0 < t / h := div_pos ht.1 hh
      have hscale := (volume : Measure F).addHaar_ball_of_pos
        (x := (0 : F)) (r := r) hr ((t / h)) htdiv
      simp only [ht, if_pos, indicator_of_mem]
      simpa [d, ENNReal.ofReal_pow (div_nonneg ht.1.le hh.le)] using hscale
    · simp [ht]
  rw [hfun, lintegral_indicator measurableSet_Ioo]
  rw [lintegral_mul_const]
  rw [lintegral_Ioo_div_pow d hh]
  rfl

end

end Sqrt6KissingBound
