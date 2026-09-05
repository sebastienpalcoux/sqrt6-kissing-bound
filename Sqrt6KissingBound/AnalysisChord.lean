import Sqrt6KissingBound.Analysis

namespace Sqrt6KissingBound

noncomputable section

open Set
open scoped Interval Real

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
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
    simp [Real.pi_pos.le]
  have hcap : Real.pi / 6 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor
    · positivity
    · nlinarith [Real.pi_pos]
  have hstrict := strictConcaveOn_sin_Icc
  have hconc := hstrict.concaveOn
  have h := hconc.2 hzero hcap (sub_nonneg.2 hx1) hx0 (by ring)

  have hxt : x * (Real.pi / 6) = t := by
    dsimp [x]
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hhalf : x * ((1 : ℝ) / 2) = 3 * t / Real.pi := by
    dsimp [x]
    ring
  simpa only [smul_eq_mul, Real.sin_zero, Real.sin_pi_div_six, mul_zero,
    zero_add, hxt, hhalf] using h

end

end Sqrt6KissingBound
