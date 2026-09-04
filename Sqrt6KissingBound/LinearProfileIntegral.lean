import Mathlib

namespace Sqrt6KissingBound

noncomputable section

open Set
open scoped Interval Real
open intervalIntegral

/-- Integral of a power of a line through the origin. -/
lemma integral_div_mul_pow (m : ℕ) {a c : ℝ} (hc : c ≠ 0) :
    (∫ t in (0 : ℝ)..a, (t / c) ^ m) =
      a ^ (m + 1) / (c ^ m * (m + 1)) := by
  calc
    (∫ t in (0 : ℝ)..a, (t / c) ^ m) =
        ∫ t in (0 : ℝ)..a, (c ^ m)⁻¹ * t ^ m := by
          apply intervalIntegral.integral_congr
          intro t ht
          change (t / c) ^ m = (c ^ m)⁻¹ * t ^ m
          rw [div_pow]
          simp only [div_eq_mul_inv]
          ring
    _ = (c ^ m)⁻¹ * ∫ t in (0 : ℝ)..a, t ^ m := by
          rw [intervalIntegral.integral_const_mul]
    _ = a ^ (m + 1) / (c ^ m * (m + 1)) := by
          rw [integral_pow]
          simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm,
            mul_assoc]

/-- Integral of a power of a line vanishing at the right endpoint. -/
lemma integral_const_mul_sub_pow (m : ℕ) {a b c : ℝ} :
    (∫ t in a..b, (c * (b - t)) ^ m) =
      c ^ m * (b - a) ^ (m + 1) / (m + 1) := by
  calc
    (∫ t in a..b, (c * (b - t)) ^ m) =
        ∫ t in a..b, c ^ m * (b - t) ^ m := by
          apply intervalIntegral.integral_congr
          intro t ht
          change (c * (b - t)) ^ m = c ^ m * (b - t) ^ m
          rw [mul_pow]
    _ = c ^ m * ∫ t in a..b, (b - t) ^ m := by
          rw [intervalIntegral.integral_const_mul]
    _ = c ^ m * (b - a) ^ (m + 1) / (m + 1) := by
          rw [intervalIntegral.integral_comp_sub_left
            (fun x : ℝ => x ^ m) b]
          rw [integral_pow]
          ring_nf

end

end Sqrt6KissingBound
