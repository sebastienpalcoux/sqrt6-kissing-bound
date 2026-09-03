import Mathlib

/-!
# Cone separation for spherical codes

This file develops the geometric disjointness argument used in the fully formalized
volume-packing proof.
-/

namespace Sqrt6KissingBound

noncomputable section

open Set
open NormedSpace
open scoped RealInnerProductSpace

private abbrev s3 : ℝ := Real.sqrt 3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The open circular cone of half-angle `π/6`, written without trigonometric functions. -/
def strictCone (x : E) : Set E :=
  {y | (s3 / 2) * ‖y‖ < ⟪x, y⟫_ℝ}

lemma sqrt3_sq_geom : s3 ^ 2 = 3 := by
  norm_num [s3]

lemma sqrt3_pos_geom : 0 < s3 := Real.sqrt_pos.2 (by norm_num)

/-- Two `π/6` cones about unit vectors with inner product at most `1/2` are disjoint. -/
lemma strictCone_disjoint {x z : E}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hxz : ⟪x, z⟫_ℝ ≤ (1 : ℝ) / 2) :
    Disjoint (strictCone x) (strictCone z) := by
  rw [Set.disjoint_left]
  intro y hyx hyz
  change (s3 / 2) * ‖y‖ < ⟪x, y⟫_ℝ at hyx
  change (s3 / 2) * ‖y‖ < ⟪z, y⟫_ℝ at hyz
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    simp at hyx
  let u : E := normalize y
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    exact norm_normalize_eq_one_iff.mpr hy0
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  let a : ℝ := ⟪x, u⟫_ℝ
  let b : ℝ := ⟪z, u⟫_ℝ
  have ha : s3 / 2 < a := by
    dsimp [a, u, normalize]
    rw [real_inner_smul_right]
    rw [← div_eq_inv_mul]
    exact (lt_div_iff₀ hny).2 (by simpa [mul_comm] using hyx)
  have hb : s3 / 2 < b := by
    dsimp [b, u, normalize]
    rw [real_inner_smul_right]
    rw [← div_eq_inv_mul]
    exact (lt_div_iff₀ hny).2 (by simpa [mul_comm] using hyz)
  let p : E := x - a • u
  let q : E := z - b • u
  have hp_sq : ‖p‖ ^ 2 = 1 - a ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [p, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hx, hu, one_pow]
    dsimp [a]
    rw [real_inner_comm u x]
    ring
  have hq_sq : ‖q‖ ^ 2 = 1 - b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [q, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hz, hu, one_pow]
    dsimp [b]
    rw [real_inner_comm u z]
    ring
  have ha_sq : (3 : ℝ) / 4 < a ^ 2 := by
    have hs := sqrt3_pos_geom
    have hs2 := sqrt3_sq_geom
    nlinarith
  have hb_sq : (3 : ℝ) / 4 < b ^ 2 := by
    have hs := sqrt3_pos_geom
    have hs2 := sqrt3_sq_geom
    nlinarith
  have hp : ‖p‖ < (1 : ℝ) / 2 := by
    have hn : 0 ≤ ‖p‖ := norm_nonneg p
    nlinarith
  have hq : ‖q‖ < (1 : ℝ) / 2 := by
    have hn : 0 ≤ ‖q‖ := norm_nonneg q
    nlinarith
  have hab : (3 : ℝ) / 4 < a * b := by
    have hs := sqrt3_pos_geom
    have hs2 := sqrt3_sq_geom
    nlinarith
  have hpq : -(1 : ℝ) / 4 < ⟪p, q⟫_ℝ := by
    have habs := abs_real_inner_le_norm p q
    have hpn : 0 ≤ ‖p‖ := norm_nonneg p
    have hqn : 0 ≤ ‖q‖ := norm_nonneg q
    have hprod : ‖p‖ * ‖q‖ < (1 : ℝ) / 4 := by nlinarith
    have hlower : -(‖p‖ * ‖q‖) ≤ ⟪p, q⟫_ℝ := by
      exact (neg_le.mp (neg_le_abs ⟪p, q⟫_ℝ)).trans (by
        simpa [neg_le_neg_iff] using neg_le_neg habs)
    linarith
  have hdecomp : ⟪x, z⟫_ℝ = a * b + ⟪p, q⟫_ℝ := by
    have hxrepr : x = p + a • u := by simp [p]
    have hzrepr : z = q + b • u := by simp [q]
    rw [hxrepr, hzrepr]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hu, one_pow]
    have hpu : ⟪p, u⟫_ℝ = 0 := by
      simp only [p, inner_sub_left, real_inner_smul_left, hu, one_pow]
      dsimp [a]
      ring
    have huq : ⟪u, q⟫_ℝ = 0 := by
      simp only [q, inner_sub_right, real_inner_smul_right, hu, one_pow]
      dsimp [b]
      ring
    rw [hpu, huq]
    ring
  rw [hdecomp] at hxz
  linarith

end

end Sqrt6KissingBound
