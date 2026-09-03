import Sqrt6KissingBound.Packing
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Spherical caps as radial sectors

This file relates the cap measure defined by `Measure.toSphere` to the volume of
the corresponding sector of the unit ball and proves its invariance under
linear isometries.
-/

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory NormedSpace

private abbrev s3 : ℝ := Real.sqrt 3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The radial sector of the open unit ball subtended by the `π/6` cap centered at `x`. -/
def capSector (x : E) : Set E :=
  strictCone x ∩ ball 0 1

lemma isOpen_capSector (x : E) : IsOpen (capSector x) :=
  (isOpen_strictCone x).inter isOpen_ball

lemma measurableSet_capSector (x : E) : MeasurableSet (capSector x) :=
  (isOpen_capSector x).measurableSet

lemma mem_strictCone_smul_iff {x y : E} {r : ℝ} (hr : 0 < r) :
    r • y ∈ strictCone x ↔ y ∈ strictCone x := by
  change (s3 / 2) * ‖r • y‖ < inner ℝ x (r • y) ↔
    (s3 / 2) * ‖y‖ < inner ℝ x y
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, real_inner_smul_right]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (mul_lt_mul_left hr :
      r * ((s3 / 2) * ‖y‖) < r * inner ℝ x y ↔
        (s3 / 2) * ‖y‖ < inner ℝ x y)

/-- The radial set used in the definition of `Measure.toSphere` is exactly the
intersection of the cone with the open unit ball. -/
lemma Ioo_smul_sphericalCap (x : E) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' sphericalCap x) = capSector x := by
  ext y
  constructor
  · rintro ⟨r, hr, u, hu, rfl⟩
    rcases hu with ⟨v, hv, rfl⟩
    have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    constructor
    · exact (mem_strictCone_smul_iff hr.1).2 hv
    · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr.1, hvnorm, mul_one]
      exact hr.2
  · rintro ⟨hycone, hyball⟩
    have hy0 : y ≠ 0 := by
      intro h
      subst y
      simp [strictCone] at hycone
    have hnorm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hnorm_lt : ‖y‖ < 1 := by
      simpa [mem_ball, dist_zero_right] using hyball
    let u : sphere (0 : E) 1 :=
      ⟨NormedSpace.normalize y, mem_sphere_zero_iff_norm.mpr (norm_normalize hy0)⟩
    have hucone : u ∈ sphericalCap x := by
      change NormedSpace.normalize y ∈ strictCone x
      have h := (mem_strictCone_smul_iff (x := x) (y := NormedSpace.normalize y) hnorm_pos).1
      simpa using h (by simpa using hycone)
    refine ⟨‖y‖, ⟨hnorm_pos, hnorm_lt⟩, (u : E), ⟨u, hucone, rfl⟩, ?_⟩
    exact NormedSpace.norm_smul_normalize y

variable [FiniteDimensional ℝ E]

/-- Surface measure of a cap equals the dimension times the volume of its radial sector. -/
lemma toSphere_sphericalCap (x : E) :
    (volume : Measure E).toSphere (sphericalCap x) =
      Module.finrank ℝ E * volume (capSector x) := by
  rw [Measure.toSphere_apply' (volume : Measure E) (measurableSet_sphericalCap x),
    Ioo_smul_sphericalCap]

/-- Linear isometries transport strict cones. -/
lemma preimage_strictCone_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) {x z : E}
    (hAx : A x = z) : A ⁻¹' strictCone z = strictCone x := by
  ext y
  change (s3 / 2) * ‖A y‖ < inner ℝ z (A y) ↔
    (s3 / 2) * ‖y‖ < inner ℝ x y
  rw [A.norm_map, ← hAx, A.inner_map_map]

/-- Linear isometries transport cap sectors. -/
lemma preimage_capSector_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) {x z : E}
    (hAx : A x = z) : A ⁻¹' capSector z = capSector x := by
  rw [capSector, capSector, preimage_inter, preimage_strictCone_linearIsometryEquiv A hAx]
  ext y
  simp [A.norm_map]

/-- The radial-sector volume is independent of the unit center. -/
lemma volume_capSector_eq_of_norm_eq {x z : E} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) :
    volume (capSector x) = volume (capSector z) := by
  let A : E ≃ₗᵢ[ℝ] E := Submodule.reflection (ℝ ∙ (x - z))ᗮ
  have hAx : A x = z := by
    exact Submodule.reflection_sub (by rw [hx, hz])
  rw [← A.measurePreserving.measure_preimage (measurableSet_capSector z),
    preimage_capSector_linearIsometryEquiv A hAx]

/-- Spherical caps with unit centers have equal `Measure.toSphere` measure. -/
lemma toSphere_sphericalCap_eq_of_norm_eq {x z : E} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) :
    (volume : Measure E).toSphere (sphericalCap x) =
      (volume : Measure E).toSphere (sphericalCap z) := by
  rw [toSphere_sphericalCap, toSphere_sphericalCap,
    volume_capSector_eq_of_norm_eq hx hz]

end

end Sqrt6KissingBound
