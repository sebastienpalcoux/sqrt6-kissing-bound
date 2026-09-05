import Sqrt6KissingBound.CoordinateVolume

/-!
# Volumes of bodies of revolution in first-coordinate form
-/

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

/-- The inverse image of a Euclidean ball under the canonical `L²` identification. -/
def tailBall (d : ℕ) (r : ℝ) : Set (Fin d → ℝ) :=
  (@WithLp.toLp 2 (Fin d → ℝ)) ⁻¹'
    ball (0 : EuclideanSpace ℝ (Fin d)) r

@[simp] lemma mem_tailBall {d : ℕ} {r : ℝ} {v : Fin d → ℝ} :
    v ∈ tailBall d r ↔
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ < r := by
  simp [tailBall, mem_ball, dist_zero_right]

lemma measurableSet_tailBall (d : ℕ) (r : ℝ) : MeasurableSet (tailBall d r) := by
  exact measurableSet_ball.preimage (PiLp.continuous_toLp 2 _).measurable

lemma volume_tailBall (d : ℕ) (r : ℝ) :
    (volume : Measure (Fin d → ℝ)) (tailBall d r) =
      (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 r) := by
  exact (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_ball.nullMeasurableSet

/-- A measurable body whose transverse section at `t` is an open Euclidean ball
of radius `g t`. -/
def profileRegion (d : ℕ) (s : Set ℝ) (g : ℝ → ℝ) :
    Set (ℝ × (Fin d → ℝ)) :=
  {p | p.1 ∈ s ∧ p.2 ∈ tailBall d (g p.1)}

lemma measurableSet_profileRegion (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    MeasurableSet (profileRegion d s g) := by
  have hnorm : Measurable fun p : ℝ × (Fin d → ℝ) =>
      ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin d))‖ :=
    (continuous_norm.comp
      ((PiLp.continuous_toLp 2 _).comp continuous_snd)).measurable
  have hsecond : MeasurableSet
      {p : ℝ × (Fin d → ℝ) |
        ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin d))‖ < g p.1} :=
    measurableSet_lt hnorm (hg.comp measurable_fst)
  rw [show profileRegion d s g =
      {p : ℝ × (Fin d → ℝ) | p.1 ∈ s} ∩
        {p | ‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin d))‖ < g p.1} by
    ext p
    simp [profileRegion]]
  exact (hs.preimage measurable_fst).inter hsecond

/-- Fubini formula for a body with ball-shaped transverse sections. -/
lemma volume_profileRegion (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    (volume : Measure (ℝ × (Fin d → ℝ))) (profileRegion d s g) =
      ∫⁻ t in s, (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 (g t)) := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_profileRegion d hs hg)]
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ s
  · have hfiber :
        Prod.mk t ⁻¹' profileRegion d s g = tailBall d (g t) := by
      ext v
      simp [profileRegion, ht]
    simp only [Set.indicator_of_mem ht]
    rw [hfiber]
    exact volume_tailBall d (g t)
  · simp [profileRegion, ht]

/-- The corresponding body in Euclidean space. -/
def rotationalProfile (d : ℕ) (s : Set ℝ) (g : ℝ → ℝ) :
    Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  (standardCoordinates d).symm ⁻¹' profileRegion d s g

lemma measurableSet_rotationalProfile (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    MeasurableSet (rotationalProfile d s g) := by
  exact (measurableSet_profileRegion d hs hg).preimage
    (standardCoordinates d).symm.measurable

lemma volume_rotationalProfile (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 1))))
        (rotationalProfile d s g) =
      ∫⁻ t in s, (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 (g t)) := by
  calc
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 1))))
          (rotationalProfile d s g) =
        (volume : Measure (ℝ × (Fin d → ℝ))) (profileRegion d s g) := by
          exact (standardCoordinates_measurePreserving d).symm.measure_preimage
            (measurableSet_profileRegion d hs hg).nullMeasurableSet
    _ = _ := volume_profileRegion d hs hg

end

end Sqrt6KissingBound
