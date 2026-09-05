import Sqrt6KissingBound.BiconeVolume
import Sqrt6KissingBound.VolumePacking
import Sqrt6KissingBound.CapMeasure

/-!
# Transporting the standard bicone to an arbitrary unit center
-/

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory

/-- A reflection carrying the first standard unit vector to `x`. -/
def axisTo (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    EuclideanSpace ℝ (Fin (k + 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (k + 2)) :=
  Submodule.reflection (ℝ ∙ (standardAxis (k + 1) - x))ᗮ

lemma axisTo_standardAxis {k : ℕ} {x : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : ‖x‖ = 1) : axisTo k x (standardAxis (k + 1)) = x := by
  exact Submodule.reflection_sub (by rw [norm_standardAxis, hx])

/-- The image of the standard bicone under the reflection carrying its axis to `x`. -/
def centeredBicone (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 2))) :
    Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  (axisTo k x).symm ⁻¹' standardBicone k

lemma measurableSet_standardBicone (k : ℕ) : MeasurableSet (standardBicone k) :=
  (measurableSet_lowerBicone k).union (measurableSet_upperBicone k)

lemma measurableSet_centeredBicone (k : ℕ)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    MeasurableSet (centeredBicone k x) :=
  (measurableSet_standardBicone k).preimage (axisTo k x).symm.continuous.measurable

lemma volumeReal_centeredBicone (k : ℕ)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real
        (centeredBicone k x) =
      (1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1) := by
  rw [centeredBicone, Measure.real,
    (axisTo k x).symm.measurePreserving.measure_preimage
      (measurableSet_standardBicone k).nullMeasurableSet,
    ← Measure.real]
  exact volumeReal_standardBicone k

lemma centeredBicone_subset_cone_ball {k : ℕ}
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBicone k x ⊆ strictCone x ∩ ball 0 1 := by
  intro y hy
  let A := axisTo k x
  let z := A.symm y
  have hz : z ∈ standardBicone k := hy
  have hzsub := standardBicone_subset k hz
  constructor
  · have hzpre : z ∈ A ⁻¹' strictCone x := by
      rw [preimage_strictCone_linearIsometryEquiv A
        (axisTo_standardAxis hx)]
      exact hzsub.1
    simpa [A, z] using hzpre
  · rw [mem_ball, dist_zero_right]
    have hzball : ‖z‖ < 1 := by
      simpa [mem_ball, dist_zero_right] using hzsub.2
    simpa [A, z] using hzball

lemma centeredBicone_subset_unitBall {k : ℕ}
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBicone k x ⊆ ball 0 1 :=
  fun _ hy => (centeredBicone_subset_cone_ball hx hy).2

lemma centeredBicone_disjoint {k : ℕ}
    {x z : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (centeredBicone k x) (centeredBicone k z) := by
  exact (strictCone_disjoint hx hz hxz).mono
    (fun _ hy => (centeredBicone_subset_cone_ball hx hy).1)
    (fun _ hy => (centeredBicone_subset_cone_ball hz hy).1)

end

end Sqrt6KissingBound
