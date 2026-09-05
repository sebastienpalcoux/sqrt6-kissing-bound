import Sqrt6KissingBound.CenteredBicone

/-! Transporting a standard cone body to arbitrary unit centers. -/
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

def centeredBody (k : ℕ) (S : Set (EuclideanSpace ℝ (Fin (k + 2))))
    (x : EuclideanSpace ℝ (Fin (k + 2))) : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  (axisTo k x).symm ⁻¹' S

lemma measurableSet_centeredBody {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))} (hS : MeasurableSet S)
    (x : EuclideanSpace ℝ (Fin (k + 2))) : MeasurableSet (centeredBody k S x) :=
  hS.preimage (axisTo k x).symm.continuous.measurable

lemma volumeReal_centeredBody {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))} (hS : MeasurableSet S)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real (centeredBody k S x) =
      (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real S := by
  rw [centeredBody, Measure.real,
    (axisTo k x).symm.measurePreserving.measure_preimage hS.nullMeasurableSet]
  rfl

lemma centeredBody_subset_cone_ball {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBody k S x ⊆ strictCone x ∩ ball 0 1 := by
  intro y hy
  let A := axisTo k x
  let z := A.symm y
  have hz : z ∈ S := hy
  have hzsub := hS hz
  constructor
  · have hzpre : z ∈ A ⁻¹' strictCone x := by
      rw [preimage_strictCone_linearIsometryEquiv A (axisTo_standardAxis hx)]
      exact hzsub.1
    simpa [A, z] using hzpre
  · rw [mem_ball, dist_zero_right]
    have hzball : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hzsub.2
    simpa [A, z] using hzball

lemma centeredBody_subset_unitBall {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : ‖x‖ = 1) :
    centeredBody k S x ⊆ ball 0 1 :=
  fun _ hy => (centeredBody_subset_cone_ball hS hx hy).2

lemma centeredBody_disjoint {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x z : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (centeredBody k S x) (centeredBody k S z) := by
  exact (strictCone_disjoint hx hz hxz).mono
    (fun _ hy => (centeredBody_subset_cone_ball hS hx hy).1)
    (fun _ hy => (centeredBody_subset_cone_ball hS hz hy).1)

end
end Sqrt6KissingBound
