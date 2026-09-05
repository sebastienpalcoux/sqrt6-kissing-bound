import Sqrt6KissingBound.VolumePacking

/-! Additivity of real volume for disjoint bounded bodies. -/

namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

lemma volumeReal_union_of_subsets_ball {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))}
    (hd : Disjoint S T) (hT : MeasurableSet T)
    (hSball : S ⊆ ball 0 1) (hTball : T ⊆ ball 0 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (S ∪ T) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real S +
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real T := by
  exact measureReal_union hd hT
    (lt_of_le_of_lt (measure_mono hSball) measure_ball_lt_top).ne
    (lt_of_le_of_lt (measure_mono hTball) measure_ball_lt_top).ne

end
end Sqrt6KissingBound
