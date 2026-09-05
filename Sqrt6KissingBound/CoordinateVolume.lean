import Mathlib

namespace Sqrt6KissingBound

noncomputable section

open MeasureTheory

/-- Split off the first Euclidean coordinate. -/
noncomputable def standardCoordinates (d : ℕ) :
    (ℝ × (Fin d → ℝ)) ≃ᵐ EuclideanSpace ℝ (Fin (d + 1)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm.trans
    (MeasurableEquiv.toLp 2 _)

lemma standardCoordinates_measurePreserving (d : ℕ) :
    MeasurePreserving (standardCoordinates d) := by
  exact
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm _).trans
      (PiLp.volume_preserving_toLp _)

end

end Sqrt6KissingBound
