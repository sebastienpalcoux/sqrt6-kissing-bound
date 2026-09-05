import Sqrt6KissingBound.Geometry
import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite packing inside the Euclidean unit ball
-/

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The real volumes of finitely many measurable, pairwise disjoint subsets of
the open unit ball sum to at most the volume of that ball. -/
lemma sum_volumeReal_le_unitBall (X : Finset ι) (body : ι → Set E)
    (hmeas : ∀ i ∈ X, MeasurableSet (body i))
    (hsub : ∀ i ∈ X, body i ⊆ ball 0 1)
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → Disjoint (body i) (body j)) :
    (∑ i ∈ X, (volume : Measure E).real (body i)) ≤
      (volume : Measure E).real (ball 0 1) := by
  let μ : Measure E := (volume : Measure E).restrict (ball 0 1)
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2
      (measure_ball_lt_top (μ := (volume : Measure E))).ne
  have hpack :
      (∑ i ∈ X, μ.real (body i)) ≤ μ.real Set.univ := by
    apply sum_measureReal_le_measureReal_univ
    · intro i hi
      exact hmeas i hi
    · intro i hi j hj hij
      exact hdisj i hi j hj hij
  have hbody (i : ι) (hi : i ∈ X) :
      μ.real (body i) = (volume : Measure E).real (body i) := by
    simp only [μ, Measure.real, Measure.restrict_apply (hmeas i hi)]
    rw [inter_eq_self_of_subset_left (hsub i hi)]
  have huniv : μ.real Set.univ =
      (volume : Measure E).real (ball 0 1) := by
    simp [μ, Measure.real]
  calc
    (∑ i ∈ X, (volume : Measure E).real (body i)) =
        ∑ i ∈ X, μ.real (body i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hbody i hi).symm
    _ ≤ μ.real Set.univ := hpack
    _ = (volume : Measure E).real (ball 0 1) := huniv

/-- Equal-volume specialization of `sum_volumeReal_le_unitBall`. -/
lemma card_mul_volumeReal_le_unitBall (X : Finset ι) (body : ι → Set E)
    (hmeas : ∀ i ∈ X, MeasurableSet (body i))
    (hsub : ∀ i ∈ X, body i ⊆ ball 0 1)
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → Disjoint (body i) (body j))
    {q : ℝ} (hvol : ∀ i ∈ X, (volume : Measure E).real (body i) = q) :
    (X.card : ℝ) * q ≤ (volume : Measure E).real (ball 0 1) := by
  have h := sum_volumeReal_le_unitBall X body hmeas hsub hdisj
  calc
    (X.card : ℝ) * q = ∑ i ∈ X, q := by simp
    _ = ∑ i ∈ X, (volume : Measure E).real (body i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hvol i hi).symm
    _ ≤ (volume : Measure E).real (ball 0 1) := h

end

end Sqrt6KissingBound
