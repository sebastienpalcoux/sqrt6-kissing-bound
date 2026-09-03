import Sqrt6KissingBound.Geometry
import Sqrt6KissingBound.CapFraction

/-!
# Packing disjoint spherical caps

This file turns the cone-separation theorem into the finite-measure packing
inequality used in the kissing-number argument.
-/

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory

private abbrev s3 : ℝ := Real.sqrt 3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The open spherical cap of angular radius `π/6` centered at the unit vector `x`. -/
def sphericalCap (x : E) : Set (sphere (0 : E) 1) :=
  {u | (u : E) ∈ strictCone x}

lemma isOpen_strictCone (x : E) : IsOpen (strictCone x) := by
  change IsOpen {y : E | (s3 / 2) * ‖y‖ < inner ℝ x y}
  exact isOpen_lt (by fun_prop) (by fun_prop)

lemma isOpen_sphericalCap (x : E) : IsOpen (sphericalCap x) := by
  change IsOpen (Subtype.val ⁻¹' strictCone x)
  exact (isOpen_strictCone x).preimage continuous_subtype_val

lemma measurableSet_sphericalCap (x : E) : MeasurableSet (sphericalCap x) :=
  (isOpen_sphericalCap x).measurableSet

lemma sphericalCap_disjoint {x z : E}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (sphericalCap x) (sphericalCap z) := by
  rw [Set.disjoint_left]
  intro u hux huz
  exact (Set.disjoint_left.mp (strictCone_disjoint hx hz hxz)) hux huz

variable [FiniteDimensional ℝ E]

/-- The total surface measure of pairwise separated `π/6` caps is at most the
surface measure of the sphere. -/
lemma sphericalCap_measure_pack (X : Finset E)
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (∑ x ∈ X, ((volume : Measure E).toSphere).real (sphericalCap x)) ≤
      ((volume : Measure E).toSphere).real Set.univ := by
  apply sum_measureReal_le_measureReal_univ
  · intro x hx
    exact measurableSet_sphericalCap x
  · intro x hx z hz hne
    exact sphericalCap_disjoint (hunit x hx) (hunit z hz) (hsep x hx z hz hne)

/-- The surface measure of the full unit sphere is positive in a nontrivial
finite-dimensional real inner-product space. -/
lemma toSphere_real_univ_pos [Nontrivial E] :
    0 < ((volume : Measure E).toSphere).real (Set.univ : Set (sphere (0 : E) 1)) := by
  rw [Measure.toSphere_real_apply_univ]
  have hdim : 0 < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hball : 0 < (volume : Measure E).real (ball (0 : E) 1) := by
    exact ENNReal.toReal_pos
      (measure_ball_pos (volume : Measure E) 0 zero_lt_one).ne'
      measure_ball_lt_top.ne
  exact mul_pos hdim hball

/-- If every cap has normalized measure `c`, then a finite spherical code has
cardinality at most `1/c`. -/
lemma card_mul_cap_le_one_of_equal_measure [Nontrivial E]
    (X : Finset E)
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2)
    {c : ℝ}
    (hcap : ∀ x ∈ X,
      ((volume : Measure E).toSphere).real (sphericalCap x) =
        c * ((volume : Measure E).toSphere).real
          (Set.univ : Set (sphere (0 : E) 1))) :
    (X.card : ℝ) * c ≤ 1 := by
  let T : ℝ := ((volume : Measure E).toSphere).real
    (Set.univ : Set (sphere (0 : E) 1))
  have hT : 0 < T := by
    simpa [T] using (toSphere_real_univ_pos (E := E))
  have hpack := sphericalCap_measure_pack X hunit hsep
  have hsum :
      (∑ x ∈ X, ((volume : Measure E).toSphere).real (sphericalCap x)) =
        (X.card : ℝ) * (c * T) := by
    calc
      (∑ x ∈ X, ((volume : Measure E).toSphere).real (sphericalCap x))
          = ∑ x ∈ X, c * T := by
              apply Finset.sum_congr rfl
              intro x hx
              simpa [T] using hcap x hx
      _ = (X.card : ℝ) * (c * T) := by simp
  have hmul : ((X.card : ℝ) * c) * T ≤ 1 * T := by
    calc
      ((X.card : ℝ) * c) * T = (X.card : ℝ) * (c * T) := by ring
      _ = ∑ x ∈ X, ((volume : Measure E).toSphere).real (sphericalCap x) := hsum.symm
      _ ≤ T := by simpa [T] using hpack
      _ = 1 * T := by ring
  exact (mul_le_mul_right hT).mp hmul

end

end Sqrt6KissingBound
