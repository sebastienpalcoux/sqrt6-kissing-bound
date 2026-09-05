import Sqrt6KissingBound.KissingBound
import Sqrt6KissingBound.StandardGeometry

/-!
# Optimality of the universal base

A regular hexagon gives a six-point kissing configuration in dimension two.
-/

namespace Sqrt6KissingBound

noncomputable section

private abbrev s3 : ℝ := Real.sqrt 3

private lemma s3_pos_opt : 0 < s3 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq_opt : s3 ^ 2 = 3 := by norm_num [s3]

/-- A point of the Euclidean plane in the standard coordinate splitting. -/
def planePoint (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  standardCoordinates 1 (x, ![y])

lemma planePoint_norm_sq (x y : ℝ) :
    ‖planePoint x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [planePoint, norm_sq_standardCoordinates]
  simp [EuclideanSpace.real_norm_sq_eq]

lemma planePoint_norm_eq_one {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    ‖planePoint x y‖ = 1 := by
  have hn : 0 ≤ ‖planePoint x y‖ := norm_nonneg _
  nlinarith [planePoint_norm_sq x y]

lemma planePoint_inner (x y u v : ℝ) :
    inner ℝ (planePoint x y) (planePoint u v) = x * u + y * v := by
  simp [planePoint, standardCoordinates, PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]

/-- The six vertices of a regular hexagon on the unit circle. -/
def hexPoint : Fin 6 → EuclideanSpace ℝ (Fin 2) :=
  ![planePoint 1 0,
    planePoint (1 / 2) (s3 / 2),
    planePoint (-1 / 2) (s3 / 2),
    planePoint (-1) 0,
    planePoint (-1 / 2) (-s3 / 2),
    planePoint (1 / 2) (-s3 / 2)]

lemma hexPoint_norm (i : Fin 6) : ‖hexPoint i‖ = 1 := by
  fin_cases i <;> apply planePoint_norm_eq_one <;> nlinarith [s3_sq_opt]

lemma hexPoint_separated (i j : Fin 6) (hij : i ≠ j) :
    inner ℝ (hexPoint i) (hexPoint j) ≤ (1 : ℝ) / 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [hexPoint, planePoint_inner] at hij ⊢ <;>
    nlinarith [s3_sq_opt, s3_pos_opt]

lemma hexPoint_injective : Function.Injective hexPoint := by
  intro i j hij
  by_contra hne
  have hsep := hexPoint_separated i j hne
  have hinner : inner ℝ (hexPoint i) (hexPoint j) = 1 := by
    rw [hij, real_inner_self_eq_norm_sq, hexPoint_norm]
    norm_num
  linarith

/-- The regular hexagon as a finite set. -/
def regularHexagon : Finset (EuclideanSpace ℝ (Fin 2)) :=
  by
    classical
    exact Finset.univ.image hexPoint

lemma regularHexagon_card : regularHexagon.card = 6 := by
  classical
  have hcard : (Finset.univ.image hexPoint).card = Finset.univ.card :=
    Finset.card_image_iff.mpr hexPoint_injective.injOn
  simpa [regularHexagon] using hcard

lemma regularHexagon_isKissingConfiguration :
    IsKissingConfiguration regularHexagon := by
  classical
  constructor
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact hexPoint_norm i
  · intro x hx z hz hxz
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    apply hexPoint_separated i j
    intro hij
    apply hxz
    exact congrArg hexPoint hij

/-- A nonnegative number is a universal kissing base if it bounds every
finite kissing configuration in every positive dimension. -/
def IsUniversalKissingBase (α : ℝ) : Prop :=
  0 ≤ α ∧ ∀ {n : ℕ}, 1 ≤ n →
    ∀ X : Finset (EuclideanSpace ℝ (Fin n)),
      IsKissingConfiguration X → (X.card : ℝ) ≤ α ^ n

lemma sqrt6_isUniversalKissingBase :
    IsUniversalKissingBase (Real.sqrt 6) := by
  constructor
  · exact Real.sqrt_nonneg 6
  · intro n hn X hX
    exact kissingConfiguration_card_le_sqrt6_pow hn X hX

lemma sqrt6_le_of_isUniversalKissingBase {α : ℝ}
    (hα : IsUniversalKissingBase α) : Real.sqrt 6 ≤ α := by
  have h6 : (6 : ℝ) ≤ α ^ 2 := by
    have h := hα.2 (n := 2) (by norm_num) regularHexagon
      regularHexagon_isKissingConfiguration
    simpa [regularHexagon_card] using h
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  nlinarith [hα.1]

/-- `√6` is the least dimension-uniform exponential base. -/
theorem sqrt6_isLeast_universalKissingBase :
    IsLeast {α : ℝ | IsUniversalKissingBase α} (Real.sqrt 6) :=
  ⟨sqrt6_isUniversalKissingBase,
    fun _ hα => sqrt6_le_of_isUniversalKissingBase hα⟩

theorem isUniversalKissingBase_iff (α : ℝ) :
    IsUniversalKissingBase α ↔ Real.sqrt 6 ≤ α := by
  constructor
  · exact sqrt6_le_of_isUniversalKissingBase
  · intro hα
    refine ⟨(Real.sqrt_nonneg 6).trans hα, ?_⟩
    intro n hn X hX
    exact (kissingConfiguration_card_le_sqrt6_pow hn X hX).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg 6) hα n)

/-- Taking the positive dimensional root preserves the universal bound. -/
lemma kissingConfiguration_root_le_sqrt6 {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : IsKissingConfiguration X) :
    (X.card : ℝ) ^ ((n : ℝ)⁻¹) ≤ Real.sqrt 6 := by
  have hbound := kissingConfiguration_card_le_sqrt6_pow hn X hX
  have hn0 : n ≠ 0 := by omega
  have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ (X.card : ℝ))
    hbound (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rwa [Real.pow_rpow_inv_natCast (Real.sqrt_nonneg _) hn0] at hroot

theorem supremum_kissing_roots_eq_sqrt6 :
    sSup {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
      IsKissingConfiguration X ∧ x = (X.card : ℝ) ^ ((n : ℝ)⁻¹)} =
      Real.sqrt 6 := by
  have hmem : Real.sqrt 6 ∈
      {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
        IsKissingConfiguration X ∧ x = (X.card : ℝ) ^ ((n : ℝ)⁻¹)} := by
    refine ⟨2, by norm_num, regularHexagon, regularHexagon_isKissingConfiguration, ?_⟩
    rw [regularHexagon_card, Real.sqrt_eq_rpow]
    norm_num
  apply le_antisymm
  · apply csSup_le
    · exact ⟨Real.sqrt 6, hmem⟩
    · intro x hx
      rcases hx with ⟨n, hn, X, hX, rfl⟩
      exact kissingConfiguration_root_le_sqrt6 hn X hX
  · apply le_csSup
    · refine ⟨Real.sqrt 6, ?_⟩
      rintro x ⟨n, hn, X, hX, rfl⟩
      exact kissingConfiguration_root_le_sqrt6 hn X hX
    · exact hmem

end

end Sqrt6KissingBound
