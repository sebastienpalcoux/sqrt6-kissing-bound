import Sqrt6KissingBound.Optimality

/-! Development candidate: the kissing number as an attained maximum. -/
namespace Sqrt6KissingBound
noncomputable section

/-- A realizable cardinality of a normalized kissing configuration. -/
def RealizableKissingCard (n m : ℕ) : Prop :=
  ∃ X : Finset (EuclideanSpace ℝ (Fin n)), IsKissingConfiguration X ∧ X.card = m

def kissingNumberCeiling (n : ℕ) : ℕ := ⌊(Real.sqrt 6) ^ n⌋₊

/-- The independently proved ceiling bounds every configuration. The theorems
below prove this finite search is the genuine maximum over all configurations. -/
def kissingNumber (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (RealizableKissingCard n) (kissingNumberCeiling n)

lemma realizableKissingCard_zero (n : ℕ) : RealizableKissingCard n 0 := by
  refine ⟨∅, ?_, rfl⟩
  simp [IsKissingConfiguration]

theorem kissingNumber_realized (n : ℕ) : RealizableKissingCard n (kissingNumber n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (realizableKissingCard_zero n)

theorem realizableKissingCard_le_kissingNumber {n m : ℕ} (hn : 1 ≤ n)
    (hm : RealizableKissingCard n m) : m ≤ kissingNumber n := by
  classical
  rcases hm with ⟨X, hX, rfl⟩
  apply Nat.le_findGreatest
  · exact kissingConfiguration_card_le_floor_sqrt6_pow hn X hX
  · exact ⟨X, hX, rfl⟩

theorem kissingConfiguration_card_le_kissingNumber {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n))) (hX : IsKissingConfiguration X) :
    X.card ≤ kissingNumber n :=
  realizableKissingCard_le_kissingNumber hn ⟨X, hX, rfl⟩

theorem kissingNumber_isGreatest {n : ℕ} (hn : 1 ≤ n) :
    IsGreatest {m : ℕ | RealizableKissingCard n m} (kissingNumber n) := by
  refine ⟨kissingNumber_realized n, ?_⟩
  intro m hm
  exact realizableKissingCard_le_kissingNumber hn hm

theorem kissingNumber_le_sqrt6_pow {n : ℕ} (hn : 1 ≤ n) :
    (kissingNumber n : ℝ) ≤ (Real.sqrt 6) ^ n := by
  rcases kissingNumber_realized n with ⟨X, hX, hcard⟩
  rw [← hcard]
  exact kissingConfiguration_card_le_sqrt6_pow hn X hX

def oneDimensionalPair : Finset (EuclideanSpace ℝ (Fin 1)) := by
  classical
  exact {standardAxis 0, -standardAxis 0}

lemma oneDimensionalPair_card : oneDimensionalPair.card = 2 := by
  classical
  have hne : standardAxis 0 ≠ -standardAxis 0 := by
    intro h
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
    norm_num [standardAxis, standardCoordinates] at hh
  simp [oneDimensionalPair, hne]

lemma oneDimensionalPair_isKissingConfiguration : IsKissingConfiguration oneDimensionalPair := by
  classical
  constructor
  · intro x hx
    simp only [oneDimensionalPair, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  · intro x hx z hz hne
    simp only [oneDimensionalPair, Finset.mem_insert, Finset.mem_singleton] at hx hz
    rcases hx with rfl | rfl <;> rcases hz with rfl | rfl <;>
      norm_num [inner_neg_left, inner_neg_right, real_inner_self_eq_norm_sq] at hne ⊢

theorem kissingNumber_one_eq_two : kissingNumber 1 = 2 := by
  apply le_antisymm
  · rcases kissingNumber_realized 1 with ⟨X, hX, hcard⟩
    rw [← hcard]
    exact code_card_le_two_dim_one X hX.1
  · apply realizableKissingCard_le_kissingNumber (n := 1) (m := 2) (by norm_num)
    exact ⟨oneDimensionalPair, oneDimensionalPair_isKissingConfiguration, oneDimensionalPair_card⟩

theorem kissingNumber_two_eq_six : kissingNumber 2 = 6 := by
  apply le_antisymm
  · rcases kissingNumber_realized 2 with ⟨X, hX, hcard⟩
    rw [← hcard]
    exact code_card_le_six_dim_two X hX.1 hX.2
  · apply realizableKissingCard_le_kissingNumber (n := 2) (m := 6) (by norm_num)
    exact ⟨regularHexagon, regularHexagon_isKissingConfiguration, regularHexagon_card⟩

theorem universal_kissingNumber_bound_iff (α : ℝ) (hα : 0 ≤ α) :
    (∀ n : ℕ, 1 ≤ n → (kissingNumber n : ℝ) ≤ α ^ n) ↔ Real.sqrt 6 ≤ α := by
  constructor
  · intro h
    apply sqrt6_le_of_isUniversalKissingBase
    refine ⟨hα, ?_⟩
    intro n hn X hX
    have hc : (X.card : ℝ) ≤ kissingNumber n := by
      exact_mod_cast kissingConfiguration_card_le_kissingNumber hn X hX
    exact hc.trans (h n hn)
  · intro h n hn
    exact (kissingNumber_le_sqrt6_pow hn).trans
      (pow_le_pow_left₀ (Real.sqrt_nonneg 6) h n)

end
end Sqrt6KissingBound
