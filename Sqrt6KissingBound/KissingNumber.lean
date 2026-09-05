import Sqrt6KissingBound.Optimality
import Mathlib.Data.Nat.Find

/-!
# The kissing number as a maximum

The earlier theorem bounds every finite kissing configuration.  Here we
package the largest realizable cardinality as an actual natural number.
-/

namespace Sqrt6KissingBound

noncomputable section

/-- `m` is the cardinality of a kissing configuration in dimension `n`. -/
def RealizableKissingCard (n m : ℕ) : Prop :=
  ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
    IsKissingConfiguration X ∧ X.card = m

/-- The certified natural-number ceiling used to take the maximum. -/
def kissingNumberCeiling (n : ℕ) : ℕ :=
  ⌊(Real.sqrt 6) ^ n⌋₊

/-- The kissing number in dimension `n`, defined as the greatest realizable
cardinality below the already proved universal ceiling. -/
def kissingNumber (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest (RealizableKissingCard n) (kissingNumberCeiling n)

lemma realizableKissingCard_zero (n : ℕ) : RealizableKissingCard n 0 := by
  refine ⟨∅, ?_, rfl⟩
  simp [IsKissingConfiguration]

theorem kissingNumber_realized (n : ℕ) :
    RealizableKissingCard n (kissingNumber n) := by
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
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : IsKissingConfiguration X) :
    X.card ≤ kissingNumber n :=
  realizableKissingCard_le_kissingNumber hn ⟨X, hX, rfl⟩

theorem kissingNumber_isGreatest {n : ℕ} (hn : 1 ≤ n) :
    IsGreatest {m : ℕ | RealizableKissingCard n m} (kissingNumber n) := by
  refine ⟨kissingNumber_realized n, ?_⟩
  intro m hm
  exact realizableKissingCard_le_kissingNumber hn hm

/-- The theorem in the usual notation: the kissing number itself is at most
the `n`-th power of `√6`. -/
theorem kissingNumber_le_sqrt6_pow {n : ℕ} (hn : 1 ≤ n) :
    (kissingNumber n : ℝ) ≤ (Real.sqrt 6) ^ n := by
  rcases kissingNumber_realized n with ⟨X, hX, hcard⟩
  rw [← hcard]
  exact kissingConfiguration_card_le_sqrt6_pow hn X hX

theorem kissingNumber_two_eq_six : kissingNumber 2 = 6 := by
  apply le_antisymm
  · have hreal := kissingNumber_realized 2
    rcases hreal with ⟨X, hX, hcard⟩
    rw [← hcard]
    exact code_card_le_six_dim_two X hX.1 hX.2
  · apply realizableKissingCard_le_kissingNumber (n := 2) (m := 6) (by norm_num)
    exact ⟨regularHexagon, regularHexagon_isKissingConfiguration,
      regularHexagon_card⟩

end

end Sqrt6KissingBound
