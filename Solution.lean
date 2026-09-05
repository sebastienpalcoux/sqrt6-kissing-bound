import Sqrt6KissingBound

/-!
# Palomar proof interface

The first four Comparator targets are already proved by the imported project.
The four adapters below state results about genuine greatest cardinalities,
without exposing the implementation's bounded-search construction of a maximum.
This module never imports Challenge.lean.
-/

namespace Sqrt6KissingBound.Palomar

noncomputable section

theorem kissingNumber_exists {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℕ, IsGreatest {m : ℕ | RealizableKissingCard n m} k ∧
      (k : ℝ) ≤ (Real.sqrt 6) ^ n := by
  exact ⟨kissingNumber n, kissingNumber_isGreatest hn,
    kissingNumber_le_sqrt6_pow hn⟩

theorem planar_kissingNumber :
    IsGreatest {m : ℕ | RealizableKissingCard 2 m} 6 := by
  simpa only [kissingNumber_two_eq_six] using
    (kissingNumber_isGreatest (n := 2) (by decide))

theorem kissingNumber_roots (τ : ℕ → ℕ)
    (hτ : ∀ n : ℕ, 1 ≤ n →
      IsGreatest {m : ℕ | RealizableKissingCard n m} (τ n)) :
    sSup {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (τ n : ℝ) ^ ((n : ℝ)⁻¹)} = Real.sqrt 6 := by
  have heq : ∀ n : ℕ, 1 ≤ n → τ n = kissingNumber n := by
    intro n hn
    exact le_antisymm
      ((kissingNumber_isGreatest hn).2 (hτ n hn).1)
      ((hτ n hn).2 (kissingNumber_isGreatest hn).1)
  have hset :
      {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = (τ n : ℝ) ^ ((n : ℝ)⁻¹)} =
      {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
        r = (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹)} := by
    ext r
    constructor
    · rintro ⟨n, hn, hr⟩
      exact ⟨n, hn, by simpa only [heq n hn] using hr⟩
    · rintro ⟨n, hn, hr⟩
      exact ⟨n, hn, by simpa only [heq n hn] using hr⟩
  rw [hset]
  exact supremum_kissingNumber_roots_eq_sqrt6

theorem kissingNumber_universal_base (τ : ℕ → ℕ)
    (hτ : ∀ n : ℕ, 1 ≤ n →
      IsGreatest {m : ℕ | RealizableKissingCard n m} (τ n)) (α : ℝ) :
    (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (τ n : ℝ) ≤ α ^ n) ↔
      Real.sqrt 6 ≤ α := by
  have heq : ∀ n : ℕ, 1 ≤ n → τ n = kissingNumber n := by
    intro n hn
    exact le_antisymm
      ((kissingNumber_isGreatest hn).2 (hτ n hn).1)
      ((hτ n hn).2 (kissingNumber_isGreatest hn).1)
  have hiff :
      (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (τ n : ℝ) ≤ α ^ n) ↔
      (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (kissingNumber n : ℝ) ≤ α ^ n) := by
    constructor
    · rintro ⟨hα, hb⟩
      exact ⟨hα, fun n hn => by simpa only [heq n hn] using hb n hn⟩
    · rintro ⟨hα, hb⟩
      exact ⟨hα, fun n hn => by simpa only [heq n hn] using hb n hn⟩
  exact hiff.trans (kissingNumber_universal_base_iff α)

end

end Sqrt6KissingBound.Palomar
