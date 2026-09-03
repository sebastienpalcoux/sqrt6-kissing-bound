import Mathlib

/-!
# Algebraic core of the square-root-of-six kissing-number bound

This file is intended to be kernel-checkable without proof holes or unsafe
evaluation shortcuts. It formalizes the numerical estimates, the parity induction
for cap fractions, and the final cancellation argument. The standard spherical-cap
packing theorem is represented by the explicit hypothesis `hpack`.
-/

namespace Sqrt6KissingBound

noncomputable section

private abbrev s6 : ℝ := Real.sqrt 6
private abbrev s3 : ℝ := Real.sqrt 3

lemma sqrt6_pos : 0 < s6 := Real.sqrt_pos.2 (by norm_num)

lemma sqrt6_sq : s6 ^ 2 = 6 := by
  norm_num [s6]

lemma sqrt3_sq : s3 ^ 2 = 3 := by
  norm_num [s3]

lemma sqrt3_lt_26_div_15 : s3 < (26 : ℝ) / 15 := by
  have hnonneg : 0 ≤ s3 := Real.sqrt_nonneg 3
  have hsq : s3 ^ 2 = 3 := sqrt3_sq
  nlinarith

lemma sqrt3_lt_7_div_4 : s3 < (7 : ℝ) / 4 := by
  have hnonneg : 0 ≤ s3 := Real.sqrt_nonneg 3
  have hsq : s3 ^ 2 = 3 := sqrt3_sq
  nlinarith

lemma twenty_div_nine_lt_sqrt6 : (20 : ℝ) / 9 < s6 := by
  have hnonneg : 0 ≤ s6 := Real.sqrt_nonneg 6
  have hsq : s6 ^ 2 = 6 := sqrt6_sq
  nlinarith

lemma seven_div_three_lt_sqrt6 : (7 : ℝ) / 3 < s6 := by
  have hnonneg : 0 ≤ s6 := Real.sqrt_nonneg 6
  have hsq : s6 ^ 2 = 6 := sqrt6_sq
  nlinarith

lemma two_lt_sqrt6 : (2 : ℝ) < s6 := by
  have hnonneg : 0 ≤ s6 := Real.sqrt_nonneg 6
  have hsq : s6 ^ 2 = 6 := sqrt6_sq
  nlinarith

lemma fourteen_lt_sqrt6_cubed : (14 : ℝ) < s6 ^ 3 := by
  have hs : (7 : ℝ) / 3 < s6 := seven_div_three_lt_sqrt6
  have hsq : s6 ^ 2 = 6 := sqrt6_sq
  calc
    (14 : ℝ) = 6 * ((7 : ℝ) / 3) := by norm_num
    _ < 6 * s6 := by nlinarith
    _ = s6 ^ 3 := by
      rw [show s6 ^ 3 = s6 ^ 2 * s6 by ring, hsq]

lemma cap5_scaled_lower :
    1 < ((1 : ℝ) / 2 - 9 * s3 / 32) * s6 ^ 5 := by
  have h3 : s3 < (26 : ℝ) / 15 := sqrt3_lt_26_div_15
  have hc : (1 : ℝ) / 80 < (1 : ℝ) / 2 - 9 * s3 / 32 := by
    nlinarith
  have h6 : (20 : ℝ) / 9 < s6 := twenty_div_nine_lt_sqrt6
  have hpow : (80 : ℝ) < s6 ^ 5 := by
    calc
      (80 : ℝ) < 36 * s6 := by nlinarith
      _ = s6 ^ 5 := by
        rw [show s6 ^ 5 = (s6 ^ 2) ^ 2 * s6 by ring, sqrt6_sq]
        norm_num
  have hpowpos : 0 < s6 ^ 5 := pow_pos sqrt6_pos 5
  have hmul := mul_lt_mul_of_pos_right hc hpowpos
  have hone : (1 : ℝ) < (1 / 80 : ℝ) * s6 ^ 5 := by nlinarith
  exact hone.trans hmul

lemma cap3_positive : 0 < ((2 : ℝ) - s3) / 4 := by
  have h : s3 < (7 : ℝ) / 4 := sqrt3_lt_7_div_4
  nlinarith

lemma fifteen_mul_cap3_gt_one :
    1 < (15 : ℝ) * (((2 : ℝ) - s3) / 4) := by
  have h : s3 < (26 : ℝ) / 15 := sqrt3_lt_26_div_15
  nlinarith

/-- Abstract cap-fraction data carrying precisely the inputs used in the two-step induction. -/
structure CapData where
  cap : ℕ → ℝ
  cap_two : cap 2 = (1 : ℝ) / 6
  cap_five : cap 5 = (1 : ℝ) / 2 - 9 * s3 / 32
  step : ∀ n : ℕ, 2 ≤ n → cap n / 6 ≤ cap (n + 2)

namespace CapData

variable (D : CapData)

lemma scaled_step {n : ℕ} (hn : 2 ≤ n)
    (hscaled : 1 ≤ D.cap n * s6 ^ n) :
    1 ≤ D.cap (n + 2) * s6 ^ (n + 2) := by
  have hpow : 0 ≤ s6 ^ (n + 2) := (pow_pos sqrt6_pos _).le
  have hmul := mul_le_mul_of_nonneg_right (D.step n hn) hpow
  have heq : (D.cap n / 6) * s6 ^ (n + 2) = D.cap n * s6 ^ n := by
    rw [pow_add, sqrt6_sq]
    ring
  calc
    1 ≤ D.cap n * s6 ^ n := hscaled
    _ = (D.cap n / 6) * s6 ^ (n + 2) := heq.symm
    _ ≤ D.cap (n + 2) * s6 ^ (n + 2) := hmul

lemma even_scaled (k : ℕ) :
    1 ≤ D.cap (2 + 2 * k) * s6 ^ (2 + 2 * k) := by
  induction k with
  | zero =>
      rw [Nat.mul_zero, add_zero, D.cap_two, sqrt6_sq]
      norm_num
  | succ k ih =>
      have h := D.scaled_step (n := 2 + 2 * k) (by omega) ih
      have hk : 2 + 2 * Nat.succ k = (2 + 2 * k) + 2 := by omega
      simpa only [hk] using h

lemma odd_scaled (k : ℕ) :
    1 ≤ D.cap (5 + 2 * k) * s6 ^ (5 + 2 * k) := by
  induction k with
  | zero =>
      simpa [D.cap_five] using cap5_scaled_lower.le
  | succ k ih =>
      have h := D.scaled_step (n := 5 + 2 * k) (by omega) ih
      have hk : 5 + 2 * Nat.succ k = (5 + 2 * k) + 2 := by omega
      simpa only [hk] using h

end CapData

/-- Cancelling a positive cap fraction converts packing plus a scaled-cap lower bound
into the desired exponential count bound. -/
lemma count_le_pow_of_pack {N n : ℕ} {c : ℝ}
    (hpack : (N : ℝ) * c ≤ 1)
    (hscaled : 1 ≤ c * s6 ^ n) :
    (N : ℝ) ≤ s6 ^ n := by
  have hp : 0 < s6 ^ n := pow_pos sqrt6_pos n
  have hc : 0 < c := by
    by_contra h
    have hc' : c ≤ 0 := le_of_not_gt h
    have hnonpos : c * s6 ^ n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc' hp.le
    linarith
  have h : c * (N : ℝ) ≤ c * s6 ^ n := by
    rw [mul_comm c (N : ℝ)]
    exact hpack.trans hscaled
  exact le_of_mul_le_mul_left h hc

lemma count_le_sqrt6_pow_even (D : CapData) {N k : ℕ}
    (hpack : (N : ℝ) * D.cap (2 + 2 * k) ≤ 1) :
    (N : ℝ) ≤ s6 ^ (2 + 2 * k) :=
  count_le_pow_of_pack hpack (D.even_scaled k)

lemma count_le_sqrt6_pow_odd_ge_five (D : CapData) {N k : ℕ}
    (hpack : (N : ℝ) * D.cap (5 + 2 * k) ≤ 1) :
    (N : ℝ) ≤ s6 ^ (5 + 2 * k) :=
  count_le_pow_of_pack hpack (D.odd_scaled k)

/-- The exceptional three-dimensional numerical step: the cap estimate alone gives `N ≤ 14`. -/
lemma count_le_fourteen_of_cap3_pack {N : ℕ}
    (hpack : (N : ℝ) * (((2 : ℝ) - s3) / 4) ≤ 1) :
    N ≤ 14 := by
  let c : ℝ := ((2 : ℝ) - s3) / 4
  have hc : 0 < c := by simpa [c] using cap3_positive
  have h15 : 1 < (15 : ℝ) * c := by simpa [c] using fifteen_mul_cap3_gt_one
  have hltmul : c * (N : ℝ) < c * 15 := by
    rw [mul_comm c (N : ℝ), mul_comm c (15 : ℝ)]
    exact hpack.trans_lt h15
  have hlt : (N : ℝ) < 15 := lt_of_mul_lt_mul_left hltmul hc.le
  have hNlt : N < 15 := by exact_mod_cast hlt
  omega

lemma count_lt_sqrt6_cubed_of_cap3_pack {N : ℕ}
    (hpack : (N : ℝ) * (((2 : ℝ) - s3) / 4) ≤ 1) :
    (N : ℝ) < s6 ^ 3 := by
  have hN : N ≤ 14 := count_le_fourteen_of_cap3_pack hpack
  have hNreal : (N : ℝ) ≤ 14 := by exact_mod_cast hN
  exact hNreal.trans_lt fourteen_lt_sqrt6_cubed

/-- Dimension two forces the universal base to be at least `sqrt 6`. -/
lemma universal_base_ge_sqrt6 {α : ℝ} (hα : 0 ≤ α)
    (h_two : (6 : ℝ) ≤ α ^ 2) : s6 ≤ α := by
  have h : Real.sqrt 6 ≤ Real.sqrt (α ^ 2) := Real.sqrt_le_sqrt h_two
  simpa [s6, Real.sqrt_sq hα] using h

end

end Sqrt6KissingBound
