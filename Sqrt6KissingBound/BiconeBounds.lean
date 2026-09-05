import Sqrt6KissingBound.CenteredBicone
import Sqrt6KissingBound.BallVolumes

/-!
# Dimension-uniform consequences of bicone packing

The volume ratio gives the bound in dimensions two and five, and a
two-step numerical induction handles every dimension at least six.
-/
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

lemma bicone_packing_inequality (k : ℕ)
    (X : Finset (EuclideanSpace ℝ (Fin (k + 2))))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) * ((1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1)) ≤
      unitBallVolumeReal (k + 2) := by
  have h := card_mul_volumeReal_le_unitBall X (centeredBicone k)
    (fun x hx => measurableSet_centeredBicone k x)
    (fun x hx => centeredBicone_subset_unitBall (hunit x hx))
    (fun x hx z hz hne => centeredBicone_disjoint
      (hunit x hx) (hunit z hz) (hsep x hx z hz hne))
    (q := (1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1))
    (fun x hx => volumeReal_centeredBicone k x)
  simpa [unitBallVolumeReal] using h

lemma unitBallVolumeReal_one : unitBallVolumeReal 1 = 2 := by
  rw [unitBallVolumeReal_formula 0]
  simp only [Nat.cast_one, zero_add, pow_one]
  change Real.sqrt Real.pi / Real.Gamma ((1 : ℝ) / 2 + 1) = 2
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Real.Gamma_one_half_eq]
  field_simp [hsp]

lemma code_card_le_six_dim_two
    (X : Finset (EuclideanSpace ℝ (Fin 2)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    X.card ≤ 6 := by
  have hpack := bicone_packing_inequality 0 X hunit hsep
  rw [unitBallVolumeReal_one, unitBallVolumeReal_two] at hpack
  have hpi : Real.pi < (7 : ℝ) / 2 := lt_trans pi_lt_22_div_7 (by norm_num)
  have hcardR : (X.card : ℝ) < 7 := by norm_num at hpack; nlinarith
  have hcN : X.card < 7 := by exact_mod_cast hcardR
  omega

lemma code_card_le_sqrt6_sq
    (X : Finset (EuclideanSpace ℝ (Fin 2)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ 2 := by
  have hc : (X.card : ℝ) ≤ 6 := by exact_mod_cast code_card_le_six_dim_two X hunit hsep
  simpa using hc

lemma code_card_le_eightyfive_dim_five
    (X : Finset (EuclideanSpace ℝ (Fin 5)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    X.card ≤ 85 := by
  have hpack := bicone_packing_inequality 3 X hunit hsep
  rw [unitBallVolumeReal_four, unitBallVolumeReal_five] at hpack
  norm_num at hpack
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hcardR : (X.card : ℝ) < 86 := by
    by_contra hnot
    have hc : (86 : ℝ) ≤ X.card := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hc hp.le
    nlinarith
  have hcN : X.card < 86 := by exact_mod_cast hcardR
  omega

lemma code_card_le_sqrt6_fifth
    (X : Finset (EuclideanSpace ℝ (Fin 5)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ 5 := by
  have hc : (X.card : ℝ) ≤ 85 := by exact_mod_cast code_card_le_eightyfive_dim_five X hunit hsep
  have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  have hs : (85 : ℝ) / 36 < Real.sqrt 6 := by
    apply (sq_lt_sq₀ (by norm_num) hs0).1
    rw [hsq]
    norm_num
  have h85 : (85 : ℝ) < (Real.sqrt 6) ^ 5 := by
    rw [show (Real.sqrt 6) ^ 5 = ((Real.sqrt 6) ^ 2) ^ 2 * Real.sqrt 6 by ring, hsq]
    nlinarith
  exact hc.trans h85.le

lemma dimension_mul_two_pow_le_sqrt6_pow :
    ∀ n : ℕ, 6 ≤ n → (n : ℝ) * (2 : ℝ) ^ (n - 1) ≤ (Real.sqrt 6) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hsquare : (Real.sqrt 6) ^ 2 = 6 := by norm_num
    by_cases h6 : n = 6
    · subst n
      rw [show (Real.sqrt 6) ^ 6 = ((Real.sqrt 6) ^ 2) ^ 3 by ring, hsquare]
      norm_num
    by_cases h7 : n = 7
    · subst n
      have hs0 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
      have hs : (56 : ℝ) / 27 < Real.sqrt 6 := by
        apply (sq_lt_sq₀ (by norm_num) hs0).1
        rw [hsquare]
        norm_num
      rw [show (Real.sqrt 6) ^ 7 = ((Real.sqrt 6) ^ 2) ^ 3 * Real.sqrt 6 by ring, hsquare]
      norm_num
      nlinarith
    have hn8 : 8 ≤ n := by omega
    have hprev := ih (n - 2) (by omega) (by omega)
    have hpow2 : (2 : ℝ) ^ (n - 1) = 4 * (2 : ℝ) ^ (n - 3) := by
      rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
      norm_num
      ring
    have hsqrtn : (Real.sqrt 6) ^ n = 6 * (Real.sqrt 6) ^ (n - 2) := by
      have h := pow_add (Real.sqrt 6) (n - 2) 2
      rw [hsquare] at h
      simpa only [show n - 2 + 2 = n by omega, mul_comm] using h
    have hprev' : ((n - 2 : ℕ) : ℝ) * (2 : ℝ) ^ (n - 3) ≤
        (Real.sqrt 6) ^ (n - 2) := by
      simpa only [show (n - 2) - 1 = n - 3 by omega] using hprev
    have hcoef : (4 : ℝ) * n ≤ 6 * (n - 2 : ℕ) := by
      exact_mod_cast (show 4 * n ≤ 6 * (n - 2) by omega)
    rw [hpow2, hsqrtn]
    calc
      (n : ℝ) * (4 * (2 : ℝ) ^ (n - 3)) = (4 * n) * (2 : ℝ) ^ (n - 3) := by ring
      _ ≤ (6 * (n - 2 : ℕ)) * (2 : ℝ) ^ (n - 3) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 6 * (((n - 2 : ℕ) : ℝ) * (2 : ℝ) ^ (n - 3)) := by ring
      _ ≤ 6 * (Real.sqrt 6) ^ (n - 2) := mul_le_mul_of_nonneg_left hprev' (by norm_num)

lemma code_card_le_sqrt6_high {k : ℕ} (hk : 4 ≤ k)
    (X : Finset (EuclideanSpace ℝ (Fin (k + 2))))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ (k + 2) := by
  let D : ℝ := (k + 2) * 2 ^ (k + 1)
  let V : ℝ := unitBallVolumeReal (k + 1)
  have hpack := bicone_packing_inequality k X hunit hsep
  change (X.card : ℝ) * ((1 / D) * V) ≤ unitBallVolumeReal (k + 2) at hpack
  have hvol : unitBallVolumeReal (k + 2) ≤ V := by
    simpa only [V, show (k + 2) - 1 = k + 1 by omega]
      using unitBallVolumeReal_antitone_from_six (k + 2) (by omega)
  have hVpos : 0 < V := by simpa only [V] using unitBallVolumeReal_pos k
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hcardD : (X.card : ℝ) ≤ D := by
    have hsmall : ((X.card : ℝ) / D) * V ≤ 1 * V := by
      calc
        ((X.card : ℝ) / D) * V = (X.card : ℝ) * ((1 / D) * V) := by ring
        _ ≤ unitBallVolumeReal (k + 2) := hpack
        _ ≤ 1 * V := by simpa using hvol
    have hratio := (mul_le_mul_iff_of_pos_right hVpos).mp hsmall
    exact (div_le_one hDpos).mp hratio
  have hnum := dimension_mul_two_pow_le_sqrt6_pow (k + 2) (by omega)
  apply hcardD.trans
  simpa only [D, show (k + 2) - 1 = k + 1 by omega, Nat.cast_add, Nat.cast_ofNat] using hnum

end
end Sqrt6KissingBound
