import Sqrt6KissingBound.CenteredBody
import Sqrt6KissingBound.BallVolumes

/-! A polynomial body gives the four-dimensional bound. -/
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000

private abbrev s3 : ℝ := Real.sqrt 3
private abbrev a : ℝ := s3 / 2
private lemma s3_pos : 0 < s3 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3 ^ 2 = 3 := by norm_num [s3]

def upperProfile4 (t : ℝ) : ℝ := (1 - t) * (14 * t + 2 - 6 * s3)
def upperBody4 : Set (EuclideanSpace ℝ (Fin 4)) :=
  rotationalProfile 3 (Set.Ioo a 1) upperProfile4
def standardBody4 : Set (EuclideanSpace ℝ (Fin 4)) := lowerBicone 2 ∪ upperBody4

lemma continuous_upperProfile4 : Continuous upperProfile4 := by
  unfold upperProfile4
  fun_prop

lemma upperProfile4_nonneg {t : ℝ} (hta : a ≤ t) (ht1 : t ≤ 1) :
    0 ≤ upperProfile4 t := by
  have hh : 0 ≤ 14 * t + 2 - 6 * s3 := by
    dsimp [a] at hta
    nlinarith [s3_pos]
  exact mul_nonneg (sub_nonneg.mpr ht1) hh

private lemma q4_nonneg {t : ℝ} (hta : a ≤ t) :
    0 ≤ 196 * t ^ 2 - (140 + 70 * s3) * t - 48 + 74 * s3 := by
  have hs15 : (3 : ℝ) / 2 < s3 := by
    have hs0 : 0 ≤ s3 := s3_pos.le
    nlinarith [s3_sq]
  have hs109 : (10 : ℝ) / 9 < s3 := by linarith
  have hbase : 0 ≤ -6 + 4 * s3 := by linarith
  have hfactor : 0 ≤ 196 * (t + a) - (140 + 70 * s3) := by
    dsimp [a] at hta ⊢
    nlinarith
  have hprod : 0 ≤ (t - a) * (196 * (t + a) - (140 + 70 * s3)) :=
    mul_nonneg (sub_nonneg.mpr hta) hfactor
  have hid :
      196 * t ^ 2 - (140 + 70 * s3) * t - 48 + 74 * s3 =
        (-6 + 4 * s3) + (t - a) * (196 * (t + a) - (140 + 70 * s3)) := by
    dsimp [a]
    nlinarith [s3_sq]
  rw [hid]
  positivity

lemma upperProfile4_sq_le {t : ℝ} (hta : a ≤ t) (ht1 : t ≤ 1) :
    upperProfile4 t ^ 2 ≤ 1 - t ^ 2 := by
  let h : ℝ := 14 * t + 2 - 6 * s3
  let q : ℝ := 196 * t ^ 2 - (140 + 70 * s3) * t - 48 + 74 * s3
  have hq : 0 ≤ q := by simpa [q] using q4_nonneg hta
  have hP : 0 ≤ 1 + t - (1 - t) * h ^ 2 := by
    have hid : 1 + t - (1 - t) * h ^ 2 = (t - a) * q := by
      dsimp [h, q, a]
      linear_combination (t + 1) * s3_sq
    rw [hid]
    exact mul_nonneg (sub_nonneg.mpr hta) hq
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hid2 : 1 - t ^ 2 - upperProfile4 t ^ 2 =
      (1 - t) * (1 + t - (1 - t) * h ^ 2) := by
    dsimp [upperProfile4, h]
    ring
  have hnonneg := mul_nonneg h1t hP
  rw [← hid2] at hnonneg
  linarith

lemma measurableSet_upperBody4 : MeasurableSet upperBody4 :=
  measurableSet_rotationalProfile 3 measurableSet_Ioo continuous_upperProfile4.measurable
lemma measurableSet_standardBody4 : MeasurableSet standardBody4 :=
  (measurableSet_lowerBicone 2).union measurableSet_upperBody4

private lemma upperBody4_point_mem {t : ℝ} {v : Fin 3 → ℝ}
    (hta : a < t) (ht1 : t < 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ < upperProfile4 t) :
    standardCoordinates 3 (t, v) ∈ strictCone (standardAxis 3) ∩ ball 0 1 := by
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have ht0 : 0 < t := lt_trans (by positivity : 0 < a) hta
  have hg0 : 0 ≤ upperProfile4 t := upperProfile4_nonneg hta.le ht1.le
  have hrsq : r ^ 2 < upperProfile4 t ^ 2 :=
    (sq_lt_sq₀ hr0 hg0).2 (by simpa [r] using hv)
  have hcircle := upperProfile4_sq_le hta.le ht1.le
  have hrball : r ^ 2 < 1 - t ^ 2 := lt_of_lt_of_le hrsq hcircle
  have ht_sq_gt : (3 : ℝ) / 4 < t ^ 2 := by
    have ha0 : 0 ≤ a := by positivity
    have hsq := (sq_lt_sq₀ ha0 ht0.le).2 hta
    dsimp [a] at hsq
    nlinarith [s3_sq]
  have hcone_sq : 3 * r ^ 2 < t ^ 2 := by nlinarith
  constructor
  · rw [standardCoordinates_mem_strictCone_iff]
    have hq : 0 ≤ t ^ 2 + r ^ 2 := by positivity
    have hleft : 0 ≤ (s3 / 2) * Real.sqrt (t ^ 2 + r ^ 2) := by positivity
    apply (sq_lt_sq₀ hleft ht0.le).1
    rw [mul_pow, Real.sq_sqrt hq]
    nlinarith [s3_sq]
  · rw [standardCoordinates_mem_ball_iff]
    nlinarith

lemma upperBody4_subset : upperBody4 ⊆ strictCone (standardAxis 3) ∩ ball 0 1 := by
  intro y hy
  let p := (standardCoordinates 3).symm y
  have hp : p ∈ profileRegion 3 (Set.Ioo a 1) upperProfile4 := hy
  rcases hp with ⟨ht, hv⟩
  have hpoint := upperBody4_point_mem ht.1 ht.2 hv
  simpa [p] using hpoint

lemma standardBody4_subset : standardBody4 ⊆ strictCone (standardAxis 3) ∩ ball 0 1 :=
  union_subset (lowerBicone_subset 2) upperBody4_subset

lemma lowerBicone_two_disjoint_upperBody4 : Disjoint (lowerBicone 2) upperBody4 := by
  rw [Set.disjoint_left]
  intro y hyl hyu
  let p := (standardCoordinates 3).symm y
  have hl : p.1 ∈ Set.Ioo 0 a := hyl.1
  have hu : p.1 ∈ Set.Ioo a 1 := hyu.1
  exact lt_asymm hl.2 hu.1

lemma upperProfile4_integral :
    (∫ t in a..1, upperProfile4 t ^ 3) = (33169 - 19150 * s3) / 40 := by
  let B : ℝ := 2 - 6 * s3
  let C : ℝ := 12 + 6 * s3
  have hfun : (fun t : ℝ => upperProfile4 t ^ 3) = fun t =>
      (-14 : ℝ) ^ 3 * t ^ 6 + 3 * (-14 : ℝ) ^ 2 * C * t ^ 5 +
      (3 * (-14 : ℝ) ^ 2 * B + 3 * (-14 : ℝ) * C ^ 2) * t ^ 4 +
      (C ^ 3 + 6 * (-14 : ℝ) * C * B) * t ^ 3 +
      (3 * C ^ 2 * B + 3 * (-14 : ℝ) * B ^ 2) * t ^ 2 +
      3 * C * B ^ 2 * t ^ 1 + B ^ 3 := by
    funext t
    dsimp [upperProfile4, B, C]
    ring
  rw [hfun]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      integral_pow, intervalIntegral.integral_const, smul_eq_mul]
  dsimp [a, B, C]
  have h3 := congrArg (fun x : ℝ => x * s3) s3_sq
  have h4 := congrArg (fun x : ℝ => x ^ 2) s3_sq
  have h5 := congrArg (fun x : ℝ => x * s3) h4
  have h6 := congrArg (fun x : ℝ => x ^ 3) s3_sq
  have h7 := congrArg (fun x : ℝ => x * s3) h6
  ring_nf
  nlinarith [s3_sq, h3, h4, h5, h6, h7]

lemma volumeReal_upperBody4 :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real upperBody4 =
      ((33169 - 19150 * s3) / 40) * unitBallVolumeReal 3 := by
  have h := volumeReal_rotationalProfile_Ioo 2
    (a := a) (b := (1 : ℝ)) (g := upperProfile4)
    (by
      have hs : s3 < 2 := by nlinarith [s3_sq, s3_pos]
      dsimp [a]
      linarith)
    continuous_upperProfile4 (by intro t ht; exact upperProfile4_nonneg ht.1 ht.2)
  simpa [upperBody4, upperProfile4_integral] using h

lemma volumeReal_standardBody4 :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real standardBody4 =
      ((265352 - 153195 * s3) / 320) * unitBallVolumeReal 3 := by
  rw [standardBody4, volumeReal_union_of_subsets_ball
    lowerBicone_two_disjoint_upperBody4 measurableSet_upperBody4
    (fun y hy => (lowerBicone_subset 2 hy).2)
    (fun y hy => (upperBody4_subset hy).2),
    volumeReal_lowerBicone, volumeReal_upperBody4]
  ring

lemma sqrt3_lt_1351_div_780 : s3 < (1351 : ℝ) / 780 := by
  have hs0 : 0 ≤ s3 := Real.sqrt_nonneg _
  have hq0 : 0 ≤ (1351 : ℝ) / 780 := by norm_num
  apply (sq_lt_sq₀ hs0 hq0).1
  rw [s3_sq]
  norm_num

lemma standardBody4_profile_gt :
    (33 : ℝ) / 1036 < (265352 - 153195 * s3) / 320 := by
  nlinarith [sqrt3_lt_1351_div_780]

lemma code_card_le_thirtysix_dim_four
    (X : Finset (EuclideanSpace ℝ (Fin 4)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    X.card ≤ 36 := by
  let T : ℝ := (265352 - 153195 * s3) / 320
  let q : ℝ := T * unitBallVolumeReal 3
  have hpack := card_mul_volumeReal_le_unitBall X
    (centeredBody 2 standardBody4)
    (fun x hx => measurableSet_centeredBody measurableSet_standardBody4 x)
    (fun x hx => centeredBody_subset_unitBall standardBody4_subset (hunit x hx))
    (fun x hx z hz hne => centeredBody_disjoint standardBody4_subset
      (hunit x hx) (hunit z hz) (hsep x hx z hz hne))
    (q := q)
    (fun x hx => by
      rw [volumeReal_centeredBody measurableSet_standardBody4, volumeReal_standardBody4])
  change (X.card : ℝ) * q ≤ unitBallVolumeReal 4 at hpack
  rw [unitBallVolumeReal_four] at hpack
  have hT : (33 : ℝ) / 1036 < T := by simpa [T] using standardBody4_profile_gt
  have hpi : Real.pi < (22 : ℝ) / 7 := pi_lt_22_div_7
  have hTpi : 3 * Real.pi / 296 < T := by nlinarith
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hqbig : Real.pi ^ 2 / 74 < q := by
    dsimp [q]
    rw [unitBallVolumeReal_three]
    have hmul := mul_lt_mul_of_pos_right hTpi (by positivity : 0 < 4 * Real.pi / 3)
    nlinarith
  have hqpos : 0 < q := lt_trans (by positivity) hqbig
  have hcardR : (X.card : ℝ) < 37 := by
    by_contra hnot
    have hc : (37 : ℝ) ≤ X.card := le_of_not_gt hnot
    have hlower : 37 * q ≤ (X.card : ℝ) * q := mul_le_mul_of_nonneg_right hc hqpos.le
    nlinarith
  have hcN : X.card < 37 := by exact_mod_cast hcardR
  omega

lemma code_card_le_sqrt6_fourth
    (X : Finset (EuclideanSpace ℝ (Fin 4)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ 4 := by
  have hc : (X.card : ℝ) ≤ 36 := by exact_mod_cast code_card_le_thirtysix_dim_four X hunit hsep
  have hs : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  calc
    (X.card : ℝ) ≤ 36 := hc
    _ = (Real.sqrt 6) ^ 4 := by
      rw [show (Real.sqrt 6) ^ 4 = ((Real.sqrt 6) ^ 2) ^ 2 by ring, hs]
      norm_num

end
end Sqrt6KissingBound
