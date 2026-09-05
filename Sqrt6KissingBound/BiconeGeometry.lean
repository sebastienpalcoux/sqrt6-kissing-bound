import Sqrt6KissingBound.StandardGeometry
import Sqrt6KissingBound.ProfileVolume

namespace Sqrt6KissingBound

noncomputable section

open Set Metric MeasureTheory

private abbrev s3 : ℝ := Real.sqrt 3
private abbrev a : ℝ := s3 / 2
private abbrev upperSlope : ℝ := 2 + s3

private lemma s3_pos : 0 < s3 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3 ^ 2 = 3 := by norm_num [s3]
private lemma upperSlope_pos : 0 < upperSlope := by
  dsimp [upperSlope]
  positivity

private lemma sq_lt_sq_nonneg_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 < y ^ 2 ↔ x < y := by
  constructor
  · intro hsq
    by_contra hnot
    have hyx : y ≤ x := le_of_not_gt hnot
    have hprod : 0 ≤ (x - y) * (x + y) :=
      mul_nonneg (sub_nonneg.mpr hyx) (add_nonneg hx hy)
    nlinarith
  · intro hxy
    have hypos : 0 < y := lt_of_le_of_lt hx hxy
    have hprod : 0 < (y - x) * (y + x) :=
      mul_pos (sub_pos.mpr hxy) (add_pos_of_pos_of_nonneg hypos hx)
    nlinarith

def lowerBicone (k : ℕ) : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  rotationalProfile (k + 1) (Set.Ioo 0 a) (fun t => t / s3)

def upperBicone (k : ℕ) : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  rotationalProfile (k + 1) (Set.Ioo a 1) (fun t => upperSlope * (1 - t))

def standardBicone (k : ℕ) : Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  lowerBicone k ∪ upperBicone k

lemma lower_profile_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ t / s3 := by
  positivity

lemma upper_profile_nonneg {t : ℝ} (ht : t ≤ 1) :
    0 ≤ upperSlope * (1 - t) := by
  positivity

lemma lower_point_mem_cone_ball (k : ℕ) {t : ℝ} {v : Fin (k + 1) → ℝ}
    (ht0 : 0 < t) (hta : t < a)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖ < t / s3) :
    standardCoordinates (k + 1) (t, v) ∈
      strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrs : r * s3 < t := (lt_div_iff₀ s3_pos).mp (by simpa [r] using hv)
  have hrs0 : 0 ≤ r * s3 := mul_nonneg hr0 s3_pos.le
  have hrsq : (r * s3) ^ 2 < t ^ 2 :=
    (sq_lt_sq_nonneg_iff hrs0 ht0.le).2 hrs
  have hr_sq : 3 * r ^ 2 < t ^ 2 := by
    nlinarith [s3_sq]
  have ht_sq : t ^ 2 < (3 : ℝ) / 4 := by
    have ha0 : 0 ≤ a := by positivity
    have hsq := (sq_lt_sq_nonneg_iff ht0.le ha0).2 hta
    dsimp [a] at hsq
    nlinarith [s3_sq]
  constructor
  · rw [standardCoordinates_mem_strictCone_iff]
    have hq : 0 ≤ t ^ 2 + r ^ 2 := by positivity
    have hleft : 0 ≤ (s3 / 2) * Real.sqrt (t ^ 2 + r ^ 2) := by positivity
    apply (sq_lt_sq_nonneg_iff hleft ht0.le).1
    rw [mul_pow, Real.sq_sqrt hq]
    nlinarith [s3_sq]
  · rw [standardCoordinates_mem_ball_iff]
    nlinarith

lemma upper_point_mem_cone_ball (k : ℕ) {t : ℝ} {v : Fin (k + 1) → ℝ}
    (hta : a < t) (ht1 : t < 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖ <
      upperSlope * (1 - t)) :
    standardCoordinates (k + 1) (t, v) ∈
      strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin (k + 1)))‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have ht0 : 0 < t := lt_trans (by positivity : 0 < a) hta
  have hprof0 : 0 < upperSlope * (1 - t) := by positivity
  have hrprof : r < upperSlope * (1 - t) := by simpa [r] using hv
  have hconeLinear : s3 * (upperSlope * (1 - t)) < t := by
    dsimp [a, upperSlope] at hta ⊢
    nlinarith [s3_sq]
  have hrs : r * s3 < t := by
    have hmul := mul_lt_mul_of_pos_right hrprof s3_pos
    nlinarith
  have hrs0 : 0 ≤ r * s3 := mul_nonneg hr0 s3_pos.le
  have hrsq : (r * s3) ^ 2 < t ^ 2 :=
    (sq_lt_sq_nonneg_iff hrs0 (by positivity : 0 ≤ t)).2 hrs
  have hr_sq : 3 * r ^ 2 < t ^ 2 := by
    nlinarith [s3_sq]
  have hballLinear : upperSlope ^ 2 * (1 - t) < 1 + t := by
    dsimp [a, upperSlope] at hta ⊢
    nlinarith [s3_sq]
  have hprof_sq : (upperSlope * (1 - t)) ^ 2 < 1 - t ^ 2 := by
    have h1t : 0 < 1 - t := by linarith
    have hmul := mul_lt_mul_of_pos_right hballLinear h1t
    nlinarith
  have hr_sq_ball : r ^ 2 < 1 - t ^ 2 := by
    have hprof_nonneg : 0 ≤ upperSlope * (1 - t) := hprof0.le
    have hsq := (sq_lt_sq_nonneg_iff hr0 hprof_nonneg).2 hrprof
    nlinarith
  constructor
  · rw [standardCoordinates_mem_strictCone_iff]
    have hq : 0 ≤ t ^ 2 + r ^ 2 := by positivity
    have hleft : 0 ≤ (s3 / 2) * Real.sqrt (t ^ 2 + r ^ 2) := by positivity
    apply (sq_lt_sq_nonneg_iff hleft (by positivity : 0 ≤ t)).1
    rw [mul_pow, Real.sq_sqrt hq]
    nlinarith [s3_sq]
  · rw [standardCoordinates_mem_ball_iff]
    nlinarith

lemma lowerBicone_subset (k : ℕ) :
    lowerBicone k ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  intro y hy
  change (standardCoordinates (k + 1)).symm y ∈
    profileRegion (k + 1) (Set.Ioo 0 a) (fun t => t / s3) at hy
  let p := (standardCoordinates (k + 1)).symm y
  change p ∈ profileRegion (k + 1) (Set.Ioo 0 a) (fun t => t / s3) at hy
  rcases hy with ⟨ht, hv⟩
  have hpoint := lower_point_mem_cone_ball k ht.1 ht.2 hv
  simpa [p] using hpoint

lemma upperBicone_subset (k : ℕ) :
    upperBicone k ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  intro y hy
  change (standardCoordinates (k + 1)).symm y ∈
    profileRegion (k + 1) (Set.Ioo a 1)
      (fun t => upperSlope * (1 - t)) at hy
  let p := (standardCoordinates (k + 1)).symm y
  change p ∈ profileRegion (k + 1) (Set.Ioo a 1)
    (fun t => upperSlope * (1 - t)) at hy
  rcases hy with ⟨ht, hv⟩
  have hpoint := upper_point_mem_cone_ball k ht.1 ht.2 hv
  simpa [p] using hpoint

lemma standardBicone_subset (k : ℕ) :
    standardBicone k ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  exact union_subset (lowerBicone_subset k) (upperBicone_subset k)

lemma lowerBicone_disjoint_upperBicone (k : ℕ) :
    Disjoint (lowerBicone k) (upperBicone k) := by
  rw [Set.disjoint_left]
  intro y hyl hyu
  change (standardCoordinates (k + 1)).symm y ∈
    profileRegion (k + 1) (Set.Ioo 0 a) (fun t => t / s3) at hyl
  change (standardCoordinates (k + 1)).symm y ∈
    profileRegion (k + 1) (Set.Ioo a 1)
      (fun t => upperSlope * (1 - t)) at hyu
  rcases hyl with ⟨hl, -⟩
  rcases hyu with ⟨hu, -⟩
  exact lt_asymm hl.2 hu.1

end

end Sqrt6KissingBound
