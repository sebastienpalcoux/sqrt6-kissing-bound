from pathlib import Path
import re,textwrap,subprocess

def run(args):
    p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print('\nCOMMAND:',' '.join(args),'EXIT:',p.returncode)
    print('\n'.join(x for x in p.stdout.splitlines() if not x.startswith('trace: .>')))
    return p

p=Path('Sqrt6KissingBound/ProfileIntegral.lean')
s=p.read_text()
s=s[:s.index('  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal')]+'''  have hI : Integrable (fun t : ℝ => g t ^ (d + 1))
      (volume.restrict (Set.Ioc a b)) := by
    exact ((hg.pow (d + 1)).intervalIntegrable (μ := volume) a b).1
  have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), 0 ≤ g t ^ (d + 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg (hg0 t ⟨ht.1.le, ht.2⟩) _
  rw [intervalIntegral.integral_of_le hab]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI hnn).symm

end
end Sqrt6KissingBound
'''
p.write_text(s)
workflow=Path('.github/workflows/develop-chord-001.yml').read_text()
body=textwrap.dedent(re.search(r"python3 - <<'PY'\n(.*?)\n\s*PY\n",workflow,re.S).group(1))
exec(compile(body.split('target = Path')[0],'<chord templates>','exec'))
Path('Sqrt6KissingBound/AnalysisChord.lean').write_text(header+bodies[0].replace('Real.strictConcaveOn_sin_Icc','strictConcaveOn_sin_Icc')+tail)

Path('Sqrt6KissingBound/BodyVolumeAdditivity.lean').write_text('''import Sqrt6KissingBound.VolumePacking

namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

lemma volumeReal_union_of_subsets_ball {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))}
    (hd : Disjoint S T) (hT : MeasurableSet T)
    (hSball : S ⊆ ball 0 1) (hTball : T ⊆ ball 0 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (S ∪ T) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real S +
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real T := by
  exact measureReal_union hd hT
    (lt_of_le_of_lt (measure_mono hSball) measure_ball_lt_top).ne
    (lt_of_le_of_lt (measure_mono hTball) measure_ball_lt_top).ne

end
end Sqrt6KissingBound
''')
p=Path('Sqrt6KissingBound/BiconeVolume.lean')
s=p.read_text().replace('import Sqrt6KissingBound.BiconeGeometry','import Sqrt6KissingBound.BodyVolumeAdditivity\nimport Sqrt6KissingBound.BiconeGeometry')
s=s.replace('measureReal_union\n    (measurableSet_lowerBicone k) (lowerBicone_disjoint_upperBicone k)', '''volumeReal_union_of_subsets_ball
    (lowerBicone_disjoint_upperBicone k) (measurableSet_upperBicone k)
    (fun y hy => (lowerBicone_subset k hy).2)
    (fun y hy => (upperBicone_subset k hy).2)''')
p.write_text(s)

Path('Sqrt6KissingBound/DimensionThree.lean').write_text('''import Sqrt6KissingBound.CenteredBody
import Sqrt6KissingBound.BallVolumes

/-! The three-dimensional bound from an exactly integrated spherical-cap sector. -/
namespace Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real

private abbrev s3 : ℝ := Real.sqrt 3
private abbrev a : ℝ := s3 / 2
private lemma s3_pos : 0 < s3 := Real.sqrt_pos.2 (by norm_num)
private lemma s3_sq : s3 ^ 2 = 3 := by norm_num [s3]
private lemma a_nonneg : 0 ≤ a := by positivity
private lemma a_le_one : a ≤ 1 := by
  dsimp [a]
  nlinarith [s3_sq, s3_pos]

def upperProfile3 (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)
def upperBody3 : Set (EuclideanSpace ℝ (Fin 3)) :=
  rotationalProfile 2 (Set.Ioo a 1) upperProfile3
def standardBody3 : Set (EuclideanSpace ℝ (Fin 3)) :=
  lowerBicone 1 ∪ upperBody3

lemma continuous_upperProfile3 : Continuous upperProfile3 := by
  unfold upperProfile3
  fun_prop
lemma upperProfile3_nonneg (t : ℝ) : 0 ≤ upperProfile3 t := Real.sqrt_nonneg _
lemma upperProfile3_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    upperProfile3 t ^ 2 = 1 - t ^ 2 := by
  exact Real.sq_sqrt (by nlinarith)

lemma measurableSet_upperBody3 : MeasurableSet upperBody3 :=
  measurableSet_rotationalProfile 2 measurableSet_Ioo continuous_upperProfile3.measurable
lemma measurableSet_standardBody3 : MeasurableSet standardBody3 :=
  (measurableSet_lowerBicone 1).union measurableSet_upperBody3

private lemma upperBody3_point_mem {t : ℝ} {v : Fin 2 → ℝ}
    (hta : a < t) (ht1 : t < 1)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖ < upperProfile3 t) :
    standardCoordinates 2 (t, v) ∈ strictCone (standardAxis 2) ∩ ball 0 1 := by
  let r : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have ht0 : 0 < t := lt_of_le_of_lt a_nonneg hta
  have hrsq : r ^ 2 < upperProfile3 t ^ 2 :=
    (sq_lt_sq₀ hr0 (upperProfile3_nonneg t)).2 (by simpa [r] using hv)
  have hrball : r ^ 2 < 1 - t ^ 2 := by
    rwa [upperProfile3_sq ht0.le ht1.le] at hrsq
  have ht_sq_gt : (3 : ℝ) / 4 < t ^ 2 := by
    have hsq := (sq_lt_sq₀ a_nonneg ht0.le).2 hta
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

lemma upperBody3_subset : upperBody3 ⊆ strictCone (standardAxis 2) ∩ ball 0 1 := by
  intro y hy
  let p := (standardCoordinates 2).symm y
  have hp : p ∈ profileRegion 2 (Set.Ioo a 1) upperProfile3 := hy
  rcases hp with ⟨ht, hv⟩
  have hpoint := upperBody3_point_mem ht.1 ht.2 hv
  simpa [p] using hpoint
lemma standardBody3_subset : standardBody3 ⊆ strictCone (standardAxis 2) ∩ ball 0 1 :=
  union_subset (lowerBicone_subset 1) upperBody3_subset
lemma lowerBicone_one_disjoint_upperBody3 : Disjoint (lowerBicone 1) upperBody3 := by
  rw [Set.disjoint_left]
  intro y hyl hyu
  have hl : ((standardCoordinates 2).symm y).1 ∈ Set.Ioo 0 a := hyl.1
  have hu : ((standardCoordinates 2).symm y).1 ∈ Set.Ioo a 1 := hyu.1
  exact lt_asymm hl.2 hu.1

lemma upperProfile3_integral :
    (∫ t in a..1, upperProfile3 t ^ 2) = (2 : ℝ) / 3 - 3 * s3 / 8 := by
  calc
    (∫ t in a..1, upperProfile3 t ^ 2) = ∫ t in a..1, (1 - t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc a 1 := by simpa only [Set.uIcc_of_le a_le_one] using ht
      exact upperProfile3_sq (a_nonneg.trans ht'.1) ht'.2
    _ = (2 : ℝ) / 3 - 3 * s3 / 8 := by
      rw [intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable _ _)
        ((continuous_id.pow 2).intervalIntegrable _ _),
        intervalIntegral.integral_const, integral_pow]
      norm_num [a, smul_eq_mul]
      linear_combination (s3 / 24) * s3_sq

lemma volumeReal_upperBody3 :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real upperBody3 =
      ((2 : ℝ) / 3 - 3 * s3 / 8) * unitBallVolumeReal 2 := by
  have h := volumeReal_rotationalProfile_Ioo 1
    (a := a) (b := (1 : ℝ)) (g := upperProfile3) a_le_one
    continuous_upperProfile3 (by intro t ht; exact upperProfile3_nonneg t)
  simpa only [upperBody3, upperProfile3_integral] using h

lemma volumeReal_standardBody3 :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real standardBody3 =
      ((2 - s3) / 3) * unitBallVolumeReal 2 := by
  rw [standardBody3, volumeReal_union_of_subsets_ball
    lowerBicone_one_disjoint_upperBody3 measurableSet_upperBody3
    (fun y hy => (lowerBicone_subset 1 hy).2)
    (fun y hy => (upperBody3_subset hy).2),
    volumeReal_lowerBicone, volumeReal_upperBody3]
  norm_num
  ring

lemma code_card_le_fourteen_dim_three
    (X : Finset (EuclideanSpace ℝ (Fin 3)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    X.card ≤ 14 := by
  let q : ℝ := ((2 - s3) / 3) * unitBallVolumeReal 2
  have hpack := card_mul_volumeReal_le_unitBall X
    (centeredBody 1 standardBody3)
    (fun x hx => measurableSet_centeredBody measurableSet_standardBody3 x)
    (fun x hx => centeredBody_subset_unitBall standardBody3_subset (hunit x hx))
    (fun x hx z hz hne => centeredBody_disjoint standardBody3_subset
      (hunit x hx) (hunit z hz) (hsep x hx z hz hne))
    (q := q)
    (fun x hx => by
      rw [volumeReal_centeredBody measurableSet_standardBody3, volumeReal_standardBody3]
      rfl)
  change (X.card : ℝ) * q ≤ unitBallVolumeReal 3 at hpack
  have hT : (4 : ℝ) / 45 < (2 - s3) / 3 := by
    nlinarith [sqrt3_lt_26_div_15]
  have hqbig : 4 * Real.pi / 45 < q := by
    dsimp [q]
    rw [unitBallVolumeReal_two]
    have h := mul_lt_mul_of_pos_right hT Real.pi_pos
    nlinarith
  have hqpos : 0 < q := lt_trans (by positivity) hqbig
  rw [unitBallVolumeReal_three] at hpack
  have hcR : (X.card : ℝ) < 15 := by
    by_contra hnot
    have hc : (15 : ℝ) ≤ X.card := le_of_not_gt hnot
    have hlower := mul_le_mul_of_nonneg_right hc hqpos.le
    nlinarith
  have hcN : X.card < 15 := by exact_mod_cast hcR
  omega

lemma code_card_le_sqrt6_cube
    (X : Finset (EuclideanSpace ℝ (Fin 3)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1)
    (hsep : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → inner ℝ x z ≤ (1 : ℝ) / 2) :
    (X.card : ℝ) ≤ (Real.sqrt 6) ^ 3 := by
  have hc : (X.card : ℝ) ≤ 14 := by
    exact_mod_cast code_card_le_fourteen_dim_three X hunit hsep
  have hs0 := Real.sqrt_nonneg (6 : ℝ)
  have hs2 : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  have hs : (7 : ℝ) / 3 < Real.sqrt 6 := by nlinarith
  rw [show (Real.sqrt 6) ^ 3 = 6 * Real.sqrt 6 by
    rw [show 3 = 2 + 1 by omega, pow_succ, hs2]]
  nlinarith

end
end Sqrt6KissingBound
''')
p=run(['lake','build','Sqrt6KissingBound.ProfileIntegralReal','Sqrt6KissingBound.AnalysisEstimate','Sqrt6KissingBound.BiconeVolume','Sqrt6KissingBound.BallVolumes','Sqrt6KissingBound.CenteredBody','Sqrt6KissingBound.BiconeBounds','Sqrt6KissingBound.DimensionThree','Sqrt6KissingBound.DimensionFour'])
Path('session-artifacts/build-005.log').write_text(p.stdout)
for name in sorted(set(re.findall(r'error: (Sqrt6KissingBound/[^:\n]+\.lean):',p.stdout))):
    if Path(name).exists():
        print('\n--- FAILED SOURCE',name,'---\n'+''.join(f'{i:4d} {line}\n' for i,line in enumerate(Path(name).read_text().splitlines(),1)))
