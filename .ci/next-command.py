from pathlib import Path
import re, textwrap, subprocess
workflow = Path('.github/workflows/full-certificate-diagnostics.yml').read_text()
body = re.search(r"python3 - <<'PY'\n(.*?)\n\s*PY\n", workflow, re.S).group(1)
body = textwrap.dedent(body)
exec(body.split("print('DEVELOPMENT ONLY:")[0])
p = Path('Sqrt6KissingBound/ProfileIntegral.lean')
s = p.read_text()
s = re.sub(r'  rw \[MeasureTheory.lintegral_mul_const.*\]\n', '''  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (g t) ^ (d + 1)) := by
    fun_prop
  rw [MeasureTheory.lintegral_mul_const (μ := volume.restrict (Set.Ioo a b))
    (unitBallVolume (d + 1)) hm]
''', s)
p.write_text(s)
Path('Sqrt6KissingBound/DimensionOne.lean').write_text('''import Sqrt6KissingBound.StandardGeometry

namespace Sqrt6KissingBound
noncomputable section

lemma unit_vector_dim_one_eq_axis_or_neg
    (x : EuclideanSpace ℝ (Fin 1)) (hx : ‖x‖ = 1) :
    x = standardAxis 0 ∨ x = -standardAxis 0 := by
  have hs : (x 0) ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hx
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] using h
  have hf : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hcoord : x 0 = 1 := by linarith
    ext i
    fin_cases i
    simpa [standardAxis, standardCoordinates] using hcoord
  · right
    have hcoord : x 0 = -1 := by linarith
    ext i
    fin_cases i
    simpa [standardAxis, standardCoordinates] using hcoord

lemma code_card_le_two_dim_one
    (X : Finset (EuclideanSpace ℝ (Fin 1)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1) : X.card ≤ 2 := by
  classical
  have hsub : X ⊆ ({standardAxis 0, -standardAxis 0} :
      Finset (EuclideanSpace ℝ (Fin 1))) := by
    intro x hx
    rcases unit_vector_dim_one_eq_axis_or_neg x (hunit x hx) with h | h
    · simp [h]
    · simp [h]
  exact (Finset.card_le_card hsub).trans (Finset.card_pair_le _ _)

lemma code_card_le_sqrt6_dim_one
    (X : Finset (EuclideanSpace ℝ (Fin 1)))
    (hunit : ∀ x ∈ X, ‖x‖ = 1) :
    (X.card : ℝ) ≤ Real.sqrt 6 := by
  have hc : (X.card : ℝ) ≤ 2 := by
    exact_mod_cast code_card_le_two_dim_one X hunit
  have hs0 := Real.sqrt_nonneg (6 : ℝ)
  have hs2 : (Real.sqrt 6) ^ 2 = 6 := by norm_num
  nlinarith

end
end Sqrt6KissingBound
''')
proc = subprocess.run(['lake','build','Sqrt6KissingBound.ProfileIntegralReal','Sqrt6KissingBound.DimensionOne','Sqrt6KissingBound.BiconeGeometry'], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(proc.stdout)
print('BUILD_EXIT_STATUS',proc.returncode)
for name in ['Sqrt6KissingBound/StandardGeometry.lean', '.github/workflows/develop-dimension-three-001.yml', '.github/workflows/develop-dimension-four-001.yml']:
    print('\n--- SOURCE',name,'---\n',Path(name).read_text())
Path('DevProbe.lean').write_text('''import Mathlib
#check MeasureTheory.lintegral_mul_const
#check Measurable.pow
#check Measurable.pow_const
#check Finset.card_pair_le
#check EuclideanSpace.real_norm_sq_eq
#check WithLp.ofLp_injective
#check WithLp.ext
''')
p = subprocess.run(['lake','env','lean','DevProbe.lean'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print('\n--- API PROBE ---\n',p.stdout)
