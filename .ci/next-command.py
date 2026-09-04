from pathlib import Path
import re, textwrap, subprocess
previous = Path('session-artifacts/result-001.txt')
if previous.exists():
    s = previous.read_text()
    print('--- PREVIOUS COMPILER RESULT ---\n' + s.split('--- SOURCE')[0])
    if '--- API PROBE ---' in s:
        print(s[s.index('--- API PROBE ---'):])
def run(args):
    p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print('\nCOMMAND:', ' '.join(args), 'EXIT:', p.returncode)
    print('\n'.join(line for line in p.stdout.splitlines() if not line.startswith('trace: .>')))
    return p
run(['lake','build','Sqrt6KissingBound.Analysis','Sqrt6KissingBound.LinearProfileIntegral'])
workflow = Path('.github/workflows/develop-chord-001.yml').read_text()
body = textwrap.dedent(re.search(r"python3 - <<'PY'\n(.*?)\n\s*PY\n", workflow, re.S).group(1))
try:
    exec(compile(body, '<chord candidate generation>', 'exec'))
except SystemExit as e:
    print('CHORD GENERATOR EXIT:',e)
print(Path('.ci/chord-candidates.log').read_text())
run(['lake','build','Sqrt6KissingBound.AnalysisChord'])
Path('Sqrt6KissingBound/AnalysisEstimate.lean').write_text('''import Sqrt6KissingBound.AnalysisChord
import Sqrt6KissingBound.LinearProfileIntegral

namespace Sqrt6KissingBound
noncomputable section
open Set intervalIntegral
open scoped Interval Real

lemma chord_integral_le_capNumerator (m : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) ≤ capNumerator m := by
  rw [capNumerator]
  apply intervalIntegral.integral_mono_on (by positivity)
  · exact (by fun_prop : Continuous (fun t : ℝ => (3 * t / Real.pi) ^ m)).intervalIntegrable
  · exact (by fun_prop : Continuous (fun t : ℝ => Real.sin t ^ m)).intervalIntegrable
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    exact pow_le_pow_left₀ (by positivity) (three_mul_div_pi_le_sin ht.1 ht.2) m

lemma chord_integral (m : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) =
      Real.pi / (6 * (m + 1) * 2 ^ m) := by
  have hbase : (Real.pi / 6) / (Real.pi / 3) = (1 : ℝ) / 2 := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  calc
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) =
        ∫ t in (0 : ℝ)..Real.pi / 6, (t / (Real.pi / 3)) ^ m := by
      apply intervalIntegral.integral_congr
      intro t ht
      congr 1
      field_simp [Real.pi_ne_zero]
      <;> ring
    _ = (Real.pi / 6) ^ (m + 1) / ((Real.pi / 3) ^ m * (m + 1)) :=
      integral_div_mul_pow m (by positivity)
    _ = ((Real.pi / 6) / (Real.pi / 3)) ^ m * (Real.pi / 6) / (m + 1) := by
      rw [div_pow, pow_succ]
      ring
    _ = Real.pi / (6 * (m + 1) * 2 ^ m) := by
      rw [hbase, div_pow]
      simp only [one_pow]
      ring

lemma pi_div_six_gt_three_sqrt3_div_ten :
    3 * Real.sqrt 3 / 10 < Real.pi / 6 := by
  have hpi := Real.pi_gt_d2
  have hs3 := sqrt3_lt_26_div_15
  norm_num at hpi
  nlinarith

lemma capNumerator_lower (m : ℕ) :
    3 * Real.sqrt 3 / (10 * (m + 1) * 2 ^ m) < capNumerator m := by
  have hD : 0 < (m + 1 : ℝ) * 2 ^ m := by positivity
  calc
    3 * Real.sqrt 3 / (10 * (m + 1) * 2 ^ m) =
        (3 * Real.sqrt 3 / 10) / ((m + 1 : ℝ) * 2 ^ m) := by ring
    _ < (Real.pi / 6) / ((m + 1 : ℝ) * 2 ^ m) :=
      div_lt_div_of_pos_right pi_div_six_gt_three_sqrt3_div_ten hD
    _ = Real.pi / (6 * (m + 1) * 2 ^ m) := by ring
    _ = (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) := (chord_integral m).symm
    _ ≤ capNumerator m := chord_integral_le_capNumerator m

end
end Sqrt6KissingBound
''')
p = Path('Sqrt6KissingBound/CapFraction.lean')
p.write_text(p.read_text().replace('import Sqrt6KissingBound.Analysis\n','import Sqrt6KissingBound.AnalysisEstimate\n'))
p = run(['lake','build','Sqrt6KissingBound.CapFraction','Sqrt6KissingBound.CenteredBody','Sqrt6KissingBound.BallVolumes','Sqrt6KissingBound.BiconeBounds','Sqrt6KissingBound.DimensionFour'])
Path('session-artifacts/volume-build-002.log').write_text(p.stdout)
for name in sorted(set(re.findall(r'error: (Sqrt6KissingBound/[^:\n]+\.lean):',p.stdout))):
    print('\n--- FAILED SOURCE:',name,'---')
    print(''.join(f'{i:4d} {line}\n' for i,line in enumerate(Path(name).read_text().splitlines(),1)))
