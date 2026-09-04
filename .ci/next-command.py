from pathlib import Path
import re, subprocess

def run(args):
    p=subprocess.run(args,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print('\nCOMMAND:',' '.join(args),'EXIT:',p.returncode)
    skip=False
    for line in p.stdout.splitlines():
        if line.startswith('trace: .>'): continue
        if line.startswith('warning:'):
            skip=True
        if line.startswith(('error:','info:','✔','✖','⚠','Some required','Build completed')):
            skip=False
        if not skip: print(line)
    return p

def replace_span(s,start,end,replacement):
    i=s.index(start); j=s.index(end,i)
    return s[:i]+replacement+s[j:]

p=Path('Sqrt6KissingBound/AnalysisEstimate.lean')
s=p.read_text()
s=replace_span(s,'lemma chord_integral (m','lemma pi_div_six', '''lemma chord_integral (m : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi / 6, (3 * t / Real.pi) ^ m) =
      Real.pi / (6 * (m + 1) * 2 ^ m) := by
  have hbase : (Real.pi / 6) / (Real.pi / 3) = (1 : ℝ) / 2 := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  have halg (u v w : ℝ) : u ^ (m + 1) / (v ^ m * w) =
      (u / v) ^ m * u / w := by
    simp only [div_pow, pow_succ, div_eq_mul_inv, mul_inv_rev]
    ring
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
    _ = ((Real.pi / 6) / (Real.pi / 3)) ^ m * (Real.pi / 6) / (m + 1) :=
      halg (Real.pi / 6) (Real.pi / 3) (m + 1)
    _ = Real.pi / (6 * (m + 1) * 2 ^ m) := by
      rw [hbase]
      simp only [div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
      ring

''')
s=s.replace(':= by ring\n',':= by\n      simp only [div_eq_mul_inv, mul_inv_rev]\n      ring\n')
p.write_text(s)

p=Path('Sqrt6KissingBound/BiconeVolume.lean')
s=p.read_text()
s=replace_span(s,'private lemma upper_power_value','lemma lower_profile_integral', '''private lemma two_power_step (k : ℕ) :
    (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 1) * 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]

private lemma upper_power_value (k : ℕ) :
    upperSlope ^ (k + 1) * (1 - a) ^ (k + 2) / (k + 2) =
      (2 - s3) / ((k + 2) * 2 ^ (k + 2)) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  calc
    upperSlope ^ (k + 1) * ((1 - a) ^ (k + 1) * (1 - a)) / (k + 2) =
        (upperSlope * (1 - a)) ^ (k + 1) * (1 - a) / (k + 2) := by
      rw [mul_pow]
      ring
    _ = ((1 : ℝ) / 2) ^ (k + 1) * (1 - a) / (k + 2) := by rw [upper_product]
    _ = (2 - s3) / ((k + 2) * 2 ^ (k + 2)) := by
      dsimp [a]
      simp only [two_power_step, div_pow, one_pow, div_eq_mul_inv, mul_inv_rev]
      ring

''')
s=s.replace('  exact lower_power_value k','  simpa [Nat.cast_add, add_assoc] using lower_power_value k')
s=s.replace('  exact upper_power_value k','  simpa [Nat.cast_add, add_assoc] using upper_power_value k')
s=s.replace('  rw [lower_profile_integral, upper_profile_integral]\n  ring','  rw [lower_profile_integral, upper_profile_integral]\n  simp only [two_power_step, div_eq_mul_inv, mul_inv_rev]\n  ring')
s=s.replace('    (by positivity)\n    (continuous_const.mul', '''    (by
      have hs : s3 < 2 := by nlinarith [s3_sq, s3_pos]
      dsimp [a]
      linarith)
    (continuous_const.mul''')
s=s.replace('  rw [volumeReal_lowerBicone, volumeReal_upperBicone]\n  ring','  rw [volumeReal_lowerBicone, volumeReal_upperBicone]\n  simp only [two_power_step, div_eq_mul_inv, mul_inv_rev]\n  ring')
p.write_text(s)

for pp in Path('.lake/packages/mathlib/Mathlib').rglob('*.lean'):
    text=pp.read_text()
    if 'theorem pi_lt_d4' in text or 'lemma pi_lt_d4' in text:
        print('PI DECIMAL SOURCE',pp)
        ls=text.splitlines()
        for i,line in enumerate(ls):
            if re.search(r'(theorem|lemma) pi_lt_d',line): print('\n'.join(ls[i:i+3]))

p=Path('Sqrt6KissingBound/BallVolumes.lean')
s=p.read_text()
anchor='/-- Gamma-function formula'
s=s.replace(anchor,'''lemma pi_lt_22_div_7 : Real.pi < (22 : ℝ) / 7 := by
  have h := Real.pi_lt_d4
  norm_num at h
  linarith

'''+anchor)
s=s.replace('  field_simp [hG]\n  ring','  field_simp [hG]\n  push_cast\n  ring')
s=s.replace('EuclideanSpace.volume_ball_fin_three]\n  simp [Real.pi_pos.le]\n  ring','EuclideanSpace.volume_ball_fin_three]\n  simp [Real.pi_pos.le]\n  rw [ENNReal.toReal_ofReal (by positivity)]')
s=s.replace('Real.pi_lt_22_div_7','pi_lt_22_div_7')
s=s.replace('  nlinarith [sq_pos_of_pos hpipos]','  have hmul := mul_lt_mul_of_pos_right hpi (sq_pos_of_pos hpipos)\n  nlinarith')
s=replace_span(s,'private lemma volume_descent_step','/-- Unit-ball volume is', '''private lemma volume_descent_step {n : ℕ} (hn : 8 ≤ n)
    (hprev : unitBallVolumeReal (n - 2) ≤ unitBallVolumeReal (n - 3)) :
    unitBallVolumeReal n ≤ unitBallVolumeReal (n - 1) := by
  have hcast : ((n - 3 : ℕ) : ℝ) + 3 = (n : ℝ) := by
    exact_mod_cast (show n - 3 + 3 = n by omega)
  have hcast' : ((n - 4 : ℕ) : ℝ) + 3 = ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n - 4 + 3 = n - 1 by omega)
  have hvn : unitBallVolumeReal n =
      (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 2) := by
    simpa only [show n - 3 + 3 = n by omega,
      show n - 3 + 1 = n - 2 by omega, hcast]
      using unitBallVolumeReal_add_two (n - 3)
  have hvn1 : unitBallVolumeReal (n - 1) =
      (2 * Real.pi / ((n - 1 : ℕ) : ℝ)) * unitBallVolumeReal (n - 3) := by
    simpa only [show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 1 = n - 3 by omega, hcast']
      using unitBallVolumeReal_add_two (n - 4)
  rw [hvn, hvn1]
  have hn1pos : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hcoef : 2 * Real.pi / (n : ℝ) ≤ 2 * Real.pi / (n - 1 : ℕ) := by
    exact div_le_div_of_nonneg_left (by positivity) hn1pos
      (by exact_mod_cast Nat.sub_le n 1)
  have hV : 0 ≤ unitBallVolumeReal (n - 3) := measureReal_nonneg
  calc
    (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 2) ≤
        (2 * Real.pi / (n : ℝ)) * unitBallVolumeReal (n - 3) :=
      mul_le_mul_of_nonneg_left hprev (by positivity)
    _ ≤ (2 * Real.pi / (n - 1 : ℕ)) * unitBallVolumeReal (n - 3) :=
      mul_le_mul_of_nonneg_right hcoef hV

''')
p.write_text(s)
for name in ['BiconeBounds','DimensionFour']:
    p=Path('Sqrt6KissingBound')/(name+'.lean')
    p.write_text(p.read_text().replace('Real.pi_lt_22_div_7','pi_lt_22_div_7'))

p=run(['lake','build','Sqrt6KissingBound.AnalysisEstimate','Sqrt6KissingBound.BiconeVolume','Sqrt6KissingBound.BallVolumes','Sqrt6KissingBound.CenteredBody','Sqrt6KissingBound.BiconeBounds','Sqrt6KissingBound.DimensionThree','Sqrt6KissingBound.DimensionFour'])
Path('session-artifacts/build-006.log').write_text(p.stdout)
for name in sorted(set(re.findall(r'error: (Sqrt6KissingBound/[^:\n]+\.lean):',p.stdout))):
    if Path(name).exists():
        lines=Path(name).read_text().splitlines()
        nums=sorted(set(int(n) for n in re.findall(r'error: '+re.escape(name)+r':(\d+):',p.stdout)))
        for n in nums[:8]:
            print('\n--- CONTEXT',name,n,'---')
            print('\n'.join(f'{i+1:4d} {lines[i]}' for i in range(max(0,n-5),min(len(lines),n+7))))
