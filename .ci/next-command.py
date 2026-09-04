from pathlib import Path
import re, textwrap, subprocess

def run(args):
    p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print('\nCOMMAND:', ' '.join(args), 'EXIT:', p.returncode)
    print('\n'.join(line for line in p.stdout.splitlines() if not line.startswith('trace: .>')))
    return p

root = Path('.lake/packages/mathlib/Mathlib')
for sub, pat in [('MeasureTheory/Integral', r'(?:theorem|lemma).*ofReal_integral_eq_lintegral_ofReal'), ('Data/Finset',r'(?:theorem|lemma).*card_insert_le'), ('Analysis/SpecialFunctions/Trigonometric',r'(?:theorem|lemma).*oncaveOn.*sin')]:
    for p in (root/sub).rglob('*.lean'):
        lines = p.read_text().splitlines()
        for i,line in enumerate(lines):
            if re.search(pat,line):
                print('\n--- MATCH',p,i+1,'---\n'+'\n'.join(lines[max(0,i-3):i+10]))

p=Path('Sqrt6KissingBound/ProfileIntegral.lean')
p.write_text(p.read_text().replace('ENNReal.ofReal_integral_eq_lintegral_ofReal','MeasureTheory.ofReal_integral_eq_lintegral_ofReal'))
p=Path('Sqrt6KissingBound/DimensionOne.lean')
p.write_text(p.read_text().replace('(Finset.card_pair_le _ _)','(by simpa using Finset.card_insert_le (standardAxis 0) ({-standardAxis 0} : Finset (EuclideanSpace ℝ (Fin 1))))'))

workflow = Path('.github/workflows/develop-chord-001.yml').read_text()
body = textwrap.dedent(re.search(r"python3 - <<'PY'\n(.*?)\n\s*PY\n", workflow, re.S).group(1))
exec(compile(body.split("target = Path")[0], '<chord templates>', 'exec'))
names=[]
for p in (root/'Analysis/SpecialFunctions/Trigonometric').rglob('*.lean'):
    names += re.findall(r'(?:theorem|lemma)\s+([A-Za-z0-9_]*oncaveOn[A-Za-z0-9_]*sin[A-Za-z0-9_]*)',p.read_text())
print('SINE CONCAVITY DECLARATIONS:',names)
target=Path('Sqrt6KissingBound/AnalysisChord.lean')
success=False
for name in dict.fromkeys(names):
    for i, candidate in enumerate(bodies,1):
        target.write_text(header + candidate.replace('Real.strictConcaveOn_sin_Icc','Real.'+name) + tail)
        p = run(['lake','env','lean',str(target)])
        if p.returncode == 0:
            print('SELECTED CONCAVITY PROOF:',name,i)
            success=True
            break
    if success:
        break
if not success:
    print('NO CONCAVITY CANDIDATE COMPILED')

p=run(['lake','build','Sqrt6KissingBound.ProfileIntegralReal','Sqrt6KissingBound.DimensionOne','Sqrt6KissingBound.AnalysisEstimate','Sqrt6KissingBound.CenteredBody','Sqrt6KissingBound.BallVolumes','Sqrt6KissingBound.BiconeBounds','Sqrt6KissingBound.DimensionFour'])
Path('session-artifacts/build-003.log').write_text(p.stdout)
for name in sorted(set(re.findall(r'error: (Sqrt6KissingBound/[^:\n]+\.lean):',p.stdout))):
    if Path(name).exists():
        print('\n--- FAILED SOURCE:',name,'---')
        print(''.join(f'{i:4d} {line}\n' for i,line in enumerate(Path(name).read_text().splitlines(),1)))
