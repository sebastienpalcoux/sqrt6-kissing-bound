from pathlib import Path
import re, textwrap, subprocess

def run(args):
    p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print('\nCOMMAND:', ' '.join(args), 'EXIT:', p.returncode)
    print('\n'.join(line for line in p.stdout.splitlines() if not line.startswith('trace: .>')))
    return p
p=Path('Sqrt6KissingBound/ProfileIntegral.lean')
p.write_text(p.read_text().replace('(hg.pow (d + 1)).intervalIntegrable.1','((hg.pow (d + 1)).intervalIntegrable a b).1'))
p=Path('Sqrt6KissingBound/AnalysisEstimate.lean')
p.write_text(p.read_text().replace(').intervalIntegrable\n',').intervalIntegrable _ _\n'))
root=Path('.lake/packages/mathlib/Mathlib')
names=[]
for p in root.rglob('*.lean'):
    s=p.read_text()
    if 'sin' not in s or ('Concave' not in s and 'concave' not in s):
        continue
    lines=s.splitlines()
    for i,line in enumerate(lines):
        if re.search(r'(concav\w*.*sin|sin.*concav)',line,re.I):
            print('\n--- GLOBAL SINE MATCH',p,i+1,'---\n'+'\n'.join(lines[max(0,i-2):i+9]))
            names+=re.findall(r'(?:theorem|lemma)\s+([A-Za-z0-9_]+)',line)
print('GLOBAL CONCAVITY NAMES',names)
if names:
    workflow=Path('.github/workflows/develop-chord-001.yml').read_text()
    body=textwrap.dedent(re.search(r"python3 - <<'PY'\n(.*?)\n\s*PY\n",workflow,re.S).group(1))
    exec(compile(body.split('target = Path')[0],'<chord templates>','exec'))
    success=False
    for name in dict.fromkeys(names):
        for i,candidate in enumerate(bodies,1):
            target=Path('Sqrt6KissingBound/AnalysisChord.lean')
            target.write_text(header+candidate.replace('Real.strictConcaveOn_sin_Icc','Real.'+name)+tail)
            p=run(['lake','env','lean',str(target)])
            if p.returncode==0:
                print('SELECTED CHORD PROOF',name,i)
                success=True
                break
        if success: break
Path('DevProbe.lean').write_text('''import Mathlib
#check MeasureTheory.measureReal_union
#check MeasureTheory.measure_union
#check ENNReal.toReal_add
#check intervalIntegral.integral_sub
#check intervalIntegral.integral_const
#check integral_pow
#check Set.uIcc_of_le
#check MeasureTheory.measureReal_nonneg
#check Real.Gamma_add_one
#check Continuous.intervalIntegrable
''')
run(['lake','env','lean','DevProbe.lean'])
p=run(['lake','build','Sqrt6KissingBound.ProfileIntegralReal','Sqrt6KissingBound.BiconeVolume','Sqrt6KissingBound.BallVolumes','Sqrt6KissingBound.AnalysisEstimate'])
Path('session-artifacts/build-004.log').write_text(p.stdout)
for name in sorted(set(re.findall(r'error: (Sqrt6KissingBound/[^:\n]+\.lean):',p.stdout))):
    if Path(name).exists():
        print('\n--- FAILED SOURCE',name,'---\n'+''.join(f'{i:4d} {line}\n' for i,line in enumerate(Path(name).read_text().splitlines(),1)))
