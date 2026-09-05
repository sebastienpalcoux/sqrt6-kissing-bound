#!/usr/bin/env python3
"""Export a promotion manifest only after the explicit complete audit passes.

This script performs no network operations and publishes no repository changes.
It reads the checked source files and emits Git tree entries and source hashes.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess


def git(*args: str) -> str:
    return subprocess.run(['git', *args], check=True, text=True,
                          stdout=subprocess.PIPE).stdout.strip()


def main() -> None:
    status = Path('static-diagnostics/status.txt').read_text()
    if 'CANDIDATE_BUILD_EXIT_STATUS=0' not in status or 'FULL_BUILD_AND_AXIOM_AUDIT_PASSED' not in status:
        raise SystemExit('Refusing export: a complete build and axiom audit have not passed.')
    pinned = '0df444a360eaa60ab8c11dca51a86af692955474'
    if git('-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD') != pinned:
        raise SystemExit('Mathlib revision does not match the pinned certificate revision.')
    subprocess.run(['git', '-C', '.lake/packages/mathlib', 'diff', '--exit-code',
                    'HEAD', '--', '*.lean'], check=True)
    tracked = {}
    for line in git('ls-tree', '-r', 'HEAD').splitlines():
        metadata, name = line.split('\t', 1)
        mode, kind, sha = metadata.split()
        if kind == 'blob':
            tracked[name] = (mode, sha)
    known = {sha for _, sha in tracked.values()}
    pending = [Path('Sqrt6KissingBound.lean'), Path('Axioms.lean')]
    closure = set()
    while pending:
        path = pending.pop()
        if path in closure:
            continue
        if not path.is_file():
            raise SystemExit(f'Missing imported project file: {path}')
        closure.add(path)
        for module in re.findall(r'^\s*import\s+(Sqrt6KissingBound(?:\.[A-Za-z0-9_]+)*)',
                                 path.read_text(), re.MULTILINE):
            pending.append(Path(module.replace('.', '/') + '.lean'))
    required = closure | {
        Path('scripts/check.sh'), Path('scripts/check_axioms.py'),
        Path('lakefile.lean'), Path('lake-manifest.json'), Path('lean-toolchain'),
    }
    entries = []
    hashes = []
    for path in sorted(required):
        data = path.read_bytes()
        sha = git('hash-object', str(path))
        digest = hashlib.sha256(data).hexdigest()
        hashes.append(f'{digest}  {path.as_posix()}')
        entry = {'path': path.as_posix(), 'mode': '100644', 'type': 'blob'}
        if sha in known:
            entry['sha'] = sha
        else:
            entry['content'] = data.decode('utf-8')
        entries.append(entry)
    for name, (mode, sha) in sorted(tracked.items()):
        if name.startswith('Sqrt6KissingBound/') and name.endswith('.lean') and Path(name) not in closure:
            entries.append({'path': '.ci/archive/unimported/' + name,
                            'mode': mode, 'type': 'blob', 'sha': sha})
            entries.append({'path': name, 'mode': mode, 'type': 'blob', 'sha': None})
    entries.append({'path': 'SOURCE_SHA256SUMS', 'mode': '100644', 'type': 'blob',
                    'content': '\n'.join(hashes) + '\n'})
    out = Path('verified-export')
    out.mkdir(exist_ok=True)
    manifest = {
        'validated_staging_commit': git('rev-parse', 'HEAD'),
        'mathlib_commit': pinned,
        'lean_toolchain': Path('lean-toolchain').read_text().strip(),
        'proof_file_count': len(closure),
        'proof_files': sorted(str(p) for p in closure),
        'tree_elements': entries,
    }
    (out / 'promotion.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    (out / 'SOURCE_SHA256SUMS').write_text('\n'.join(hashes) + '\n')
    print(json.dumps(manifest, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
