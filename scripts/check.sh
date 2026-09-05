#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p certification

# This scan supplements (and does not replace) Lean's dependency audit.
python3 - <<'PY'
from pathlib import Path
import re

paths = sorted(Path('Sqrt6KissingBound').rglob('*.lean'))
paths += [Path('Sqrt6KissingBound.lean'), Path('Axioms.lean')]


def without_comments_and_strings(text: str) -> str:
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)

for path in paths:
    source = without_comments_and_strings(path.read_text(encoding='utf-8'))
    bad = re.search(r'\b(?:sorry|admit|native_decide|axiom|unsafe|sorryAx|ofReduceBool|trustCompiler)\b', source)
    if bad:
        raise SystemExit(f'Forbidden proof construct in {path}: {bad.group()}')
print(f'SOURCE_SCAN_PASSED: {len(paths)} Lean source files')
PY

lake build 2>&1 | tee certification/build.log
lake env lean Axioms.lean 2>&1 | tee certification/axioms.log
python3 scripts/check_axioms.py certification/axioms.log | tee certification/axiom-whitelist.log
printf 'Full Lean build, source scan, and public-theorem axiom audit passed.\n'
