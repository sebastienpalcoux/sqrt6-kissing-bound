#!/usr/bin/env python3
"""Reject missing, duplicate, or non-whitelisted public-theorem axiom reports."""
from pathlib import Path
import re
import sys

EXPECTED = {
    'isKissingConfiguration_iff_norm_dist',
    'kissingConfiguration_card_le_sqrt6_pow',
    'kissingConfiguration_card_le_floor_sqrt6_pow',
    'kissingConfiguration_card_le_sqrt6_pow_of_dist',
    'kissingNumber_realized',
    'kissingNumber_isGreatest',
    'kissingNumber_le_sqrt6_pow',
    'kissingNumber_one_eq_two',
    'kissingNumber_two_eq_six',
    'sqrt6_isLeast_universalKissingBase',
    'isUniversalKissingBase_iff',
    'universal_kissingNumber_bound_iff',
}
EXPECTED = {'Sqrt6KissingBound.' + name for name in EXPECTED}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python3 scripts/check_axioms.py AXIOMS_LOG')
    text = Path(sys.argv[1]).read_text(encoding='utf-8')
    if re.search(r'\b(?:sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler)\b', text):
        raise SystemExit('ERROR: a forbidden proof dependency appears in the audit output')
    found: dict[str, set[str]] = {}
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
    reports += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    for name, raw in reports:
        if name in found:
            raise SystemExit(f'ERROR: duplicate axiom report for {name}')
        axioms = {a.strip() for a in raw.split(',') if a.strip()}
        unexpected = axioms - ALLOWED
        if unexpected:
            raise SystemExit(f'ERROR: {name} uses non-whitelisted axioms: {sorted(unexpected)}')
        found[name] = axioms
    missing = EXPECTED - found.keys()
    extra = found.keys() - EXPECTED
    if missing or extra:
        raise SystemExit(f'ERROR: incomplete or unexpected audit. Missing={sorted(missing)}; extra={sorted(extra)}')
    for name in sorted(found):
        print(f'PASS {name}: {", ".join(sorted(found[name])) or "no axioms"}')
    print(f'AXIOM_WHITELIST_AUDIT_PASSED: {len(EXPECTED)} public theorems')


if __name__ == '__main__':
    main()
