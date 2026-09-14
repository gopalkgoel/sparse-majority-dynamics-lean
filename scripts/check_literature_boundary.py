#!/usr/bin/env python3
"""Check the independent literature import closure; optionally emit cache roots.

This checks architecture, not proof completion. Lean's transitive axiom audit is
responsible for mathematical completion.
"""
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parents[1]
SHARED = {
    'MajorityDynamics.Probability.RandomGraph.Basic',
    'MajorityDynamics.Probability.DegreeConcentration.Basic',
    'MajorityDynamics.Probability.FixedDegreeSampling.Basic',
    'MajorityDynamics.Probability.FixedDegreeSampling.BipartiteBasic',
    'MajorityDynamics.Probability.FixedDegreeSampling.BipartiteRemoval',
    'MajorityDynamics.Probability.FixedDegreeSampling.FiniteLaw',
    'MajorityDynamics.Probability.FixedDegreeSampling.GraphRemoval',
    'MajorityDynamics.Probability.FixedDegreeSampling.Laws',
}

def without_comments(text):
    """Erase nested Lean comments and strings, preserving line breaks."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            if text[i] == '\\': i += 2; continue
            if text[i] == '"': quoted = False
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; i += 2; out.append(' ')
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"': quoted = True; i += 1; out.append(' ')
        else: out.append(text[i]); i += 1
    if depth or quoted: raise ValueError('Unterminated Lean comment or string')
    return ''.join(out)

def imports(path):
    text = without_comments(path.read_text())
    for line in text.splitlines():
        match = re.match(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
        if match:
            yield from match.group(1).split()

def check(root=ROOT):
    seen, external = set(), set()
    def visit(module):
        if module in seen: return
        path = root / (module.replace('.', '/') + '.lean')
        if not path.exists():
            if module.startswith('MajorityDynamics') or module == 'LiteratureGoals':
                raise ValueError(f'Missing project import: {module}')
            external.add(module); return
        if not (module == 'LiteratureGoals' or
                module.startswith('MajorityDynamics.Literature.') or module in SHARED):
            raise ValueError(f'Literature imports a paper/contribution module: {module}')
        seen.add(module)
        for dependency in imports(path): visit(dependency)
    visit('LiteratureGoals')
    return seen, external

def mathlib_cache_roots(external):
    # The umbrella module requires the entire Mathlib import closure. Omitting
    # it silently turns a cache download into a large source rebuild in CI.
    if 'Mathlib' in external:
        return ['Mathlib']
    return sorted(m for m in external if m.startswith('Mathlib.'))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-roots', type=Path)
    args = parser.parse_args()
    modules, external = check()
    if args.cache_roots:
        args.cache_roots.parent.mkdir(parents=True, exist_ok=True)
        args.cache_roots.write_text('\n'.join(mathlib_cache_roots(external)) + '\n')
    print(f'Literature boundary passed: {len(modules)} project modules; no paper proof imports.')
