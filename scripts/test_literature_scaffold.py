#!/usr/bin/env python3
"""Regression checks for report integrity and independent CI scheduling (GitHub Actions)."""
import json
from pathlib import Path
import unittest
from unittest.mock import patch
import tempfile
from check_literature_boundary import check, imports, mathlib_cache_roots, ROOT
from literature_report import parse_report

REPO = Path(__file__).resolve().parents[1]

def sample_log(complete=0):
    rows=[]
    for i in range(1, 12):
        rows.append({'id': f'L{i:02}', 'declaration':f'fixture.goal{i}',
                     'status':'complete' if i <= complete else 'open',
                     'axioms':[] if i <= complete else [f'fixture.goal{i}'], 'unexpected_axioms':[]})
    lines=['Fixture.lean:1:0: info: LITERATURE_GOAL '+json.dumps(r) for r in rows]
    lines.append('Fixture.lean:1:0: info: LITERATURE_SUMMARY '+json.dumps({'complete':complete,'total':11,'invalid':False}))
    if complete < 11:
        lines.append(f'Fixture.lean:1:0: error: Literature completion: {complete}/11 goals proved from foundations; unresolved literature inputs remain')
    return '\n'.join(lines)

class ScaffoldTests(unittest.TestCase):
    def test_progress_and_finish(self):
        for done in (0, 3, 11):
            self.assertEqual(parse_report(sample_log(done),0 if done==11 else 1)['complete'],done)

    def test_missing_duplicate_and_error_do_not_report_success(self):
        raw=sample_log()
        for bad in (raw.replace('"L01"','"L02"'), raw.split('\n',1)[1],
                    raw+'\nFixture.lean:2:0: error: unrelated compile failure'):
            with self.assertRaises(ValueError):parse_report(bad,1)
        with self.assertRaises(ValueError):parse_report(raw,0)
        with self.assertRaises(ValueError):parse_report(sample_log(11),1)

    def test_actual_boundary(self):
        check()

    def test_mathlib_umbrella_import_is_included_in_cache_closure(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'LiteratureGoals.lean').write_text('import Mathlib Mathlib.Tactic Lean\n')
            _, external=check(root)
            self.assertEqual(mathlib_cache_roots(external), ['Mathlib'])
        self.assertEqual(mathlib_cache_roots({'Mathlib.Tactic', 'Lean', 'Mathlib.Data.Finset.Basic'}),
                         ['Mathlib.Data.Finset.Basic', 'Mathlib.Tactic'])

    def test_boundary_rejects_transitive_paper_import(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/'LiteratureGoals.lean').write_text('import MajorityDynamics.Paper.Main\n')
            p=root/'MajorityDynamics/Paper/Main.lean';p.parent.mkdir(parents=True);p.write_text('')
            with self.assertRaisesRegex(ValueError,'contribution module'):check(root)

    def test_comment_and_multiple_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'Test.lean'
            p.write_text('/- outer /- import Fake -/ import Fake -/\nimport A B\n-- import Fake\n')
            self.assertEqual(list(imports(p)),['A','B'])

    def test_ci_literature_jobs_are_independent_of_the_paper_build(self):
        # The literature goals must be built on their own, never as a side effect
        # of the full paper build, and the strict completion check must stay a
        # separate hard failure.
        workflow=(REPO/'.github/workflows/lean.yml').read_text()
        jobs=parse_jobs(workflow)
        self.assertNotIn('needs',jobs['literature-build'])
        self.assertEqual(jobs['literature-completion'].get('needs'),'literature-build')
        self.assertNotIn('needs',jobs['build'])
        self.assertNotIn('continue-on-error',workflow)
        self.assertIn('lake build --wfail LiteratureGoals',workflow)
        self.assertNotIn("build-args: '--wfail LiteratureGoals'",workflow)
        self.assertIn('lake env lean LiteratureCompletion.lean',workflow)
        self.assertIn('lake env lean PaperCompletion.lean',workflow)
        self.assertIn('lake env lean UniformCompletion.lean',workflow)

def parse_jobs(workflow):
    """Read the job names and their top-level `needs:` from the workflow without PyYAML."""
    jobs={};current=None;in_jobs=False
    for line in workflow.splitlines():
        if line.startswith('jobs:'):in_jobs=True;continue
        if not in_jobs or not line.strip() or line.lstrip().startswith('#'):continue
        indent=len(line)-len(line.lstrip())
        if indent==2 and line.rstrip().endswith(':'):
            current=line.strip()[:-1];jobs[current]={};continue
        if indent==4 and current and ':' in line:
            key,_,value=line.strip().partition(':')
            jobs[current][key]=value.strip().strip('"\'')
    return jobs

if __name__ == '__main__':unittest.main()

