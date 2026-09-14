#!/usr/bin/env python3
"""Exercise the actual Lean auditor on isolated temporary proof fixtures.

Synthetic assumptions/placeholders are never imported by a project target.
"""
import argparse
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
HEADER = '''import MajorityDynamics.Literature.GoalAudit
namespace LiteratureAuditFixture
open MajorityDynamics.Literature.GoalAudit
def Contract : Prop := ∀ n : Nat, n = n
'''
GOAL = '''def goals : Array Goal := #[{
  id := "test", title := "Fixture", declaration := ``endpoint,
  contract := ``Contract, wave := "test" }]
run_cmd audit goals (requireComplete := STRICT)
end LiteratureAuditFixture
'''
CASES = [
    ('checked proof', 'theorem endpoint : Contract := fun _ => rfl\n', True, True, '"status":"complete"'),
    ('open axiom', 'axiom endpoint : Contract\n', True, False, 'unresolved literature inputs remain'),
    ('hidden transitive axiom', 'axiom hidden : Contract\ntheorem endpoint : Contract := hidden\n', False, False, 'unlisted mathematical axioms'),
    ('extra premise', 'theorem endpoint (h : Contract) : Contract := h\n', False, False, 'frozen closed contract'),
    ('unsafe endpoint', 'unsafe def endpoint : Contract := unsafeCast True.intro\n', False, False, 'must be a theorem'),
    ('placeholder', 'theorem endpoint : Contract := by sorry\n', False, False, 'sorryAx'),
]

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-command', default='lake env lean')
    args = parser.parse_args()
    for label, declaration, strict, passes, expected in CASES:
        with tempfile.TemporaryDirectory(prefix='literature-audit-') as tmp:
            fixture = Path(tmp) / 'Fixture.lean'
            fixture.write_text(HEADER+declaration+GOAL.replace('STRICT', str(strict).lower()))
            proc = subprocess.run(shlex.split(args.lean_command) +
                ['-DautoImplicit=false', '-DwarningAsError=true', '-R', tmp, str(fixture)],
                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if (proc.returncode == 0) != passes or expected not in proc.stdout:
            raise SystemExit(f'{label}: unexpected audit result\n{proc.stdout}')
        print(f'Passed audit regression: {label}')
