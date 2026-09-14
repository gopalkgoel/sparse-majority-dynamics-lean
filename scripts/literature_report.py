#!/usr/bin/env python3
"""Validate Lean's eleven-goal report and render a Markdown/JSON CI artifact."""
import argparse
import json
import re
from pathlib import Path


def parse_report(text, returncode):
    rows, summary = [], None
    for line in text.splitlines():
        if match := re.search(r'(?:^|: info: )LITERATURE_GOAL (.*)$', line):
            rows.append(json.loads(match.group(1)))
        elif match := re.search(r'(?:^|: info: )LITERATURE_SUMMARY (.*)$', line):
            if summary is not None: raise ValueError('Duplicate literature summary')
            summary = json.loads(match.group(1))
    if len(rows) != 11 or {r['id'] for r in rows} != {f'L{i:02}' for i in range(1, 12)}:
        raise ValueError('Expected exactly one result for each of the eleven literature goals')
    if len({r['declaration'] for r in rows}) != 11:
        raise ValueError('Duplicate literature declaration')
    if summary is None or summary.get('total') != 11 or summary.get('invalid') is not False:
        raise ValueError('Missing or invalid Lean summary')
    for r in rows:
        if r['unexpected_axioms'] or r['status'] not in ('open', 'complete'):
            raise ValueError(f"Invalid dependency audit for {r['id']}")
        if (r['status'] == 'complete') != (not r['axioms']):
            raise ValueError(f"Inconsistent dependencies for {r['id']}")
    complete = sum(r['status'] == 'complete' for r in rows)
    if summary['complete'] != complete:
        raise ValueError('Inconsistent completion count')
    # A compiler crash/error must never become an ordinary unfinished-goal result.
    expected_rc = 0 if complete == 11 else 1
    expected_error = f'Literature completion: {complete}/11 goals proved from foundations; unresolved literature inputs remain'
    errors = [line for line in text.splitlines() if 'error:' in line]
    if returncode != expected_rc or (complete < 11 and
            (len(errors) != 1 or expected_error not in errors[0])) or (complete == 11 and errors):
        raise ValueError('Compiler outcome does not match the expected completion result')
    return {'complete': complete, 'total': 11, 'goals': rows}


def markdown(report, commit):
    lines = [f"# Literature goals: {report['complete']}/11 complete", '',
             f'Commit: `{commit}`', '',
             'Completion requires checked proofs using only Lean\'s standard foundations.', '',
             '| Goal | Literature theorem | Work wave | Result | Remaining axioms |',
             '| --- | --- | --- | --- | --- |']
    for r in report['goals']:
        axioms = ', '.join(f'`{a}`' for a in r['axioms']) or 'None'
        lines.append(f"| {r['id']} | {r['title']} | {r['wave']} | {r['status']} | {axioms} |")
    return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--exit-code', type=int, required=True)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = parse_report(args.log.read_text(), args.exit_code)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'goals.json').write_text(json.dumps({'commit': args.commit, **report}, indent=2)+'\n')
    (args.output / 'goals.md').write_text(markdown(report, args.commit))
    (args.output / 'completion-exit-code').write_text(str(0 if report['complete'] == 11 else 1)+'\n')

