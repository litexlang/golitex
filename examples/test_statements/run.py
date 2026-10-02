#!/usr/bin/env python3
"""Run isolated statement scenarios, whole fixtures, and explicit known gaps."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

SUITE = Path(__file__).resolve().parent
ROOT = SUITE.parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/release/litex')
    parser.add_argument('--leaf', help='Run one exact Stmt leaf, for example HaveObjEqualStmt')
    parser.add_argument('--require-no-gaps', action='store_true',
                        help='Fail while any recorded language gap remains')
    parser.add_argument('--report', type=Path, help='Save the complete JSON verification report')
    args = parser.parse_args()
    binary = args.binary.resolve()
    if not binary.is_file():
        parser.error('Release binary missing; run cargo build --release first')
    manifest = json.loads((SUITE / 'manifest.json').read_text())
    audit_inventory(manifest)
    selected = [entry for entry in manifest['statements']
                if args.leaf is None or entry['leaf'] == args.leaf]
    if not selected:
        parser.error('Unknown statement leaf: ' + str(args.leaf))

    records = []
    for entry in selected:
        file = checked_path(entry['file'])
        cases = split_cases(file)
        expected_names = [case['name'] for case in entry['cases']]
        if list(cases) != expected_names:
            raise ValueError(f'{file}: case markers differ from manifest')
        records.append(run(binary, entry['leaf'] + '/whole-file',
                           ['-f', str(file)], entry['file_strict'], {'success': True}))
        for case in entry['cases']:
            records.append(run(binary, entry['leaf'] + '/' + case['name'],
                               ['-e', cases[case['name']]], case['strict'], case['expect']))
        for case in entry['negative']:
            records.append(run(binary, entry['leaf'] + '/' + case['name'],
                               ['-f', str(checked_path(case['file']))],
                               case['strict'], case['expect']))
    for case in manifest['boundaries']:
        if args.leaf and case['leaf'] != args.leaf:
            continue
        records.append(run(binary, 'boundary/' + case['name'],
                           ['-f', str(checked_path(case['file']))],
                           case['strict'], case['expect']))
    for case in manifest['known_gaps']:
        if args.leaf and case['leaf'] != args.leaf:
            continue
        record = run(binary, 'known-gap/' + case['id'],
                     ['-f', str(checked_path(case['file']))],
                     case['strict'], case['observed'])
        record['known_gap'] = True
        record['desired_success'] = case['desired_success']
        record['issue_file'] = str(Path(case['file']).with_name('README.md'))
        records.append(record)

    failures = [record for record in records if not record['matches']]
    gaps = [record for record in records if record.get('known_gap')]
    for record in failures:
        print('FAIL ' + record['name'] + ': ' + '; '.join(record['errors']))
        print(json.dumps(record['output'], ensure_ascii=False, indent=2))
        if record['stderr']:
            print(record['stderr'])
    for record in gaps:
        print('KNOWN ' + record['name'] + ' (see ' + record['issue_file'] + ')')
    report = {'schema_version': 1, 'binary': str(binary),
              'statement_leaves': len(selected), 'checks': len(records),
              'passed': len(records) - len(failures), 'unexpected_failures': len(failures),
              'known_gaps': len(gaps), 'records': records}
    if args.report:
        args.report.resolve().parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(f"{len(selected)} statement leaves; {len(records)} checks; "
          f"{len(failures)} unexpected failures; {len(gaps)} recorded gaps")
    return 1 if failures or (args.require_no_gaps and gaps) else 0


def checked_path(relative):
    path = (SUITE / relative).resolve()
    if not path.is_relative_to(SUITE) or not path.is_file():
        raise ValueError('Invalid fixture path: ' + str(relative))
    return path


def split_cases(file):
    source = file.read_text()
    markers = list(re.finditer(r'^# case: ([a-zA-Z0-9_-]+)\s*$', source, re.M))
    if not markers or len({marker[1] for marker in markers}) != len(markers):
        raise ValueError(f'{file}: missing or duplicate case markers')
    if any(line.strip() and not line.startswith('#')
           for line in source[:markers[0].start()].splitlines()):
        raise ValueError(f'{file}: executable code precedes first case')
    cases = {}
    for index, marker in enumerate(markers):
        end = markers[index + 1].start() if index + 1 < len(markers) else len(source)
        code = source[marker.end():end].strip() + '\n'
        if not any(line.strip() and not line.startswith('#') for line in code.splitlines()):
            raise ValueError(f'{file}: empty case {marker[1]}')
        cases[marker[1]] = code
    return cases


def enum_variants(source, name):
    source = re.sub(r'//[^\n]*', '', source)
    match = re.search(r'pub enum ' + re.escape(name) + r'\s*\{([^{}]*)\}', source, re.S)
    if match is None:
        raise ValueError('Cannot audit enum ' + name + '; update inventory reader explicitly')
    body = re.sub(r'//[^\n]*', '', match[1])
    variants = re.findall(r'(\w+)\s*\(\s*(\w+)\s*\)\s*,', body)
    remainder = re.sub(r'\w+\s*\(\s*\w+\s*\)\s*,', '', body).strip()
    if remainder or not variants:
        raise ValueError('Unrecognized variant shape in ' + name + ': ' + remainder)
    return variants


def audit_inventory(manifest):
    source = (ROOT / 'src/ast/stmt.rs').read_text()
    enums = set(re.findall(r'pub enum (\w+)', source))
    actual = {}

    def descend(name, path):
        for variant, payload in enum_variants(source, name):
            next_path = path + [variant]
            if name == 'Stmt' and variant == 'Fact':
                actual[variant] = {'path': next_path, 'payload': payload}
            elif payload in enums:
                descend(payload, next_path)
            else:
                if variant in actual:
                    raise ValueError('Ambiguous statement leaf: ' + variant)
                actual[variant] = {'path': next_path, 'payload': payload}

    descend('Stmt', [])
    recorded = {entry['leaf']: {'path': entry['ast_path'], 'payload': entry['payload']}
                for entry in manifest['statements']}
    if len(recorded) != len(manifest['statements']) or recorded != actual:
        raise ValueError('Stmt inventory drift: update per-leaf fixtures and manifest')
    templates = {name for name, _ in enum_variants(source, 'TemplateDefEnum')}
    if templates != set(manifest['template_bodies']):
        raise ValueError('TemplateDefEnum inventory drift')
    expected_files = {entry['file'] for entry in manifest['statements']}
    if expected_files != {file.name for file in SUITE.glob('*.lit')}:
        raise ValueError('Missing or unlisted primary .lit fixture')
    listed = expected_files | {case['file'] for entry in manifest['statements']
                              for case in entry['negative']}
    listed |= {case['file'] for case in manifest['boundaries'] + manifest['known_gaps']}
    actual_files = {str(file.relative_to(SUITE)) for file in SUITE.rglob('*.lit')}
    if listed != actual_files:
        raise ValueError('Missing or unlisted supporting .lit fixture')


def run(binary, name, inputs, strict, expect):
    flags = ['-strict'] if strict else []
    command = [str(binary), '-lang', 'en', *flags, *inputs]
    errors = []
    try:
        proc = subprocess.run(command, cwd=SUITE, capture_output=True, text=True, timeout=20)
    except subprocess.TimeoutExpired:
        return {'name': name, 'matches': False, 'errors': ['timeout'],
                'output': None, 'stderr': '', 'exit_code': None}
    try:
        output = json.loads(proc.stdout)
    except json.JSONDecodeError:
        output = None
        errors.append('stdout is not a single JSON run envelope')
    if proc.returncode not in (0, 1):
        errors.append('crash/launch error/abnormal exit: ' + str(proc.returncode))
    if proc.stderr.strip():
        errors.append('unexpected stderr')
    if output is not None:
        if output.get('kind') != 'run' or output.get('detail') != 'normal':
            errors.append('unexpected JSON envelope')
        if output.get('success') is not expect['success']:
            errors.append('success differs from expectation')
        if proc.returncode != (0 if expect['success'] else 1):
            errors.append('exit code differs from expectation')
        results = output.get('statement_results')
        session_error = output.get('session_error')
        if not isinstance(results, list):
            errors.append('statement_results is not a list')
            results = []
        if expect['success'] and (session_error is not None or not results
                                  or any(result.get('success') is not True for result in results)):
            errors.append('positive contains an error or no executed statements')
        if 'statement_success' in expect:
            if [result.get('success') for result in results] != expect['statement_success']:
                errors.append('statement success sequence differs')
        if expect.get('session_error_contains'):
            if expect['session_error_contains'] not in str(session_error):
                errors.append('wrong session error')
        elif 'failed_phase' in expect:
            failed = [result for result in results if result.get('success') is False]
            if session_error is not None or not failed:
                errors.append('expected a soft statement failure')
            elif [result.get('why_failed', {}).get('phase') for result in failed] != expect['failed_phase']:
                errors.append('wrong failure phase')
        if expect.get('empty_effects'):
            if any(result.get('stores') or result.get('infers') for result in results):
                errors.append('command or sketch exported facts')
    return {'name': name, 'command': command, 'exit_code': proc.returncode,
            'matches': not errors, 'errors': errors, 'output': output, 'stderr': proc.stderr}


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, OSError, KeyError) as error:
        print('SUITE ERROR: ' + str(error), file=sys.stderr)
        sys.exit(2)
