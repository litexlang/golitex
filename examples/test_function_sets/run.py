#!/usr/bin/env python3
"""Check function-set composition through the current strict release CLI."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

SUITE = Path(__file__).resolve().parent
ROOT = SUITE.parents[1]
BINARY = ROOT / 'target/release/litex'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', action='append', help='Select case IDs (repeatable)')
    parser.add_argument('--report', type=Path, default=SUITE / 'results.json')
    args = parser.parse_args()
    manifest = json.loads((SUITE / 'manifest.json').read_text())
    cases = manifest['cases']
    if not cases or len({case['id'] for case in cases}) != len(cases):
        raise ValueError('Empty inventory or duplicate case ID')
    fixtures = {case['file'] for case in cases}
    if len(fixtures) != len(cases) or fixtures != {str(path.relative_to(SUITE)) for path in SUITE.rglob('*.lit')}:
        raise ValueError('Fixture inventory differs from manifest')
    if args.case:
        unknown = set(args.case) - {case['id'] for case in cases}
        if unknown:
            parser.error('Unknown case IDs: ' + ', '.join(sorted(unknown)))
        cases = [case for case in cases if case['id'] in args.case]
    source = source_digest()
    build = subprocess.run(['cargo', 'build', '--release'], cwd=ROOT, capture_output=True, text=True)
    if build.returncode != 0 or source != source_digest():
        print('Current-source build failed or source changed during build.', file=sys.stderr)
        print((build.stdout + build.stderr)[-3000:], file=sys.stderr)
        return 2
    binary_hash = hashlib.sha256(BINARY.read_bytes()).hexdigest()
    report = dict(schema_version=1, built_from_current_source=True,
        source_sha256=source, binary_sha256=binary_hash, observations=[])
    for case in cases:
        path = SUITE / case['file']
        code = path.read_text()
        if any('trust' in line.split('#', 1)[0].split() for line in code.splitlines()):
            raise ValueError('Trust is forbidden in ' + str(path))
        result = evaluate(path)
        result.update({key: case[key] for key in ['id', 'group', 'title', 'file', 'expect']})
        result['fixture_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        result['matches'] = result['observed'] == case['expect']
        if case['expect'] == 'reject':
            statuses = result['statement_statuses']
            setup = case['setup_statements']
            if case['phase'] == 'parse':
                result['matches'] &= result['phase'] == 'parse' and statuses == [True] * setup
            else:
                result['matches'] &= result['phase'] == case['phase'] and statuses == [True] * setup + [False]
        else:
            result['matches'] &= result['statement_statuses'] == [True] * case['statements']
        report['observations'].append(result)
        print(('PASS' if result['matches'] else 'FAIL') + ' ' + case['id'] + ': ' + result['observed'] + '/' + result['phase'] + ' — ' + case['title'])
    report['identity_stable'] = source == source_digest() and binary_hash == hashlib.sha256(BINARY.read_bytes()).hexdigest()
    report['ok'] = report['identity_stable'] and all(item['matches'] for item in report['observations'])
    report['counts'] = dict(total=len(cases), positive=sum(c['expect']=='accept' for c in cases),
        negative=sum(c['expect']=='reject' for c in cases), passed=sum(o['matches'] for o in report['observations']),
        unexpected=sum(not o['matches'] for o in report['observations']))
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps(report['counts']) + '; identity_stable=' + str(report['identity_stable']))
    return 0 if report['ok'] else 1


def source_digest():
    digest = hashlib.sha256()
    for path in sorted((ROOT / 'src').rglob('*.rs')) + [ROOT / 'Cargo.toml', ROOT / 'Cargo.lock']:
        digest.update(str(path.relative_to(ROOT)).encode() + b'\0' + path.read_bytes())
    return digest.hexdigest()


def evaluate(path):
    command = [str(BINARY), '-strict', '-f', str(path.relative_to(ROOT))]
    result = dict(command=command, observed='infrastructure_failure', phase='protocol', statement_statuses=[])
    try:
        process = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=15)
    except subprocess.TimeoutExpired:
        return dict(result, phase='timeout', diagnostic='CLI exceeded 15 seconds', exit_code=None)
    result['exit_code'] = process.returncode
    if process.stderr:
        return dict(result, phase='stderr', diagnostic=process.stderr[-4000:])
    try:
        envelope = json.loads(process.stdout)
    except json.JSONDecodeError:
        return dict(result, phase='invalid_json', diagnostic=process.stdout[-4000:])
    if not isinstance(envelope, dict) or envelope.get('kind') != 'run' or type(envelope.get('success')) is not bool:
        return dict(result, phase='invalid_envelope', diagnostic=repr(envelope)[-4000:])
    statements = envelope.get('statement_results')
    if not isinstance(statements, list) or any(type(s.get('success')) is not bool for s in statements):
        return dict(result, phase='invalid_statements', diagnostic=repr(envelope)[-4000:])
    statuses = [s['success'] for s in statements]
    result['statement_statuses'] = statuses
    result['session_error'] = envelope.get('session_error')
    failed = [s for s in statements if not s['success']]
    if envelope['success'] and process.returncode == 0 and all(statuses) and result['session_error'] is None:
        return dict(result, observed='accept', phase='success')
    if not envelope['success'] and process.returncode == 1:
        error = result['session_error']
        if failed and (error is None or (isinstance(error, str) and error.startswith('Runtime(ParseError('))):
            return dict(result, observed='reject', phase=failed[0].get('why_failed', {}).get('phase', 'verification'), failures=failed)
        if isinstance(error, str) and error.startswith('Runtime(ParseError('):
            return dict(result, observed='reject', phase='parse', diagnostic=error, failures=failed)
    return dict(result, diagnostic=repr(envelope)[-4000:])


if __name__ == '__main__':
    sys.exit(main())
