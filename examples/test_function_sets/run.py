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
    parser.add_argument('--capabilities', action='store_true',
        help='Observe original direct claims separately from supported proof regressions')
    parser.add_argument('--report', type=Path, default=SUITE / 'results.json')
    args = parser.parse_args()
    manifest = json.loads((SUITE / 'manifest.json').read_text())
    inventory = manifest['cases'] + manifest.get('capability_probes', [])
    if not inventory or len({case['id'] for case in inventory}) != len(inventory):
        raise ValueError('Empty inventory or duplicate case ID')
    fixtures = {case['file'] for case in inventory}
    if len(fixtures) != len(inventory) or fixtures != {str(path.relative_to(SUITE)) for path in SUITE.rglob('*.lit')}:
        raise ValueError('Fixture inventory differs from manifest')
    cases = manifest.get('capability_probes', []) if args.capabilities else manifest['cases']
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
        mode='capability_observation' if args.capabilities else 'supported_regression',
        source_sha256=source, binary_sha256=binary_hash, observations=[])
    for case in cases:
        path = SUITE / case['file']
        code = path.read_text()
        if any('trust' in line.split('#', 1)[0].split() for line in code.splitlines()):
            raise ValueError('Trust is forbidden in ' + str(path))
        result = evaluate(path)
        result.update({key: case[key] for key in ['id', 'group', 'title', 'file', 'expect']})
        result['fixture_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        result['matches'] = None if args.capabilities else result['observed'] == case['expect']
        if args.capabilities:
            pass
        elif case['expect'] == 'reject':
            statuses = result['statement_statuses']
            setup = case['setup_statements']
            if case['phase'] == 'parse':
                result['matches'] &= result['phase'] == 'parse' and statuses == [True] * setup
            else:
                result['matches'] &= result['phase'] == case['phase'] and statuses == [True] * setup + [False]
        else:
            result['matches'] &= result['statement_statuses'] == [True] * case['statements']
        if not args.capabilities and case.get('failure_contains'):
            failure_text = json.dumps(result.get('failures', []), ensure_ascii=False)
            result['matches'] &= all(text in failure_text for text in case['failure_contains'])
        report['observations'].append(result)
        label = 'OBSERVED' if args.capabilities else ('PASS' if result['matches'] else 'FAIL')
        print(label + ' ' + case['id'] + ': ' + result['observed'] + '/' + result['phase'] + ' — ' + case['title'])
    report['identity_stable'] = source == source_digest() and binary_hash == hashlib.sha256(BINARY.read_bytes()).hexdigest()
    if args.capabilities:
        report['ok'] = report['identity_stable'] and all(o['observed'] in ['accept', 'reject'] for o in report['observations'])
        report['counts'] = dict(total=len(cases), accepted=sum(o['observed']=='accept' for o in report['observations']),
            rejected=sum(o['observed']=='reject' for o in report['observations']),
            infrastructure_failures=sum(o['observed'] not in ['accept', 'reject'] for o in report['observations']))
    else:
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
        parse_error = isinstance(error, str) and error.startswith(('parse_error:', 'Runtime(ParseError('))
        if failed and (error is None or parse_error):
            return dict(result, observed='reject', phase=failed[0].get('why_failed', {}).get('phase', 'verification'), failures=failed)
        if parse_error:
            return dict(result, observed='reject', phase='parse', diagnostic=error, failures=failed)
    return dict(result, diagnostic=repr(envelope)[-4000:])


if __name__ == '__main__':
    sys.exit(main())
