#!/usr/bin/env python3
"""Validate and measure the unfiltered search/expansion batch using bench.py.

Run after `cargo build --release`, with an existing Lean/Mathlib project:
  python3 examples/litex_vs_lean_speed/harness/search_expansion.py all
  python3 examples/litex_vs_lean_speed/harness/search_expansion.py all --lean-project /path/to/project
"""
import argparse
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
from zoneinfo import ZoneInfo

import bench as base

BENCH = Path(__file__).resolve().parents[1]
ROOT = BENCH.parents[1]
DATA = BENCH / 'cases/search-expansion.json'
SOURCES = BENCH / 'sources/search-expansion'
RESULTS = BENCH / 'results'


def save(name, value):
    (RESULTS / ('search-expansion-' + name + '.json')).write_text(
        json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def freeze_release():
    """Keep concurrent Cargo builds from changing this run's native artifacts."""
    source = ROOT / 'target/release'
    dest = base.WORK / 'release-snapshot'
    dest.mkdir(exist_ok=True)
    paths = [source / 'litex', source / 'liblitex.rlib']
    # Current Litex has no third-party runtime crates. Copy any future crate
    # dependencies too, so rustc never falls back to the moving target tree.
    paths += [p for p in (source / 'deps').glob('*.rlib') if not p.name.startswith('liblitex-')]
    def hashes():
        return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    before = hashes()
    for p in paths:
        shutil.copy2(p, dest / p.name)
    copied = {p.name: hashlib.sha256((dest / p.name).read_bytes()).hexdigest() for p in paths}
    if before != hashes() or before != copied:
        raise SystemExit('release artifacts changed while copying; rerun after the build finishes')
    base.LITEX, base.RLIB, base.RUST_DEPS = dest / 'litex', dest / 'liblitex.rlib', dest
    return copied


def strict_run(source_path):
    p = base.call([base.LITEX, '-lang', 'en', '-strict', '-f', source_path], cwd=base.WORK, timeout=60)
    result = json.loads(p.stdout)
    return p.returncode, result


def validate(cases):
    positive, negative = [], []
    for c in cases:
        code, result = strict_run(SOURCES / (c['id'] + '.lit'))
        ok = (code == 0 and result.get('run_result') == 'success' and
              not result.get('session_terminated') and result.get('termination') is None)
        positive.append({'case': c['id'], 'passed': ok, 'exit': code, 'errors': result.get('errors', [])})
        bad = base.WORK / (c['id'] + '-false.lit')
        bad.write_text(c['reject_litex'] + '\n')
        code, result = strict_run(bad)
        errors = result.get('errors', [])
        ok = (code != 0 and result.get('run_result') == 'failure' and errors and
              not result.get('session_terminated') and result.get('termination') is None and
              all(e.get('category') == 'proof_search' for e in errors))
        negative.append({'case': c['id'], 'rejected_false_statement': bool(ok),
                         'exit': code, 'errors': errors})
    lean = base.validate_lean(cases)
    lean['file'] = 'temporary bundle of the public Lean routes'
    old_processes, old_reps = base.PROCESSES, base.LEAN_REPS
    base.PROCESSES, base.LEAN_REPS = 1, 0
    guard = False
    try:
        try:
            base.measure_lean([{'id': 'expected_failure', 'lean': '(0 : Nat) = 1',
                                'methods': {'false_proof': 'by decide'}}])
        except SystemExit as ex:
            guard = 'did not succeed' in str(ex)
    finally:
        base.PROCESSES, base.LEAN_REPS = old_processes, old_reps
    report = {'litex': positive, 'false_neighbors': negative, 'lean': lean,
              'failed_lean_probe_rejected': guard}
    save('validation', report)
    if (not all(r['passed'] for r in positive) or
        not all(r['rejected_false_statement'] for r in negative) or
        lean['exit'] != 0 or lean['sorry'] or not guard):
        raise SystemExit('validation failed; see results/search-expansion-validation.json')
    print(f'PASS: {len(cases)} strict Litex files, {sum(len(c["methods"]) for c in cases)} Lean routes, '
          f'{len(negative)} false neighbors, failed-probe guard', flush=True)


def table(cases, summary):
    lines = ['| Case | Litex ms | Lean expanded/all ms | Lean only ms | Lean direct ms | Direct/Litex |',
             '| --- | ---: | ---: | ---: | ---: | ---: |']
    for c in cases:
        lit = summary['litex/' + c['id']]['median_ms']
        slow = 'expanded' if c['family'] == 'sum_expansion' else 'all_hypotheses'
        direct = 'formula' if c['family'] == 'sum_expansion' else 'lemma'
        naive = summary['lean/' + c['id'] + '__' + slow]['median_ms']
        fast = summary['lean/' + c['id'] + '__' + direct]['median_ms']
        only = (f'{summary["lean/" + c["id"] + "__only_certificate"]["median_ms"]:.3f}'
                if c['family'] == 'context_load' else '—')
        lines.append(f'| {c["id"]} | {lit:.3f} | {naive:.3f} | {only} | {fast:.3f} | {fast/lit:.2f} |')
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['validate', 'measure', 'all'])
    parser.add_argument('--lean-project', type=Path, default=ROOT / 'showcases/litex_to_lean_adapter')
    args = parser.parse_args()
    project = args.lean_project.resolve()
    os.environ['ELAN_TOOLCHAIN'] = (project / 'lean-toolchain').read_text().strip()
    os.environ['LEAN'] = subprocess.check_output(['elan', 'which', 'lean'], text=True).strip()
    libraries = [project / '.lake/build/lib/lean', *sorted((project / '.lake/packages').glob('*/.lake/build/lib/lean'))]
    if not (project / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').exists():
        raise SystemExit('the Lean project must already have the Mathlib cache')
    os.environ['LEAN_PATH'] = os.pathsep.join(str(p) for p in libraries)
    day = datetime.now(ZoneInfo('Asia/Shanghai')).date().isoformat()
    base.WORK = ROOT / 'tmp' / day / 'search-expansion-examples'
    base.WORK.mkdir(parents=True, exist_ok=True)
    base.SOURCES = base.WORK
    base.CASES_FILE = DATA
    base.PROCESSES, base.LEAN_REPS, base.LITEX_REPS = 3, 3, 11
    artifact_hashes = freeze_release()
    cases = json.loads(DATA.read_text())
    for c in cases:
        expected = {SOURCES / (c['id'] + '.lit'): c['litex'].rstrip() + '\n'}
        for method, proof in c['methods'].items():
            expected[SOURCES / f'{c["id"]}__{method}.lean'] = (
                'import Mathlib\n\nset_option linter.unusedVariables false\n\nexample : '
                + c['lean'] + ' := ' + proof + '\n')
        for path, text in expected.items():
            if path.read_text() != text:
                raise SystemExit(f'case/source drift: {path.relative_to(ROOT)}')
    environment = base.environment()
    environment['date'] = datetime.now(ZoneInfo('Asia/Shanghai')).isoformat()
    environment['mathlib_commit'] = subprocess.check_output(
        ['git', 'rev-parse', 'HEAD'], cwd=project / '.lake/packages/mathlib', text=True).strip()
    environment['source_hashes'] = {str(p.relative_to(BENCH)): hashlib.sha256(p.read_bytes()).hexdigest()
                                    for p in [DATA, *sorted(SOURCES.glob('*.lit')), *sorted(SOURCES.glob('*.lean'))]}
    environment['scope'] = 'warm checking paths; all completed cases retained; startup/imports excluded'
    environment['reps']['litex_warm_per_process'] = 10
    environment['reps']['first_per_route_per_process'] = 1
    environment['artifact_snapshot_hashes'] = artifact_hashes
    environment['timing_harness_hashes'] = {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in (Path(__file__).resolve(), Path(base.__file__).resolve())}
    if args.stage in ('validate', 'all'):
        validate(cases)
    if args.stage in ('measure', 'all'):
        native = base.measure_litex(cases)
        for r in native:
            r['rep'] = 'first' if r['rep'] == 0 else r['rep'] - 1
        print('Litex samples complete; measuring 15 Lean routes in 3 processes', flush=True)
        lean = base.measure_lean(cases)
        for proc in range(base.PROCESSES):
            for c in cases:
                samples = [r for r in native if r['process'] == proc and r['case'] == c['id']]
                assert len(samples) == 11 and sum(r['rep'] == 'first' for r in samples) == 1
                for method in c['methods']:
                    samples = [r for r in lean if r['process'] == proc and r['case'] == base.slug(c['id'], method)]
                    assert len(samples) == 4 and sum(r['rep'] == 'first' for r in samples) == 1
        rows = native + lean
        if environment['sha256'] != base.environment()['sha256']:
            raise SystemExit('release artifacts changed during measurement; discard samples and rerun')
        summary = base.summarise(rows)
        save('raw', rows)
        save('summary', summary)
        save('environment', environment)
        (RESULTS / 'search-expansion.md').write_text(table(cases, summary))
        print(table(cases, summary), flush=True)


if __name__ == '__main__':
    main()
