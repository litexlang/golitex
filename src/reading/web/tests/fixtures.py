#!/usr/bin/env python3
"""Export real public reading inputs for the offline viewer acceptance suite."""
import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
CASES = {
    'syllogism': ('problems/missing-premise-fixed.lit', True),
    'missing-premise': ('problems/missing-premise.lit', False),
    'sqrt-two': ('04-sqrt-two-irrational.lit', True),
    'definition': ('43-checking-03-2.lit', True),
    'sets': ('02-union-and-intersection.lit', True),
    'zero-divisor': ('problems/zero-divisor.lit', False),
    'sqrt-domain': ('problems/sqrt-domain.lit', False),
    'undefined-name': ('problems/undefined-name.lit', False),
}
INLINE_CASES = {
    'predicate-membership-failure': ('1 $in intersect({1, 2}, {2, 3})', False),
    'predicate-membership-known': ('2 $in {1, 2}\n2 $in {2, 3}\n2 $in intersect({1, 2}, {2, 3})', True),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/release/litex')
    parser.add_argument('--lessons', action='store_true', help='Also verify the bilingual lessons and their concrete repair exercises.')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    report = {}
    for name, (relative, succeeds) in CASES.items():
        source = ROOT / 'examples/reading/homepage' / relative
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                              '-strict', '-lang', 'zh', '-f', str(source)],
                             capture_output=True, text=True)
        expected = 'success' if succeeds else 'failure'
        if run.returncode != (0 if succeeds else 1):
            raise RuntimeError(f'{name}: unexpected exit {run.returncode}\n{run.stderr}')
        bundle = json.loads(run.stdout)
        if bundle.get('kind') != 'reading' or bundle.get('run_result') != expected:
            raise RuntimeError(f'{name}: expected a reading {expected} bundle')
        if not any(item.get('content') == source.read_text()
                   for item in bundle.get('sources', [])):
            raise RuntimeError(f'{name}: source snapshot mismatch')
        (args.output / f'{name}.json').write_text(run.stdout)
        report[name] = {'source': relative, 'exit': run.returncode,
                        'run_result': bundle['run_result']}
    for name, (content, succeeds) in INLINE_CASES.items():
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                              '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
        bundle = json.loads(run.stdout)
        expected = 'success' if succeeds else 'failure'
        if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
            raise RuntimeError(f'{name}: unexpected inline outcome\n{run.stderr}')
        if not any(source.get('content') == content for source in bundle.get('sources', [])):
            raise RuntimeError(f'{name}: inline source snapshot mismatch')
        (args.output / f'{name}.json').write_text(run.stdout)
        report[name] = {'source': '<inline>', 'exit': run.returncode, 'run_result': expected}
    project = ROOT / 'examples/reading/book'
    run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                          '-strict', '-lang', 'zh', '-r', str(project)],
                         capture_output=True, text=True)
    if run.returncode:
        raise RuntimeError(f'book: unexpected exit {run.returncode}\n{run.stderr}')
    bundle = json.loads(run.stdout)
    if bundle.get('run_result') != 'success' or len(bundle.get('sources', [])) != 3:
        raise RuntimeError('book: expected three successful real source chapters')
    for item in bundle['sources']:
        if item.get('content') != (project / item['path']).read_text():
            raise RuntimeError('book: source snapshot mismatch')
    (args.output / 'book.json').write_text(run.stdout)
    report['book'] = {'source': 'examples/reading/book', 'exit': 0,
                      'run_result': 'success', 'sources': 3}
    if args.lessons:
        lessons = ROOT / 'examples/reading/lessons'
        subprocess.run(['python3', str(lessons / 'build.py'), '--check', '--verify',
                        '--binary', str(args.binary.resolve()),
                        '--reading-output', str(args.output),
                        '--receipt', str(args.output / 'lesson-verification.json')], check=True)
        items = json.loads((lessons / 'catalogue.json').read_text())['lessons']
        repairs = {
            'missing-premise': ('forall people nonempty_set, socrates people:\n',
                                'forall people nonempty_set, socrates people:\n    $is_human(socrates)\n'),
            'sqrt-domain': ('sqrt(-1) $in R', 'sqrt(4) $in R'),
            'definition-failure': ('by def $nonnegative(-1)', 'by def $nonnegative(3)'),
        }
        # Execute the already-established repairs described in the source, with
        # exact submitted text retained. No fabricated success/proof fixture.
        for item in items:
            if item['id'] not in repairs:
                continue
            for locale in ('zh', 'en'):
                before, after = repairs[item['id']]
                original = (lessons / item['litex_code'][locale]).read_text()
                if original.count(before) != 1:
                    raise RuntimeError(f'{item["id"]}: repair anchor is ambiguous')
                content = original.replace(before, after, 1)
                source = args.output / 'repair-source' / locale / (item['id'] + '.lit')
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text(content)
                run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                      '-strict', '-lang', locale, '-f', str(source)], capture_output=True, text=True)
                if run.returncode:
                    raise RuntimeError(f'{source}: repair failed\n{run.stderr}')
                bundle = json.loads(run.stdout)
                if bundle.get('run_result') != 'success' or not any(
                        value.get('content') == content for value in bundle.get('sources', [])):
                    raise RuntimeError(f'{source}: repaired source/result mismatch')
                (args.output / f'lesson-{item["id"]}-repair-{locale}.json').write_text(run.stdout)
        report['lessons'] = {'bilingual_sources': len(items) * 2,
                             'expected_successes': 12, 'expected_failures': 6, 'repairs': 6}
    (args.output / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'{len(CASES) + len(INLINE_CASES) + 1} core reading fixtures' + (' and bilingual lesson/repair fixtures' if args.lessons else '') + f' exported to {args.output}')


if __name__ == '__main__':
    main()
