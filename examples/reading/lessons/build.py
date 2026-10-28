#!/usr/bin/env python3
"""Build bilingual source lessons without silently changing imported mathematics."""
import argparse
import hashlib
import json
import subprocess
import textwrap
from pathlib import Path

HOME = Path(__file__).resolve().parent
ROOT = HOME.parents[2]
LANGUAGES = ('zh', 'en')


def catalogue():
    data = json.loads((HOME / 'catalogue.json').read_text())
    if data.get('kind') != 'source_reading_lessons' or data.get('version') != 1:
        raise ValueError('Unsupported source lesson catalogue')
    ids = [item['id'] for item in data['lessons']]
    if len(ids) != len(set(ids)):
        raise ValueError('Lesson IDs must be unique')
    return data['lessons']


def comment(lines, locale, indent=''):
    result = []
    for line in lines:
        wrapped = textwrap.wrap(line, width=max(40, 78 - len(indent) - 2),
                                break_long_words=False, break_on_hyphens=False) if locale == 'en' else [line]
        result.extend(indent + '# ' + value for value in wrapped)
    return result


def lesson_text(item, locale):
    path = (ROOT / item['source']['path']).resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError('Source must belong to the repository')
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != item['source']['sha256']:
        raise ValueError(f'{item["id"]}: original source changed; review annotation anchors first')
    lines = raw.decode('utf-8').splitlines()
    before, after = {}, {}
    for annotation in item['annotations']:
        line = annotation['before_line']
        if not 1 <= line <= len(lines):
            raise ValueError(f'{item["id"]}: annotation is outside the original source')
        before.setdefault(line, []).extend(annotation[locale])
    for insertion in item['insertions']:
        line = insertion['after_line']
        if not 1 <= line <= len(lines):
            raise ValueError(f'{item["id"]}: insertion is outside the original source')
        after.setdefault(line, []).append(insertion)
    result = comment([item['titles'][locale], item['problem'][locale]], locale) + ['']
    expected_code = []
    for number, line in enumerate(lines, 1):
        indent = line[:len(line) - len(line.lstrip())]
        result.extend(comment(before.get(number, []), locale, indent))
        # Authored locale comments replace imported full-line prose. Mathematical
        # source, including indentation and any inline comment, stays byte-exact.
        if not line.lstrip().startswith('#'):
            result.append(line)
            if line.strip():
                expected_code.append(line)
        for insertion in after.get(number, []):
            result.extend(comment(insertion[locale], locale))
            result.extend(insertion['code'].splitlines())
            result.append('')
            expected_code.extend(value for value in insertion['code'].splitlines() if value.strip())
    actual_code = [value for value in result if value.strip() and not value.lstrip().startswith('#')]
    if actual_code != expected_code:
        raise ValueError(f'{item["id"]}: generated mathematical source changed')
    return '\n'.join(result).rstrip() + '\n'


def outputs(items):
    generated = {}
    for locale in LANGUAGES:
        titles = {}
        for item in items:
            relative = Path(item['litex_code'][locale])
            if relative.parent != Path(locale) or relative.suffix != '.lit':
                raise ValueError('Lessons must be independent files in their language directory')
            generated[HOME / relative] = lesson_text(item, locale)
            titles[relative.name] = item['titles']
        generated[HOME / locale / 'reading-titles.json'] = json.dumps(
            {'kind': 'reading_titles', 'sources': titles}, ensure_ascii=False, indent=2) + '\n'
    return generated


def verify(items, binary, receipt, reading_output):
    report = []
    for item in items:
        for locale in LANGUAGES:
            source = HOME / item['litex_code'][locale]
            command = [str(binary), '-reading', '-json', '-strict', '-lang', locale, '-f', str(source)]
            run = subprocess.run(command, capture_output=True, text=True)
            expected = item['expected']
            if run.returncode != (0 if expected == 'success' else 1):
                raise RuntimeError(f'{source}: unexpected exit {run.returncode}\n{run.stderr}')
            bundle = json.loads(run.stdout)
            if bundle.get('kind') != 'reading' or bundle.get('run_result') != expected:
                raise RuntimeError(f'{source}: expected a reading {expected} document')
            if bundle.get('execution_policy', {}).get('strict') is not True:
                raise RuntimeError(f'{source}: strict policy was not retained')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != source.read_text():
                raise RuntimeError(f'{source}: expected its exact independent source snapshot')
            trust = bundle.get('trust_summary', {})
            if trust.get('user_assumptions') or trust.get('axioms'):
                raise RuntimeError(f'{source}: unexpected trust or axiom')
            if reading_output:
                reading_output.mkdir(parents=True, exist_ok=True)
                (reading_output / f'lesson-{item["id"]}-{locale}.json').write_text(run.stdout)
            report.append({'lesson': item['id'], 'locale': locale,
                           'source': str(source.relative_to(ROOT)),
                           'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                           'expected': expected, 'exit': run.returncode,
                           'run_result': bundle['run_result'], 'sources': 1,
                           'executable_id': bundle.get('engine', {}).get('executable_id'),
                           'strict': True, 'trust': 0, 'axioms': 0})
            print(f'{locale}/{item["id"]}: {expected}')
    receipt.parent.mkdir(parents=True, exist_ok=True)
    receipt.write_text(json.dumps({'kind': 'source_lessons_verification', 'lessons': report},
                                 ensure_ascii=False, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Check generated sources without writing them.')
    parser.add_argument('--verify', action='store_true', help='Check each independent lesson with the strict verifier.')
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/release/litex')
    parser.add_argument('--receipt', type=Path, default=HOME / 'verification.json')
    parser.add_argument('--reading-output', type=Path, help='Retain actual reading bundles in a task-owned directory.')
    args = parser.parse_args()
    items = catalogue()
    for path, content in outputs(items).items():
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise ValueError(f'{path}: generated source is stale')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    if args.verify:
        verify(items, args.binary.resolve(), args.receipt, args.reading_output)
    print(f'{len(items)} bilingual source lessons {"checked" if args.check else "built"}.')


if __name__ == '__main__':
    main()
