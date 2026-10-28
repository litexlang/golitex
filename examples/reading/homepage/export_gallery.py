#!/usr/bin/env python3
"""Export the checked reading gallery and separate expected-failure exercises."""
import argparse
import hashlib
import html as html_markup
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from urllib.parse import urlsplit

HOME = Path(__file__).resolve().parent
ROOT = HOME.parents[2]
MARKER = 'reading-example-groups'


def inject(page, groups):
    if not page.exists():
        return
    html = page.read_text()
    html = re.sub(r'<script type="application/json" id="' + MARKER + r'">.*?</script>\s*', '', html, flags=re.S)
    data = json.dumps(groups, ensure_ascii=False).replace('<', '\\u003c')
    html = html.replace('</body>', '<script type="application/json" id="' + MARKER + '">' + data + '</script>\n</body>')
    page.write_text(html)


def export(binary, source, output, expected, locale='zh'):
    result = subprocess.run([str(binary), '-reading', '-strict', '-lang', locale,
                             '-f', str(source), '-export', str(output)], capture_output=True, text=True)
    if result.returncode != (0 if expected == 'success' else 1):
        raise RuntimeError(f'{source}: unexpected exit {result.returncode}\n{result.stdout}\n{result.stderr}')
    envelope = json.loads(result.stdout)
    if envelope.get('kind') != 'reading_export' or envelope.get('run_result') != expected:
        raise RuntimeError(f'{source}: no matching export envelope')
    data = json.loads((output / 'reading.json').read_text())
    if data.get('kind') != 'reading' or data.get('run_result') != expected:
        raise RuntimeError(f'{source}: expected {expected}')
    if not any(item.get('content') == source.read_text() for item in data.get('sources', [])):
        raise RuntimeError(f'{source}: exported source does not match input')
    return {'source': str(source.relative_to(ROOT)), 'expected': expected,
            'run_result': data['run_result'], 'exit': result.returncode}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/release/litex')
    parser.add_argument('--reuse-main', action='store_true', help='Reuse an already verified main export; rebuild only the exercises.')
    parser.add_argument('--build-endpoint', help='Optional checking API for the editable local/hosted gallery.')
    parser.add_argument('--mechanics-export', type=Path,
                        help='Include an existing successful reading export of The Mechanics of Litex Proof.')
    args = parser.parse_args()
    binary = args.binary.resolve()
    output = args.output.resolve()
    if args.build_endpoint:
        endpoint = urlsplit(args.build_endpoint)
        if any(char in args.build_endpoint for char in '<>\r\n') or not (
                args.build_endpoint.startswith('/') and not args.build_endpoint.startswith('//') or
                endpoint.scheme in ('http', 'https') and endpoint.netloc):
            parser.error('--build-endpoint requires a site-relative path starting with / or an HTTP(S) URL')
    lessons_home = HOME.parent / 'lessons'
    subprocess.run([sys.executable, str(lessons_home / 'build.py'), '--check'], check=True)
    lessons = json.loads((lessons_home / 'catalogue.json').read_text())['lessons']
    book = None
    book_titles = {'zh': 'The Mechanics of Litex Proof', 'en': 'The Mechanics of Litex Proof'}
    if args.mechanics_export:
        book = args.mechanics_export.resolve()
        if not (book / 'index.html').is_file() or not (book / 'reading.json').is_file():
            parser.error('--mechanics-export requires a complete reading export')
        book_data = json.loads((book / 'reading.json').read_text())
        if book_data.get('kind') != 'reading' or book_data.get('run_result') != 'success':
            parser.error('--mechanics-export requires a successful reading export')
        trust = book_data.get('trust_summary', {})
        if trust.get('user_assumptions') or trust.get('axioms'):
            book_titles = {'zh': 'The Mechanics of Litex Proof（部分证明待补全）',
                           'en': 'The Mechanics of Litex Proof (contains assumptions)'}
        destination = output / 'books/mechanics'
        if book != destination:
            shutil.copytree(book, destination, dirs_exist_ok=True)
        book = destination
    if args.reuse_main:
        if not (output / 'index.html').is_file() or not (output / 'reading.json').is_file():
            parser.error('--reuse-main requires an existing main reading export')
    else:
        run = subprocess.run([str(binary), '-reading', '-strict', '-lang', 'zh', '-r', str(HOME), '-export', str(output)], capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    registry = json.loads((HOME / 'problems/cases.json').read_text())
    titles = json.loads((HOME / 'problems/reading-titles.json').read_text())['sources']
    cases = registry['cases']
    report = []
    destinations = [output]
    for case in cases:
        for mode, expected in [('broken', 'failure'), ('corrected', 'success')]:
            target = output / 'cases' / (case['id'] + ('-fixed' if mode == 'corrected' else ''))
            report.append(export(binary, HOME / 'problems' / case['litex_code'][mode], target, expected))
            destinations.append(target)
    for lesson in lessons:
        for locale in ('zh', 'en'):
            target = output / 'lessons' / locale / lesson['id']
            result = export(binary, lessons_home / lesson['litex_code'][locale], target, lesson['expected'], locale)
            result.update({'lesson': lesson['id'], 'locale': locale})
            report.append(result)
            destinations.append(target)
            alternates = []
            for alternate_locale in ('zh', 'en'):
                alternate = os.path.relpath(output / 'lessons' / alternate_locale / lesson['id'], target).replace(os.sep, '/')
                href = ('./' if alternate == '.' else alternate + '/') + 'index.html'
                alternates.append(f'<link rel="alternate" hreflang="{alternate_locale}" href="{html_markup.escape(href, quote=True)}">')
            for page_name in ('index.html', 'standalone.html'):
                page = target / page_name
                if page.is_file():
                    page.write_text(page.read_text().replace('</head>', '\n'.join(alternates) + '\n</head>'))

    def groups(prefix='', current=None, mode=None, current_lesson=None):
        def lesson_link(lesson):
            return {'titles': lesson['titles'], 'hrefs': {
                locale: prefix + 'lessons/' + locale + '/' + lesson['id'] + '/'
                for locale in ('zh', 'en')}}
        result = [{'titles': {'zh': '从这里读起', 'en': 'Start reading'}, 'items': [
            lesson_link(lesson) for lesson in lessons
            if lesson['expected'] == 'success' and lesson['id'] != current_lesson]}]
        if book:
            result.append({'titles': {'zh': '整本书', 'en': 'Complete books'}, 'items': [
                {'titles': book_titles,
                 'href': prefix + 'books/mechanics/'}]})
        for category, label in [
            ('corrected', {'zh': '能通过', 'en': 'Passes'}),
            ('broken', {'zh': '不能通过', 'en': 'Does not pass'})
        ]:
            items = []
            if category == 'broken':
                items.extend(lesson_link(lesson) for lesson in lessons
                             if lesson['expected'] == 'failure' and lesson['id'] != current_lesson)
            if prefix and category == 'corrected':
                items.append({'titles': {'zh': '更多能通过的示例', 'en': 'More passing examples'}, 'href': prefix})
            for case in cases:
                if case['id'] == current and category == mode:
                    continue
                slug = case['id'] + ('-fixed' if category == 'corrected' else '')
                items.append({'titles': titles[case['litex_code'][category]], 'href': prefix + 'cases/' + slug + '/'})
            result.append({'titles': label, 'includeSources': (mode or 'corrected') == category, 'items': items})
        return result

    for page_name in ['index.html', 'standalone.html']:
        inject(output / page_name, groups())
    for case in cases:
        for mode in ['broken', 'corrected']:
            target = output / 'cases' / (case['id'] + ('-fixed' if mode == 'corrected' else ''))
            for page_name in ['index.html', 'standalone.html']:
                inject(target / page_name, groups('../../', case['id'], mode))
    for lesson in lessons:
        for locale in ('zh', 'en'):
            target = output / 'lessons' / locale / lesson['id']
            for page_name in ('index.html', 'standalone.html'):
                inject(target / page_name, groups('../../../', mode='corrected' if lesson['expected'] == 'success' else 'broken', current_lesson=lesson['id']))
    if book:
        destinations.append(book)
        for page_name in ['index.html', 'standalone.html']:
            inject(book / page_name, [
                {'titles': {'zh': '本书章节', 'en': 'Book chapters'}, 'includeSources': True, 'items': []},
                groups('../../')[0],
                {'titles': {'zh': '其他示例', 'en': 'Other examples'}, 'items': [
                    {'titles': {'zh': '返回示例目录', 'en': 'Back to examples'}, 'href': '../../'}]}
            ])
    # Current shared component, including when reusing an older main export.
    destinations.extend(path for path in (output / 'cases').iterdir()
                        if path.is_dir() and path not in destinations)
    for dest in destinations:
        if dest.is_dir():
            for name in ['reader.js', 'reader.css', 'app.js']:
                shutil.copyfile(ROOT / 'src/reading/web' / name, dest / name)
            for page_name in ['index.html', 'standalone.html']:
                page = dest / page_name
                if not page.is_file():
                    continue
                html = page.read_text()
                html = html.replace("location.replace('standalone.html'+location.hash)",
                                    "location.replace('standalone.html'+location.search+location.hash)")
                if args.build_endpoint:
                    html = re.sub(r'<script[^>]*id="reading-build-endpoint"[^>]*>.*?</script>\s*', '', html, flags=re.S)
                    html = html.replace('</body>', '<script type="text/plain" id="reading-build-endpoint">' + args.build_endpoint + '</script>\n</body>')
                for name in ['reader.js', 'reader.css', 'app.js']:
                    version = hashlib.sha256((dest / name).read_bytes()).hexdigest()[:12]
                    html = re.sub(r'((?:src|href)=")' + re.escape(name) + r'(?:\?[^"]*)?"',
                                  r'\g<1>' + name + '?v=' + version + '"', html)
                page.write_text(html)
    (output / 'problem-examples-verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'{len(lessons)} bilingual lessons, {len(cases)} rejected exercises and {len(cases)} corrected examples exported to {output}')


if __name__ == '__main__':
    main()
