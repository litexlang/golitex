#!/usr/bin/env python3
"""Compile real CLI output for all locales; require XeLaTeX and its documented fonts."""
import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', default='target/release/litex')
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    binary = (root / args.binary).resolve()
    output = Path(args.output_dir).resolve()
    output.mkdir(parents=True, exist_ok=True)
    locales = ['en', 'zh', 'zh-hant', 'fr', 'ru', 'es', 'ar', 'ja', 'ko', 'vi']
    statements = sorted((root / 'examples/test_statements').glob('*.lit'))
    objects = sorted((root / 'examples/test_objs').glob('*.lit'))

    def convert(source, language, document=False):
        command = [str(binary), '-latex', '-lang', language, '-e', source]
        if document:
            command.append('-document')
        result = subprocess.run(command, cwd=root, capture_output=True, text=True, check=False)
        artifact = json.loads(result.stdout)
        if result.returncode != 0 or not artifact['success']:
            raise RuntimeError(f'{language}: {artifact}')
        return artifact['content']

    for language in locales:
        fragments = [convert(path.read_text(), language) for path in statements + objects]
        # The actual CLI document wrapper supplies the correct locale/font setup.
        wrapper = convert('1 = 1', language, document=True)
        preamble = wrapper.split('\\begin{document}', 1)[0]
        (output / f'corpus.{language}.tex').write_text(
            preamble + '\\begin{document}\n' + '\n'.join(fragments) + '\\end{document}\n'
        )
        print(f'{language}: converted {len(statements)} statement and {len(objects)} object fixtures', flush=True)

    env = dict(os.environ)
    env['TEXMFVAR'] = str(output / 'tex-cache')
    env['TEXMFCONFIG'] = str(output / 'tex-config')

    def compile_pdf(language):
        filename = f'corpus.{language}.tex'
        result = subprocess.run(
            ['xelatex', '-interaction=nonstopmode', '-halt-on-error', filename],
            cwd=output, env=env, capture_output=True, text=True, check=False,
        )
        log = (output / filename.replace('.tex', '.log')).read_text(errors='replace')
        (output / f'corpus.{language}.stdout').write_text(result.stdout + result.stderr)
        if result.returncode != 0 or 'Missing character:' in log:
            raise RuntimeError(f'{language}: XeLaTeX failed or missing glyphs; see {output / filename.replace(".tex", ".log")}')
        print(f'{language}: XeLaTeX passed, no missing glyphs', flush=True)
        return language

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        list(pool.map(compile_pdf, locales))
    print('All ten generated corpus documents compiled.', flush=True)


if __name__ == '__main__':
    main()
