#!/usr/bin/env python3
"""Produce real CLI bundles for the mathematical reading acceptance tests."""
import argparse
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/release/litex')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    cases = [('proof', ROOT / 'examples/stmt_nodes/compile_to_latex/structured_proof_layout.lit', True),
             ('duplicate', 'claim:\n    ? 1=1\n    1=1\n1=1\n', True),
             ('failed', '1=1\n1=2\nhave\n3=3\n', True)]
    for locale in ['en', 'zh']:
        for name, source, strict in cases:
            command = [str(args.binary.resolve()), '-reading', '-latex', '-json', '-lang', locale]
            command += ['-f', str(source)] if isinstance(source, Path) else ['-e', source]
            if strict:
                command.append('-strict')
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            assert result.returncode in (0, 1), result.stderr
            bundle = json.loads(result.stdout)
            assert bundle['kind'] == 'reading' and bundle['reading_layout'] == 'latex'
            assert (bundle['run_result'] == 'success') == (name != 'failed')
            (args.output / f'{name}-{locale}.json').write_text(result.stdout)
    for source in sorted((ROOT / 'examples/test_statements').glob('*.lit')):
        result = subprocess.run([str(args.binary.resolve()), '-reading', '-latex', '-json',
                                 '-lang', 'en', '-f', str(source)], cwd=ROOT,
                                capture_output=True, text=True)
        assert result.returncode in (0, 1), result.stderr
        bundle = json.loads(result.stdout)
        assert bundle['reading_layout'] == 'latex'
        (args.output / f'type-{source.stem}.json').write_text(result.stdout)
    print(f'Wrote native mathematical reading bundles to {args.output}')


if __name__ == '__main__':
    main()
