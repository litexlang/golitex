"""Check the full imported consumer and share one strict Session for refusals."""

import argparse
import json
import os
from pathlib import Path
import selectors
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BINARY = ROOT / 'target/release/litex'
ENV = {**os.environ, 'LITEX_STD_PATH': str(ROOT / 'std')}
REFUSALS = [
    ('decrease_below_root', 'premise'),
    ('error_bound_before_first_step', 'premise'),
    ('initial_step_may_increase', 'search_proof'),
    ('negative_iteration_index', 'argument_type'),
    ('quadratic_bound_below_root', 'premise'),
    ('zero_initial_value', 'argument_type'),
    ('zero_radicand', 'argument_type'),
]


def envelope(data):
    assert data['kind'] == 'run', data
    assert data['session_terminated'] is False, data
    assert data['termination'] is None, data


def positive():
    result = subprocess.run(
        [str(BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'main.lit')],
        cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=600,
    )
    data = json.loads(result.stdout)
    envelope(data)
    assert result.returncode == 0 and data['run_result'] == 'success', data
    assert not data['errors'] and data['statement_results'], data
    assert all(s['statement_result'] == 'accepted' for s in data['statement_results']), data
    print('main.lit: accepted', flush=True)


def refusals():
    process = subprocess.Popen(
        [str(BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'negative/context.lit'), '-session'],
        cwd=ROOT, env=ENV, text=True, stdin=subprocess.PIPE,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=1,
    )
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)

    def receive():
        assert selector.select(600), 'Verifier response timed out'
        raw = ''
        while True:
            line = process.stdout.readline()
            if not line:
                raise RuntimeError('Verifier exited before returning a complete JSON response')
            raw += line
            try:
                return json.loads(raw)
            except json.JSONDecodeError:
                pass

    try:
        for name, expected_phase in REFUSALS:
            path = HERE / 'negative' / (name + '.lit')
            statements = [s.strip() for s in path.read_text().split('\n\n') if s.strip()]
            assert statements, path
            for index, source in enumerate(statements):
                process.stdin.write(source + '\n\n')
                process.stdin.flush()
                data = receive()
                envelope(data)
                assert data['target'] == 'repl', data
                assert len(data['statement_results']) == 1, data
                if index < len(statements) - 1:
                    assert data['run_result'] == 'success' and not data['errors'], (path, index, data)
                    assert data['statement_results'][0]['statement_result'] == 'accepted', data
                else:
                    assert data['run_result'] == 'failure', (path, data)
                    assert data['statement_results'][0]['statement_result'] == 'rejected', data
                    assert len(data['errors']) == 1, data
                    assert data['errors'][0]['statement_index'] == 0, data
                    assert data['errors'][0]['phase'] == expected_phase, (path, data)
            print(f'negative/{name}.lit: {expected_phase} rejected', flush=True)
        process.stdin.write('exit\n')
        process.stdin.flush()
        aggregate = receive()
        envelope(aggregate)
        assert len(aggregate['errors']) == len(REFUSALS), aggregate
        assert process.wait(timeout=30) in (0, 1), process.returncode
    finally:
        selector.close()
        if process.poll() is None:
            process.kill()
        process.communicate(timeout=30)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-only', action='store_true')
    args = parser.parse_args()
    if not args.negative_only:
        positive()
    refusals()


if __name__ == '__main__':
    main()
