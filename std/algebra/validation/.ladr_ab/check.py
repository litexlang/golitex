"""Validate selected additive inverses and the LADR 1.32 identity."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
spec = importlib.util.spec_from_file_location('std_checks', HERE.parent / '.standard_fields/check.py')
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)

def boundaries():
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'main.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = 'main::u(2)=2'
    cases = [(s, True) for s in ['release obj def main::u', 'release obj def main::inverse', 'release obj def main::negative_empty', valid]] + [('main::inverse(2)=2', False), (valid, True), ('let wrong_carrier=\\Algebra::vector_space::vector_neg<R,Algebra::field::real_field,finite_seq(R,2),main::plane>(main::z)', False), (valid, True), ('let empty_point=main::negative_empty(1)', False), (valid, True)]
    records = []
    try:
        for source, expected in cases:
            process.stdin.write(source + '\n\n')
            process.stdin.flush()
            data = common.read_response(process)
            assert data['kind'] == 'run' and data['target'] == 'repl', data
            assert not data['session_terminated'] and data['termination'] is None, data
            assert (data['run_result'] == 'success') == expected, (source, data)
            assert len(data['statement_results']) == 1, data
            assert data['statement_results'][0]['statement_result'] == ('accepted' if expected else 'rejected'), data
            assert len(data['errors']) == (0 if expected else 1), data
            if not expected:
                assert data['errors'][0]['phase'] == 'search_proof', data
            records.append({'source': source, 'expected_success': expected, 'errors': data['errors']})
        process.stdin.write('exit\n')
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1), process.returncode
        assert final['run_result'] == 'failure' and len(final['errors']) == 3, final
        assert not final['session_terminated'] and final['termination'] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    print('Selected inverse Session: 3 expected refusals; accepted context retained', flush=True)
    return {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True}

def main():
    gates = {'source': common.successful_file(ROOT / 'std/algebra/vector_space.lit'), 'imported_consumer': common.successful_file(HERE / 'main.lit'), 'boundaries': boundaries(), 'binary_sha256': hashlib.sha256(common.BINARY.read_bytes()).hexdigest()}
    assert gates['source']['binary_sha256'] == gates['imported_consumer']['binary_sha256'] == gates['binary_sha256']
if __name__ == '__main__':
    main()
