"""Check constant-coefficient laws and guarded linear-root existence."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sum_checks', HERE / 'check_sums.py')
sums = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sums)
common = sums.common
ROOT = sums.ROOT

def boundaries():
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'polynomial_zero_use.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = '\\Algebra::polynomial::complex_polynomial_value<1>(polynomial_zero_use::zero_check_complex_coefficients,0)=1+i'
    cases = [(source, True) for source in ['release obj def polynomial_zero_use::zero_check_complex_coefficients', 'release obj def polynomial_zero_use::zero_check_constant_coefficients', 'release obj def polynomial_zero_use::zero_check_real_coefficients', 'release obj def polynomial_zero_use::zero_check_other_coefficients', valid]] + [('release thm Algebra::polynomial::complex_linear_polynomial_has_root(polynomial_zero_use::zero_check_constant_coefficients)', False), (valid, True), ('\\Algebra::polynomial::complex_polynomial_value<1>(polynomial_zero_use::zero_check_complex_coefficients,0)=0', False), (valid, True), ('\\Algebra::polynomial::real_polynomial_from_coefficients<1>(polynomial_zero_use::zero_check_real_coefficients)=\\Algebra::polynomial::real_polynomial_from_coefficients<1>(polynomial_zero_use::zero_check_other_coefficients)', False), (valid, True)]
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
            assert len(data['errors']) == (0 if expected else 1), data
            if not expected:
                assert data['errors'][0]['phase'] in ('premise', 'search_proof'), data
            records.append({'source': source, 'expected_success': expected, 'errors': data['errors']})
        process.stdin.write('exit\n')
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final['run_result'] == 'failure' and len(final['errors']) == 3, final
        assert not final['session_terminated'] and final['termination'] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    return {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True}

def main():
    paths = [common.BINARY, ROOT / 'std/algebra/polynomial.lit', HERE / 'polynomial_zero_use.lit']
    hashes = [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    data = {'source': sums.file_gate(paths[1]), 'imported_consumer': sums.file_gate(paths[2]), 'boundaries': boundaries(), 'binary_sha256': hashes[0]}
    assert hashes == [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    print('Polynomial constant coefficients and linear roots: all gates passed', flush=True)
if __name__ == '__main__':
    main()
