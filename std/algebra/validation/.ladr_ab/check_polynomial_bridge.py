"""Check first-class evaluation, linearity and point-domain boundaries."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
spec = importlib.util.spec_from_file_location('sum_checks', HERE / 'check_sums.py')
sums = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sums)
common = sums.common

def boundaries():
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'polynomial_bridge_use.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = '\\Algebra::polynomial::complex_monomials<0>(1)(0)=1'
    cases = [(s, True) for s in ['release thm Algebra::polynomial::complex_monomials_carrier(0)', 'release thm Algebra::polynomial::complex_monomials_entry(0,1,0)', 'release thm Algebra::polynomial::complex_monomials_carrier(2)', 'release thm Algebra::polynomial::complex_monomials_entry(2,3,i)', valid]] + [('let invalid_zero=\\Algebra::polynomial::complex_monomials<2>(0)', False), (valid, True), ('let invalid_two=\\Algebra::polynomial::complex_monomials<0>(2)', False), (valid, True), ('\\Algebra::polynomial::complex_monomials<2>(3)(i)=1', False), (valid, True)]
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
                error = data['errors'][0]
                assert error['phase'] == 'search_proof', data
                if 'invalid_zero' in source:
                    assert error.get('obligation', '').startswith('0 $in closed_range'), data
                elif 'invalid_two' in source:
                    assert error.get('obligation', '').startswith('2 $in closed_range'), data
                else:
                    assert error.get('obligation', '').endswith(' = 1'), data
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
    print('Monomial Session: invalid indices and false square rejected; context retained', flush=True)
    return {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True}

def main():
    binary_before = hashlib.sha256(common.BINARY.read_bytes()).hexdigest()
    consumer_before = hashlib.sha256((HERE / 'polynomial_bridge_use.lit').read_bytes()).hexdigest()
    source_before = hashlib.sha256((ROOT / 'std/algebra/polynomial.lit').read_bytes()).hexdigest()
    data = {'boundaries': boundaries(), 'binary_sha256': binary_before, 'consumer_sha256': consumer_before, 'source_sha256': source_before}
    assert hashlib.sha256(common.BINARY.read_bytes()).hexdigest() == binary_before
    assert hashlib.sha256((HERE / 'polynomial_bridge_use.lit').read_bytes()).hexdigest() == consumer_before
    assert hashlib.sha256((ROOT / 'std/algebra/polynomial.lit').read_bytes()).hexdigest() == source_before
if __name__ == '__main__':
    main()
