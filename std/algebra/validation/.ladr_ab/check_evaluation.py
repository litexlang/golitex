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
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'evaluation_use.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = '\\Algebra::vector_space::function_evaluation<R,R,3>(fn(t R) R {t^2})=9'
    valid_complex = '\\Algebra::vector_space::function_evaluation<C,C,i>(fn(t C) C {t^2})=-1'
    cases = [(s, True) for s in ['release thm Algebra::vector_space::function_evaluation_spec(R,R,3,fn(t R) R {t^2})', 'release thm Algebra::vector_space::function_evaluation_spec(C,C,i,fn(t C) C {t^2})', valid, valid_complex]] + [('let invalid_real_evaluation=\\Algebra::vector_space::function_evaluation<R,R,i>', False), (valid, True), ('let invalid_empty_evaluation=\\Algebra::vector_space::function_evaluation<{},R,0>', False), (valid, True), ('\\Algebra::vector_space::function_evaluation<C,C,i>(fn(t C) C {t^2})=1', False), (valid_complex, True)]
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
                if 'invalid_real_evaluation' in source:
                    assert error['phase'] == 'requirement' and error.get('obligation') == 'i $in R', data
                elif 'invalid_empty_evaluation' in source:
                    assert error['phase'] == 'requirement' and error.get('obligation') == '0 $in {}', data
                else:
                    assert error['phase'] == 'search_proof', data
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
    print('Evaluation Session: invalid points and false square rejected; context retained', flush=True)
    return {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True}

def main():
    source_before = hashlib.sha256((HERE / 'evaluation_use.lit').read_bytes()).hexdigest()
    before = hashlib.sha256(common.BINARY.read_bytes()).hexdigest()
    polynomial_before = hashlib.sha256((ROOT / 'std/algebra/vector_space.lit').read_bytes()).hexdigest()
    gates = {'source': sums.file_gate(ROOT / 'std/algebra/vector_space.lit'), 'imported_consumer': sums.file_gate(HERE / 'evaluation_use.lit'), 'boundaries': boundaries(), 'binary_sha256': before, 'source_sha256': source_before}
    assert hashlib.sha256(common.BINARY.read_bytes()).hexdigest() == before
    assert hashlib.sha256((HERE / 'evaluation_use.lit').read_bytes()).hexdigest() == source_before, 'Consumer changed during verification'
    assert hashlib.sha256((ROOT / 'std/algebra/vector_space.lit').read_bytes()).hexdigest() == polynomial_before, 'Polynomial source changed during verification'
    assert gates['source']['binary_sha256'] == gates['imported_consumer']['binary_sha256'] == before
if __name__ == '__main__':
    main()
