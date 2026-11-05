"""Check imported scalar function spaces and their exact-domain boundaries."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
helper_path = HERE.parent / '.standard_fields/check.py'
spec = importlib.util.spec_from_file_location('standard_field_checks', helper_path)
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)

def boundaries():
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'main.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    real = 'Algebra::field::real_field'
    add = '\\Algebra::vector_space::function_add<R,' + real + ',N>'
    zero_empty = '\\Algebra::vector_space::function_zero<R,' + real + ',{}>'
    calculation = add + '(main::sequence,main::sequence)(3)=' + real + '.add(main::sequence(3),main::sequence(3))=' + real + '.add(3,3)=Algebra::field::real_add(3,3)=6'
    cases = [(source, True) for source in ['release obj def Algebra::field::real_add', 'release obj def Algebra::field::real_field', 'release struct def Algebra::field::real_field', 'release obj def main::sequence', 'main::sequence(3)=3']] + [('let invalid_empty_point=' + zero_empty + '(0)', False), (calculation, True), ('have fn full_real_function(x R) R=x', True), ('let invalid_domain_sum=' + add + '(full_real_function,main::sequence)', False), (calculation, True), (add + '(main::sequence,main::sequence)(3)=7', False), (calculation, True)]
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
            if expected:
                assert not data['errors'], data
            else:
                assert len(data['errors']) == 1, data
                assert data['errors'][0]['phase'] == 'search_proof', data
                obligation = data['errors'][0]['obligation']
                if 'invalid_empty_point' in source:
                    assert '0 $in {}' in obligation, data
                elif 'invalid_domain_sum' in source:
                    assert 'full_real_function $in fn' in obligation, data
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
    print('Function-space Session: 3 expected refusals; valid calculations retained', flush=True)
    return {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True}

def main():
    gates = {'source': common.successful_file(ROOT / 'std/algebra/vector_space.lit'), 'imported_consumer': common.successful_file(HERE / 'main.lit'), 'boundaries': boundaries(), 'binary_sha256': hashlib.sha256(common.BINARY.read_bytes()).hexdigest()}
    assert gates['source']['binary_sha256'] == gates['imported_consumer']['binary_sha256'] == gates['binary_sha256'], 'Binary changed between gates'
if __name__ == '__main__':
    main()
