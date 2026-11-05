"""Check pair directness, a proper ambient sum and continued Session use."""
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
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'pair_use.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = 'continuation_marker+1=3'
    cases = [(s, True) for s in ['release obj def Algebra::field::real_field', 'release struct def Algebra::field::real_field', 'release obj def main::plane', 'release struct def main::plane', 'have continuation_marker R=2', 'have bad_length_family finite_seq(power_set(finite_seq(R,2)),3)=fn(j closed_range(1,3)) power_set(finite_seq(R,2)) {{main::plane.zero}}']] + [('release thm Algebra::subspace_sums::trivial_pair_intersection_implies_direct(R,Algebra::field::real_field,finite_seq(R,2),main::plane,bad_length_family)', False), (valid, True), ('pair_use::proper_sum=finite_seq(R,2)', False), (valid, True), ('2=0', False), (valid, True)]
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
                if 'trivial_pair_intersection' in source:
                    assert error['phase'] == 'argument_type', data
                    assert 'finite_seq' in error.get('obligation', ''), data
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
    print('Pair-family Session: wrong length and two false equalities rejected; context retained', flush=True)
    return {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True}

def main():
    gates = {'sum_source': sums.file_gate(ROOT / 'std/algebra/finite_span.lit'), 'family_source': sums.file_gate(ROOT / 'std/algebra/subspace_sums.lit'), 'imported_consumer': sums.file_gate(HERE / 'pair_use.lit'), 'boundaries': boundaries(), 'binary_sha256': hashlib.sha256(common.BINARY.read_bytes()).hexdigest()}
    assert all((gates[k]['binary_sha256'] == gates['binary_sha256'] for k in ('sum_source', 'family_source', 'imported_consumer')))
if __name__ == '__main__':
    main()
