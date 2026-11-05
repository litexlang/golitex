"""Check basis and dependence converses, including their necessary premises."""
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
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'basis_characterization_use.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    valid = '$Algebra::basis::is_linearly_dependent(R,Algebra::field::real_field,R,basis_characterization_use::basis_check_space,4,basis_characterization_use::basis_check_vectors)'
    cases = [(source, True) for source in ['release obj def Algebra::field::real_field', 'release obj def basis_characterization_use::basis_check_space', 'release obj def basis_characterization_use::basis_check_vectors', 'release obj def basis_characterization_use::basis_check_empty', valid]] + [('release thm Algebra::basis_characterization::unique_representations_imply_basis(R,Algebra::field::real_field,R,basis_characterization_use::basis_check_space,4,basis_characterization_use::basis_check_vectors)', False), (valid, True), ('release thm Algebra::basis_characterization::nontrivial_dependence_coefficients_imply_dependent(R,Algebra::field::real_field,R,basis_characterization_use::basis_check_space,0,basis_characterization_use::basis_check_empty)', False), (valid, True), ('$Algebra::basis::is_linearly_independent(R,Algebra::field::real_field,R,basis_characterization_use::basis_check_space,4,basis_characterization_use::basis_check_vectors)', False), (valid, True)]
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
    paths = [common.BINARY, ROOT / 'std/algebra/basis_characterization.lit', HERE / 'basis_characterization_use.lit']
    hashes = [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    data = {'source': sums.file_gate(paths[1]), 'imported_consumer': sums.file_gate(paths[2]), 'boundaries': boundaries(), 'binary_sha256': hashes[0]}
    assert hashes == [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths]
    print('Basis characterizations: source/import gates and three refusals passed', flush=True)
if __name__ == '__main__':
    main()
