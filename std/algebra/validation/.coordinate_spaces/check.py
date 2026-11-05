"""Check native finite coordinate spaces and their scalar/index boundaries."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
spec = importlib.util.spec_from_file_location('standard_field_checks', HERE.parent / '.standard_fields/check.py')
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)

def boundaries():
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'main.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    cases = [(source, True) for source in ['release obj def main::u', 'release obj def main::empty_vector', 'release obj def main::plane', 'release struct def main::plane', 'main::u(2)=2']] + [('let invalid_empty_coordinate=main::empty_vector(1)', False), ('main::u(2)=2', True), ('let invalid_real_scalar=main::plane.smul(i,main::u)', False), ('main::plane.smul(2,main::u) $in finite_seq(R,2)', True), ('main::u(2)=3', False), ('main::u(2)=2', True)]
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
                obligation = data['errors'][0].get('obligation', '')
                if 'invalid_empty_coordinate' in source:
                    assert '1 $in closed_range(1, 0)' in obligation, data
                elif 'invalid_real_scalar' in source:
                    assert 'i $in R' in obligation, data
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
    print('Coordinate-space Session: 3 expected refusals; valid use retained', flush=True)
    return {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True}

def main():
    gates = {'source': common.successful_file(ROOT / 'std/algebra/finite_span.lit'), 'imported_consumer': common.successful_file(HERE / 'main.lit'), 'boundaries': boundaries(), 'binary_sha256': hashlib.sha256(common.BINARY.read_bytes()).hexdigest()}
    assert gates['source']['binary_sha256'] == gates['imported_consumer']['binary_sha256'] == gates['binary_sha256'], 'Binary changed between gates'
if __name__ == '__main__':
    main()
