"""Check the standard scalar instances, imported use and guarded inverses."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BINARY = Path(os.environ.get('LITEX_CHECK_BINARY', str(ROOT / 'target/release/litex')))
ENV = {**os.environ, 'LITEX_STD_PATH': str(ROOT / 'std')}

def successful_file(path):
    source_before = hashlib.sha256(path.read_bytes()).hexdigest()
    binary_before = hashlib.sha256(BINARY.read_bytes()).hexdigest()
    command = [str(BINARY), '-lang', 'en', '-strict', '-f', str(path)]
    result = subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=600)
    data = json.loads(result.stdout)
    assert result.returncode == 0 and data['kind'] == 'run', data
    assert data['run_result'] == 'success' and (not data['errors']), data
    assert not data['session_terminated'] and data['termination'] is None, data
    assert all((s['statement_result'] == 'accepted' for s in data['statement_results'])), data
    assert hashlib.sha256(BINARY.read_bytes()).hexdigest() == binary_before, 'Binary changed during verification'
    assert hashlib.sha256(path.read_bytes()).hexdigest() == source_before, 'Source changed during verification'
    record = {'command': command, 'exit_code': result.returncode, 'kind': data['kind'], 'run_result': data['run_result'], 'session_terminated': data['session_terminated'], 'termination': data['termination'], 'statements': len(data['statement_results']), 'all_statements_accepted': True, 'errors': data['errors'], 'source_sha256': source_before, 'binary_sha256': binary_before}
    print(f"{path.relative_to(ROOT)}: {record['statements']} accepted", flush=True)
    return record

def read_response(process):
    chunks = []
    while True:
        line = process.stdout.readline()
        assert line, 'Session ended before a complete response'
        chunks.append(line)
        try:
            return json.loads(''.join(chunks))
        except json.JSONDecodeError:
            pass

def inverse_boundaries():
    command = [str(BINARY), '-lang', 'en', '-strict', '-f', str(ROOT / 'std/algebra/field.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    prefix = ['release obj def field::real_inv',
              'release obj def field::complex_inv',
              'release obj def field::complex_mul',
              'release obj def field::real_field',
              'release obj def field::complex_field',
              'release struct def field::real_field',
              'release struct def field::complex_field',
              'field::real_field.zero=0',
              'field::complex_field.zero=0']
    checks = [(source, True) for source in prefix] + [('let invalid_real_inverse=field::real_field.inv(0)', False), ('field::real_field.inv(2)=1/2', True), ('let invalid_complex_inverse=field::complex_field.inv(0)', False), ('field::complex_field.inv(i)=-i', True), ('field::complex_field.mul(i,i)=1', False), ('field::complex_field.mul(i,i)=-1', True), ('field::real_field.inv(-2)=-1/2', True)]
    records = []
    try:
        for source, expected in checks:
            process.stdin.write(source + '\n\n')
            process.stdin.flush()
            data = read_response(process)
            assert data['kind'] == 'run' and data['target'] == 'repl', data
            assert not data['session_terminated'] and data['termination'] is None, data
            assert (data['run_result'] == 'success') == expected, (source, data)
            statements = data['statement_results']
            assert len(statements) == 1, data
            assert statements[0]['statement_result'] == ('accepted' if expected else 'rejected'), data
            if expected:
                assert not data['errors'], data
            else:
                assert len(data['errors']) == 1, data
                assert data['errors'][0]['phase'] == 'search_proof', data
                if 'inverse=' in source:
                    obligation = data['errors'][0]['obligation']
                    assert '0 != ' in obligation and '.zero' in obligation, data
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
    print('Session: 3 expected refusals; every following valid statement accepted', flush=True)
    return {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True}

def main():
    gates = {'field_source': successful_file(ROOT / 'std/algebra/field.lit'), 'imported_consumer': successful_file(HERE / 'main.lit'), 'boundaries': inverse_boundaries(), 'binary_sha256': hashlib.sha256(BINARY.read_bytes()).hexdigest()}
    assert gates['field_source']['binary_sha256'] == gates['imported_consumer']['binary_sha256'] == gates['binary_sha256'], 'Binary changed between gates'
if __name__ == '__main__':
    main()
