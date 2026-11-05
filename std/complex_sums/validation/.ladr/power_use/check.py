"""Check native complex power coefficients and the exact hypotheses they require."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
spec = importlib.util.spec_from_file_location('std_checks', ROOT / 'std/algebra/validation/.standard_fields/check.py')
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)
MODULE = ROOT / 'std/complex_sums'
SOURCE_PATHS = [MODULE / name for name in ('litex.config', 'main.lit', 'growth.lit', 'coefficients.lit')]
USE_PATHS = SOURCE_PATHS + [HERE / 'litex.config', HERE / 'main.lit']

def snapshot(paths):
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths} | {'binary': hashlib.sha256(common.BINARY.read_bytes()).hexdigest()}

def file_gate(path, paths):
    before = snapshot(paths)
    data = common.successful_file(path)
    assert snapshot(paths) == before, 'Consumed sources changed during verification'
    data['snapshot'] = before
    return data

def boundaries(force=False):
    before = snapshot(USE_PATHS)
    prefix = [block for block in (HERE / 'main.lit').read_text().strip().split('\n\n') if block.strip() and (not block.lstrip().startswith('#'))]
    assert len(prefix) == 64
    names = ('linear_coefficients',
             'linear_value',
             'padded_coefficients',
             'padded_for_representation',
             'empty_coefficients',
             'zero_value',
             'zero_terms',
             'zero_coefficients')
    pattern = re.compile('\\b(' + '|'.join(names) + ')\\b')

    def qualify(source):
        return pattern.sub(lambda match: 'main::' + match.group(), source)
    cases = [('release obj def main::' + name, True) for name in names[:-1]]
    cases += [(qualify(s), True) for s in prefix if not s.startswith(('have ', 'template<'))]
    cases += [(qualify(r['source']), r['expected_success']) for r in [{'source': 'let invalid_shrinking_padding=\\ComplexSums::coefficients::complex_finite_sequence_zero_padding<2,1,linear_coefficients>', 'expected_success': False}, {'source': 'linear_coefficients(1)=i', 'expected_success': True}, {'source': 'let invalid_padding_index=\\ComplexSums::coefficients::complex_finite_sequence_zero_padding<2,4,linear_coefficients>(0)', 'expected_success': False}, {'source': 'linear_coefficients(1)=i', 'expected_success': True}, {'source': 'release thm ComplexSums::growth::complex_power_representation_has_nonzero_value(3,padded_for_representation,linear_value)', 'expected_success': False}, {'source': 'linear_coefficients(1)=i', 'expected_success': True}, {'source': 'release thm ComplexSums::growth::complex_zero_power_representation_coefficients(1,linear_coefficients,linear_value,1)', 'expected_success': False}, {'source': 'linear_coefficients(1)=i', 'expected_success': True}, {'source': 'release thm ComplexSums::growth::complex_power_representation_coefficients_unique(1,linear_coefficients,\\zero_coefficients<1>,linear_value,1)', 'expected_success': False}, {'source': 'linear_coefficients(1)=i', 'expected_success': True}, {'source': 'release thm ComplexSums::coefficients::complex_finite_sequence_zero_padding_head(2,4,linear_coefficients,3)', 'expected_success': False}, {'source': 'linear_coefficients(1)=i', 'expected_success': True}, {'source': 'linear_coefficients(1)=0', 'expected_success': False}, {'source': 'linear_coefficients(1)=i', 'expected_success': True}]]
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(HERE / 'main.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
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
                assert data['errors'][0]['phase'] in ('requirement', 'search_proof', 'premise'), data
            records.append({'source': source, 'expected_success': expected, 'errors': data['errors']})
        process.stdin.write('exit\n')
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final['run_result'] == 'failure' and len(final['errors']) == 7, final
        assert not final['session_terminated'] and final['termination'] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert snapshot(USE_PATHS) == before, 'Consumed sources changed during Session'
    data = {'origin': 'clean_retained_session', 'command': command, 'checks': records, 'expected_refusals': 7, 'context_retained': True, 'snapshot': before}
    return data

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--refresh-boundaries', action='store_true')
    args = parser.parse_args()
    source = file_gate(MODULE / 'coefficients.lit', SOURCE_PATHS)
    imported = file_gate(HERE / 'main.lit', USE_PATHS)
    boundary = boundaries(args.refresh_boundaries)
    result = {'source': source, 'imported_consumer': imported, 'boundaries': boundary}
    print(f"Complex power coefficients: {source['statements']} source / {imported['statements']} imported / 7 refusal controls passed")
if __name__ == '__main__':
    main()
