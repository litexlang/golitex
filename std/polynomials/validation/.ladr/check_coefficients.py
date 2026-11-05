"""Recheck native R/C polynomial coefficient interfaces and their premises."""
import configparser
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MODULE = ROOT / 'std/polynomials'
USE = HERE / 'use'
spec = importlib.util.spec_from_file_location('std_checks', ROOT / 'std/algebra/validation/.standard_fields/check.py')
common = importlib.util.module_from_spec(spec)
spec.loader.exec_module(common)

def module_paths(module, seen=None):
    seen = set() if seen is None else seen
    module = module.resolve()
    if module in seen:
        return []
    seen.add(module)
    manifest = module / 'litex.config'
    config = configparser.ConfigParser(interpolation=None)
    config.read(manifest)
    paths = [manifest]
    if config.has_section('import std'):
        for _, name in config.items('import std'):
            paths += module_paths(ROOT / 'std' / name.strip('"'), seen)
    if config.has_section('import'):
        for _, name in config.items('import'):
            paths += module_paths(module / name.strip('"'), seen)
    paths += [(module / name.strip('"')).resolve() for _, name in config.items('export')]
    return paths

def snapshot(module):
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in module_paths(module)} | {'binary': hashlib.sha256(common.BINARY.read_bytes()).hexdigest()}

def file_gate(path, module):
    before = snapshot(module)
    data = common.successful_file(path)
    assert before == snapshot(module), 'Consumed sources changed during verification'
    data['snapshot'] = before
    return data

def boundaries():
    before = snapshot(USE)
    names = tuple((kind + suffix for kind in ('complex', 'real') for suffix in ('_constant_coefficients', '_trailing_coefficients', '_constant_terms', '_zero_constant_coefficients')))
    pattern = re.compile('\\b(' + '|'.join(names) + ')\\b')

    def qualify(source):
        return pattern.sub(lambda match: 'main::' + match.group(), source)
    prefix = [block for block in (USE / 'main.lit').read_text().strip().split('\n\n') if block.strip() and (not block.lstrip().startswith('#'))]
    cases = [('release obj def main::' + name, True) for name in names]
    cases += [(qualify(s), True) for s in prefix if not s.startswith('have ')]
    cases += [(qualify(r['source']), r['expected_success']) for r in [{'source': 'release thm Polynomials::coefficients::complex_polynomial_leading_bounds_unique(0,3,complex_constant_coefficients,complex_trailing_coefficients)', 'expected_success': False}, {'source': 'complex_constant_coefficients(1)=i', 'expected_success': True}, {'source': 'release thm Polynomials::coefficients::complex_polynomial_coefficients_unique(0,3,complex_constant_coefficients,complex_trailing_coefficients,2)', 'expected_success': False}, {'source': 'complex_constant_coefficients(1)=i', 'expected_success': True}, {'source': 'release thm Polynomials::coefficients::complex_polynomial_coefficient_vector_unique(0,complex_constant_coefficients,complex_zero_constant_coefficients)', 'expected_success': False}, {'source': 'complex_constant_coefficients(1)=i', 'expected_success': True}, {'source': 'release thm Polynomials::coefficients::real_polynomial_leading_bounds_unique(0,3,real_constant_coefficients,real_trailing_coefficients)', 'expected_success': False}, {'source': 'real_constant_coefficients(1)=-3', 'expected_success': True}, {'source': 'release thm Polynomials::coefficients::real_polynomial_coefficients_unique(0,3,real_constant_coefficients,real_trailing_coefficients,2)', 'expected_success': False}, {'source': 'real_constant_coefficients(1)=-3', 'expected_success': True}, {'source': 'release thm Polynomials::coefficients::real_polynomial_coefficient_vector_unique(0,real_constant_coefficients,real_zero_constant_coefficients)', 'expected_success': False}, {'source': 'real_constant_coefficients(1)=-3', 'expected_success': True}]]
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(USE / 'main.lit'), '-session']
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
                assert data['errors'][0]['phase'] == 'premise', data
            records.append({'source': source, 'expected_success': expected, 'errors': data['errors']})
        process.stdin.write('exit\n')
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final['run_result'] == 'failure' and len(final['errors']) == 6, final
        assert not final['session_terminated'] and final['termination'] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == snapshot(USE), 'Consumed sources changed during Session'
    data = {'command': command, 'checks': records, 'expected_refusals': 6, 'context_retained': True, 'snapshot': before}
    return data

def main():
    source = file_gate(MODULE / 'coefficients.lit', MODULE)
    imported = file_gate(USE / 'main.lit', USE)
    boundary = boundaries()
    result = {'source': source, 'imported_consumer': imported, 'boundaries': boundary}
    print(f"Native polynomial coefficients: {source['statements']} source / {imported['statements']} imported / 6 refusal controls passed")
if __name__ == '__main__':
    main()
