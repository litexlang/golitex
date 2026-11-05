"""Check expansion of the original polynomial-set carrier into selector domains."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
USE = HERE / 'membership_use'
spec = importlib.util.spec_from_file_location('degree_checks', HERE / 'check_degree.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
common = base.common

def boundaries():
    prefix = [block for block in (USE / 'main.lit').read_text().strip().split('\n\n') if block.strip() and (not block.lstrip().startswith('#'))]
    assert len(prefix) == 28 == 28
    canonical = '# Independent use from the original named polynomial-set carrier.\n\n'
    canonical += '\n\n'.join(prefix)
    assert (USE / 'main.lit').read_text().strip() == canonical.strip()
    expected = [('release thm '
                 'membership::complex_polynomial_definition_membership(unproven_complex_function)',
                 False),
                ('member_complex_degree $in Polynomials::degree_value::PolynomialDegree',
                 True),
                ('let '
                 'unproved_complex_degree=degree::complex_polynomial_degree(unproven_complex_function)',
                 False),
                ('member_complex_degree $in Polynomials::degree_value::PolynomialDegree',
                 True),
                ('release thm '
                 'membership::real_polynomial_definition_membership(unproven_real_function)',
                 False),
                ('member_real_degree $in Polynomials::degree_value::PolynomialDegree', True),
                ('let '
                 'unproved_real_degree=degree::real_polynomial_degree(unproven_real_function)',
                 False),
                ('member_real_degree $in Polynomials::degree_value::PolynomialDegree', True)]
    digest = hashlib.sha256(json.dumps([prefix, expected]).encode()).hexdigest()
    before = base.checks.snapshot(USE)
    declaration = re.compile('^(?:have (?:fn )?|let )([A-Za-z][A-Za-z0-9_]*)')
    names = [declaration.match(s).group(1) for s in prefix if declaration.match(s)]
    assert len(names) == len(set(names)) == 6, names
    pattern = re.compile('\\b(' + '|'.join(sorted(names, key=len, reverse=True)) + ')\\b')

    def qualify(source):
        return pattern.sub(lambda match: 'main::' + match.group(), source)
    cases = []
    for source in prefix:
        match = declaration.match(source)
        cases.append(('release obj def main::' + match.group(1), True) if match else (qualify(source), True))
    cases += [(qualify(source), success) for source, success in expected]
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(USE / 'main.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    records = []
    try:
        for source, expected_success in cases:
            process.stdin.write(source + '\n\n')
            process.stdin.flush()
            data = common.read_response(process)
            assert data['kind'] == 'run' and data['target'] == 'repl', data
            assert not data['session_terminated'] and data['termination'] is None, data
            assert (data['run_result'] == 'success') == expected_success, {'source': source, 'result': data['run_result'], 'errors': data['errors']}
            assert len(data['statement_results']) == 1, data
            assert len(data['errors']) == (0 if expected_success else 1), data
            if not expected_success:
                assert data['errors'][0]['phase'] in ('argument_type', 'search_proof'), data
            records.append({'source': source, 'expected_success': expected_success, 'errors': data['errors']})
        process.stdin.write('exit\n')
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final['run_result'] == 'failure' and len(final['errors']) == 4, final
        assert not final['session_terminated'] and final['termination'] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == base.checks.snapshot(USE)
    data = {'command': command, 'checks': records, 'expected_refusals': 4, 'context_retained': True, 'case_source_sha256': digest, 'snapshot': before}
    return data

def main():
    source = base.file_gate(base.checks.MODULE / 'membership.lit', base.checks.MODULE)
    imported = base.file_gate(USE / 'main.lit', USE)
    boundary = boundaries()
    result = {'source': source, 'imported_consumer': imported, 'boundaries': boundary, 'registered_predecessor_statements': 87, 'total_module_statements': 94}
    print(f"Polynomial membership: {source['statements']} source / {imported['statements']} imported / 4 refusal controls passed")
if __name__ == '__main__':
    main()
