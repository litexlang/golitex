"""Check the actual linear-map VectorSpace and its pointwise interfaces."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MODULE = ROOT / 'std/linear_maps'
USE = HERE / 'space_use'
spec = importlib.util.spec_from_file_location('linear_checks', HERE / 'check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
base = checks.base
common = checks.common

def boundaries():
    prefix = [block for block in (USE / 'main.lit').read_text().strip().split('\n\n') if block.strip() and (not block.lstrip().startswith('#'))]
    assert len(prefix) == 121 == 121
    canonical = '# Independent actual linear-map space consumers.\n\n'
    canonical += '\n\n'.join(prefix)
    assert (USE / 'main.lit').read_text().strip() == canonical.strip()
    expected = [('release thm '
                 'space::linear_map_belongs_to_carrier(R,Algebra::field::real_field,R,\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,R,\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,nonlinear_real_function)',
                 False),
                ('complex_sum(1+i)=2*i', True),
                ('release thm '
                 'space::linear_map_carrier_specification(R,Algebra::field::real_field,R,\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,R,\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,nonlinear_real_function)',
                 False),
                ('complex_sum(1+i)=2*i', True),
                ('release thm '
                 'space::linear_map_space_add_function_carrier(R,Algebra::field::real_field,R,\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,R,\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,real_linear_identity,nonlinear_real_function)',
                 False),
                ('complex_sum(1+i)=2*i', True),
                ('release thm '
                 'space::linear_map_space_smul_function_carrier(R,Algebra::field::real_field,R,\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,R,\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,i,real_linear_identity)',
                 False),
                ('complex_sum(1+i)=2*i', True),
                ('complex_sum(1+i)=0', False),
                ('complex_sum(1+i)=2*i', True)]
    assert len(expected) == 10 and sum((not success for _, success in expected)) == 5
    digest = hashlib.sha256(json.dumps([prefix, expected]).encode()).hexdigest()
    before = base.checks.snapshot(USE)
    declaration = re.compile('^have (?:fn )?([A-Za-z][A-Za-z0-9_]*)')
    names = [declaration.match(s).group(1) for s in prefix if declaration.match(s)]
    assert len(names) == len(set(names)) == 16, names
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
        for source, success in cases:
            process.stdin.write(source + '\n\n')
            process.stdin.flush()
            data = common.read_response(process)
            assert data['kind'] == 'run' and data['target'] == 'repl', data
            assert not data['session_terminated'] and data['termination'] is None, data
            assert (data['run_result'] == 'success') == success, {'source': source, 'result': data['run_result'], 'errors': data['errors']}
            assert len(data['statement_results']) == 1, data
            assert len(data['errors']) == (0 if success else 1), data
            if not success:
                assert data['errors'][0]['phase'] in ('premise', 'argument_type', 'search_proof'), data
            records.append({'source': source, 'expected_success': success, 'errors': data['errors']})
        process.stdin.write('exit\n')
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final['run_result'] == 'failure' and len(final['errors']) == 5, final
        assert not final['session_terminated'] and final['termination'] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == base.checks.snapshot(USE)
    data = {'command': command, 'checks': records, 'expected_refusals': 5, 'context_retained': True, 'case_source_sha256': digest, 'snapshot': before}
    return data

def main():
    source = base.file_gate(MODULE / 'space.lit', MODULE)
    imported = base.file_gate(USE / 'main.lit', USE)
    boundary = boundaries()
    data = {'source': source, 'registered_predecessor_statements': 19, 'total_module_statements': 65, 'selected_ids': ['3.2', '3.5', '3.6'], 'imported_consumer': imported, 'boundaries': boundary}
    print('Linear-map space: 46 source / 121 imported / 5 refusal controls passed')
if __name__ == '__main__':
    main()
