"""Check original-hypothesis inverse and isomorphism source interfaces."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
MODULE = ROOT / 'std/linear_maps'
USE = HERE / 'use'
spec = importlib.util.spec_from_file_location('degree_checks', ROOT / 'std/polynomials/validation/.ladr/check_degree.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
common = base.common

def boundaries():
    prefix = [block for block in (USE / 'main.lit').read_text().strip().split('\n\n') if block.strip() and (not block.lstrip().startswith('#'))]
    assert len(prefix) == 72 == 72
    canonical = '# Independent two-sided inverse and isomorphism consumers.\n\n'
    canonical += '\n\n'.join(prefix)
    assert (USE / 'main.lit').read_text().strip() == canonical.strip()
    expected = [('claim:\n'
                 '    ? forall V,W set,T fn(v V) W,S fn(w W) V:\n'
                 '        forall v V:\n'
                 '            S(T(v))=v\n'
                 '        =>:\n'
                 '            $bijective(V,W,T)\n'
                 '    release thm inv::two_sided_inverse_implies_bijective(V,W,T,S)',
                 False),
                ('complex_backward(i)=1', True),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W:\n'
                 '        $Algebra::vector_space::is_linear_map(K,F,V,source,W,target,T)\n'
                 '        =>:\n'
                 '            $inv::is_linear_isomorphism(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'inv::linear_bijection_is_isomorphism(K,F,V,source,W,target,T)',
                 False),
                ('complex_backward(i)=1', True),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W:\n'
                 '        $Algebra::basis::is_finite_dimensional(K,F,V,source)\n'
                 '        $Algebra::basis::is_finite_dimensional(K,F,W,target)\n'
                 '        $Algebra::vector_space::is_linear_map(K,F,V,source,W,target,T)\n'
                 '        $injective(V,W,T)\n'
                 '        =>:\n'
                 '            $inv::is_linear_isomorphism(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'dim::equal_dimension_injection_is_linear_isomorphism(K,F,V,source,W,target,T)',
                 False),
                ('complex_backward(i)=1', True),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W,S fn(w W) V:\n'
                 '        $Algebra::basis::is_finite_dimensional(K,F,V,source)\n'
                 '        $Algebra::basis::is_finite_dimensional(K,F,W,target)\n'
                 '        $Algebra::vector_space::is_linear_map(K,F,V,source,W,target,T)\n'
                 '        $Algebra::vector_space::is_linear_map(K,F,W,target,V,source,S)\n'
                 '        '
                 '\\Algebra::vector_space::map_compose<V,W,V>(S,T)=\\Algebra::vector_space::identity<V>\n'
                 '        =>:\n'
                 '            '
                 '\\Algebra::vector_space::map_compose<W,V,W>(T,S)=\\Algebra::vector_space::identity<W>\n'
                 '    release thm '
                 'ident::equal_dimension_left_inverse_is_right_inverse(K,F,V,source,W,target,T,S)',
                 False),
                ('complex_backward(i)=1', True),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W,S fn(w W) V:\n'
                 '        $inv::is_linear_isomorphism(K,F,V,source,W,target,T)\n'
                 '        =>:\n'
                 '            S=\\Algebra::linear_criteria::inverse_bijection<V,W,T>\n'
                 '    release thm '
                 'inv::linear_isomorphism_inverse_unique(K,F,V,source,W,target,T,S)',
                 False),
                ('complex_backward(i)=1', True)]
    assert len(expected) == 10 and sum((not success for _, success in expected)) == 5
    digest = hashlib.sha256(json.dumps([prefix, expected]).encode()).hexdigest()
    before = base.checks.snapshot(USE)
    declaration = re.compile('^have (?:fn )?([A-Za-z][A-Za-z0-9_]*)')
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
                assert data['errors'][0]['phase'] == 'premise', data
            records.append({'source': source, 'expected_success': expected_success, 'errors': data['errors']})
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
    source = base.file_gate(MODULE / 'identity_compositions.lit', MODULE)
    imported = base.file_gate(USE / 'main.lit', USE)
    boundary = boundaries()
    result = {'source': source, 'registered_predecessor_statements': {'inverse': 10, 'dimension': 5}, 'total_module_statements': 19, 'imported_consumer': imported, 'boundaries': boundary}
    print(f"Linear inverses: {source['statements']} final source / {imported['statements']} imported / 5 refusal controls passed")
if __name__ == '__main__':
    main()
