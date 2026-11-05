"""Audit existing Algebra interfaces against the original LADR 3A/3B hypotheses."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
USE = HERE / 'existing'
spec = importlib.util.spec_from_file_location('linear_checks', HERE / 'check.py')
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
base = checks.base
common = checks.common
IDS = ['3.1', '3.4', '3.7', '3.10', '3.11', '3.13', '3.14', '3.15', '3.16', '3.18', '3.19', '3.21', '3.22', '3.24']

def boundaries():
    prefix = [block for block in (USE / 'main.lit').read_text().strip().split('\n\n') if block.strip() and (not block.lstrip().startswith('#'))]
    assert len(prefix) == 33 == 33
    canonical = '# Original-hypothesis reuse for LADR 3A and 3B.\n\n'
    canonical += '\n\n'.join(prefix)
    assert (USE / 'main.lit').read_text().strip() == canonical.strip()
    expected = [('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W:\n'
                 '        preimage(T,target.zero)={source.zero}\n'
                 '        =>:\n'
                 '            $injective(V,W,T)\n'
                 '    release thm '
                 'Algebra::vector_space::zero_kernel_is_injective(K,F,V,source,W,target,T)',
                 False),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W:\n'
                 '        $Algebra::basis::is_finite_dimensional(K,F,V,source)\n'
                 '        $Algebra::vector_space::is_linear_map(K,F,V,source,W,target,T)\n'
                 '        =>:\n'
                 '            '
                 '\\Algebra::dimension::finite_dimension<K,F,V>(source)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)+\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_has_finite_kernel(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_has_finite_image(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_rank_carrier(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_nullity_carrier(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::rank_nullity(K,F,V,source,W,target,T)\n'
                 '    '
                 '\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)\n'
                 '    '
                 '\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)\n'
                 '    '
                 '\\Algebra::dimension::finite_dimension<K,F,V>(source)=\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)+\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)=\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)+\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)+\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)',
                 True),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,n N,u '
                 'finite_seq(V,n),w finite_seq(W,n):\n'
                 '        =>:\n'
                 '            exist! T fn(v V) W st '
                 '{$Algebra::vector_space::is_linear_map(K,F,V,source,W,target,T),\\Algebra::finite_span::map_vectors<V,W,n>(T,u)=w}\n'
                 '    release thm '
                 'Algebra::coordinate_maps::linear_map_from_basis_carrier(K,F,V,source,W,target,n,u,w)\n'
                 '    release thm '
                 'Algebra::coordinate_maps::linear_map_from_basis_is_linear(K,F,V,source,W,target,n,u,w)\n'
                 '    claim:\n'
                 '        ? forall j closed_range(1,n):\n'
                 '            '
                 '\\Algebra::finite_span::map_vectors<V,W,n>(\\Algebra::coordinate_maps::linear_map_from_basis<K,F,V,source,W,target,n,u,w>,u)(j)=w(j)\n'
                 '        release thm '
                 'Algebra::coordinate_maps::linear_map_from_basis_entry(K,F,V,source,W,target,n,u,w,j)\n'
                 '        '
                 '\\Algebra::finite_span::map_vectors<V,W,n>(\\Algebra::coordinate_maps::linear_map_from_basis<K,F,V,source,W,target,n,u,w>,u)(j)=\\Algebra::coordinate_maps::linear_map_from_basis<K,F,V,source,W,target,n,u,w>(u(j))=w(j)\n'
                 '    by fn_extension '
                 '\\Algebra::finite_span::map_vectors<V,W,n>(\\Algebra::coordinate_maps::linear_map_from_basis<K,F,V,source,W,target,n,u,w>,u)=w\n'
                 '    claim:\n'
                 '        ? forall first,second fn(v V) W:\n'
                 '            '
                 '$Algebra::vector_space::is_linear_map(K,F,V,source,W,target,first)\n'
                 '            '
                 '$Algebra::vector_space::is_linear_map(K,F,V,source,W,target,second)\n'
                 '            \\Algebra::finite_span::map_vectors<V,W,n>(first,u)=w\n'
                 '            \\Algebra::finite_span::map_vectors<V,W,n>(second,u)=w\n'
                 '            =>:\n'
                 '                first=second\n'
                 '        have first_values '
                 'finite_seq(W,n)=\\Algebra::finite_span::map_vectors<V,W,n>(first,u)\n'
                 '        have second_values '
                 'finite_seq(W,n)=\\Algebra::finite_span::map_vectors<V,W,n>(second,u)\n'
                 '        first_values=w\n'
                 '        second_values=w\n'
                 '        claim:\n'
                 '            ? forall j closed_range(1,n):\n'
                 '                first(u(j))=second(u(j))\n'
                 '            '
                 'first_values(j)=\\Algebra::finite_span::map_vectors<V,W,n>(first,u)(j)=first(u(j))\n'
                 '            '
                 'second_values(j)=\\Algebra::finite_span::map_vectors<V,W,n>(second,u)(j)=second(u(j))\n'
                 '            first_values(j)=w(j)\n'
                 '            second_values(j)=w(j)\n'
                 '            '
                 'first(u(j))=first_values(j)=w(j)=second_values(j)=second(u(j))\n'
                 '        release thm '
                 'Algebra::coordinate_maps::linear_maps_equal_on_basis(K,F,V,source,W,target,n,u,first,second)\n'
                 '    witness exist! T fn(v V) W st '
                 '{$Algebra::vector_space::is_linear_map(K,F,V,source,W,target,T),\\Algebra::finite_span::map_vectors<V,W,n>(T,u)=w} '
                 'from '
                 '\\Algebra::coordinate_maps::linear_map_from_basis<K,F,V,source,W,target,n,u,w>',
                 False),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W:\n'
                 '        $Algebra::basis::is_finite_dimensional(K,F,V,source)\n'
                 '        $Algebra::vector_space::is_linear_map(K,F,V,source,W,target,T)\n'
                 '        =>:\n'
                 '            '
                 '\\Algebra::dimension::finite_dimension<K,F,V>(source)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)+\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_has_finite_kernel(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_has_finite_image(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_rank_carrier(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_nullity_carrier(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::rank_nullity(K,F,V,source,W,target,T)\n'
                 '    '
                 '\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)\n'
                 '    '
                 '\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)\n'
                 '    '
                 '\\Algebra::dimension::finite_dimension<K,F,V>(source)=\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)+\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)=\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)+\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)+\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)',
                 True),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W:\n'
                 '        $Algebra::vector_space::is_subspace(K,F,W,target,fn_range(T))\n'
                 '    release thm '
                 'Algebra::vector_space::range_is_subspace(K,F,V,source,W,target,T)',
                 False),
                ('claim:\n'
                 '    ? forall K nonempty_set,F &Algebra::field::Field<K>,V '
                 'nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W '
                 'nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,T fn(v V) '
                 'W:\n'
                 '        $Algebra::basis::is_finite_dimensional(K,F,V,source)\n'
                 '        $Algebra::vector_space::is_linear_map(K,F,V,source,W,target,T)\n'
                 '        =>:\n'
                 '            '
                 '\\Algebra::dimension::finite_dimension<K,F,V>(source)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)+\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_has_finite_kernel(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_has_finite_image(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_rank_carrier(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::finite_source_nullity_carrier(K,F,V,source,W,target,T)\n'
                 '    release thm '
                 'Algebra::linear_dimension::rank_nullity(K,F,V,source,W,target,T)\n'
                 '    '
                 '\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)\n'
                 '    '
                 '\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)\n'
                 '    '
                 '\\Algebra::dimension::finite_dimension<K,F,V>(source)=\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)+\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)=\\Algebra::linear_dimension::linear_map_nullity<K,F,V,source,W,target>(T)+\\Algebra::linear_dimension::linear_map_rank<K,F,V,source,W,target>(T)=\\Algebra::dimension::finite_dimension<K,F,preimage(T,target.zero)>(\\Algebra::subspace::restricted_space<K,F,V,source,preimage(T,target.zero)>)+\\Algebra::dimension::finite_dimension<K,F,fn_range(T)>(\\Algebra::subspace::restricted_space<K,F,W,target,fn_range(T)>)',
                 True)]
    assert len(expected) == 6 and sum((not success for _, success in expected)) == 3
    digest = hashlib.sha256(json.dumps([prefix, expected]).encode()).hexdigest()
    before = base.checks.snapshot(USE)
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(USE / 'main.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    records = []
    try:
        for source, success in [(s, True) for s in prefix] + expected:
            process.stdin.write(source + '\n\n')
            process.stdin.flush()
            data = common.read_response(process)
            assert data['kind'] == 'run' and data['target'] == 'repl', data
            assert not data['session_terminated'] and data['termination'] is None, data
            assert (data['run_result'] == 'success') == success, {'source': source, 'result': data['run_result'], 'errors': data['errors']}
            assert len(data['statement_results']) == 1, data
            assert len(data['errors']) == (0 if success else 1), data
            if not success:
                assert data['errors'][0]['phase'] == 'premise', data
            records.append({'source': source, 'expected_success': success, 'errors': data['errors']})
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
    assert before == base.checks.snapshot(USE)
    data = {'command': command, 'checks': records, 'expected_refusals': 3, 'context_retained': True, 'case_source_sha256': digest, 'snapshot': before}
    return data

def main():
    imported = base.file_gate(USE / 'main.lit', USE)
    boundary = boundaries()
    data = {'new_public_source_statements': 0, 'reused_module': 'Algebra', 'selected_ids': IDS, 'imported_consumer': imported, 'boundaries': boundary}
    print('Existing linear maps: 33 imported statements / 3 refusal controls passed')
if __name__ == '__main__':
    main()
