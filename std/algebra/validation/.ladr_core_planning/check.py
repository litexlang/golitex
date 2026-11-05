"""Verify isolated linear-algebra planning prototypes, not public delivery."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
USE = HERE / 'use'
spec = importlib.util.spec_from_file_location('planning_base', ROOT / 'std/polynomials/validation/.ladr/check_degree.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
common = base.common

def boundaries():
    prefix = [block for block in (USE / 'main.lit').read_text().strip().split('\n\n') if block.strip() and (not block.lstrip().startswith('#'))]
    assert len(prefix) == 14 == 14
    assert (USE / 'main.lit').read_text().strip() == ('# Independent use of isolated core-planning interface prototypes.\n\n' + '\n\n'.join(prefix)).strip()
    cases = [(s, True) for s in prefix]
    cases += [('release obj def p::planning_bad_real_pair', True), ('p::planning_bad_real_pair(1,1)=-1', True), ('release obj def p::planning_test_matrix', True), ('p::planning_test_matrix $in matrix(R,2,3)', True), ('release obj def Algebra::field::real_field', True), ('release thm Algebra::vector_space::scalar_space_carrier(R,Algebra::field::real_field)', True)]
    cases += [(r['source'], r['expected_success']) for r in [{'source': 'claim:\n    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,n,m N,domain_basis finite_seq(V,n),codomain_basis finite_seq(W,m),T fn(v V) W:\n        $Algebra::basis::is_basis(K,F,V,source,n,domain_basis)\n        $Algebra::basis::is_basis(K,F,W,target,m,codomain_basis)\n        =>:\n            \\p::planning_matrix_of_linear_map<K,F,V,source,W,target,n,m,domain_basis,codomain_basis>(T) $in matrix(K,m,n)\n    K=K', 'expected_success': False}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=3', 'expected_success': True}, {'source': '\\p::planning_matrix_column<R,2,3,p::planning_test_matrix,0> $in finite_seq(R,2)', 'expected_success': False}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=3', 'expected_success': True}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=-3', 'expected_success': False}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=3', 'expected_success': True}, {'source': '(\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,p::planning_bad_real_pair) $in &p::PlanningRealInnerProductSpace<R>', 'expected_success': False}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=3', 'expected_success': True}]]
    assert len([{'source': 'claim:\n    ? forall K nonempty_set,F &Algebra::field::Field<K>,V nonempty_set,source &Algebra::vector_space::VectorSpace<K,F,V>,W nonempty_set,target &Algebra::vector_space::VectorSpace<K,F,W>,n,m N,domain_basis finite_seq(V,n),codomain_basis finite_seq(W,m),T fn(v V) W:\n        $Algebra::basis::is_basis(K,F,V,source,n,domain_basis)\n        $Algebra::basis::is_basis(K,F,W,target,m,codomain_basis)\n        =>:\n            \\p::planning_matrix_of_linear_map<K,F,V,source,W,target,n,m,domain_basis,codomain_basis>(T) $in matrix(K,m,n)\n    K=K', 'expected_success': False}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=3', 'expected_success': True}, {'source': '\\p::planning_matrix_column<R,2,3,p::planning_test_matrix,0> $in finite_seq(R,2)', 'expected_success': False}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=3', 'expected_success': True}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=-3', 'expected_success': False}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=3', 'expected_success': True}, {'source': '(\\Algebra::vector_space::scalar_space<R,Algebra::field::real_field>,p::planning_bad_real_pair) $in &p::PlanningRealInnerProductSpace<R>', 'expected_success': False}, {'source': '\\p::planning_real_inner_norm<R,p::planning_real_scalar_ip>(-3)=3', 'expected_success': True}]) == 8
    before = base.checks.snapshot(USE)
    digest = hashlib.sha256(json.dumps(cases).encode()).hexdigest()
    command = [str(common.BINARY), '-lang', 'en', '-strict', '-f', str(USE / 'main.lit'), '-session']
    process = subprocess.Popen(command, cwd=ROOT, env=common.ENV, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    checks = []
    try:
        for source, success in cases:
            process.stdin.write(source + '\n\n')
            process.stdin.flush()
            response = common.read_response(process)
            assert response['target'] == 'repl' and response['kind'] == 'run', response
            assert response['session_terminated'] is False and response['termination'] is None, response
            assert len(response['statement_results']) == 1, response
            assert (response['run_result'] == 'success') == success, {'source': source, 'response': response}
            assert len(response['errors']) == (0 if success else 1), response
            if not success:
                assert response['errors'][0]['phase'] in ('goal_wd', 'well_defined', 'requirement', 'search_proof'), response
                if 'planning_matrix_column' in source:
                    assert '0' in response['errors'][0].get('obligation', ''), response
            checks.append({'source': source, 'expected_success': success, 'errors': response['errors']})
        process.stdin.write('exit\n')
        process.stdin.flush()
        tail, _ = process.communicate(timeout=60)
        final = json.loads(tail)
        assert process.returncode in (0, 1)
        assert final['run_result'] == 'failure' and len(final['errors']) == 4, final
        assert final['session_terminated'] is False and final['termination'] is None, final
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    assert before == base.checks.snapshot(USE)
    data = {'snapshot': before, 'case_source_sha256': digest, 'checks': checks, 'expected_refusals': 4, 'context_retained': True, 'command': command}
    print('Planning boundaries: four mathematical/WD refusals, retained context', flush=True)
    return data

def main():
    source = base.file_gate(HERE / 'main.lit', HERE)
    imported = base.file_gate(USE / 'main.lit', USE)
    assert source['statements'] == 54 and imported['statements'] == 14
    boundary = boundaries()
    result = {'scope': 'Isolated planning evidence; no public std or LADR item acceptance.', 'source': source, 'independent_use': imported, 'boundaries': boundary}
    print('Planning prototypes: 54 source / 14 imported / 4 refusal controls passed', flush=True)
if __name__ == '__main__':
    main()
