#!/usr/bin/env python3
"""Export real public reading inputs for the offline viewer acceptance suite."""
import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
CASES = {
    'syllogism': ('problems/missing-premise-fixed.lit', True),
    'missing-premise': ('problems/missing-premise.lit', False),
    'sqrt-two': ('04-sqrt-two-irrational.lit', True),
    'definition': ('43-checking-03-2.lit', True),
    'sets': ('02-union-and-intersection.lit', True),
    'zero-divisor': ('problems/zero-divisor.lit', False),
    'sqrt-domain': ('problems/sqrt-domain.lit', False),
    'undefined-name': ('problems/undefined-name.lit', False),
}
INLINE_CASES = {
    'predicate-membership-failure': ('1 $in intersect({1, 2}, {2, 3})', False),
    'predicate-membership-known': ('2 $in {1, 2}\n2 $in {2, 3}\n2 $in intersect({1, 2}, {2, 3})', True),
}
CORRESPONDENCE_CASES = {
    'known': ('examples/proof_nodes/atomic/by_known_atomic_fact/cite_via_nested_arg_equality.lit', 'en'),
    'builtin': ('examples/proof_nodes/atomic/by_builtin_rule/dvd_one.lit', 'en'),
    'strategy': ('examples/proof_nodes/atomic/by_builtin_strategy/pos_add_pos_is_pos.lit', 'en'),
    'named-strategy': ('examples/stmt_nodes/definition/def_strategy.lit', 'en'),
    'forall-zh': ('examples/reading/lessons/zh/syllogism.lit', 'zh'),
    'forall-en': ('examples/reading/lessons/en/syllogism.lit', 'en'),
    'least-squares': ('examples/reading/lessons/en/least-squares.lit', 'en'),
}
DEFINITION_CASES = {
    'reciprocal': 'examples/reading/homepage/17-reciprocal-definition.lit',
    'predicate': 'examples/proof_nodes/atomic/by_definition/ambient_prop_expand.lit',
    'by-def': 'examples/reading/lessons/en/definitions.lit',
    'nested': 'examples/proof_nodes/equal/by_object_definition/nested_call_one_step.lit',
    'both': 'examples/proof_nodes/equal/by_object_definition/by_fn_application/both_function_bodies.lit',
    'alias': 'examples/proof_nodes/equal/by_object_definition/by_fn_application/callable_alias_special_property.lit',
    'tuple': 'examples/proof_nodes/equal/by_known_special_property/tuple_projection.lit',
    'fn-tuple': 'examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit',
    'codomain': 'examples/proof_nodes/atomic/by_known_special_property/in_fn_application_in_codomain.lit',
}
# The guard pair comes from function_body_evaluation's existing kernel test.
DEFINITION_CONTROLS = {
    'body-guard': ('forall f fn(x R) R:\n    f = fn(x R: x!=0) R {1/x}\n    =>:\n        f(2)=1/2\n', True),
    'missing-body-guard': ('forall f fn(x R) R:\n    f = fn(x R: x!=0) R {1/x}\n    =>:\n        f(0)=0\n', False),
    'wrong-reciprocal': ('have fn reciprocal(x R: x != 0) R = 1 / x\nreciprocal(2) = 2\n', False),
}
GLOSSARY_CASES = {
    'glossary-by-thm': 'examples/reading/lessons/en/definitions.lit',
    'glossary-have-equal': 'examples/stmt_nodes/definition/have_obj_equal.lit',
    'glossary-have-arbitrary': 'examples/stmt_nodes/definition/have_obj_in_nonempty_set.lit',
    'glossary-function-cases': 'examples/stmt_nodes/definition/have_fn_equal_case_by_case.lit',
    'glossary-algorithm': 'examples/stmt_nodes/definition/def_algo.lit',
    'glossary-preimage': 'examples/stmt_nodes/definition/have_by_fn_preimage.lit',
    'glossary-release-tuple': 'examples/stmt_nodes/release_and_expand/release_tuple_def.lit',
    'glossary-enumerate': 'examples/stmt_nodes/by/by_enumerate_finite_set.lit',
    'glossary-extension': 'examples/stmt_nodes/by/by_extension.lit',
    'glossary-cases': 'examples/stmt_nodes/by/by_cases.lit',
    'glossary-injective': 'examples/proof_nodes/atomic/by_definition/builtin_injective.lit',
    'glossary-syllogism': 'examples/reading/lessons/en/syllogism.lit',
    'glossary-continuity': 'examples/real_analysis/continuity_limits.lit',
    'glossary-lipschitz': 'examples/real_analysis/lipschitz_uniform_continuous.lit',
    'glossary-sequence': 'examples/wd/sequence_limit_interfaces.lit',
    'glossary-symmetric-difference': 'examples/proof_nodes/equal/by_builtin_rule/symmetric_difference.lit',
    'glossary-unicode': 'examples/tokenize/unicode_math_aliases.lit',
    'glossary-composition': 'examples/wd/function_composition.lit',
}
THEOREM_CASES = {
    'selected': 'examples/stmt_nodes/by/by_thm.lit',
    'selection': 'examples/stmt_nodes/by/by_thm_strict_selection.lit',
    'predicate': 'examples/reading/lessons/en/definitions.lit',
    'release': 'examples/stmt_nodes/definition/release_thm.lit',
    'builtin': 'examples/stmt_nodes/release_and_expand/builtin_thm/rational_has_unique_reduced_fraction.lit',
    'existential': 'examples/stmt_nodes/release_and_expand/builtin_thm/finite_set_has_bijective_index.lit',
    'missing-premise': 'examples/test_statements/negative/release_thm_stmt/unsatisfied-theorem-premise.lit',
}
OBJECT_CASES = {
    'matrix-basic': 'examples/test_objs/matrix_operators.lit',
    'matrix-arithmetic': 'examples/test_objs/matrix_arithmetic.lit',
    'matrix-inverse': 'examples/test_objs/matrix_minors_inverse.lit',
    'inner-product': 'examples/test_objs/finite_inner_product_norm.lit',
    'ranges': 'examples/test_objs/finite_set_size.lit',
    'finite-sequences': 'examples/test_objs/finite_seq_set.lit',
    'cartesian': 'examples/test_objs/cart.lit',
    'index-cartesian': 'examples/wd/obj/index_cart.lit',
    'image': 'examples/test_objs/fn_range.lit',
    'preimages': 'examples/wd/function_preimages.lit',
    'composition': 'examples/wd/function_composition.lit',
    'sum-product': 'examples/wd/obj/sum_product.lit',
    'finite-product': 'examples/test_objs/product_of_finite_set.lit',
    'ordered-fold': 'examples/test_objs/reduce.lit',
    'set-fold': 'examples/test_objs/finite_set_reduce.lit',
    'finite-extrema': 'examples/wd/finite_extrema_real_carrier.lit',
    'sequence-limit': 'examples/wd/sequence_limit_interfaces.lit',
    'sequence-extrema': 'examples/wd/sequence_extrema_convergent.lit',
    'function-limit': 'examples/wd/real_function_limit_interfaces.lit',
    'side-limits': 'examples/wd/real_function_limit_sides_interfaces.lit',
    'positive-infinity': 'examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_pos_inf_selected.lit',
    'negative-infinity': 'examples/stmt_nodes/release_and_expand/builtin_thm/fn_limit_neg_inf_selected.lit',
    'real-bounds': 'examples/real_analysis/open_interval_bounds.lit',
    'derivative': 'examples/real_analysis/antiderivative_relations.lit',
    'integral': 'examples/stmt_nodes/release_and_expand/builtin_thm/riemann_integral_add.lit',
    'preimage-command': 'examples/stmt_nodes/definition/have_by_fn_preimage.lit',
}
OBJECT_REJECTIONS = {
    'fractional-index': 'examples/test_objs/negative/sum__n02.lit',
    'noncommutative-fold': 'examples/test_objs/negative/finite_set_reduce__n01.lit',
    'missing-integral-proof': 'examples/wd_negative/riemann_integral_without_proof.lit',
}
MULTIVARIABLE_CASES = {
    'calculus': ('examples/real_analysis/multivariable/main.lit', True),
    'wrong-coordinate': ('examples/wd_negative/multivariable_wrong_coordinate.lit', False),
    'without-proof': ('examples/wd_negative/multivariable_without_proof.lit', False),
}
SYMBOL_CASES = {
    'factorial': ('examples/test_objs/factorial.lit', True),
    'factorial-negative': ('examples/test_objs/negative/factorial__n01.lit', False),
    'factorial-fractional': ('examples/test_objs/negative/factorial__n02.lit', False),
    'factorial-wrong-value': ('examples/test_objs/negative/factorial__n03.lit', False),
    'structure': ('examples/test_objs/struct_obj.lit', True),
    'field': ('examples/test_objs/field_access.lit', True),
    'template': ('examples/test_objs/instantiated_template_obj.lit', True),
    'closed-range': ('examples/proof_nodes/or/by_builtin_rule/closed_integer_range_equality_cover.lit', True),
    'unique': ('examples/tokenize/unicode_math_aliases.lit', True),
}
REPEATED_CASES = {
    'sets': 'examples/test_objs/list_set.lit',
    'body-braces': 'examples/proof_nodes/equal/by_builtin_rule/fn_range_of_constant_anonymous_fn.lit',
    'fields-calls': 'examples/test_objs/field_access.lit',
}
CONTEXT_CASES = {
    'open-open': 'examples/test_objs/interval_open_open.lit',
    'open-closed': 'examples/test_objs/interval_open_closed.lit',
    'closed-open': 'examples/test_objs/interval_closed_open.lit',
    'closed-closed': 'examples/test_objs/interval_closed_closed.lit',
    'lower-open': 'examples/test_objs/one_side_interval_lower_open.lit',
    'lower-closed': 'examples/test_objs/one_side_interval_lower_closed.lit',
    'upper-open': 'examples/test_objs/one_side_interval_upper_open.lit',
    'upper-closed': 'examples/test_objs/one_side_interval_upper_closed.lit',
    'listed-set': 'examples/wd/obj/list_set.lit',
    'set-builder': 'examples/test_objs/set_builder.lit',
    'anonymous': 'examples/wd/obj/anonymous_fn.lit',
    'function-space': 'examples/wd/obj/fn_set.lit',
    'structure': 'examples/test_objs/struct_obj.lit',
    'field': 'examples/test_objs/field_access.lit',
    'template': 'examples/test_objs/instantiated_template_obj.lit',
    'call': 'examples/reading/homepage/17-reciprocal-definition.lit',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/release/litex')
    parser.add_argument('--lessons', action='store_true', help='Also verify the bilingual lessons and their concrete repair exercises.')
    parser.add_argument('--correspondence', action='store_true', help='Also export the four atomic proof routes and named strategy examples.')
    parser.add_argument('--definitions', action='store_true', help='Also export definition applications, tuple properties and rejection controls.')
    parser.add_argument('--glossary', action='store_true', help='Also export mathematical language-reference hover cases.')
    parser.add_argument('--theorems', action='store_true', help='Also export actual theorem applications and their rejection control.')
    parser.add_argument('--objects', action='store_true', help='Also export native object-operation help and domain controls.')
    parser.add_argument('--contexts', action='store_true', help='Also export AST-owned expression-position help.')
    parser.add_argument('--multivariable', action='store_true', help='Also export multivariable expression help and domain controls.')
    parser.add_argument('--symbols', action='store_true', help='Also export postfix and structural-symbol help controls.')
    parser.add_argument('--repeated', action='store_true', help='Also export repeated-expression anchors and mixed-role brace controls.')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    report = {}
    if args.repeated:
        for name, relative in REPEATED_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True, timeout=120)
            bundle = json.loads(run.stdout)
            if run.returncode != 0 or bundle.get('run_result') != 'success':
                raise RuntimeError(f'{name}: unexpected repeated-expression result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: repeated-expression source snapshot mismatch')
            (args.output / f'repeated-{name}.json').write_text(run.stdout)
            report[f'repeated-{name}'] = {'source': relative, 'exit': 0, 'run_result': 'success'}
    if args.symbols:
        for name, (relative, succeeds) in SYMBOL_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True, timeout=120)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected symbol-source result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: symbol source snapshot mismatch')
            (args.output / f'symbol-{name}.json').write_text(run.stdout)
            report[f'symbol-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected}
    if args.multivariable:
        for name, (relative, succeeds) in MULTIVARIABLE_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True, timeout=120)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected multivariable result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: multivariable source snapshot mismatch')
            (args.output / f'multivariable-{name}.json').write_text(run.stdout)
            report[f'multivariable-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected}
    if args.contexts:
        for name, relative in CONTEXT_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True, timeout=60)
            bundle = json.loads(run.stdout)
            if run.returncode != 0 or bundle.get('run_result') != 'success':
                raise RuntimeError(f'{name}: unexpected contextual result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: contextual source snapshot mismatch')
            (args.output / f'context-{name}.json').write_text(run.stdout)
            report[f'context-{name}'] = {'source': relative, 'exit': 0, 'run_result': 'success'}
        # Same regression as tests/reading_expression_hints.rs: field names
        # must not receive the identity of a same-spelled bound variable.
        content = 'struct Point:\n    x R\n    y R\nforall x R, p &Point:\n    p.x + x = p.x + x\n'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                              '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
        bundle = json.loads(run.stdout)
        if run.returncode != 0 or bundle.get('run_result') != 'success':
            raise RuntimeError(f'field-shadow: unexpected result\n{run.stderr}')
        (args.output / 'context-field-shadow.json').write_text(run.stdout)
        report['context-field-shadow'] = {'source': '<native field-shadow regression>', 'exit': 0, 'run_result': 'success'}
    if args.objects:
        for name, relative in {**OBJECT_CASES, **OBJECT_REJECTIONS}.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True, timeout=60)
            bundle = json.loads(run.stdout)
            expected = 'failure' if name in OBJECT_REJECTIONS else 'success'
            if run.returncode != (1 if expected == 'failure' else 0) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected object result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: object source snapshot mismatch')
            (args.output / f'object-{name}.json').write_text(run.stdout)
            report[f'object-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected}
    if args.theorems:
        for name, relative in THEOREM_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'failure' if name == 'missing-premise' else 'success'
            if run.returncode != (1 if expected == 'failure' else 0) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected theorem result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: theorem source snapshot mismatch')
            (args.output / f'theorem-{name}.json').write_text(run.stdout)
            report[f'theorem-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected}
        # The same checked two-conclusion theorem, invoked with release.
        content = (ROOT / THEOREM_CASES['selected']).read_text().replace(
            'by thm zero_sides(2) => 2 + 0 = 2', 'release thm zero_sides(2)')
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                              '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
        bundle = json.loads(run.stdout)
        if run.returncode != 0 or bundle.get('run_result') != 'success':
            raise RuntimeError(f'theorem-multiple: unexpected result\n{run.stderr}')
        (args.output / 'theorem-multiple.json').write_text(run.stdout)
        report['theorem-multiple'] = {'source': THEOREM_CASES['selected'],
                                     'variation': 'release both conclusions', 'exit': 0, 'run_result': 'success'}
    if args.glossary:
        for name, relative in GLOSSARY_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != 0 or bundle.get('run_result') != 'success':
                raise RuntimeError(f'{name}: public glossary example failed\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: glossary source snapshot mismatch')
            (args.output / f'{name}.json').write_text(run.stdout)
            report[name] = {'source': relative, 'exit': 0, 'run_result': 'success'}
        tuple_source = (ROOT / GLOSSARY_CASES['glossary-release-tuple']).read_text()
        controls = {
            'glossary-release-spaced': (tuple_source.replace('release tuple def', 'release   tuple\t def'), True),
            'glossary-release-comment': (tuple_source.replace('release tuple def', 'release # tuple def\n'), False),
            'glossary-removed-predicate': ('$fn_eq(1, 1)\n', False),
        }
        for name, (content, succeeds) in controls.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != ('success' if succeeds else 'failure'):
                raise RuntimeError(f'{name}: glossary boundary result mismatch\n{run.stderr}')
            (args.output / f'{name}.json').write_text(run.stdout)
            report[name] = {'source': '<glossary-control>', 'exit': run.returncode,
                            'run_result': bundle['run_result']}
    if args.definitions:
        # Isolate these public files from their containing project's exports;
        # the CLI still verifies and retains every exact source byte.
        definitions = {name: ((ROOT / relative).read_text(), True)
                       for name, relative in DEFINITION_CASES.items()}
        for name, (content, succeeds) in {**definitions, **DEFINITION_CONTROLS}.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content],
                                 capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected definition result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: definition source snapshot mismatch')
            (args.output / f'{name}.json').write_text(run.stdout)
            report[name] = {'source': DEFINITION_CASES.get(name, '<control>'),
                            'exit': run.returncode, 'run_result': expected}
    for name, (relative, succeeds) in CASES.items():
        source = ROOT / 'examples/reading/homepage' / relative
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                              '-strict', '-lang', 'zh', '-f', str(source)],
                             capture_output=True, text=True)
        expected = 'success' if succeeds else 'failure'
        if run.returncode != (0 if succeeds else 1):
            raise RuntimeError(f'{name}: unexpected exit {run.returncode}\n{run.stderr}')
        bundle = json.loads(run.stdout)
        if bundle.get('kind') != 'reading' or bundle.get('run_result') != expected:
            raise RuntimeError(f'{name}: expected a reading {expected} bundle')
        if not any(item.get('content') == source.read_text()
                   for item in bundle.get('sources', [])):
            raise RuntimeError(f'{name}: source snapshot mismatch')
        (args.output / f'{name}.json').write_text(run.stdout)
        report[name] = {'source': relative, 'exit': run.returncode,
                        'run_result': bundle['run_result']}
    for name, (content, succeeds) in INLINE_CASES.items():
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                              '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
        bundle = json.loads(run.stdout)
        expected = 'success' if succeeds else 'failure'
        if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
            raise RuntimeError(f'{name}: unexpected inline outcome\n{run.stderr}')
        if not any(source.get('content') == content for source in bundle.get('sources', [])):
            raise RuntimeError(f'{name}: inline source snapshot mismatch')
        (args.output / f'{name}.json').write_text(run.stdout)
        report[name] = {'source': '<inline>', 'exit': run.returncode, 'run_result': expected}
    if args.correspondence:
        for name, (relative, locale) in CORRESPONDENCE_CASES.items():
            source = ROOT / relative
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', locale, '-f', str(source)], capture_output=True, text=True)
            if run.returncode:
                raise RuntimeError(f'{name}: proof-route example failed\n{run.stderr}')
            bundle = json.loads(run.stdout)
            if bundle.get('run_result') != 'success' or not any(
                    value.get('content') == source.read_text() for value in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: proof-route source/result mismatch')
            (args.output / f'{name}.json').write_text(run.stdout)
            report[name] = {'source': relative, 'exit': run.returncode, 'run_result': 'success'}
    project = ROOT / 'examples/reading/book'
    run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                          '-strict', '-lang', 'zh', '-r', str(project)],
                         capture_output=True, text=True)
    if run.returncode:
        raise RuntimeError(f'book: unexpected exit {run.returncode}\n{run.stderr}')
    bundle = json.loads(run.stdout)
    if bundle.get('run_result') != 'success' or len(bundle.get('sources', [])) != 3:
        raise RuntimeError('book: expected three successful real source chapters')
    for item in bundle['sources']:
        if item.get('content') != (project / item['path']).read_text():
            raise RuntimeError('book: source snapshot mismatch')
    (args.output / 'book.json').write_text(run.stdout)
    report['book'] = {'source': 'examples/reading/book', 'exit': 0,
                      'run_result': 'success', 'sources': 3}
    if args.lessons:
        lessons = ROOT / 'examples/reading/lessons'
        subprocess.run(['python3', str(lessons / 'build.py'), '--check', '--verify',
                        '--binary', str(args.binary.resolve()),
                        '--reading-output', str(args.output),
                        '--receipt', str(args.output / 'lesson-verification.json')], check=True)
        items = json.loads((lessons / 'catalogue.json').read_text())['lessons']
        repairs = {
            'missing-premise': ('forall people nonempty_set, socrates people:\n',
                                'forall people nonempty_set, socrates people:\n    $is_human(socrates)\n'),
            'sqrt-domain': ('sqrt(-1) $in R', 'sqrt(4) $in R'),
            'definition-failure': ('by def $nonnegative(-1)', 'by def $nonnegative(3)'),
        }
        # Execute the already-established repairs described in the source, with
        # exact submitted text retained. No fabricated success/proof fixture.
        for item in items:
            if item['id'] not in repairs:
                continue
            for locale in ('zh', 'en'):
                before, after = repairs[item['id']]
                original = (lessons / item['litex_code'][locale]).read_text()
                if original.count(before) != 1:
                    raise RuntimeError(f'{item["id"]}: repair anchor is ambiguous')
                content = original.replace(before, after, 1)
                source = args.output / 'repair-source' / locale / (item['id'] + '.lit')
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text(content)
                run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                      '-strict', '-lang', locale, '-f', str(source)], capture_output=True, text=True)
                if run.returncode:
                    raise RuntimeError(f'{source}: repair failed\n{run.stderr}')
                bundle = json.loads(run.stdout)
                if bundle.get('run_result') != 'success' or not any(
                        value.get('content') == content for value in bundle.get('sources', [])):
                    raise RuntimeError(f'{source}: repaired source/result mismatch')
                (args.output / f'lesson-{item["id"]}-repair-{locale}.json').write_text(run.stdout)
        report['lessons'] = {'bilingual_sources': len(items) * 2,
                             'expected_successes': 12, 'expected_failures': 6, 'repairs': 6}
    (args.output / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'{len(CASES) + len(INLINE_CASES) + 1} core reading fixtures' + (' and proof-route examples' if args.correspondence else '') + (' and bilingual lesson/repair fixtures' if args.lessons else '') + f' exported to {args.output}')


if __name__ == '__main__':
    main()
