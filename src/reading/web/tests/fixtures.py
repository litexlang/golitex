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
INFERRED_RULE_CASES = {
    'definitions': 'examples/reading/lessons/en/definitions.lit',
    'nested-predicate': 'examples/reading/inferred_facts.lit',
    'rule-families': 'examples/infer/atomic/infer_result_rule_families.lit',
    'nonzero-cancellation': 'examples/infer/equal/nonzero_factor_cancellation.lit',
    'function-range': 'examples/infer/atomic/in_fn_range.lit',
    'union': 'examples/infer/atomic/in_union_or.lit',
    'builder': 'examples/infer/atomic/set_builder_projection_replay.lit',
    'function-carrier': 'examples/infer/atomic/in_equal_fn_set_expand.lit',
    'template': 'examples/infer/atomic/template_set_builder_carrier.lit',
    'injective': 'examples/infer/atomic/injective_definition.lit',
}
# Actual object-introduction probes and existing public rejection boundaries.
FAILED_INTRODUCTION_CASES = {'membership-unchecked-suffix': ('have first, second, third N = 1, -1, 2\n', False),
 'dependent-product-membership-failure': ('have product_A set, product_x cart(product_A, product_A) = R, (1, {})\n', False),
 'have-second-nonempty-failure': ('have a R, b {}, c R\n', False),
 'have-second-wd-failure': ('have wd_a R, wd_b {1 / 0}, wd_c R\n', False),
 'equal-second-membership-failure': ('have equal_a, equal_b N = 1, -1\n', False),
 'equal-second-rhs-wd-failure': ('have rhs_a, rhs_b R = 1, 1 / 0\n', False),
 'equal-second-domain-wd-failure': ('have type_a R, type_b {1 / 0} = 1, 0\n', False),
 'obtain-verified-source-arity-failure': ('witness exist u R st {u = 2} from 2\n'
                                          '\n'
                                          'obtain obtained_a, obtained_b from exist u R st {u = 2}\n',
                                          False),
 'obtain-predicate-source-arity-failure': ('prop has_copy(t R):\n'
                                           '    exist x R st {x = t}\n'
                                           '\n'
                                           'witness exist u R st {u = 2} from 2\n'
                                           '\n'
                                           'by def $has_copy(2)\n'
                                           '\n'
                                           'obtain copy_a, copy_b from $has_copy(2)\n',
                                           False),
 'obtain-predicate-source-type-failure': ('prop has_copy(t R):\n'
                                          '    exist x R st {x = t}\n'
                                          '\n'
                                          'obtain copy_c from $has_copy({})\n',
                                          False),
 'have-existence-failure': ('have impossible_n N:\n    impossible_n < 0\n', False),
 'have-good': ('have good_a R, good_b {0}\n', True),
 'have-equal-good': ('have good_eq_a, good_eq_b N = 1, 2\n', True),
 'obtain-good': ('witness exist u R st {u = 2} from 2\n\nobtain good_obtained from exist u R st {u = 2}\n',
                 True),
 'have-first-empty': ('# Expected rejection: empty-carrier\n# Owner: HaveObjInNonemptySetStmt\n\nhave x {}\n',
                      False),
 'equal-count': ('# Expected rejection: wrong-value-count\n# Owner: HaveObjEqualStmt\n\nhave x, y R = 1\n',
                 False),
 'obtain-false': ('# Expected rejection: false-existence\n'
                  '# Owner: ObtainObjFromExistFact\n'
                  '\n'
                  'obtain a from exist x N st {x = -1}\n',
                  False),
 'atomic-nonexistential': ('# Expected rejection: nonexistential-prop\n'
                           '# Owner: ObtainObjFromAtomicFact\n'
                           '\n'
                           'prop P(x R):\n'
                           '    x = x\n'
                           'obtain a from $P(1)\n',
                           False)}

# Actual contradiction probes checked one statement per turn in a retained strict Session.
FAILED_CONTRA_CASES = {'closing-positive-prefix': ('by contra:\n    ? 1 = 2\n    impossible 1 = 1 and 0 = 0\n', False),
 'closing-first-failure': ('by contra:\n    ? 1 = 2\n    impossible 0 = 1\n', False),
 'predicate-definition': ('prop narrow(x R):\n    x > 0\n    x < 1\n', True),
 'body-prefix-inferences': ('prop narrow(x R):\n'
                            '    x > 0\n'
                            '    x < 1\n'
                            '\n'
                            'by contra:\n'
                            '    ? not $narrow(2)\n'
                            '    2 > 0\n'
                            '    7 = 8\n'
                            '    have unexecuted R = 9\n'
                            '    impossible 2 < 1\n',
                            False),
 'predicate-success': ('prop narrow(x R):\n'
                       '    x > 0\n'
                       '    x < 1\n'
                       '\n'
                       'by contra:\n'
                       '    ? not $narrow(2)\n'
                       '    2 > 0\n'
                       '    impossible 2 < 1\n',
                       True),
 'goal-wd': ('by contra:\n    ? 1 / 0 = 1\n    impossible 1 = 1\n', False),
 'case-compound-closing-rejected': ('by cases:\n'
                                    '    ? 1 = 2\n'
                                    '    case 1 = 1:\n'
                                    '        impossible 1 = 1 and 0 = 0\n',
                                    False),
 'case-atomic-closing-prefix': ('by cases:\n    ? 1 = 2\n    case 1 = 1:\n        impossible 1 = 1\n', False),
 'nested-assumption-citation': ('prop narrow(x R):\n'
                                '    x > 0\n'
                                '    x < 1\n'
                                '\n'
                                'claim:\n'
                                '    ? forall x R:\n'
                                '        x = x\n'
                                '    by contra:\n'
                                '        ? not $narrow(x)\n'
                                '        x > 0\n'
                                '        7 = 8\n'
                                '        impossible x < 1\n',
                                False),
 'forall-goal-body-failure': ('by contra:\n'
                              '    ? forall y R:\n'
                              '        y = y\n'
                              '    7 = 8\n'
                              '    impossible 1 = 1\n',
                              False),
 'or-goal-body-failure': ('by contra:\n    ? 1 = 2 or 0 = 1\n    7 = 8\n    impossible 1 = 1\n', False),
 'exist-witness-body-failure': ('by contra:\n'
                                '    ? not exist y {0} st {y = 1}\n'
                                '    obtain chosen from exist y {0} st {y = 1}\n'
                                '    7 = 8\n'
                                '    impossible chosen = 1\n',
                                False),
 'unsupported-quantified-negation': ('by contra:\n'
                                     '    ? forall y R:\n'
                                     '        forall z R:\n'
                                     '            z = z\n'
                                     '        =>:\n'
                                     '            y = y\n'
                                     '    impossible 1 = 1\n',
                                     False),
 'atomic-success': ('by contra:\n    ? 1 != 0\n    impossible 1 = 0\n', True),
 'closing-negation-unsupported': ('by contra:\n'
                                  '    ? 1 = 2\n'
                                  '    impossible forall y R:\n'
                                  '        forall z R:\n'
                                  '            z = z\n'
                                  '        =>:\n'
                                  '            y = y\n',
                                  False),
 'closing-wd-failure': ('by contra:\n    ? 1 = 2\n    impossible 1 / 0 = 0\n', False),
 'compound-success': ('by contra:\n    ? 1 = 1\n    impossible 1 = 1 and 0 = 0\n', True),
 'closing-after-prefix': ('by contra:\n'
                          '    ? 1 = 2\n'
                          '    have temporary R = 2\n'
                          '    temporary = 2\n'
                          '    impossible 1 = 1 and 0 = 0\n',
                          False),
 'quantified-theorem-premise-failure': ('thm quantified_guard:\n'
                                        '    ? forall t R:\n'
                                        '        forall u R:\n'
                                        '            u = u\n'
                                        '        t > 0\n'
                                        '        =>:\n'
                                        '            t != 0\n'
                                        '\n'
                                        'by thm quantified_guard(0) => 0 != 0\n',
                                        False),
 'empty-domain-assumption-boundary': ('by contra:\n'
                                      '    ? forall empty_x {}:\n'
                                      '        1 / 0 = 0\n'
                                      '    impossible 1 = 1\n',
                                      False),
 'chain-goal-body-failure': ('by contra:\n    ? 0 <= 1 <= 2\n    7 = 8\n    impossible 1 = 1\n', False),
 'unique-exist-goal-body-failure': ('by contra:\n'
                                    '    ? exist! unique_x {0} st {unique_x = unique_x}\n'
                                    '    7 = 8\n'
                                    '    impossible 1 = 1\n',
                                    False),
 'iff-goal-body-failure': ('by contra:\n'
                           '    ? forall iff_x R:\n'
                           '        =>:\n'
                           '            iff_x = iff_x\n'
                           '        <=>:\n'
                           '            iff_x + 0 = iff_x\n'
                           '    7 = 8\n'
                           '    impossible 1 = 1\n',
                           False),
 'and-goal-body-failure': ('by contra:\n    ? 1 = 2 and 0 = 1\n    7 = 8\n    impossible 1 = 1\n', False),
 'not-forall-goal-body-failure': ('by contra:\n'
                                  '    ? not forall opposite_x {0}:\n'
                                  '        opposite_x = 1\n'
                                  '    7 = 8\n'
                                  '    impossible 1 = 1\n',
                                  False),
 'exist-goal-body-failure': ('by contra:\n'
                             '    ? exist existence_x {0} st {existence_x = 0}\n'
                             '    7 = 8\n'
                             '    impossible 1 = 1\n',
                             False)}

# Actual theorem invocation probes checked in one persistent strict Session.
FORALL_EQUALITY_SYMMETRY_CASES = {'direct': {'source': 'forall f fn(t R) R, a R:\n'
                      '    forall x R:\n'
                      '        f(x) = x\n'
                      '    =>:\n'
                      '        a = f(a)\n',
            'strict': True,
            'success': True},
 'conditional': {'source': 'forall f fn(t R) R, a R:\n'
                           '    forall x R:\n'
                           '        x >= 0\n'
                           '        =>:\n'
                           '            f(x) = x\n'
                           '    a >= 0\n'
                           '    =>:\n'
                           '        a = f(a)\n',
                 'strict': True,
                 'success': True},
 'alias': {'source': 'forall f, g fn(t R) R, a R:\n'
                     '    f = g\n'
                     '    forall x R:\n'
                     '        f(x) = x\n'
                     '    =>:\n'
                     '        a = g(a)\n',
           'strict': True,
           'success': True},
 'and-component': {'source': 'forall f fn(t R) R, a R:\n'
                             '    forall x R:\n'
                             '        f(x) = x and x = x\n'
                             '    =>:\n'
                             '        a = f(a)\n',
                   'strict': True,
                   'success': True},
 'chain': {'source': 'forall f fn(t R) R, a R:\n'
                     '    forall x R:\n'
                     '        f(x) = x\n'
                     '    =>:\n'
                     '        a = f(a) = a\n',
           'strict': True,
           'success': True},
 'failed-prefix': {'source': 'thm incomplete_identity:\n'
                             '    ? forall f fn(t R) R, a R:\n'
                             '        forall x R:\n'
                             '            f(x) = x\n'
                             '        =>:\n'
                             '            a = f(a)\n'
                             '    a = f(a)\n'
                             '    1 = 2\n',
                   'strict': True,
                   'success': False},
 'missing-premise': {'source': 'forall f fn(t R) R, a R:\n    a = f(a)\n', 'strict': True, 'success': False},
 'forward': {'source': 'forall f fn(t R) R, a R:\n'
                       '    forall x R:\n'
                       '        f(x) = x\n'
                       '    =>:\n'
                       '        f(a) = a\n',
             'strict': True,
             'success': True},
 'arithmetic-control': {'source': '# Node: equal.ByKnownForallFactViaSymmetry\n'
                                  '# Struct: EqualFactSearchedProofByKnownForallViaSymmetry\n'
                                  '# Run: litex -f '
                                  'examples/proof_nodes/equal/by_known_forall/via_symmetry.lit\n'
                                  '#\n'
                                  '# Forall concludes `rhs = lhs` orientation; goal asks the swapped sides.\n'
                                  '\n'
                                  'forall x R:\n'
                                  '    0 + x = x\n'
                                  '\n'
                                  'have a R = 3\n'
                                  'a = 0 + a\n',
                        'strict': True,
                        'success': True},
 'public-tracer': {'source': '# If f agrees with the identity on R, then a = f(a) for every real a.\n'
                             '# Instantiate the assumed universal to get f(a) = a, then use equality '
                             'symmetry.\n'
                             '# Gate: litex -strict -f '
                             'examples/proof_nodes/equal/by_known_forall/instantiation_then_symmetry.lit\n'
                             '\n'
                             'forall f fn(t R) R, a R:\n'
                             '    forall x R:\n'
                             '        f(x) = x\n'
                             '    =>:\n'
                             '        a = f(a)\n',
                   'strict': True,
                   'success': True}}
FORALL_EQUALITY_SYMMETRY_BOOK = {'litex.config': '[export]\nfunctions = "./01-functions.lit"\napplication = "./02-application.lit"\n',
 '01-functions.lit': 'have F fn(t R) R\n',
 '02-application.lit': 'release obj def functions::F\n'
                       '\n'
                       'forall a R:\n'
                       '    forall x R:\n'
                       '        functions::F(x) = x\n'
                       '    =>:\n'
                       '        a = functions::F(a)\n'}

FAILED_THEOREM_CASES = {'selected-premise-failure': ('thm positive_is_nonzero:\n'
                              '    ? forall x R:\n'
                              '        x > 0\n'
                              '        =>:\n'
                              '            x != 0\n'
                              '\n'
                              'by thm positive_is_nonzero(0) => 0 != 0\n',
                              False),
 'release-premise-failure': ('thm positive_is_nonzero:\n'
                             '    ? forall x R:\n'
                             '        x > 0\n'
                             '        =>:\n'
                             '            x != 0\n'
                             '\n'
                             'release thm positive_is_nonzero(0)\n',
                             False),
 'late-premise-failure': ('thm sum_positive:\n'
                          '    ? forall x, y R:\n'
                          '        x > 0\n'
                          '        y > 0\n'
                          '        =>:\n'
                          '            x + y > 0\n'
                          '\n'
                          'by thm sum_positive(1, 0) => 1 + 0 > 0\n',
                          False),
 'dependent-type-failure': ('thm carrier_reflexive:\n'
                            '    ? forall A nonempty_set, x A:\n'
                            '        x = x\n'
                            '\n'
                            'by thm carrier_reflexive({1}, 2) => 2 = 2\n',
                            False),
 'first-type-failure': ('thm carrier_reflexive:\n'
                        '    ? forall A nonempty_set, x A:\n'
                        '        x = x\n'
                        '\n'
                        'release thm carrier_reflexive({}, 1)\n',
                        False),
 'not-returned': ('thm carrier_reflexive:\n'
                  '    ? forall A nonempty_set, x A:\n'
                  '        x = x\n'
                  '\n'
                  'by thm carrier_reflexive({1}, 1) => 2 = 2\n',
                  False),
 'preparation-arity': ('thm positive_is_nonzero:\n'
                       '    ? forall x R:\n'
                       '        x > 0\n'
                       '        =>:\n'
                       '            x != 0\n'
                       '\n'
                       'by thm positive_is_nonzero(1, 2) => 1 != 0\n',
                       False),
 'preparation-unknown': ('release thm missing_invocation_theorem(1)\n', False),
 'unchecked-premise': ('thm three_positive_sum:\n'
                       '    ? forall x, y, z R:\n'
                       '        x > 0\n'
                       '        y > 0\n'
                       '        z > 0\n'
                       '        =>:\n'
                       '            x + y + z > 0\n'
                       '\n'
                       'release thm three_positive_sum(1, 0, 1)\n',
                       False),
 'nested-assumption': ('thm sum_positive:\n'
                       '    ? forall x, y R:\n'
                       '        x > 0\n'
                       '        y > 0\n'
                       '        =>:\n'
                       '            x + y > 0\n'
                       '\n'
                       'claim:\n'
                       '    ? forall caller R:\n'
                       '        caller > 0\n'
                       '        =>:\n'
                       '            caller != 0\n'
                       '    by thm sum_positive(caller, 0) => caller + 0 > 0\n',
                       False),
 'tuple-right-domain': ('release thm tuple_equal_from_coordinates((1, 2), (1, 2, 3))\n', False),
 'tuple-left-domain': ('release thm tuple_equal_from_coordinates((1, 2, 3), (1, 2))\n', False),
 'builtin-premise': ('release thm prime_divides_power(6, 4, 2)\n', True),
 'builtin-arity': ('release thm rational_has_unique_reduced_fraction()\n', False),
 'selected-success': ('thm positive_is_nonzero:\n'
                      '    ? forall x R:\n'
                      '        x > 0\n'
                      '        =>:\n'
                      '            x != 0\n'
                      '\n'
                      'by thm positive_is_nonzero(2) => 2 != 0\n',
                      True),
 'release-success': ('thm sum_positive:\n'
                     '    ? forall x, y R:\n'
                     '        x > 0\n'
                     '        y > 0\n'
                     '        =>:\n'
                     '            x + y > 0\n'
                     '\n'
                     'release thm sum_positive(1, 2)\n',
                     True),
 'builtin-prime-failure': ('release thm prime_divides_power(6, 2, 4)\n', False),
 'tuple-good': ('release thm tuple_equal_from_coordinates((1, 2), (1, 2))\n', True),
 'tuple-actual-left-domain': ('have fn short_tuple(k closed_range(1, 2)) R = k\n'
                              '\n'
                              'release thm tuple_equal_from_coordinates(short_tuple, (1, 2, 3))\n',
                              False),
 'function-no-domain': ('release thm fn_set_member(1, fn(x R) R)\n', False),
 'function-wd': ('release thm fn_set_member(1 / 0, fn(x R) R)\n', False)}

# Actual inputs checked one statement per turn in the retained strict Session.
FAILED_DEFINITION_CASES = {'nonnegative-failure': ('prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(-1)\n', False),
 'nonnegative-success': ('prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(3)\n', True),
 'multiple-failure': ('prop increasing_negative(x R, y R):\n'
                      '    x <= y\n'
                      '    y < 0\n'
                      '\n'
                      'by def $increasing_negative(1, 2)\n',
                      False),
 'type-failure': ('prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative({1})\n', False),
 'unchecked-suffix': ('prop small_positive(x R):\n'
                      '    x > 0\n'
                      '    x < 1\n'
                      '    x != 0\n'
                      '\n'
                      'by def $small_positive(2)\n',
                      False),
 'goal-wd': ('prop nonnegative(x R):\n    x >= 0\n\nby def $nonnegative(1 / 0)\n', False),
 'unavailable': ('abstract_prop no_definition(x)\n\nby def $no_definition(1)\n', False),
 'nested-failure': ('prop small_positive(x R):\n'
                    '    x > 0\n'
                    '    x < 1\n'
                    '    x != 0\n'
                    '\n'
                    'claim:\n'
                    '    ? forall scoped R:\n'
                    '        scoped > 0\n'
                    '        =>:\n'
                    '            $small_positive(scoped)\n'
                    '    by def $small_positive(scoped)\n',
                    False),
 'dependent-failure': ('prop equals_one_in(A set, x A):\n'
                       '    x = 1\n'
                       '\n'
                       'by def $equals_one_in({1, 2}, 2)\n',
                       False),
 'arity': ('prop increasing_negative(x R, y R):\n'
           '    x <= y\n'
           '    y < 0\n'
           '\n'
           'by def $increasing_negative(1)\n',
           False),
 'builtin-failure': ('by def $dvd(3, 2)\n', False),
 'builtin-success': ('by def $dvd(6, 2)\n', True),
 'builtin-late-failure': ('by def R $proper_subset R\n', False)}

WHOLE_CHAIN_FORALL_CASES = {'direct': ('forall t R:\n'
            '    t = t + 0 = t\n'
            '\n'
            'have chain_value R = 2\n'
            '\n'
            'chain_value = chain_value + 0 = chain_value\n',
            True),
 'carrier-fallback': ('forall t R:\n'
                      '    t = t + 0 = t\n'
                      '\n'
                      'have arbitrary_complex C\n'
                      '\n'
                      'arbitrary_complex = arbitrary_complex + 0 = arbitrary_complex\n',
                      True),
 'undefined': ('forall t R:\n    t = t + 0 = t\n\n1 / 0 = 1 / 0 + 0 = 1 / 0\n', False),
 'location': ('claim:\n'
              '    ? 1 = 1\n'
              '    forall selected R:\n'
              '        selected = selected\n'
              '        selected = selected + 0 = selected\n'
              '    have location_value R = 3\n'
              '    location_value = location_value + 0 = location_value\n',
              True),
 'rebound': ('claim:\n'
             '    ? 1 = 1\n'
             '    forall repeated R:\n'
             '        repeated = repeated = repeated\n'
             '    have rebound_value R = 2\n'
             '    rebound_value = 2 = rebound_value\n',
             True),
 'guarded': ('claim:\n'
             '    ? 1 = 1\n'
             '    forall nonnegative R:\n'
             '        nonnegative >= 0\n'
             '        =>:\n'
             '            0 <= nonnegative = nonnegative\n'
             '    have guarded_value R = 2\n'
             '    0 <= guarded_value = guarded_value\n',
             True),
 'missing-premise': ('claim:\n'
                     '    ? 1 = 1\n'
                     '    forall nonnegative R:\n'
                     '        nonnegative >= 0\n'
                     '        =>:\n'
                     '            0 <= nonnegative = nonnegative\n'
                     '    have negative_value R = -1\n'
                     '    0 <= negative_value = negative_value\n',
                     False),
 'alias': ('claim:\n'
           '    ? 1 = 1\n'
           '    forall number R:\n'
           '        number = number + 0 = number\n'
           '    have original_value R = 4\n'
           '    let alias_value = original_value\n'
           '    alias_value = alias_value + 0 = alias_value\n',
           True),
 'guarded-known': ('claim:\n'
                   '    ? 1 = 1\n'
                   '    forall nonnegative R:\n'
                   '        nonnegative >= 0\n'
                   '        =>:\n'
                   '            0 <= nonnegative = nonnegative\n'
                   '    have guarded_value R = 2\n'
                   '    guarded_value >= 0\n'
                   '    0 <= guarded_value = guarded_value\n',
                   True),
 'grouped': ('claim:\n'
             '    ? 1 = 1\n'
             '    forall a, b R:\n'
             '        a + b = b + a = a + b\n'
             '    have first_value R = 1\n'
             '    have second_value R = 2\n'
             '    first_value + second_value = second_value + first_value = first_value + '
             'second_value\n',
             True),
 'long': ('claim:\n'
          '    ? 1 = 1\n'
          '    forall term R:\n'
          '        term = term + 0 = term + 0 + 0 = term\n'
          '    have long_value R = 2\n'
          '    long_value = long_value + 0 = long_value + 0 + 0 = long_value\n',
          True)}


FAILED_CHAIN_CASES = {'direct-middle': ('1 = 1 = 2 = 2\n', False),
 'direct-first': ('1 = 2 = 2\n', False),
 'direct-last': ('1 = 1 = 1 = 2\n', False),
 'direct-mixed': ('0 < 1 = 1 = 2\n', False),
 'direct-wd': ('1 = 1 = 1 / 0\n', False),
 'direct-first-wd': ('1 / 0 = 1 = 1\n', False),
 'universal': ('forall z R:\n    z > 0\n    =>:\n        z + 0 = z = 0\n        z = z\n',
               False),
 'claim-universal': ('claim:\n'
                     '    ? forall c R:\n'
                     '        c > 0\n'
                     '        =>:\n'
                     '            c + 0 = c = 0\n'
                     '    c > 0\n',
                     False),
 'claim-nonforall': ('claim:\n    ? 1 = 1 = 2 = 2\n    1 = 1\n', False),
 'universal-wd': ('forall wd R:\n    wd + 0 = wd = 1 / 0\n', False),
 'nested-claim': ('claim:\n'
                  '    ? forall outer R:\n'
                  '        outer > 0\n'
                  '        =>:\n'
                  '            outer >= 0\n'
                  '    forall inner R:\n'
                  '        inner > 0\n'
                  '        =>:\n'
                  '            inner + 0 = inner = 0\n'
                  '            inner = inner\n',
                  False),
 'cited-prefix': ('forall left, middle, right R:\n'
                  '    left = middle\n'
                  '    =>:\n'
                  '        left = middle = right = right\n'
                  '        left = left\n',
                  False),
 'mixed-failed-inequality': ('1 = 1 < 0\n', False),
 'only-inequalities': ('1 < 2 < 1\n', False),
 'positive-chain': ('1 = 1 = 1\n', True),
 'definition': ('prop failed_chain_condition(x R):\n    x + 0 = x = 0\n', True),
 'claim-goal-wd-before-entry': ('claim:\n'
                                '    ? forall not_entered R:\n'
                                '        not_entered + 0 = not_entered = 1 / 0\n'
                                '    1 = 1\n',
                                False)}

LOCAL_SOURCE_EQUALITY_CASES = {'failed-prefix': ('forall x R:\n'
                   '    x > 0\n'
                   '    =>:\n'
                   '        x + 0 = x = 0 + x\n'
                   '        x < 0\n',
                   False),
 'successful-universal': ('forall y R:\n    y + 0 = y = 0 + y\n', True),
 'claim-closing-prefix': ('claim:\n'
                          '    ? forall c R:\n'
                          '        c > 0\n'
                          '        =>:\n'
                          '            c + 0 = c = 0 + c\n'
                          '            c < 0\n'
                          '    c > 0\n',
                          False),
 'claim-before-closing': ('claim:\n    ? forall d R:\n        d + 0 = d = 0 + d\n    2 = 3\n',
                          False),
 'nested-claim': ('claim:\n'
                  '    ? forall a R:\n'
                  '        a > 0\n'
                  '        =>:\n'
                  '            a >= 0\n'
                  '    forall b R:\n'
                  '        b > 0\n'
                  '        =>:\n'
                  '            b + 0 = b = 0 + b\n'
                  '            b < 0\n',
                  False),
 'unexecuted-chain': ('forall u R:\n'
                      '    u > 0\n'
                      '    =>:\n'
                      '        u < 0\n'
                      '        u + 0 = u = 0 + u\n',
                      False),
 'definition': ('prop local_chain_condition(p R):\n    p + 0 = p = 0 + p\n', True),
 'atomic-local': ('forall q R:\n    q > 0\n    =>:\n        q + 0 = q\n        q < 0\n',
                  False),
 'theorem': ('thm local_equality_law:\n    ? forall t R:\n        t + 0 = t = 0 + t\n', True),
 'failed-chain': ('forall z R:\n    z > 0\n    =>:\n        z + 0 = z = 0\n        z = z\n',
                  False),
 'strategy-with-body': ('strategy local_equality_strategy:\n'
                        '    ? forall s R:\n'
                        '        s + 0 = s = 0 + s\n'
                        '    s + 0 = s = 0 + s\n',
                        True),
 'cited-equalities': ('forall first, middle, last R:\n'
                      '    first = middle\n'
                      '    middle = last\n'
                      '    =>:\n'
                      '        first = middle = last\n'
                      '        first < first\n',
                      False),
 'mixed-chain': ('forall mixed R:\n'
                 '    mixed > 0\n'
                 '    =>:\n'
                 '        0 < mixed = mixed + 0\n'
                 '        mixed < 0\n',
                 False)}

FAILED_CLAIM_CASES = {'canonical': ('examples/test_statements/negative/claim_stmt/retained-quantified-context.lit',
               False),
 'canonical-positive': ('examples/reading/claim_context.lit', True),
 'false-nonempty-claim': ('examples/test_statements/negative/claim_stmt/false-nonempty-claim.lit',
                          False),
 'false-bodyless-claim': ('examples/test_statements/negative/claim_stmt/false-bodyless-claim.lit',
                          False),
 'local-name-does-not-escape': ('examples/test_statements/negative/claim_stmt/local-name-does-not-escape.lit',
                                False)}
FAILED_CLAIM_INLINE_CASES = {'quantified-body-failure': ('claim:\n'
                             '    ? forall x R:\n'
                             '        x > 0\n'
                             '        =>:\n'
                             '            x >= 0\n'
                             '    x > 0\n'
                             '    2 = 3\n'
                             '    x >= 0\n',
                             False),
 'closing-prefix-failure': ('claim:\n    ? forall t R:\n        t = t\n        t >= 0\n    t = t\n',
                            False),
 'nonforall-body-failure': ('claim:\n'
                            '    ? 1 = 1\n'
                            '    have claim_inner R = 2\n'
                            '    claim_inner = 2\n'
                            '    2 = 3\n'
                            '    4 = 4\n',
                            False),
 'premise-inference-body-failure': ('prop claim_positive(v R):\n'
                                    '    v > 0\n'
                                    '\n'
                                    'claim:\n'
                                    '    ? forall v R:\n'
                                    '        $claim_positive(v)\n'
                                    '        =>:\n'
                                    '            v >= 0\n'
                                    '    v > 0\n'
                                    '    2 = 3\n'
                                    '    v >= 0\n',
                                    False),
 'nested-body-failure': ('claim:\n'
                         '    ? forall outer_x R:\n'
                         '        outer_x > 0\n'
                         '        =>:\n'
                         '            outer_x >= 0\n'
                         '    claim:\n'
                         '        ? forall inner_y R:\n'
                         '            inner_y < 0\n'
                         '            =>:\n'
                         '                inner_y <= 0\n'
                         '        outer_x > 0\n'
                         '        inner_y < 0\n'
                         '        2 = 3\n'
                         '    outer_x >= 0\n',
                         False),
 'goal-wd-failure': ('claim:\n    ? 1 / 0 = 0\n    1 = 1\n', False),
 'positive-claim': ('claim:\n'
                    '    ? forall good_x R:\n'
                    '        good_x > 0\n'
                    '        =>:\n'
                    '            good_x >= 0\n'
                    '    good_x > 0\n',
                    True),
 'positive-local-helper': ('claim:\n'
                           '    ? 1 = 1\n'
                           '    have success_inner R = 2\n'
                           '    success_inner = 2\n',
                           True)}
EMPTY_DOMAIN_CASES = {
    'empty': ('examples/proof_nodes/forall/empty_parameter_domain.lit', True),
    'publication-failure': ('examples/negative/exact_function_domains/empty_forall_false_publication.lit', False),
    'wd-failure': ('examples/negative/exact_function_domains/empty_forall_undefined_conclusion.lit', False),
    'replacement': ('examples/test_statements/have_by_replacement_axiom_stmt.lit', True),
}
EMPTY_DOMAIN_LATER_GROUP = 'forall a R, b {}:\n    a = b\n'
EQUIVALENCE_CASES = {
    'simple': ('examples/test_statements/release_basics/fixtures/L/forall-iff.lit', True),
    'directions': ('lean/examples/equivalence_directions/statement.lit', True),
    'cross-guard': ('examples/wd_negative/quantifier_domain_iff_cross_assumption.lit', False),
    'reverse-guard': ('examples/test_statements/release_basics/fixtures/W/iff-guard-cannot-cross.lit', False),
}
# Checked one statement per turn in one persistent strict Session. Failed
# directions leave earlier accepted context available; none is a user axiom.
EQUIVALENCE_INLINE_CASES = {
    'forward-failure': ('forall failure_x R:\n    =>:\n        failure_x = failure_x\n    <=>:\n        failure_x = 0\n', False),
    'reverse-failure': ('forall failure_y R:\n    =>:\n        failure_y = 0\n    <=>:\n        failure_y = failure_y\n', False),
    'unquantified': ('forall:\n    =>:\n        1 = 1\n    <=>:\n        2 = 2\n', True),
    'multiple': ('forall a, b R:\n    =>:\n        a = b\n        a = a\n    <=>:\n        b = a\n        b = b\n', True),
    'empty': ('forall empty_iff_a, empty_iff_b {}:\n    =>:\n        1 = 2\n    <=>:\n        2 = 3\n', True),
    'nested-premise': ('forall:\n    forall nested_a R:\n        forall nested_b R:\n            nested_b = nested_b\n        =>:\n            nested_a = nested_a\n        <=>:\n            nested_a + 0 = nested_a\n    =>:\n        1 = 1\n', True),
}
FUNCTION_PROPERTY_INLINE_CASES = {'standard-return': ('have fn property_reader_q(x R) Q = 0\n'
                     '\n'
                     'property_reader_q $in fn(y R) R\n'
                     '\n'
                     'property_reader_q(1) $in C\n',
                     True),
 'codomain-return': ('have fn property_reader_q(x R) Q = 0\n'
                     '\n'
                     'property_reader_q $in fn(y R) R\n'
                     '\n'
                     'property_reader_q(1) $in Q\n',
                     True),
 'alias-standard-return-after-interface': ('have fn property_reader_q(x R) Q = 0\n'
                                           '\n'
                                           'property_reader_q $in fn(y R) R\n'
                                           '\n'
                                           'let property_reader_alias = property_reader_q\n'
                                           '\n'
                                           'property_reader_alias $in fn(x R) Q\n'
                                           '\n'
                                           'property_reader_alias(1) $in C\n',
                                           True),
 'alias-codomain-return': ('have fn property_reader_q(x R) Q = 0\n'
                           '\n'
                           'property_reader_q $in fn(y R) R\n'
                           '\n'
                           'let property_reader_alias = property_reader_q\n'
                           '\n'
                           'property_reader_alias $in fn(x R) Q\n'
                           '\n'
                           'property_reader_alias(1) $in Q\n',
                           True),
 'guard-standard-return': ('have fn property_reader_guard(x R: x != 0) R = 1 / x\n'
                           '\n'
                           'property_reader_guard(2) $in C\n',
                           True),
 'guard-failure': ('have fn property_reader_guard(x R: x != 0) R = 1 / x\n\nproperty_reader_guard(0) $in C\n',
                   False),
 'known-exact': ('have fn property_reader_entries(r, c closed_range(1, 2)) R = r + c\n'
                 '\n'
                 'property_reader_entries $in matrix(R, 2, 2)\n',
                 True),
 'declared-exact': ('fn(r, c closed_range(1, 2)) R {r + c} $in matrix(R, 2, 2)\n', True),
 'declared-alias-exact': ('let property_reader_literal = fn(r, c closed_range(1, 2)) R {r + c}\n'
                          '\n'
                          'property_reader_literal $in matrix(R, 2, 2)\n',
                          True),
 'wrong-matrix-domain': ('have fn property_reader_entries(r, c closed_range(1, 2)) R = r + c\n'
                         '\n'
                         'property_reader_entries $in matrix(R, 2, 3)\n',
                         False),
 'wrong-return': ('have fn property_reader_entries(r, c closed_range(1, 2)) R = r + c\n'
                  '\n'
                  'property_reader_entries $in matrix(Z, 2, 2)\n',
                  False),
 'widened-matrix': ('have fn property_reader_entries(r, c closed_range(1, 2)) R = r + c\n'
                    '\n'
                    'property_reader_entries $in matrix(C, 2, 2)\n',
                    True),
 'nested-standard-return': ('have fn property_reader_builder(t R: t != 0) fn(x R) R = fn(x R) R {t + x}\n'
                            '\n'
                            'property_reader_builder(1)(2) $in C\n',
                            True),
 'nested-codomain-return': ('have fn property_reader_builder(t R: t != 0) fn(x R) R = fn(x R) R {t + x}\n'
                            '\n'
                            'property_reader_builder(1)(2) $in R\n',
                            True),
 'dependent-input-standard-return': ('have fn property_reader_pick(n N, k Z: 1 <= k <= n) R = k\n'
                                     '\n'
                                     'property_reader_pick(2, 1) $in C\n',
                                     True),
 'apply-guarded': ('have fn property_reader_guard(x R: x != 0) R = 1 / x\n'
                   '\n'
                   'have fn property_reader_apply(g fn(x R: x != 0) R) R = g(1)\n'
                   '\n'
                   'property_reader_apply(property_reader_guard) $in C\n',
                   True),
 'apply-wrong-domain': ('have fn property_reader_apply(g fn(x R: x != 0) R) R = g(1)\n'
                        '\n'
                        'property_reader_apply(fn(x R) R {x}) $in R\n',
                        False),
 'apply-literal-guarded': ('have fn property_reader_apply(g fn(x R: x != 0) R) R = g(1)\n'
                           '\n'
                           'property_reader_apply(fn(x R: x != 0) R {1 / x}) $in C\n',
                           True),
 'positive-standard-return': ('have fn property_reader_positive(x R) R+ = 1\n'
                              '\n'
                              'property_reader_positive(2) $in C\n',
                              True),
 'empty-exact': ('have fn property_reader_empty(r closed_range(1, 0), c closed_range(1, 3)) R = 0\n'
                 '\n'
                 'property_reader_empty $in matrix(R, 0, 3)\n',
                 True),
 'local-exact': ('claim:\n'
                 '    ? forall property_local fn(r, c closed_range(1, 2)) R:\n'
                 '        property_local $in matrix(R, 2, 2)\n'
                 '    property_local $in matrix(R, 2, 2)\n',
                 True),
 'local-standard-return': ('claim:\n'
                           '    ? forall property_callable fn(x R) R:\n'
                           '        property_callable(1) $in C\n'
                           '    property_callable(1) $in C\n',
                           True),
 'local-codomain-return': ('claim:\n'
                           '    ? forall property_callable_q fn(x R) Q:\n'
                           '        property_callable_q(1) $in Q\n'
                           '    property_callable_q(1) $in Q\n',
                           True),
 'invalid-literal-body': ('fn(r, c closed_range(1, 2)) Z {1 / 2} $in matrix(Z, 2, 2)\n', False),
 'aliased-nested-standard-return': ('have property_reader_range set = fn(x R) R\n'
                                    '\n'
                                    'have fn property_reader_aliased_builder(t R) property_reader_range = '
                                    'fn(x R) R {t + x}\n'
                                    '\n'
                                    'property_reader_aliased_builder(1)(2) $in C\n',
                                    True),
 'aliased-nested-codomain-return': ('have property_reader_range set = fn(x R) R\n'
                                    '\n'
                                    'have fn property_reader_aliased_builder(t R) property_reader_range = '
                                    'fn(x R) R {t + x}\n'
                                    '\n'
                                    'property_reader_aliased_builder(1)(2) $in R\n',
                                    True)}

FUNCTION_MEMBERSHIP_CASES = {'exact': ('examples/proof_nodes/atomic/by_builtin_strategy/exact_function_space_membership.lit', True),
 'return-alias': ('examples/proof_nodes/atomic/by_builtin_strategy/function_space_return_carrier_aliases.lit',
                  True),
 'cart': ('examples/proof_nodes/atomic/by_builtin_strategy/cart_membership.lit', True),
 'cart-zero-one': ('examples/proof_nodes/atomic/by_builtin_rule/cart_zero_one_membership.lit', True),
 'finite-application': ('examples/proof_nodes/atomic/by_builtin_strategy/finite_function_application_membership.lit',
                        True),
 'homogeneous-cart': ('examples/proof_nodes/atomic/by_builtin_rule/homogeneous_cartesian_sequence_membership.lit',
                      True),
 'short-domain': ('examples/negative/exact_function_domains/default_short_domain.lit', False)}
FUNCTION_MEMBERSHIP_INLINE_CASES = {'empty': ('fn(x {}) Z {0} $in fn(y {}) R\n', True),
 'composition': ('compose(fn(x R) Z {0}, fn(y R) R {y}) $in fn(z R) R\n', True),
 'matrix': ('zero_matrix(2, 3) $in matrix(C, 2, 3)\n', True),
 'membership-source': ('claim:\n'
                       '    ? forall reader_input fn(x R) Z:\n'
                       '        reader_input $in fn(y R) R\n'
                       '    reader_input $in fn(y R) R\n',
                       True),
 'wrong-cart-length': ('(1, 2) $in cart(R)\n', False),
 'guard': ('have fn reader_guard(x Z: x != 0) R = 1 / x\n\nreader_guard $in fn(y Z: y != 0) C\n', True),
 'cart-alias': ('have ReaderRect set = cart(R, Z)\n\n(1, 2) $in ReaderRect\n', True),
 'template': ('template<S set, z S>:\n'
              '    have fn reader_const(x S) S = z\n'
              '\n'
              '\\reader_const<R, 0> $in fn(x R) C\n',
              True),
 'returned': ('have fn reader_builder(t R) fn(x R) Z = fn(x R) Z {0}\n\nreader_builder(1) $in fn(y R) R\n',
              True),
 'dropped-guard': ('have fn reader_guard(x Z: x != 0) R = 1 / x\n\nreader_guard $in fn(y Z) C\n', False),
 'selector': ('claim:\n'
              '    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2):\n'
              '        exist g cart_n(R, 2) st {$has_gradient_at(f, p, 2, g)}\n'
              '        =>:\n'
              '            gradient_at(f, p, 2) $in fn(k closed_range(1, 2)) C\n'
              '    gradient_at(f, p, 2) $in fn(k closed_range(1, 2)) R\n'
              '    gradient_at(f, p, 2) $in fn(k closed_range(1, 2)) C\n',
              True),
 'selector-search-boundary': ('claim:\n'
                              '    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2):\n'
                              '        exist g cart_n(R, 2) st {$has_gradient_at(f, p, 2, g)}\n'
                              '        =>:\n'
                              '            gradient_at(f, p, 2) $in fn(k closed_range(1, 2)) C\n'
                              '    gradient_at(f, p, 2) $in fn(k closed_range(1, 2)) C\n',
                              False),
 'empty-equivalent': ('fn(x {}) Z {0} $in finite_seq(R, 0)\n', True),
 'complex-cart': ('(i, 0) $in cart(C, R)\n', True),
 'return-bound': ('fn(x R) R {x} $in fn(y R) Z\n', False),
 'guarded-interval-search-boundary': ('have fn reader_interval(k closed_range(1, 2)) Z = 0\n'
                                      'reader_interval $in fn(y Z: 1 <= y, y <= 2) R\n',
                                      False)}

MATRIX_MEMBERSHIP_INLINE_CASES = {'constants': ('zero_matrix(2, 3) $in fn(r closed_range(1, 2), c closed_range(1, 3)) C\n', True),
 'matrix-space': ('zero_matrix(2, 3) $in matrix(C, 2, 3)\n', True),
 'identity': ('identity_matrix(2) $in fn(r closed_range(1, 2), c closed_range(1, 2)) R\n', True),
 'real-input': ('have fn matrix_reader_real(r closed_range(1, 2), c closed_range(1, 3)) R = r + c\n'
                '\n'
                'transpose(matrix_reader_real, 2, 3) $in fn(r closed_range(1, 3), c closed_range(1, 2)) R\n',
                True),
 'complex-input': ('have fn matrix_reader_complex(r closed_range(1, 2), c closed_range(1, 3)) C = i\n'
                   '\n'
                   'transpose(matrix_reader_complex, 2, 3) $in fn(r closed_range(1, 3), c closed_range(1, '
                   '2)) C\n',
                   True),
 'real-operands': ('have fn matrix_reader_real(r closed_range(1, 2), c closed_range(1, 3)) R = r + c\n'
                   '\n'
                   'matrix_add(matrix_reader_real, matrix_reader_real, 2, 3) $in fn(r closed_range(1, 2), c '
                   'closed_range(1, 3)) C\n',
                   True),
 'finite-operands': ('diagonal_matrix((2, 3), 2) $in fn(r closed_range(1, 2), c closed_range(1, 2)) R\n',
                     True),
 'returned-input': ('have fn matrix_reader_make(t R) matrix(R, 2, 2) = fn(r closed_range(1, 2), c '
                    'closed_range(1, 2)) R {t + r + c}\n'
                    '\n'
                    'transpose(matrix_reader_make(1), 2, 2) $in fn(r closed_range(1, 2), c closed_range(1, '
                    '2)) R\n',
                    True),
 'alias-input': ('let matrix_reader_zero = zero_matrix(2, 3)\n'
                 '\n'
                 'matrix_reader_zero $in fn(r closed_range(1, 2), c closed_range(1, 3)) C\n',
                 True),
 'empty-input': ('zero_matrix(0, 3) $in fn(r closed_range(1, 0), c closed_range(1, 3)) R\n', True),
 'wrong-domain': ('zero_matrix(2, 3) $in fn(r closed_range(1, 2), c closed_range(1, 2)) C\n', False),
 'dropped-rows': ('zero_matrix(2, 3) $in fn(r R, c closed_range(1, 3)) C\n', False),
 'nonreal-return': ('have fn matrix_reader_complex(r closed_range(1, 2), c closed_range(1, 3)) C = i\n'
                    '\n'
                    'transpose(matrix_reader_complex, 2, 3) $in fn(r closed_range(1, 3), c closed_range(1, '
                    '2)) R\n',
                    False),
 'guard-mismatch': ('zero_matrix(2, 3) $in fn(r closed_range(1, 2), c closed_range(1, 3): r = 1) C\n', False),
 'local-input': ('claim:\n'
                 '    ? forall reader_local matrix(R, 2, 3):\n'
                 '        transpose(reader_local, 2, 3) $in fn(r closed_range(1, 3), c closed_range(1, 2)) '
                 'R\n'
                 '    transpose(reader_local, 2, 3) $in fn(r closed_range(1, 3), c closed_range(1, 2)) R\n',
                 True),
 'vector-interface': ('have fn matrix_reader_real(r closed_range(1, 2), c closed_range(1, 3)) R = r + c\n'
                      '\n'
                      'matrix_apply(matrix_reader_real, (1, 2, 3), 2, 3) $in fn(k closed_range(1, 2)) R\n',
                      True),
 'bad-application': ('zero_matrix(2, 3)(1, 4) $in C\n', False)}

CASE_CONSEQUENCES_INLINE_CASES = {'accepted-cases': ('prop case_prefix_nonnegative(x R):\n'
                    '    x >= 0\n'
                    'have case_prefix_value R\n'
                    'by cases:\n'
                    '    ? $case_prefix_nonnegative(0)\n'
                    '    case case_prefix_value = 0:\n'
                    '        by def $case_prefix_nonnegative(0)\n'
                    '    case case_prefix_value != 0:\n'
                    '        by def $case_prefix_nonnegative(0)\n',
                    True),
 'accepted-square-cases': ('prop case_prefix_nonnegative(x R):\n'
                           '    x >= 0\n'
                           'have case_prefix_value R\n'
                           'by cases:\n'
                           '    ? $case_prefix_nonnegative(case_prefix_value ^ 2)\n'
                           '    case case_prefix_value = 0:\n'
                           '        by def $case_prefix_nonnegative(case_prefix_value ^ 2)\n'
                           '    case case_prefix_value != 0:\n'
                           '        by def $case_prefix_nonnegative(case_prefix_value ^ 2)\n',
                           True),
 'partial-target-inferences': ('prop case_prefix_nonnegative(x R):\n'
                               '    x >= 0\n'
                               'have case_prefix_value R\n'
                               'by cases:\n'
                               '    ? $case_prefix_nonnegative(case_prefix_value ^ 2)\n'
                               '    ? case_prefix_value = 0\n'
                               '    case case_prefix_value = 0:\n'
                               '        by def $case_prefix_nonnegative(case_prefix_value ^ 2)\n'
                               '    case case_prefix_value != 0:\n'
                               '        by def $case_prefix_nonnegative(case_prefix_value ^ 2)\n',
                               False)}

COMPLETED_CASE_PREFIX_INLINE_CASES = {'prior-complete-second-fails-third-unchecked': ('prop case_prefix_nonnegative(x R):\n'
                                                 '    x >= 0\n'
                                                 'have case_prefix_value R\n'
                                                 'by cases:\n'
                                                 '    ? case_prefix_value = case_prefix_value\n'
                                                 '    case case_prefix_value = 0:\n'
                                                 '        by def '
                                                 '$case_prefix_nonnegative(case_prefix_value)\n'
                                                 '    case case_prefix_value != 0:\n'
                                                 '        3 = 3\n'
                                                 '        2 = 3\n'
                                                 '    case case_prefix_value = case_prefix_value:\n'
                                                 '        4 = 4\n',
                                                 False),
 'negative-common-goal': ('prop case_prefix_nonnegative(x R):\n'
                          '    x >= 0\n'
                          'have case_prefix_value R\n'
                          'by cases:\n'
                          '    ? $case_prefix_nonnegative(case_prefix_value)\n'
                          '    case case_prefix_value = 0:\n'
                          '        by def $case_prefix_nonnegative(case_prefix_value)\n'
                          '    case case_prefix_value != 0:\n'
                          '        3 = 3\n'
                          '        2 = 3\n'
                          '    case case_prefix_value = case_prefix_value:\n'
                          '        4 = 4\n',
                          False),
 'completed-impossible-branch': ('by cases:\n'
                                 '    ? 0 = 0\n'
                                 '    case 0 != 0:\n'
                                 '        impossible 0 != 0\n'
                                 '    case 0 = 0:\n'
                                 '        2 = 3\n'
                                 '    case 1 = 1:\n'
                                 '        4 = 4\n',
                                 False),
 'completed-first-closing-goal-fails': ('by cases:\n'
                                        '    ? 2 = 3\n'
                                        '    case 2 = 3:\n'
                                        '        0 = 0\n'
                                        '    case 2 != 3:\n'
                                        '        0 = 0\n',
                                        False),
 'two-complete-then-failed': ('by cases:\n'
                              '    ? 0 = 0\n'
                              '    case 0 = 0:\n'
                              '        3 = 3\n'
                              '    case 1 = 1:\n'
                              '        4 = 4\n'
                              '    case 2 = 2:\n'
                              '        2 = 3\n'
                              '    case 3 = 3:\n'
                              '        5 = 5\n',
                              False),
 'nested-completed-cases': ('prop case_prefix_nonnegative(x R):\n'
                            '    x >= 0\n'
                            'have case_prefix_value R\n'
                            'by cases:\n'
                            '    ? case_prefix_value = case_prefix_value\n'
                            '    case case_prefix_value = 0:\n'
                            '        by cases:\n'
                            '            ? case_prefix_value = case_prefix_value\n'
                            '            case case_prefix_value = 0:\n'
                            '                by def $case_prefix_nonnegative(case_prefix_value)\n'
                            '            case case_prefix_value != 0:\n'
                            '                0 = 0\n'
                            '    case case_prefix_value != 0:\n'
                            '        2 = 3\n',
                            False),
 'complete-positive': ('prop case_prefix_nonnegative(x R):\n'
                       '    x >= 0\n'
                       'have case_prefix_value R\n'
                       'by cases:\n'
                       '    ? case_prefix_value = case_prefix_value\n'
                       '    case case_prefix_value = 0:\n'
                       '        by def $case_prefix_nonnegative(case_prefix_value)\n'
                       '    case case_prefix_value != 0:\n'
                       '        3 = 3\n',
                       True),
 'sibling-cannot-cite-first-property': ('prop case_prefix_nonnegative(x R):\n'
                                        '    x >= 0\n'
                                        'have case_prefix_value R\n'
                                        'by cases:\n'
                                        '    ? case_prefix_value = case_prefix_value\n'
                                        '    case case_prefix_value = 0:\n'
                                        '        by def '
                                        '$case_prefix_nonnegative(case_prefix_value)\n'
                                        '    case case_prefix_value != 0:\n'
                                        '        $case_prefix_nonnegative(case_prefix_value)\n',
                                        False),
 'quantified-completed-prefix': ('prop case_prefix_nonnegative(x R):\n'
                                 '    x >= 0\n'
                                 'claim:\n'
                                 '    ? forall case_prefix_x R:\n'
                                 '        case_prefix_x = case_prefix_x\n'
                                 '    by cases:\n'
                                 '        ? case_prefix_x = case_prefix_x\n'
                                 '        case case_prefix_x = 0:\n'
                                 '            by def $case_prefix_nonnegative(case_prefix_x)\n'
                                 '        case case_prefix_x != 0:\n'
                                 '            2 = 3\n',
                                 False),
 'closing-prefix': ('by cases:\n'
                    '    ? 0 = 0\n'
                    '    ? 2 = 3\n'
                    '    case 2 = 3:\n'
                    '        0 = 0\n'
                    '    case 2 != 3:\n'
                    '        0 = 0\n',
                    False)}

FAILED_CASE_CONTEXT_INLINE_CASES = {'body-first': ('by cases:\n'
                '    ? 0 = 0\n'
                '    case 0 = 0:\n'
                '        2 = 3\n'
                '    case 0 != 0:\n'
                '        0 = 0\n',
                False),
 'body-after-prefix': ('by cases:\n'
                       '    ? 0 = 0\n'
                       '    case 0 = 0:\n'
                       '        0 = 0\n'
                       '        2 = 3\n'
                       '        4 = 4\n'
                       '    case 0 != 0:\n'
                       '        0 = 0\n',
                       False),
 'closing-goal': ('by cases:\n'
                  '    ? 2 = 3\n'
                  '    case 0 = 0:\n'
                  '        0 = 0\n'
                  '    case 0 != 0:\n'
                  '        impossible 0 != 0\n',
                  False),
 'closing-impossible': ('by cases:\n'
                        '    ? 0 = 0\n'
                        '    case 0 = 0:\n'
                        '        impossible 1 = 1\n'
                        '    case 0 != 0:\n'
                        '        impossible 0 != 0\n',
                        False),
 'body-second': ('claim:\n'
                 '    ? forall case_context_x R:\n'
                 '        case_context_x = case_context_x\n'
                 '    by cases:\n'
                 '        ? case_context_x = case_context_x\n'
                 '        case case_context_x = 0:\n'
                 '            case_context_x = case_context_x\n'
                 '        case case_context_x != 0:\n'
                 '            2 = 3\n',
                 False),
 'coverage-wd': ('by cases:\n'
                 '    ? 0 = 0\n'
                 '    case 1 / 0 = 1:\n'
                 '        0 = 0\n'
                 '    case 1 / 0 != 1:\n'
                 '        0 = 0\n',
                 False),
 'nested-cases': ('by cases:\n'
                  '    ? 0 = 0\n'
                  '    case 0 = 0:\n'
                  '        by cases:\n'
                  '            ? 0 = 0\n'
                  '            case 1 = 1:\n'
                  '                2 = 3\n'
                  '            case 1 != 1:\n'
                  '                impossible 1 != 1\n'
                  '    case 0 != 0:\n'
                  '        impossible 0 != 0\n',
                  False),
 'duplicate-conditions': ('by cases:\n'
                          '    ? 0 = 0\n'
                          '    case 0 = 0:\n'
                          '        0 = 0\n'
                          '    case 0 = 0:\n'
                          '        2 = 3\n',
                          False),
 'conjunction': ('by cases:\n    ? 0 = 0\n    case 0 = 0 and 1 = 1:\n        2 = 3\n', False),
 'chain': ('by cases:\n    ? 0 = 0\n    case 0 = 0 = 0:\n        2 = 3\n', False),
 'accepted': ('by cases:\n'
              '    ? 0 = 0\n'
              '    case 0 = 0:\n'
              '        0 = 0\n'
              '    case 0 != 0:\n'
              '        0 = 0\n',
              True),
 'source-style': ('# 范围与分支\n'
                  'by cases: # 按情况推理\n'
                  '    ? 0 = 0\n'
                  '    case (0) = 0: # 当前条件\n'
                  '        2 = 3\n'
                  '    case 0 != 0:\n'
                  '        0 = 0\n',
                  False),
 'existing-cases-missing': ('claim:\n'
                            '    ? forall x R:\n'
                            '        x = 0 or x = 1\n'
                            '        =>:\n'
                            '            x >= 0\n'
                            '    by cases:\n'
                            '        ? x >= 0\n'
                            '        case x = 0:\n'
                            '            x >= 0\n',
                            False),
 'existing-cases-false': ('claim:\n'
                          '    ? forall x R:\n'
                          '        x = 0 or x = 1\n'
                          '        =>:\n'
                          '            x > 0\n'
                          '    by cases:\n'
                          '        ? x > 0\n'
                          '        case x = 0:\n'
                          '            x > 0\n'
                          '        case x = 1:\n'
                          '            x > 0\n',
                          False),
 'claim-prefix': ('claim:\n    ? 0 = 0\n    3 = 3\n    2 = 3\n    4 = 4\n', False),
 'case-scope-failure': ('have case_context_value R\n'
                        '\n'
                        'by cases:\n'
                        '    ? case_context_value = case_context_value\n'
                        '    case case_context_value = 0:\n'
                        '        3 = 3\n'
                        '        2 = 3\n'
                        '    case case_context_value != 0:\n'
                        '        case_context_value = case_context_value\n',
                        False),
 'scope-recovery': ('have case_context_value R\n'
                    '\n'
                    'by cases:\n'
                    '    ? case_context_value = case_context_value\n'
                    '    case case_context_value = 0:\n'
                    '        3 = 3\n'
                    '        2 = 3\n'
                    '    case case_context_value != 0:\n'
                    '        case_context_value = case_context_value\n'
                    '\n'
                    'case_context_value = 0\n'
                    '\n'
                    'case_context_value $in R\n',
                    False)}

FAILED_HEADER_CASES = {'cases-missing': ('examples/test_statements/release_basics/fixtures/P/cases-missing-branch.lit', False),
 'cases-false': ('examples/test_statements/release_basics/fixtures/P/cases-false-goal.lit', False),
 'contra-closing': ('examples/test_statements/negative/by_contra_stmt/fake-contradiction.lit', False),
 'claim-positive': ('examples/test_statements/claim_stmt.lit', True)}
FAILED_HEADER_INLINE_CASES = {
    'selector-body': FUNCTION_MEMBERSHIP_INLINE_CASES['selector-search-boundary'],
    **{'claim-body': ('claim:\n    ? 0 = 0\n    0 = 1\n', False),
 'nested': ('claim:\n    ? 0 = 0\n    0 = 0\n    claim:\n        ? 1 = 1\n        1 = 2\n', False),
 'goal-wd': ('claim:\n    ? 1 / 0 = 1\n    1 = 1\n', False),
 'claim-closing': ('claim:\n    ? 0 = 1\n    1 = 1\n', False),
 'sketch-body': ('sketch:\n    0 = 1\n', False),
 'contra-body': ('by contra:\n    ? 0 = 1\n    2 = 3\n    impossible 0 = 1\n', False),
 'cases-body': ('by cases:\n    ? 0 = 0\n    case 0 = 0:\n        2 = 3\n    case 0 != 0:\n        0 = 0\n',
                False),
 'forall-closing': ('forall reader_x R:\n    reader_x = 0\n', False),
 'theorem-body': ('thm reader_failed_theorem:\n'
                  '    ? forall reader_y R:\n'
                  '        reader_y = reader_y\n'
                  '    0 = 1\n',
                  False),
 'claim-success': ('claim:\n    ? 1 = 1\n    1 = 1\n', True),
 'parse-empty-claim': ('claim:\n    ? 0 = 1\n', False),
 'parse-incomplete-contra': ('by contra:\n    ? 0 = 1\n    2 = 3\n', False),
 'unicode-body': ('# 一个中文注释\nclaim:\n    ? 0 = 0\n    0 = 1\n', False)}
}

FUNCTION_DOMAIN_CASES = {
    'membership': ('examples/stmt_nodes/release_and_expand/builtin_thm/fn_set_member.lit', True),
    'tuple': ('examples/stmt_nodes/release_and_expand/builtin_thm/tuple_equal_from_coordinates.lit', True),
    'cart': ('examples/stmt_nodes/release_and_expand/builtin_thm/cart_member_from_coordinates.lit', True),
    'matrix-interface': ('examples/test_objs/matrix_fn_space.lit', True),
    'short-domain': ('examples/negative/exact_function_domains/release_short_domain.lit', False),
    'tuple-length': ('examples/negative/exact_function_domains/tuple_equal_wrong_complete_length.lit', False),
    'dropped-guard': ('examples/negative/exact_function_domains/dropped_guard.lit', False),
}
FUNCTION_DOMAIN_INLINE_CASES = {
    'selected': ('have fn checked_short(k closed_range(1, 2)) R = k\nby thm fn_set_member(checked_short, finite_seq(R, 2)) => checked_short $in finite_seq(R, 2)\n', True),
    'distinct-peers': ('have fn checked_short(k closed_range(1, 2)) R = k\nby thm tuple_equal_from_coordinates((1, 2), checked_short) => (1, 2) = checked_short\n', True),
    'outer-domain': ('claim:\n    ? forall S power_set(R):\n        fn(x S) R {0} $in fn(y S) R\n    release thm fn_set_member(fn(x S) R {0}, fn(y S) R)\n', True),
    'membership-source': ('claim:\n    ? forall input_fn fn(x R) R:\n        input_fn $in fn(y R) R\n    release thm fn_set_member(input_fn, fn(y R) R)\n', True),
    'composition': ('release thm fn_set_member(compose(fn(x R) R {x}, fn(y R) R {y}), fn(z R) R)\n', True),
    'application-return': ('have fn make_domain_fn(t R) fn(x R) R = fn(x R) R {t + x}\nrelease thm fn_set_member(make_domain_fn(1), fn(y R) R)\n', True),
    'template': ('template<S set, z S>:\n    have fn domain_const(x S) S = z\n\nrelease thm fn_set_member(\\domain_const<R, 0>, fn(x R) R)\n', True),
    'matrix-constructor': ('release thm fn_set_member(zero_matrix(2, 3), matrix(R, 2, 3))\n', True),
    'selector': ('claim:\n    ? forall f fn(x cart_n(R, 2)) R, p cart_n(R, 2):\n        exist g cart_n(R, 2) st {$has_gradient_at(f, p, 2, g)}\n        =>:\n            gradient_at(f, p, 2) $in fn(k closed_range(1, 2)) R\n    release thm fn_set_member(gradient_at(f, p, 2), fn(k closed_range(1, 2)) R)\n', True),
    'guard': ('have fn guarded_domain_fn(x R: x != 0) R = 1 / x\nrelease thm fn_set_member(guarded_domain_fn, fn(y R: y != 0) R)\n', True),
    'arity': ('have fn checked_short(k closed_range(1, 2)) R = k\nrelease thm fn_set_member(checked_short, fn(x R, y R) R)\n', False),
    'no-complete': ('release thm fn_set_member(1, fn(x R) R)\n', False),
    'function-wd': ('release thm fn_set_member(1 / 0, fn(x R) R)\n', False),
    'target-wd': ('have fn checked_short(k closed_range(1, 2)) R = k\nrelease thm fn_set_member(checked_short, fn(x R: 1 / x > 0) R)\n', False),
    'selected-short': ('have fn checked_short(k closed_range(1, 2)) R = k\nby thm fn_set_member(checked_short, fn(x R) R) => checked_short $in fn(x R) R\n', False),
    'return-bound': ('have fn domain_identity(x R) R = x\nrelease thm fn_set_member(domain_identity, fn(y R) Z)\n', False),
    'complex-tuple': ('release thm tuple_equal_from_coordinates((i, 0), (i, 0))\n', True),
    'complex-cart': ('release thm cart_member_from_coordinates((i, 0), cart(C, R))\n', True),
}
# Actual ordinary compound inputs checked in one retained strict Session.
AUTOMATIC_STRUCT_ORIGIN_BOOK = {'01-definitions.lit': 'struct ScalarOperations:\n'
                       '    unit R\n'
                       '    combine fn(x, y R) R\n'
                       '    <=>:\n'
                       '        unit = 1\n'
                       '\n'
                       'struct ScalarAction:\n'
                       '    scalars &ScalarOperations\n'
                       '    act fn(a, x R) R\n'
                       '    <=>:\n'
                       '        forall a, b, x R:\n'
                       '            act(scalars.combine(a, b), x) = act(a, act(b, x))\n'
                       '\n'
                       'struct ScalarIdentity<S nonempty_set>:\n'
                       '    zero S\n'
                       '    add fn(x, y S) S\n'
                       '    <=>:\n'
                       '        forall x S:\n'
                       '            add(zero, x) = x\n'
                       '\n'
                       'struct IdentityCarrier<S nonempty_set>:\n'
                       '    scalars &ScalarIdentity<S>\n'
                       '    element S\n',
 '02-proofs.lit': 'forall p &structures::ScalarOperations:\n'
                  '    p.unit = 1\n'
                  '\n'
                  'thm reading_structural_unit:\n'
                  '    ? forall p &structures::ScalarOperations:\n'
                  '        p.unit = 1\n'
                  '\n'
                  'forall p, q &structures::ScalarOperations:\n'
                  '    p.unit = q.unit\n'
                  '\n'
                  'claim:\n'
                  '    ? forall p &structures::ScalarOperations:\n'
                  '        p.unit = 1\n'
                  '    p.unit = 1\n'
                  '\n'
                  'claim:\n'
                  '    ? forall action &structures::ScalarAction, a, b, x R:\n'
                  '        action.act(action.scalars.combine(a, b), x) = action.act(a, '
                  'action.act(b, x))\n'
                  '    release struct def action\n'
                  '\n'
                  'claim:\n'
                  '    ? forall action &structures::ScalarAction:\n'
                  '        action.scalars.unit = 1\n'
                  '    release struct def action.scalars\n'
                  '\n'
                  'claim:\n'
                  '    ? forall S nonempty_set, carrier &structures::IdentityCarrier<S>:\n'
                  '        carrier.scalars.add(carrier.scalars.zero, carrier.scalars.zero) = '
                  'carrier.scalars.zero\n'
                  '    release struct def carrier.scalars\n',
 'litex.config': '[export]\nstructures = "./01-definitions.lit"\nproofs = "./02-proofs.lit"\n',
 'reading-titles.json': '{"kind": "reading_titles", "sources": {"01-definitions.lit": {"zh": '
                        '"结构定义", "en": "Structural definitions"}, "02-proofs.lit": {"zh": '
                        '"结构性质的使用", "en": "Using structural properties"}}}\n'}

AUTOMATIC_STRUCT_ORIGIN_CASES = {'standalone-automatic-law': {'source': 'struct ScalarOperations:\n'
                                        '    unit R\n'
                                        '    combine fn(x, y R) R\n'
                                        '    <=>:\n'
                                        '        unit = 1\n'
                                        '\n'
                                        'struct ScalarAction:\n'
                                        '    scalars &ScalarOperations\n'
                                        '    act fn(a, x R) R\n'
                                        '    <=>:\n'
                                        '        forall a, b, x R:\n'
                                        '            act(scalars.combine(a, b), x) = act(a, act(b, '
                                        'x))\n'
                                        '\n'
                                        'struct ScalarIdentity<S nonempty_set>:\n'
                                        '    zero S\n'
                                        '    add fn(x, y S) S\n'
                                        '    <=>:\n'
                                        '        forall x S:\n'
                                        '            add(zero, x) = x\n'
                                        '\n'
                                        'struct IdentityCarrier<S nonempty_set>:\n'
                                        '    scalars &ScalarIdentity<S>\n'
                                        '    element S\n'
                                        '\n'
                                        'forall p &ScalarOperations:\n'
                                        '    p.unit = 1\n',
                              'success': True},
 'theorem-automatic-law': {'source': 'struct ScalarOperations:\n'
                                     '    unit R\n'
                                     '    combine fn(x, y R) R\n'
                                     '    <=>:\n'
                                     '        unit = 1\n'
                                     '\n'
                                     'struct ScalarAction:\n'
                                     '    scalars &ScalarOperations\n'
                                     '    act fn(a, x R) R\n'
                                     '    <=>:\n'
                                     '        forall a, b, x R:\n'
                                     '            act(scalars.combine(a, b), x) = act(a, act(b, '
                                     'x))\n'
                                     '\n'
                                     'struct ScalarIdentity<S nonempty_set>:\n'
                                     '    zero S\n'
                                     '    add fn(x, y S) S\n'
                                     '    <=>:\n'
                                     '        forall x S:\n'
                                     '            add(zero, x) = x\n'
                                     '\n'
                                     'struct IdentityCarrier<S nonempty_set>:\n'
                                     '    scalars &ScalarIdentity<S>\n'
                                     '    element S\n'
                                     '\n'
                                     'thm reading_structural_unit:\n'
                                     '    ? forall p &ScalarOperations:\n'
                                     '        p.unit = 1\n',
                           'success': True},
 'two-automatic-members': {'source': 'struct ScalarOperations:\n'
                                     '    unit R\n'
                                     '    combine fn(x, y R) R\n'
                                     '    <=>:\n'
                                     '        unit = 1\n'
                                     '\n'
                                     'struct ScalarAction:\n'
                                     '    scalars &ScalarOperations\n'
                                     '    act fn(a, x R) R\n'
                                     '    <=>:\n'
                                     '        forall a, b, x R:\n'
                                     '            act(scalars.combine(a, b), x) = act(a, act(b, '
                                     'x))\n'
                                     '\n'
                                     'struct ScalarIdentity<S nonempty_set>:\n'
                                     '    zero S\n'
                                     '    add fn(x, y S) S\n'
                                     '    <=>:\n'
                                     '        forall x S:\n'
                                     '            add(zero, x) = x\n'
                                     '\n'
                                     'struct IdentityCarrier<S nonempty_set>:\n'
                                     '    scalars &ScalarIdentity<S>\n'
                                     '    element S\n'
                                     '\n'
                                     'forall p, q &ScalarOperations:\n'
                                     '    p.unit = q.unit\n',
                           'success': True},
 'claim-conclusion-failure-after-entry': {'source': 'struct ScalarOperations:\n'
                                                    '    unit R\n'
                                                    '    combine fn(x, y R) R\n'
                                                    '    <=>:\n'
                                                    '        unit = 1\n'
                                                    '\n'
                                                    'struct ScalarAction:\n'
                                                    '    scalars &ScalarOperations\n'
                                                    '    act fn(a, x R) R\n'
                                                    '    <=>:\n'
                                                    '        forall a, b, x R:\n'
                                                    '            act(scalars.combine(a, b), x) = '
                                                    'act(a, act(b, x))\n'
                                                    '\n'
                                                    'struct ScalarIdentity<S nonempty_set>:\n'
                                                    '    zero S\n'
                                                    '    add fn(x, y S) S\n'
                                                    '    <=>:\n'
                                                    '        forall x S:\n'
                                                    '            add(zero, x) = x\n'
                                                    '\n'
                                                    'struct IdentityCarrier<S nonempty_set>:\n'
                                                    '    scalars &ScalarIdentity<S>\n'
                                                    '    element S\n'
                                                    '\n'
                                                    'claim:\n'
                                                    '    ? forall p &ScalarOperations:\n'
                                                    '        p.unit = 2\n'
                                                    '    p.unit = 1\n',
                                          'success': False},
 'claim-repair-after-entry': {'source': 'struct ScalarOperations:\n'
                                        '    unit R\n'
                                        '    combine fn(x, y R) R\n'
                                        '    <=>:\n'
                                        '        unit = 1\n'
                                        '\n'
                                        'struct ScalarAction:\n'
                                        '    scalars &ScalarOperations\n'
                                        '    act fn(a, x R) R\n'
                                        '    <=>:\n'
                                        '        forall a, b, x R:\n'
                                        '            act(scalars.combine(a, b), x) = act(a, act(b, '
                                        'x))\n'
                                        '\n'
                                        'struct ScalarIdentity<S nonempty_set>:\n'
                                        '    zero S\n'
                                        '    add fn(x, y S) S\n'
                                        '    <=>:\n'
                                        '        forall x S:\n'
                                        '            add(zero, x) = x\n'
                                        '\n'
                                        'struct IdentityCarrier<S nonempty_set>:\n'
                                        '    scalars &ScalarIdentity<S>\n'
                                        '    element S\n'
                                        '\n'
                                        'claim:\n'
                                        '    ? forall p &ScalarOperations:\n'
                                        '        p.unit = 1\n'
                                        '    p.unit = 1\n',
                              'success': True},
 'witness-with-structural-parameter': {'source': 'struct ReadingAutoPoint:\n'
                                                 '    x R\n'
                                                 '    y R\n'
                                                 'release thm struct_member((0, 1), '
                                                 '&ReadingAutoPoint)\n'
                                                 'witness exist p &ReadingAutoPoint st {p = p} '
                                                 'from (0, 1)\n',
                                       'success': True},
 'witness-with-structural-membership': {'source': 'struct ReadingAutoPoint:\n'
                                                  '    x R\n'
                                                  '    y R\n'
                                                  'release thm struct_member((0, 1), '
                                                  '&ReadingAutoPoint)\n'
                                                  'witness exist p &ReadingAutoPoint st {p $in '
                                                  '&ReadingAutoPoint} from (0, 1)\n',
                                        'success': True},
 'witness-with-structure': {'source': 'struct ReadingAutoPoint:\n'
                                      '    x R\n'
                                      '    y R\n'
                                      'release thm struct_member((0, 1), &ReadingAutoPoint)\n'
                                      'witness exist p &ReadingAutoPoint st {p.x = 0} from (0, '
                                      '1)\n',
                            'success': False},
 'witness-uses-automatic-field-domain': {'source': 'struct ReadingAutoPoint:\n'
                                                   '    x R\n'
                                                   '    y R\n'
                                                   'release thm struct_member((0, 1), '
                                                   '&ReadingAutoPoint)\n'
                                                   'witness exist p &ReadingAutoPoint st {p.x $in '
                                                   'R} from (0, 1)\n',
                                         'success': False},
 'nested': {'source': '# Field paths produced by substitution use the same flat path as source '
                      'syntax.\n'
                      '# Before: these direct struct consequences failed because substitution '
                      'retained\n'
                      '# (action.scalars).combine / (action.scalars).unit as nested receiver '
                      'objects.\n'
                      '# claim:\n'
                      '#     ? forall action &ScalarAction, a, b, x R:\n'
                      '#         action.act(action.scalars.combine(a, b), x) = action.act(a, '
                      'action.act(b, x))\n'
                      '#     release struct def action\n'
                      "# Boundary: missing fields and another action's scalar operations are not "
                      'licensed.\n'
                      '# Gate: target/release/litex -strict -f '
                      'examples/stmt_nodes/definition/struct_nested_field_instantiation.lit\n'
                      'struct ScalarOperations:\n'
                      '    unit R\n'
                      '    combine fn(x, y R) R\n'
                      '    <=>:\n'
                      '        unit = 1\n'
                      '\n'
                      'struct ScalarAction:\n'
                      '    scalars &ScalarOperations\n'
                      '    act fn(a, x R) R\n'
                      '    <=>:\n'
                      '        forall a, b, x R:\n'
                      '            act(scalars.combine(a, b), x) = act(a, act(b, x))\n'
                      '\n'
                      'claim:\n'
                      '    ? forall action &ScalarAction, a, b, x R:\n'
                      '        action.act(action.scalars.combine(a, b), x) = action.act(a, '
                      'action.act(b, x))\n'
                      '    release struct def action\n'
                      '\n'
                      'claim:\n'
                      '    ? forall action &ScalarAction:\n'
                      '        action.scalars.unit = 1\n'
                      '    release struct def action.scalars\n'
                      '\n'
                      '# Releasing a nested parameterized scalar structure also flattens '
                      'substitutions\n'
                      '# of plain field identifiers, both callable heads and their zero '
                      'arguments.\n'
                      'struct ScalarIdentity<S nonempty_set>:\n'
                      '    zero S\n'
                      '    add fn(x, y S) S\n'
                      '    <=>:\n'
                      '        forall x S:\n'
                      '            add(zero, x) = x\n'
                      '\n'
                      'struct IdentityCarrier<S nonempty_set>:\n'
                      '    scalars &ScalarIdentity<S>\n'
                      '    element S\n'
                      '\n'
                      'claim:\n'
                      '    ? forall S nonempty_set, carrier &IdentityCarrier<S>:\n'
                      '        carrier.scalars.add(carrier.scalars.zero, carrier.scalars.zero) = '
                      'carrier.scalars.zero\n'
                      '    release struct def carrier.scalars\n',
            'success': True},
 'direct': {'source': '# Stmt: ReleaseStructDefStmt\n'
                      '# AST: Stmt::ReleaseAndExpand::ReleaseStructDefStmt\n'
                      '# Run all scenarios and boundaries: python3 examples/test_statements/run.py '
                      '--leaf ReleaseStructDefStmt\n'
                      '\n'
                      '# case: nested-law-opening\n'
                      'struct OpenInner:\n'
                      '    x R\n'
                      '    y R\n'
                      '    <=>:\n'
                      '        x = 0\n'
                      'struct OpenOuter:\n'
                      '    inner &OpenInner\n'
                      '    tag N\n'
                      'claim:\n'
                      '    ? forall p &OpenOuter:\n'
                      '        p.inner.x = 0\n'
                      '    release struct def p.inner\n'
                      '\n'
                      '# case: explicit-direct-opening\n'
                      'struct OpenPoint:\n'
                      '    x R\n'
                      '    y R\n'
                      'claim:\n'
                      '    ? forall p &OpenPoint:\n'
                      '        p.x $in R\n'
                      '    release struct def p\n'
                      '\n'
                      '# case: parameterized-opening\n'
                      'struct OpenPair<A set>:\n'
                      '    left A\n'
                      '    right A\n'
                      'claim:\n'
                      '    ? forall p &OpenPair<R>:\n'
                      '        p.left $in R\n'
                      '    release struct def p\n',
            'success': True},
 'field-parameter-shadow': {'source': 'struct Point:\n'
                                      '    x R\n'
                                      '    y R\n'
                                      'forall x R, p &Point:\n'
                                      '    p.x + x = p.x + x\n',
                            'success': True},
 'standalone-failure-after-opening': {'source': 'struct ScalarOperations:\n'
                                                '    unit R\n'
                                                '    combine fn(x, y R) R\n'
                                                '    <=>:\n'
                                                '        unit = 1\n'
                                                '\n'
                                                'struct ScalarAction:\n'
                                                '    scalars &ScalarOperations\n'
                                                '    act fn(a, x R) R\n'
                                                '    <=>:\n'
                                                '        forall a, b, x R:\n'
                                                '            act(scalars.combine(a, b), x) = '
                                                'act(a, act(b, x))\n'
                                                '\n'
                                                'struct ScalarIdentity<S nonempty_set>:\n'
                                                '    zero S\n'
                                                '    add fn(x, y S) S\n'
                                                '    <=>:\n'
                                                '        forall x S:\n'
                                                '            add(zero, x) = x\n'
                                                '\n'
                                                'struct IdentityCarrier<S nonempty_set>:\n'
                                                '    scalars &ScalarIdentity<S>\n'
                                                '    element S\n'
                                                '\n'
                                                'forall p &ScalarOperations:\n'
                                                '    p.unit = 2\n',
                                      'success': False},
 'forall-goal-formation-failure': {'source': 'struct ScalarOperations:\n'
                                             '    unit R\n'
                                             '    combine fn(x, y R) R\n'
                                             '    <=>:\n'
                                             '        unit = 1\n'
                                             '\n'
                                             'struct ScalarAction:\n'
                                             '    scalars &ScalarOperations\n'
                                             '    act fn(a, x R) R\n'
                                             '    <=>:\n'
                                             '        forall a, b, x R:\n'
                                             '            act(scalars.combine(a, b), x) = act(a, '
                                             'act(b, x))\n'
                                             '\n'
                                             'struct ScalarIdentity<S nonempty_set>:\n'
                                             '    zero S\n'
                                             '    add fn(x, y S) S\n'
                                             '    <=>:\n'
                                             '        forall x S:\n'
                                             '            add(zero, x) = x\n'
                                             '\n'
                                             'struct IdentityCarrier<S nonempty_set>:\n'
                                             '    scalars &ScalarIdentity<S>\n'
                                             '    element S\n'
                                             '\n'
                                             'forall p &ScalarOperations:\n'
                                             '    1 / 0 = 0\n',
                                   'success': False},
 'object-type-preflight': {'source': 'sketch:\n'
                                     '    struct Point:\n'
                                     '        x R\n'
                                     '        y R\n'
                                     '    have p &Point = (1, 2)\n'
                                     '    p.x = p(1) = 1\n'
                                     '    p.y = p(2) = 2\n',
                           'success': True},
 'claim-preentry-formation-control': {'source': 'struct ScalarOperations:\n'
                                                '    unit R\n'
                                                '    combine fn(x, y R) R\n'
                                                '    <=>:\n'
                                                '        unit = 1\n'
                                                '\n'
                                                'struct ScalarAction:\n'
                                                '    scalars &ScalarOperations\n'
                                                '    act fn(a, x R) R\n'
                                                '    <=>:\n'
                                                '        forall a, b, x R:\n'
                                                '            act(scalars.combine(a, b), x) = '
                                                'act(a, act(b, x))\n'
                                                '\n'
                                                'struct ScalarIdentity<S nonempty_set>:\n'
                                                '    zero S\n'
                                                '    add fn(x, y S) S\n'
                                                '    <=>:\n'
                                                '        forall x S:\n'
                                                '            add(zero, x) = x\n'
                                                '\n'
                                                'struct IdentityCarrier<S nonempty_set>:\n'
                                                '    scalars &ScalarIdentity<S>\n'
                                                '    element S\n'
                                                '\n'
                                                'claim:\n'
                                                '    ? forall p &ScalarOperations:\n'
                                                '        1 / 0 = 0\n'
                                                '    1 = 1\n',
                                      'success': False}}

STRUCT_EXPANSION_CASES = {
    'nested': ('examples/stmt_nodes/definition/struct_nested_field_instantiation.lit', True),
    'direct': ('examples/test_statements/release_struct_def_stmt.lit', True),
    'scalar': ('examples/test_statements/negative/release_struct_def_stmt/scalar-has-no-view.lit', False),
    'undefined': ('examples/test_statements/negative/release_struct_def_stmt/undefined-view-target.lit', False),
}

ATOMIC_FACT_FORMATION_CASES = {'equal-zero-denominator': {'source': '1 / 0 = 1 / 0\n', 'success': False},
 'equal-repair': {'source': '1 / 2 = 1 / 2\n', 'success': True},
 'sqrt-negative': {'source': 'sqrt(-1) $in R\n', 'success': False},
 'sqrt-repair': {'source': 'sqrt(4) $in R\n', 'success': True},
 'order-outside-domain': {'source': '{1} < {2}\n', 'success': False},
 'order-repair': {'source': '1 < 2\n', 'success': True},
 'predicate-domain': {'source': 'prop singleton_member(x {1}):\n'
                                '    x = x\n'
                                '\n'
                                '$singleton_member(2)\n',
                      'success': False},
 'predicate-repair': {'source': 'prop singleton_member(x {1}):\n'
                                '    x = x\n'
                                '\n'
                                '$singleton_member(1)\n',
                      'success': True},
 'predicate-arity': {'source': 'prop singleton_member(x {1}):\n'
                               '    x = x\n'
                               '\n'
                               '$singleton_member(1, 2)\n',
                     'success': False},
 'unknown-predicate': {'source': '$reading_unknown_predicate(1)\n', 'success': False},
 'claim-equal-goal': {'source': 'claim:\n    ? 1 / 0 = 0\n    1 = 1\n', 'success': False},
 'claim-equal-goal-repair': {'source': 'claim:\n    ? 1 / 1 = 1\n    1 / 1 = 1\n', 'success': True},
 'contra-equal-goal': {'source': 'by contra:\n    ? 1 / 0 = 0\n    impossible 1 = 1\n',
                       'success': False},
 'claim-equal-body': {'source': 'claim:\n    ? 1 = 1\n    1 / 0 = 0\n', 'success': False},
 'claim-equal-body-repair': {'source': 'claim:\n    ? 1 = 1\n    1 / 1 = 1\n', 'success': True},
 'contra-equal-body': {'source': 'by contra:\n    ? 1 = 1\n    1 / 0 = 0\n    impossible 1 = 1\n',
                       'success': False},
 'contra-equal-body-repair': {'source': 'by contra:\n'
                                        '    ? 1 = 1\n'
                                        '    1 / 1 = 1\n'
                                        '    impossible 1 = 1\n',
                              'success': True},
 'claim-member-goal': {'source': 'claim:\n    ? sqrt(-1) $in R\n    1 = 1\n', 'success': False},
 'claim-order-goal': {'source': 'claim:\n    ? {1} < {2}\n    1 = 1\n', 'success': False},
 'claim-or-goal': {'source': 'claim:\n    ? 1 = 1 or 1 / 0 = 0\n    1 = 1\n', 'success': False},
 'claim-and-goal': {'source': 'claim:\n    ? 1 = 1 and 1 / 0 = 0\n    1 = 1\n', 'success': False},
 'claim-chain-goal': {'source': 'claim:\n    ? 1 = 1 = 1 / 0\n    1 = 1\n', 'success': False},
 'contra-or-goal': {'source': 'by contra:\n    ? 1 = 1 or 1 / 0 = 0\n    impossible 1 = 1\n',
                    'success': False},
 'forall-equal-body': {'source': 'forall atomic_x R:\n'
                                 '    atomic_x != 0\n'
                                 '    =>:\n'
                                 '        1 / (atomic_x - 1) = 1 / (atomic_x - 1)\n',
                       'success': False},
 'forall-equal-repair': {'source': 'forall atomic_x R:\n'
                                   '    atomic_x - 1 != 0\n'
                                   '    =>:\n'
                                   '        1 / (atomic_x - 1) = 1 / (atomic_x - 1)\n',
                         'success': True},
 'truth-search-failure': {'source': '1 = 2\n', 'success': False},
 'claim-truth-failure': {'source': 'claim:\n    ? 1 = 2\n    1 = 1\n', 'success': False},
 'nested-goal-unicode': {'source': '# 检查内层目标的位置\n'
                                   'claim:\n'
                                   '    ? 1 = 1\n'
                                   '    claim:\n'
                                   '        ? sqrt(-1) $in R\n'
                                   '        1 = 1\n',
                         'success': False},
 'nested-goal-comment': {'source': 'claim:\n'
                                   '    # 检查内层目标的位置\n'
                                   '    ? 1 = 1\n'
                                   '    claim:\n'
                                   '        ? sqrt(-1) $in R\n'
                                   '        1 = 1\n',
                         'success': False},
 'nested-body-comment': {'source': 'claim:\n'
                                   '    # 检查内层证明的位置\n'
                                   '    ? 1 = 1\n'
                                   '    claim:\n'
                                   '        ? 1 = 1\n'
                                   '        1 / 0 = 0\n',
                         'success': False},
 'malformed-syntax': {'source': '1 =\n', 'success': False},
 'order-second-domain': {'source': '1 < {2}\n', 'success': False},
 'order-second-repair': {'source': '1 < 2\n', 'success': True}}

COMPOUND_FACT_FORMATION_CASES = {'or-middle': {'source': '1 = 2 or 1 / 0 = 0 or 1 = 1\n', 'success': False},
 'or-middle-repair': {'source': '1 = 2 or 1 / 1 = 0 or 1 = 1\n', 'success': True},
 'or-first': {'source': '1 / 0 = 0 or 1 = 1 or 2 = 2\n', 'success': False},
 'or-last': {'source': '1 = 1 or 2 = 2 or 1 / 0 = 0\n', 'success': False},
 'or-nested-and': {'source': '1 = 1 or 1 < 2 and 1 / 0 = 0 or 2 = 2\n', 'success': False},
 'or-nested-chain': {'source': '1 = 1 or 1 = 1 = 1 / 0 or 2 = 2\n', 'success': False},
 'and-middle': {'source': '1 < 2 and 1 / 0 = 0 and 2 = 2\n', 'success': False},
 'and-middle-repair': {'source': '1 < 2 and 1 / 1 = 1 and 2 = 2\n', 'success': True},
 'and-first': {'source': '1 / 0 = 0 and 1 = 1\n', 'success': False},
 'and-last': {'source': '1 = 1 and 2 = 2 and 1 / 0 = 0\n', 'success': False},
 'and-truth-before-wd': {'source': '1 = 2 and 1 / 0 = 0\n', 'success': False},
 'chain-middle': {'source': '1 = 1 = 1 / 0 = 2\n', 'success': False},
 'chain-middle-repair': {'source': '1 = 1 = 1 / 1 = 1\n', 'success': True},
 'chain-first': {'source': '1 / 0 = 0 = 1\n', 'success': False},
 'chain-last': {'source': '1 = 1 = 1 = 1 / 0\n', 'success': False},
 'chain-truth-before-wd': {'source': '1 = 2 = 1 / 0\n', 'success': False},
 'mixed-chain-middle': {'source': '1 < 2 <= 1 / 0 < 4\n', 'success': False},
 'claim-or-body': {'source': 'claim:\n    ? 1 = 1\n    1 = 2 or 1 / 0 = 0 or 1 = 1\n', 'success': False},
 'claim-and-body': {'source': 'claim:\n    ? 1 = 1\n    1 < 2 and 1 / 0 = 0 and 2 = 2\n',
                    'success': False},
 'claim-chain-body': {'source': 'claim:\n    ? 1 = 1\n    1 = 1 = 1 / 0 = 2\n', 'success': False},
 'contra-or-body': {'source': 'by contra:\n'
                              '    ? 1 = 1\n'
                              '    1 = 2 or 1 / 0 = 0 or 1 = 1\n'
                              '    impossible 1 = 1\n',
                    'success': False},
 'forall-and-condition': {'source': 'forall local_x R:\n'
                                    '    local_x > 0\n'
                                    '    =>:\n'
                                    '        local_x > 0 and 1 / 0 = 0\n',
                          'success': False},
 'claim-or-goal': {'source': 'claim:\n    ? 1 = 1 or 1 / 0 = 0\n    1 = 1\n', 'success': False},
 'claim-and-goal': {'source': 'claim:\n    ? 1 = 1 and 1 / 0 = 0\n    1 = 1\n', 'success': False},
 'claim-chain-goal': {'source': 'claim:\n    ? 1 = 1 = 1 / 0\n    1 = 1\n', 'success': False},
 'contra-or-goal': {'source': 'by contra:\n    ? 1 = 1 or 1 / 0 = 0\n    impossible 1 = 1\n',
                    'success': False},
 'or-predicate-prefix': {'source': 'prop reading_positive(x R):\n'
                                   '    x > 0\n'
                                   '\n'
                                   '$reading_positive(-1) or 1 / 0 = 0 or 1 = 1\n',
                         'success': False},
 'or-predicate-prefix-repair': {'source': 'prop reading_positive(x R):\n'
                                          '    x > 0\n'
                                          '\n'
                                          '$reading_positive(-1) or 1 / 1 = 0 or 1 = 1\n',
                                'success': True},
 'or-nested-and-repair': {'source': '1 = 1 or 1 < 2 and 1 / 1 = 0 or 2 = 2\n', 'success': True},
 'or-nested-chain-repair': {'source': '1 = 1 or 1 = 1 = 1 / 1 or 2 = 2\n', 'success': True},
 'claim-or-body-repair': {'source': 'claim:\n    ? 1 = 1\n    1 = 2 or 1 / 1 = 0 or 1 = 1\n',
                          'success': True},
 'claim-and-body-repair': {'source': 'claim:\n    ? 1 = 1\n    1 < 2 and 1 / 1 = 1 and 2 = 2\n',
                           'success': True},
 'claim-chain-body-repair': {'source': 'claim:\n    ? 1 = 1\n    1 = 1 = 1 / 1 = 1\n', 'success': True},
 'contra-or-body-repair': {'source': 'by contra:\n'
                                     '    ? 1 = 1\n'
                                     '    1 = 2 or 1 / 1 = 0 or 1 = 1\n'
                                     '    impossible 1 = 1\n',
                           'success': True}}

CONNECTIVE_CASES = {
    'selected': ('examples/proof_nodes/or/by_selected_branch/assume_negated_others_prove_one_arm.lit', True),
    'and': ('examples/proof_nodes/and/components.lit', True),
    'known': ('examples/proof_nodes/or/by_known_or_fact/set_builder_union_membership.lit', True),
    'transport': ('examples/proof_nodes/or/by_known_or_fact/stored_equality_transport.lit', True),
    'forall': ('examples/proof_nodes/or/by_known_forall/instantiate_forall_then_or.lit', True),
    'classical': ('examples/proof_nodes/or/by_builtin_rule/classical_implication.lit', True),
    'builtin-abs_sign_split': ('examples/proof_nodes/or/by_builtin_rule/abs_sign_split.lit', True),
    'builtin-classical_implication': ('examples/proof_nodes/or/by_builtin_rule/classical_implication.lit', True),
    'builtin-closed_integer_range_equality_cover': ('examples/proof_nodes/or/by_builtin_rule/closed_integer_range_equality_cover.lit', True),
    'builtin-complementary_atomic': ('examples/proof_nodes/or/by_builtin_rule/complementary_atomic.lit', True),
    'builtin-complete_residues': ('examples/proof_nodes/or/by_builtin_rule/complete_residues.lit', True),
    'builtin-equality_plus_strict_covers_weak': ('examples/proof_nodes/or/by_builtin_rule/equality_plus_strict_covers_weak.lit', True),
    'builtin-greater_or_less_equal': ('examples/proof_nodes/or/by_builtin_rule/greater_or_less_equal.lit', True),
    'builtin-half_open_integer_range_equality_cover': ('examples/proof_nodes/or/by_builtin_rule/half_open_integer_range_equality_cover.lit', True),
    'builtin-integer_discrete_split': ('examples/proof_nodes/or/by_builtin_rule/integer_discrete_split.lit', True),
    'builtin-integer_successor_tail': ('examples/proof_nodes/or/by_builtin_rule/integer_successor_tail.lit', True),
    'builtin-less_or_greater_equal': ('examples/proof_nodes/or/by_builtin_rule/less_or_greater_equal.lit', True),
    'builtin-natural_zero_or_at_least_one': ('examples/proof_nodes/or/by_builtin_rule/natural_zero_or_at_least_one.lit', True),
    'builtin-real_line_trichotomy_eq_less_greater': ('examples/proof_nodes/or/by_builtin_rule/real_line_trichotomy_eq_less_greater.lit', True),
    'builtin-real_line_trichotomy_greater_eq_less': ('examples/proof_nodes/or/by_builtin_rule/real_line_trichotomy_greater_eq_less.lit', True),
    'builtin-real_line_trichotomy_less_eq_greater': ('examples/proof_nodes/or/by_builtin_rule/real_line_trichotomy_less_eq_greater.lit', True),
    'builtin-square_sum_component_nonzero': ('examples/proof_nodes/or/by_builtin_rule/square_sum_component_nonzero.lit', True),
    'builtin-weak_order_le_or_ge': ('examples/proof_nodes/or/by_builtin_rule/weak_order_le_or_ge.lit', True),
    'builtin-zero_product_split': ('examples/proof_nodes/or/by_builtin_rule/zero_product_split.lit', True),
}
CONNECTIVE_INLINE_CASES = {
    'forall-route': ('abstract_prop logical_p(x)\nabstract_prop logical_q(x)\nforall:\n    forall x R:\n        $logical_p(x) or $logical_q(x)\n    =>:\n        $logical_p(3) or $logical_q(3)\n', True),
    'compound': ('1 < 2 and 2 < 3 or 3 < 4 and 4 < 5\n', True),
    'chain': ('1 < 2 < 3 or 1 = 4\n', True),
    'classical-route': ('forall logical_a R:\n    logical_a != 0 or logical_a ^ 2 >= 0\n', True),
    'or-search-failure': ('1 = 2 or 2 = 3\n', False),
    'or-wd-failure': ('1 = 1 or 1 / 0 = 0\n', False),
    'and-search-failure': ('1 < 2 and 3 < 2\n', False),
    'and-wd-failure': ('1 < 2 and 1 / 0 = 0\n', False),
    'classical-identity': ('forall classical_a R:\n    classical_a != 0 or 1 = 1\n', True),
}
COUNTEREXAMPLE_CASES = {
    'counterexample': ('examples/proof_nodes/not_forall/via_derived_exist.lit', True),
}
# Accepted/expected-rejected inputs checked in one persistent strict Session;
# the standalone forall case retains 0+1 for structural argument matching.
COUNTEREXAMPLE_INLINE_CASES = {
    'assumption': ('forall :\n    not forall assumed_x R:\n        assumed_x > 0\n    =>:\n        exist assumed_result R st {not assumed_result > 0}\n', True),
    'premise': ('witness exist y R st {y > 0, not y > 1} from 1\n\nnot forall y R:\n    y > 0\n    =>:\n        y > 1\n', True),
    'multiple': ('witness exist z R st {not z > 0 or not z < 1} from 0\n\nnot forall z R:\n    z > 0\n    z < 1\n', True),
    'builtin': ('not forall builtin_x R:\n    builtin_x = 100\n', True),
    'local': ('claim:\n    ? not forall local_x R:\n        local_x > 0\n    witness exist local_w R st {not local_w > 0} from 0\n', True),
    'forall-publication': ('claim:\n    ? forall counter_bound R:\n        exist counter_candidate R st {counter_candidate > counter_bound, counter_candidate = (counter_bound + 1)}\n    witness exist counter_w R st {counter_w > counter_bound, counter_w = (counter_bound + 1)} from (counter_bound + 1)\n\nnot forall fresh_q R:\n    fresh_q > 0\n    =>:\n        fresh_q != (0 + 1)\n\nexist fresh_later R st {fresh_later > 0, fresh_later = (0 + 1)}\n', True),
    'disjunction': ('witness exist sign_x R st {not sign_x > 0, not sign_x < 0} from 0\n\nnot forall sign_x R:\n    sign_x > 0 or sign_x < 0\n', True),
    'chain': ('witness exist chain_x R st {not 0 < chain_x or not chain_x < 1} from 0\n\nnot forall chain_x R:\n    0 < chain_x < 1\n', True),
    'guarded': ('witness exist reciprocal_x R st {reciprocal_x != 0, (1 / reciprocal_x) != 2} from 1\n\nnot forall reciprocal_x R:\n    reciprocal_x != 0\n    =>:\n        (1 / reciprocal_x) = 2\n', True),
    'reflexive-failure': ('not forall impossible_x R:\n    impossible_x = impossible_x\n', False),
    'empty-failure': ('not forall empty_x {}:\n    empty_x = 0\n', False),
    'wd-failure': ('not forall undefined_x R:\n    (1 / undefined_x) = 1\n', False),
}
LOGICAL_CASES = {
    'logic-sqrt-two': ('examples/reading/homepage/04-sqrt-two-irrational.lit', True),
    'logic-contra-positive': ('examples/stmt_nodes/by/by_contra_impossible_not.lit', True),
    'logic-contra-classified': ('examples/stmt_nodes/by/by_contra_classified_goals.lit', True),
    'logic-contra-compound': ('examples/stmt_nodes/by/by_contra_compound_impossible.lit', True),
    'logic-cases-scoped': ('examples/test_statements/release_basics/fixtures/P/cases-exhaustive.lit', True),
    'logic-cases-absolute': ('examples/litex_vs_lean_speed/sources/declarations/cases_proof.lit', True),
    'logic-claim': ('examples/test_statements/claim_stmt.lit', True),
    'logic-forall': ('examples/reading/homepage/problems/missing-premise-fixed.lit', True),
    'logic-cantor': ('examples/reading/lessons/en/cantor.lit', True),
    'logic-repeated': ('examples/stmt_nodes/by/by_induc.lit', True),
    'logic-cases-missing': ('examples/test_statements/release_basics/fixtures/P/cases-missing-branch.lit', False),
    'logic-cases-false': ('examples/test_statements/release_basics/fixtures/P/cases-false-goal.lit', False),
    'logic-contra-false': ('examples/test_statements/negative/by_contra_stmt/fake-contradiction.lit', False),
}
PROCESS_CASES = {
    'induction': ('examples/stmt_nodes/by/by_induc_order.lit', True),
    'induction-actions': ('examples/stmt_nodes/by/induction_domain_and_proof_actions.lit', True),
    'strong': ('examples/stmt_nodes/by/by_strong_induc.lit', True),
    'enumeration': ('examples/test_statements/by_enumerate_finite_set_stmt.lit', True),
    'for': ('examples/stmt_nodes/by/by_for.lit', True),
    'witness': ('examples/stmt_nodes/witness/witness_detailed_evidence.lit', True),
    'witness-exist': ('examples/stmt_nodes/witness/witness_exist_fact.lit', True),
    'witness-unique': ('examples/stmt_nodes/witness/witness_exist_unique_fact.lit', True),
    'witness-nonempty': ('examples/stmt_nodes/witness/witness_nonempty_set.lit', True),
    'induction-false-base': ('examples/test_statements/negative/by_induc_stmt/false-base-case.lit', False),
    'induction-false-step': ('examples/test_statements/negative/by_induc_stmt/false-step-case.lit', False),
    'induction-start': ('examples/test_statements/negative/by_induc_stmt/noninteger-start.lit', False),
    'strong-false-step': ('examples/test_statements/negative/by_strong_induc_stmt/false-step-case.lit', False),
    'enumeration-false': ('examples/test_statements/negative/by_enumerate_finite_set_stmt/false-conditional-conclusion.lit', False),
    'enumeration-domain': ('examples/test_statements/negative/by_enumerate_finite_set_stmt/nonenumerable-domain.lit', False),
    'for-false': ('examples/test_statements/negative/by_for_stmt/false-range-instance.lit', False),
    'witness-body': ('examples/test_statements/negative/witness_exist_fact/false-witness-body.lit', False),
    'witness-type': ('examples/test_statements/negative/witness_atomic_fact/wrong-predicate-witness-type.lit', False),
    'witness-member': ('examples/test_statements/negative/witness_nonempty_set/nonmember-witness.lit', False),
    'witness-unsupported-unique': ('examples/test_statements/negative/witness_atomic_fact/unique-exist-predicate-is-unsupported.lit', False),
}
INTERFACE_CASES = {
    **{name: (f'examples/test_statements/{leaf}_stmt.lit', True, strict)
       for name, leaf, strict in [('prop', 'def_prop', True), ('abstract', 'def_abstract_prop', True),
                                  ('theorem', 'def_thm', True), ('strategy', 'def_strategy', True),
                                  ('struct', 'def_struct', True), ('template', 'def_template', False)]},
    'template-laws': ('examples/stmt_nodes/definition/template_definition_facts.lit', True, True),
    'template-types': ('examples/stmt_nodes/definition/template_type_interfaces.lit', True, True),
    'struct-existential': ('examples/proof_nodes/exist/by_known_forall/struct_existential_law.lit', True, True),
    'struct-ordered': ('examples/stmt_nodes/definition/struct_ordered_conditions.lit', True, True),
    'struct-nested': ('examples/stmt_nodes/definition/struct_nested_field_instantiation.lit', True, True),
    'strategy-nested': ('examples/stmt_nodes/definition/strategy_nested_proof.lit', True, True),
    'reciprocal-compatibility': ('examples/reading/homepage/17-reciprocal-definition.lit', True, True),
    **{family+'-'+source.stem: (str(source.relative_to(ROOT)), False, True)
       for family, directory in [('prop', 'def_prop_stmt'), ('abstract', 'def_abstract_prop_stmt'),
                                ('theorem', 'def_thm_stmt'), ('strategy', 'def_strategy_stmt'),
                                ('struct', 'def_struct_stmt'), ('template', 'def_template_stmt')]
       for source in sorted((ROOT/'examples/test_statements/negative'/directory).glob('*.lit'))},
}
FOUNDATION_EVAL_CASES = {
    **{name: (f'examples/test_statements/{leaf}_stmt.lit', True, strict)
       for name, leaf, strict in [('zorn', 'release_zorn_lemma', False),
                                  ('choice', 'release_axiom_of_choice', False),
                                  ('regularity', 'release_regularity_axiom', False),
                                  ('eval', 'eval', True)]},
    **{name: (f'examples/stmt_nodes/command/{file}.lit', True, True)
       for name, file in [('aggregates', 'aggregate_eval'), ('stored', 'eval_store_result'),
                          ('coordinates', 'eval_finite_function_coordinate'),
                          ('source-domain', 'eval_source_domain'),
                          ('complex', 'eval_closed_numeric_complex')]},
    'strict-choice': ('examples/test_statements/boundaries/strict-choice-allowed.lit', True, True),
    'strict-regularity': ('examples/test_statements/boundaries/strict-regularity-allowed.lit', True, True),
    **{family+'-'+source.stem: (str(source.relative_to(ROOT)), False, family == 'eval')
       for family, directory in [('zorn', 'release_zorn_lemma_stmt'),
                                ('choice', 'release_axiom_of_choice_stmt'),
                                ('regularity', 'release_regularity_axiom_stmt'), ('eval', 'eval_stmt')]
       for source in sorted((ROOT/'examples/test_statements/negative'/directory).glob('*.lit'))},
}
# Exact existing native evaluation regressions; no new mathematical assumptions.
EVAL_NATIVE_TRACERS = {
    'empty-sum': ('src/execute/execute_eval_stmt/exec_eval_stmt_tests.rs',
                  'eval finite_set_sum({},fn(k Z) Z {k})'),
    'empty-product': ('src/execute/execute_eval_stmt/exec_eval_stmt_tests.rs',
                      'eval finite_set_product({},fn(k Z) Z {k})'),
    'reduce': ('tests/unit/compile_to_lean/eval_fold_tests.rs',
               'eval reduce(1,3,fn(k Z) Z{k},fn(a,b Z) Z{a-b},0)'),
    'set-reduce': ('tests/unit/compile_to_lean/eval_fold_tests.rs',
                   'eval finite_set_reduce({3,1,2},fn(k Z) Z{k},fn(a,b Z) Z{a+b},10)'),
}
STATE_CHANGE_CASES = {
    'trust-have-release': ('examples/test_statements/trust_have_stmt.lit', True, False),
    **{name: (f'examples/test_statements/{leaf}_stmt.lit', True, strict)
       for name, leaf, strict in [
           ('reflexive', 'register_reflexive_prop', True),
           ('symmetric', 'register_symmetric_prop', True),
           ('transitive', 'register_transitive_prop', True),
           ('trust', 'trust', False), ('trust-have', 'trust_have', False),
           ('axiom', 'axiom', False), ('sketch', 'sketch', True)]},
    **{family+'-'+source.stem: (str(source.relative_to(ROOT)), False, strict)
       for family, directory, strict in [
           ('reflexive', 'register_reflexive_prop_stmt', True),
           ('symmetric', 'register_symmetric_prop_stmt', True),
           ('transitive', 'register_transitive_prop_stmt', True),
           ('trust', 'trust_stmt', False), ('trust-have', 'trust_have_stmt', False),
           ('axiom', 'axiom_stmt', False), ('sketch', 'sketch_stmt', True)]
       for source in sorted((ROOT/'examples/test_statements/negative'/directory).glob('*.lit'))},
    **{name: (f'examples/test_statements/boundaries/{name}.lit', False, True)
       for name in ['strict-trust-rejected', 'strict-trust-have-rejected',
                    'strict-axiom-rejected', 'strict-sketch-trust-rejected']},
}
EXPANSION_CASES = {
    'set': ('examples/test_statements/by_extension_stmt.lit', True),
    'function': ('examples/test_statements/by_fn_extension_stmt.lit', True),
    'function-curried': ('examples/proof_nodes/equal/by_object_definition/by_fn_application/both_function_bodies.lit', True),
    'function-callback': ('examples/proof_nodes/equal/by_builtin_rule/anonymous_function_beta_extension.lit', True),
    'function-matrix': ('examples/test_objs/matrix_operators.lit', True),
    'object': ('examples/test_statements/release_obj_def_stmt.lit', True),
    'object-exist': ('examples/stmt_nodes/definition/release_obj_def.lit', True),
    'object-unique': ('examples/have_fn_by_unique_existence.lit', True),
    'object-replacement': ('examples/test_statements/have_by_replacement_axiom_stmt.lit', True),
    'struct': ('examples/test_statements/release_struct_def_stmt.lit', True),
    'cart': ('examples/test_statements/release_cart_def_stmt.lit', True),
    'tuple': ('examples/stmt_nodes/release_and_expand/release_tuple_def.lit', True),
    'expand': ('examples/test_statements/expand_range_stmt.lit', True),
    'expand-single': ('examples/stmt_nodes/release_and_expand/expand_closed_range.lit', True),
    'set-unequal': ('examples/test_statements/negative/by_extension_stmt/unequal-sets.lit', False),
    'set-shape': ('examples/test_statements/negative/by_extension_stmt/non-equality-goal.lit', False),
    'function-domain': ('examples/test_statements/negative/by_fn_extension_stmt/different-carriers.lit', False),
    'function-value': ('examples/test_statements/negative/by_fn_extension_stmt/different-functions.lit', False),
    'object-undefined': ('examples/test_statements/negative/release_obj_def_stmt/undefined-object-definition.lit', False),
    'object-expression': ('examples/test_statements/negative/release_obj_def_stmt/expression-not-name.lit', False),
    'struct-scalar': ('examples/test_statements/negative/release_struct_def_stmt/scalar-has-no-view.lit', False),
    'struct-undefined': ('examples/test_statements/negative/release_struct_def_stmt/undefined-view-target.lit', False),
    'cart-constructor': ('examples/test_statements/negative/release_cart_def_stmt/non-constructor.lit', False),
    'cart-undefined': ('examples/test_statements/negative/release_cart_def_stmt/undefined-factor.lit', False),
    'cart-body': ('examples/test_statements/negative/release_cart_def_stmt/trailing-body.lit', False),
    'tuple-infinite': ('examples/test_statements/negative/release_tuple_def_stmt/infinite-domain.lit', False),
    'tuple-scalar': ('examples/test_statements/negative/release_tuple_def_stmt/scalar.lit', False),
    'tuple-wd': ('examples/test_statements/negative/release_tuple_def_stmt/invalid-wd.lit', False),
    'tuple-body': ('examples/test_statements/negative/release_tuple_def_stmt/trailing-body.lit', False),
    'expand-kind': ('examples/test_statements/negative/expand_range_stmt/not-a-numeric-range.lit', False),
    'expand-nonmember': ('examples/test_statements/negative/expand_range_stmt/nonmember-range.lit', False),
}
FUNCTION_CASES = {
    'formula': ('examples/test_statements/have_fn_equal_stmt.lit', True),
    'guard': ('examples/reading/homepage/17-reciprocal-definition.lit', True),
    'cases': ('examples/stmt_nodes/definition/have_fn_cases_evidence.lit', True),
    'cases-multiple': ('examples/test_statements/have_fn_equal_case_by_case_stmt.lit', True),
    'unique': ('examples/test_statements/have_fn_by_forall_exist_unique_stmt.lit', True),
    'unique-carriers': ('examples/stmt_nodes/definition/have_fn_by_exist.lit', True),
    'recursive': ('examples/test_statements/have_fn_by_induc_stmt.lit', True),
    'recursive-single': ('examples/stmt_nodes/definition/have_fn_by_induc.lit', True),
    'algo-cases': ('examples/test_statements/def_algo_by_cases_stmt.lit', True),
    'algo-induc': ('examples/test_statements/def_algo_by_induc_stmt.lit', True),
    'local': ('examples/stmt_nodes/definition/local_function_and_preimage_bindings.lit', True),
    'template': ('examples/proof_nodes/equal/by_object_definition/by_template/have_fn_equal_case_by_case_application.lit', True),
    'local-family': ('examples/stmt_nodes/definition/local_function_family_bindings.lit', True),
    'higher-order': ('examples/proof_nodes/equal/by_object_definition/by_fn_application/function_value_parameter_application.lit', True),
    'empty-graph': ('examples/negative/exact_function_domains/empty_function_graph_nonempty.lit', False),
    'empty-return': ('examples/negative/exact_function_domains/empty_constructor_false_body_membership.lit', False),
    'wrong-codomain': ('examples/test_statements/negative/have_fn_equal_stmt/wrong-codomain.lit', False),
    'wrong-call': ('examples/test_statements/negative/have_fn_equal_stmt/wrong-call-arity.lit', False),
    'ill-defined': ('examples/test_statements/negative/have_fn_equal_stmt/ill-defined-function-body.lit', False),
    'missing-case': ('examples/test_statements/negative/have_fn_equal_case_by_case_stmt/missing-case.lit', False),
    'case-codomain': ('examples/test_statements/negative/have_fn_equal_case_by_case_stmt/wrong-case-codomain.lit', False),
    'ordinary-existence': ('examples/test_statements/negative/have_fn_by_forall_exist_unique_stmt/ordinary-existence-is-insufficient.lit', False),
    'false-unique': ('examples/test_statements/negative/have_fn_by_forall_exist_unique_stmt/false-unique-natural.lit', False),
    'nondecreasing': ('examples/test_statements/negative/have_fn_by_induc_stmt/nondecreasing-recursion.lit', False),
    'bad-base': ('examples/test_statements/negative/have_fn_by_induc_stmt/bad-base-carrier.lit', False),
    'algo-coverage': ('examples/test_statements/negative/def_algo_by_cases_stmt/nonexhaustive-algorithm.lit', False),
    'algo-result': ('examples/test_statements/negative/def_algo_by_cases_stmt/bad-algorithm-result.lit', False),
    'algo-base': ('examples/test_statements/negative/def_algo_by_induc_stmt/wrong-base-value.lit', False),
    'algo-recursion': ('examples/test_statements/negative/def_algo_by_induc_stmt/nondecreasing-algorithm-recursion.lit', False),
}
INTRODUCTION_CASES = {
    'let': ('examples/test_statements/let_obj_stmt.lit', True),
    'have': ('examples/test_statements/have_obj_in_nonempty_set_stmt.lit', True),
    'equal': ('examples/test_statements/have_obj_equal_stmt.lit', True),
    'dependent': ('examples/stmt_nodes/definition/dependent_have.lit', True),
    'have-exist': ('examples/test_statements/have_obj_by_exist_facts_stmt.lit', True),
    'have-comparison': ('examples/stmt_nodes/definition/have_obj_by_exist_facts.lit', True),
    'obtain-exist': ('examples/test_statements/obtain_obj_from_exist_fact.lit', True),
    'obtain-atomic': ('examples/test_statements/obtain_obj_from_atomic_fact.lit', True),
    'preimage': ('examples/stmt_nodes/definition/have_by_fn_preimage.lit', True),
    'preimage-multiple': ('examples/test_statements/have_by_preimage_stmt.lit', True),
    'preimage-returned': ('examples/stmt_nodes/definition/returned_function_preimage.lit', True),
    'preimage-field': ('examples/stmt_nodes/definition/field_function_preimage.lit', True),
    'local': ('examples/stmt_nodes/definition/local_function_and_preimage_bindings.lit', True),
    'finite': ('examples/proof_nodes/equal/by_builtin_rule/power_set_finite_set_size.lit', True),
    'repeated': ('examples/stmt_nodes/by/induction_domain_and_proof_actions.lit', True),
    'scope': ('examples/claim_obtain_scope.lit', True),
    'contra': ('examples/stmt_nodes/by/by_contra_classified_goals.lit', True),
    'replacement': ('examples/test_statements/have_by_replacement_axiom_stmt.lit', True),
    'let-zero': ('examples/test_statements/negative/let_obj_stmt/zero-divisor.lit', False),
    'let-duplicate': ('examples/test_statements/negative/let_obj_stmt/duplicate-name.lit', False),
    'let-undefined': ('examples/test_statements/negative/let_obj_stmt/undefined-value.lit', False),
    'have-empty': ('examples/test_statements/negative/have_obj_in_nonempty_set_stmt/empty-carrier.lit', False),
    'have-undefined': ('examples/test_statements/negative/have_obj_in_nonempty_set_stmt/undefined-carrier.lit', False),
    'equal-negative': ('examples/test_statements/negative/have_obj_equal_stmt/negative-natural-tracer.lit', False),
    'equal-count': ('examples/test_statements/negative/have_obj_equal_stmt/wrong-value-count.lit', False),
    'have-exist-false': ('examples/test_statements/negative/have_obj_by_exist_facts_stmt/impossible-natural-existence.lit', False),
    'have-exist-undefined': ('examples/test_statements/negative/have_obj_by_exist_facts_stmt/undefined-existence-body.lit', False),
    'obtain-false': ('examples/test_statements/negative/obtain_obj_from_exist_fact/false-existence.lit', False),
    'obtain-count': ('examples/test_statements/negative/obtain_obj_from_exist_fact/wrong-witness-count.lit', False),
    'atomic-type': ('examples/test_statements/negative/obtain_obj_from_atomic_fact/wrong-prop-argument-type.lit', False),
    'atomic-nonexistential': ('examples/test_statements/negative/obtain_obj_from_atomic_fact/nonexistential-prop.lit', False),
    'preimage-target': ('examples/test_statements/negative/have_by_preimage_stmt/non-range-target.lit', False),
    'preimage-count': ('examples/test_statements/negative/have_by_preimage_stmt/wrong-arity.lit', False),
    'replacement-arity': ('examples/test_statements/negative/have_by_replacement_axiom_stmt/wrong-prop-arity.lit', False),
    'replacement-unknown': ('examples/test_statements/negative/have_by_replacement_axiom_stmt/unknown-prop.lit', False),
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
    'canonical': 'examples/test_statements/release_thm_stmt.lit',
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
# Native theorem rejection controls; these must reach actual theorem failures.
def rejected_theorem_probe(parameters, premises, call):
    """Keep the target WD trivial so the actual BT call must check its premises."""
    context='\n'.join('        '+line for line in premises.splitlines())
    target=context+'\n        =>:\n            1 = 1' if premises.strip() else '        1 = 1'
    return 'claim:\n    ? forall '+parameters+':\n'+target+'\n    release thm '+call

BUILTIN_REFERENCE_REJECTIONS = {
    'seq-no-candidate': rejected_theorem_probe('a,b seq(R),L,M R','', 'seq_limit_add(a,b,L,M)'),
    'seq-no-epsilon-proof': rejected_theorem_probe('a seq(R),L R','', 'seq_limit_from_epsilon(a,L)'),
    'seq-tail-zero': 'have fn a(k N+) R=0\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_tail(a,0,0)',
    'seq-complex-scale': 'have fn a(k N+) R=0\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_scale(a,0,i)',
    'seq-power-negative': 'have fn a(k N+) R=1\nrelease thm seq_limit_constant(a,1)\nrelease thm seq_limit_power(a,1,-1)',
    'seq-shift-negative': 'have fn a(k N+) R=0\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_shift(a,0,-1)',
    'seq-eventual-false': 'have fn a(k N+) R=0\nhave fn b(k N+) R=1\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_eventually_equal(a,b,0,1)',
    'seq-compare-false': 'have fn a(k N+) R=1\nhave fn b(k N+) R=0\nrelease thm seq_limit_constant(a,1)\nrelease thm seq_limit_constant(b,0)\nrelease thm seq_limit_compare(a,b,1,0,1)',
    'seq-squeeze-false': 'have fn a(k N+) R=0\nhave fn b(k N+) R=1\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_squeeze(a,b,a,0,1)',
    'seq-missing-denom-terms': rejected_theorem_probe('a,b seq(R),L,M R','$has_seq_limit(a,L)\n$has_seq_limit(b,M)\nM!=0','seq_limit_divide(a,b,L,M)'),
    'seq-missing-denom-limit': rejected_theorem_probe('a,b seq(R),L,M R','$has_seq_limit(a,L)\n$has_seq_limit(b,M)\nforall n N+:\n    b(n)!=0','seq_limit_divide(a,b,L,M)'),
    'seq-selected-no-existence': rejected_theorem_probe('a seq(R)','','seq_limit_selected(a)'),
    'seq-finite-domain': 'have fn short(k closed_range(1,2)) R=0\nrelease thm seq_limit_constant(short,0)',
    'tuple-domain': 'release thm tuple_equal_from_coordinates((1, 2), (1, 2, 3))',
    'cart-domain': 'release thm cart_member_from_coordinates((1, 2, 3), cart(R, Z))',
    'function-domain': 'have fn wide(i1 N+) R = 0\nrelease thm fn_set_member(wide, finite_seq(R, 2))',
    'builder-condition': 'release thm set_builder_member(-1, {x R: x > 0})',
    'defined-condition': 'let positives = {x R: x > 0}\nrelease thm defined_set_member(-1, positives)',
    'structure-fields': 'struct Point:\n    x R\n    y R\nrelease thm struct_member((1, {}), &Point)',
    'family-empty': 'release thm family_intersect_member(1, family_intersect({}))',
    'family-missing-membership': 'release thm family_intersect_member_facts(1, family_intersect({{2}}))',
    'index-fiber': 'release thm index_intersect_member(1, index_intersect({1}, R, fn(k {1}) power_set(R) {{2}}))',
    'upper-candidate': 'release thm real_least_upper_bound_from_definition({0}, 1)',
    'lower-candidate': 'release thm real_greatest_lower_bound_from_definition({0}, -1)',
    'upper-empty': 'release thm real_least_upper_bound_exists({}, 1)',
    'lower-empty': 'release thm real_greatest_lower_bound_exists({}, -1)',
    'density-equal': 'release thm rational_between_reals(1, 1)',
    'selected-prime-domain': 'by thm prime_divisor(1) => 1 = 1',
    'fold-shape': 'release thm finite_set_reduce_singleton(1, 1)',
    'prime-domain': 'release thm prime_divisor(1)',
    'finite-arity': 'release thm finite_set_has_bijective_index()',
    'sum-order': 'release thm finite_set_sum_le_from_pointwise(finite_set_sum({1}, fn(x {1}) R {2}), finite_set_sum({1}, fn(y {1}) R {1}))',
    'choice-family': 'release thm index_cart_nonempty_by_choice_from_family(index_cart({1}, {{}, {1}}, fn(k {1}) {{}, {1}} {{1}}))',
}
for side,other in [('limsup','liminf'),('liminf','limsup')]:
    prefix='extrema-'+side
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-wrong-negation']=rejected_theorem_probe(
        'a,b seq(R),L R',f'$has_seq_{side}(a,L)\nforall n N+:\n    b(n)=-a(n)',f'seq_{side}_scale_nonnegative(a,b,L,-1)')
    neg_call=f'seq_{side}_neg(a,b,L)'
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-negation-kind']=rejected_theorem_probe(
        'a,b seq(R),L R',f'$has_seq_{side}(a,L)\nforall n N+:\n    b(n)=-a(n)',neg_call).replace('release thm '+neg_call,'by thm '+neg_call+f' => $has_seq_{side}(b,-L)')
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-zero-negative-scale']='have fn a(k N+) R=0\nrelease thm seq_'+side+'_constant(a,0)\nrelease thm seq_'+side+'_scale_negative(a,a,0,0)'
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-zero-hit-epsilon']='have fn a(k N+) R=0\nrelease thm seq_'+side+'_constant(a,0)\nrelease thm seq_'+side+'_hit(a,0,0,1)'
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-zero-hit-cutoff']='have fn a(k N+) R=0\nrelease thm seq_'+side+'_constant(a,0)\nrelease thm seq_'+side+'_hit(a,0,1,0)'
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-selected-no-existence']=rejected_theorem_probe('a seq(R)','','seq_'+side+'_selected(a)')
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-sum-no-bounds']=rejected_theorem_probe(
        'a,b,h seq(R),L,M,H R,B1,B2 R+',f'$has_seq_{side}(a,L)\n$has_seq_{side}(b,M)\n$has_seq_{side}(h,H)\nforall n N+:\n    h(n)=a(n)+b(n)',f'seq_{side}_sum_bound(a,b,h,L,M,H,B1,B2)')
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-add-no-convergence']=rejected_theorem_probe(
        'a,b,h seq(R),L,M R',f'$has_seq_{side}(a,L)\n$has_seq_{side}(b,M)\nforall n N+:\n    h(n)=a(n)+b(n)',f'seq_{side}_add_convergent(a,b,h,L,M)')
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-bounded-zero']='have fn a(k N+) R=0\nrelease thm seq_'+side+'_bounded_exists(a,0)'
    ray='v<L+epsilon' if side=='limsup' else 'L-epsilon<v'
    BUILTIN_REFERENCE_REJECTIONS[prefix+'-missing-tail-hits']=rejected_theorem_probe(
        'a seq(R),L R','forall epsilon R+:\n    exist N0 N+ st {{n N+:n>=N0} $subset preimage_set(a,{v R:'+ray+'})}',f'seq_{side}_from_epsilon(a,L)')
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



# Actual sources checked in persistent strict Sessions.
FAILED_UNIVERSAL_INLINE_CASES = {'prefix': ('forall x R:\n    x > 0\n    =>:\n        x >= 0\n        x < 0\n', False),
 'no-premise': ('forall y R:\n    y = y\n    y > 0\n', False),
 'dependent': ('forall A nonempty_set, t A:\n    t $in A\n    2 = 3\n', False),
 'predicate-premise': ('prop universal_positive(v R):\n'
                       '    v > 0\n'
                       '\n'
                       'forall v R:\n'
                       '    $universal_positive(v)\n'
                       '    =>:\n'
                       '        v >= 0\n'
                       '        v < 0\n',
                       False),
 'first-failure': ('forall w R:\n    w > 0\n    =>:\n        w < 0\n        w = w\n', False),
 'goal-wd': ('forall z R:\n    1 / 0 = z\n', False),
 'nested-claim': ('claim:\n'
                  '    ? forall a R:\n'
                  '        a > 0\n'
                  '        =>:\n'
                  '            a >= 0\n'
                  '    a > 0\n'
                  '    forall b R:\n'
                  '        b > 0\n'
                  '        =>:\n'
                  '            b >= 0\n'
                  '            b < 0\n',
                  False),
 'positive': ('forall good R:\n    good > 0\n    =>:\n        good >= 0\n', True),
 'parameter-wd': ('forall z (1 / 0):\n    z = z\n', False),
 'nested': ('forall a R:\n'
            '    a > 0\n'
            '    =>:\n'
            '        a >= 0\n'
            '        forall b R:\n'
            '            b > 0\n'
            '            =>:\n'
            '                b >= 0\n'
            '                b < 0\n',
            False)}


QUANTIFIER_FORMATION_CASES = {'forall-second-parameter-wd': ('forall a R, b {1 / 0}:\n    a = a', False),
 'forall-second-parameter-repair': ('forall a R, b {1 / 2}:\n    a = a', True),
 'forall-premise-prefix-wd': ('forall x R:\n    x > 0\n    1 / (x - 1) > 0\n    =>:\n        x = x',
                              False),
 'forall-premise-prefix-repair': ('forall x R:\n'
                                  '    x > 0\n'
                                  '    x != 1\n'
                                  '    1 / (x - 1) > 0\n'
                                  '    =>:\n'
                                  '        x = x',
                                  True),
 'definition-nested-forall-parameter-wd': ('prop quantified_parameter(t R):\n'
                                           '    forall a R, b {1 / 0}:\n'
                                           '        a = a',
                                           False),
 'definition-nested-forall-parameter-repair': ('prop quantified_parameter(t R):\n'
                                               '    forall a R, b {1 / 2}:\n'
                                               '        a = a',
                                               True),
 'definition-nested-forall-premise-wd': ('prop quantified_premises(t R):\n'
                                         '    forall x R:\n'
                                         '        x > 0\n'
                                         '        1 / (x - 1) > 0\n'
                                         '        =>:\n'
                                         '            x = x',
                                         False),
 'definition-nested-forall-conclusion-wd': ('prop quantified_conclusions(t R):\n'
                                            '    forall x R:\n'
                                            '        x > 0\n'
                                            '        =>:\n'
                                            '            x = x\n'
                                            '            1 / (x - 1) > 0\n'
                                            '            x + 0 = x',
                                            False),
 'definition-false-consequent-formation-prefix': ('prop check_only(t R):\n'
                                                  '    forall x R:\n'
                                                  '        x > 0\n'
                                                  '        =>:\n'
                                                  '            x = 0\n'
                                                  '            1 / (x - 1) > 0\n'
                                                  '            x = x',
                                                  False),
 'definition-false-consequent-formation-repair': ('prop check_only(t R):\n'
                                                  '    forall x R:\n'
                                                  '        x > 0\n'
                                                  '        x != 1\n'
                                                  '        =>:\n'
                                                  '            x = 0\n'
                                                  '            1 / (x - 1) > 0\n'
                                                  '            x = x',
                                                  True),
 'definition-only-not-instance-proof': ('prop check_only(t R):\n'
                                        '    forall x R:\n'
                                        '        x > 0\n'
                                        '        x != 1\n'
                                        '        =>:\n'
                                        '            x = 0\n'
                                        '            1 / (x - 1) > 0\n'
                                        '            x = x\n'
                                        '\n'
                                        'by def $check_only(2)',
                                        False),
 'positive-reciprocal-universal': ('forall x R:\n    x > 0\n    =>:\n        1 / x > 0', True),
 'nested-exist-parameter-wd-compatibility': ('prop existential_parameters(t R):\n'
                                             '    exist a R, b {1 / 0} st {a = a}',
                                             False),
 'nested-notforall-parameter-wd-compatibility': ('prop negated_universal_parameters(t R):\n'
                                                 '    not forall a R, b {1 / 0}:\n'
                                                 '        a = a',
                                                 False),
 'nested-iff-parameter-wd-compatibility': ('prop equivalence_parameters(t R):\n'
                                           '    forall a R, b {1 / 0}:\n'
                                           '        =>:\n'
                                           '            a = a\n'
                                           '        <=>:\n'
                                           '            a = a',
                                           False),
 'local-inference-definition': ('prop reading_nonzero(t R):\n    t != 0', True),
 'forall-local-inference-before-premise-failure': ('prop reading_nonzero(t R):\n'
                                                   '    t != 0\n'
                                                   '\n'
                                                   'forall x R:\n'
                                                   '    $reading_nonzero(x)\n'
                                                   '    1 / (x - 1) > 0\n'
                                                   '    =>:\n'
                                                   '        x = x',
                                                   False),
 'real-quotient-definition-failure': ('prop quotients_are_real(a R):\n'
                                      '    forall x R:\n'
                                      '        x / a $in R',
                                      False),
 'real-quotient-definition-repair': ('prop quotients_are_real(a R):\n'
                                     '    a != 0\n'
                                     '    forall x R:\n'
                                     '        x / a $in R',
                                     True),
 'real-quotient-instance': ('prop quotients_are_real(a R):\n'
                            '    a != 0\n'
                            '    forall x R:\n'
                            '        x / a $in R\n'
                            '\n'
                            'by def $quotients_are_real(2)',
                            True)}

FAILED_INTERFACE_CASES = {'prop-second-parameter-wd': ('prop P(a R, b {1 / 0}):\n    a = a', False),
 'prop-condition-prefix-failure': ('prop guarded(x R):\n'
                                   '    x > 0\n'
                                   '    1 / (x - 1) $in R\n'
                                   '    x = x',
                                   False),
 'prop-repair-retains-context': ('prop P(a R, b {1 / 2}):\n    a = a', True),
 'struct-field-prefix-failure': ('struct BadFields:\n    x R\n    y {1 / 0}', False),
 'struct-parameter-prefix-failure': ('struct BadHeader<A set, b {1 / 0}>:\n    x A\n    y A',
                                     False),
 'struct-condition-prefix-failure': ('struct BadLaw:\n'
                                     '    x R\n'
                                     '    y R\n'
                                     '    <=>:\n'
                                     '        x > 0\n'
                                     '        1 / (x - 1) $in R\n'
                                     '        y = y',
                                     False),
 'template-parameter-prefix-failure': ('template<A set, b {1 / 0}>:\n'
                                       '    have bad_parameter_body set = A',
                                       False),
 'template-body-failure': ('template<T set>:\n    have bad_value R = 1 / 0', False),
 'prop-condition-repair': ('prop guarded(x R):\n'
                           '    x > 0\n'
                           '    x != 1\n'
                           '    1 / (x - 1) $in R\n'
                           '    x = x',
                           True),
 'template-domain-prefix-predicate-failure': ('template<x R: $is_set({x}), $is_set({1 / (x - '
                                              '1)})>:\n'
                                              '    have bad_domain_body R = x',
                                              False),
 'struct-field-repair': ('struct BadFields:\n    x R\n    y R', True),
 'template-body-repair': ('template<T set>:\n    have bad_value R = 1 / 2', True),
 'struct-callable-field-wd-failure': ('struct BadCallableField:\n'
                                      '    point R\n'
                                      '    at fn(t R: 1 / 0 = t) R',
                                      False),
 'reciprocal-window-definition-failure': ('prop reciprocal_window(x R):\n'
                                          '    x > 0\n'
                                          '    1 / (x - 1) > 0\n'
                                          '    x < 2',
                                          False),
 'reciprocal-window-definition-repair': ('prop reciprocal_window(x R):\n'
                                         '    x > 0\n'
                                         '    x != 1\n'
                                         '    1 / (x - 1) > 0\n'
                                         '    x < 2',
                                         True),
 'reciprocal-window-instance': ('prop reciprocal_window(x R):\n'
                                '    x > 0\n'
                                '    x != 1\n'
                                '    1 / (x - 1) > 0\n'
                                '    x < 2\n'
                                '\n'
                                'by def $reciprocal_window(3 / 2)\n',
                                True)}


TRUST_HAVE_HISTORY_CASES = {'body-formation-prefix': {'source': 'trust have denominator R:\n'
                                     '    denominator != 0\n'
                                     '    1 / denominator $in R\n',
                           'success': False,
                           'strict': False},
 'body-formation-repair': {'source': 'trust have denominator R:\n    denominator != 0\n',
                           'success': True,
                           'strict': False},
 'second-parameter-wd': {'source': 'trust have first R, second {1 / 0}:\n    first = first\n',
                         'success': False,
                         'strict': False},
 'second-parameter-repair': {'source': 'trust have first R, second {1 / 2}:\n    first = first\n',
                             'success': True,
                             'strict': False},
 'formed-false-body': {'source': 'trust have arbitrary R:\n    arbitrary = 0\n    arbitrary = 1\n',
                       'success': True,
                       'strict': False},
 'template-body-formation': {'source': 'template<A set>:\n'
                                       '    trust have template_a R:\n'
                                       '        template_a != 0\n'
                                       '        1 / template_a $in R\n',
                             'success': False,
                             'strict': False},
 'template-body-repair': {'source': 'template<A set>:\n'
                                    '    trust have template_a R:\n'
                                    '        template_a != 0\n',
                          'success': True,
                          'strict': False},
 'body-prefix-with-unchecked': {'source': 'trust have later R:\n'
                                          '    later = later\n'
                                          '    1 / later $in R\n'
                                          '    later = 0\n',
                                'success': False,
                                'strict': False},
 'first-parameter-wd': {'source': 'trust have no_first {1 / 0}:\n    no_first = no_first\n',
                        'success': False,
                        'strict': False},
 'strict-policy': {'source': 'trust have denominator R:\n    denominator != 0\n',
                   'success': False,
                   'strict': True},
 'strict-template-policy': {'source': 'template<A set>:\n'
                                      '    trust have template_a R:\n'
                                      '        template_a != 0\n',
                            'success': False,
                            'strict': True}}


PEER_QUANTIFIER_FORMATION_CASES = {'exist-second-parameter': {'source': 'prop bounded_pair(t R):\n'
                                      '    exist a R, b {1 / 0} st {a = a}\n',
                            'success': False},
 'exist-second-parameter-repair': {'source': 'prop bounded_pair(t R):\n'
                                             '    exist a R, b {1 / 2} st {a = a}\n',
                                   'success': True},
 'exist-body-prefix': {'source': 'prop existential_body(t R):\n'
                                 '    exist x R st {x > 0, 1 / (x - 1) > 0, x = x}\n',
                       'success': False},
 'exist-body-prefix-repair': {'source': 'prop existential_body(t R):\n'
                                        '    exist x R st {x > 0, x - 1 != 0, 1 / (x - 1) > 0, x = '
                                        'x}\n',
                              'success': True},
 'unique-second-parameter': {'source': 'prop unique_parameters(t R):\n'
                                       '    exist! a R, b {1 / 0} st {a = a}\n',
                             'success': False},
 'unique-second-parameter-repair': {'source': 'prop unique_parameters(t R):\n'
                                              '    exist! a R, b {1 / 2} st {a = a}\n',
                                    'success': True},
 'notexist-second-parameter': {'source': 'prop absent_parameters(t R):\n'
                                         '    not exist a R, b {1 / 0} st {a = a}\n',
                               'success': False},
 'notexist-second-parameter-repair': {'source': 'prop absent_parameters(t R):\n'
                                                '    not exist a R, b {1 / 2} st {a = a}\n',
                                      'success': True},
 'notforall-second-parameter': {'source': 'prop refutation_parameters(t R):\n'
                                          '    not forall a R, b {1 / 0}:\n'
                                          '        a = a\n',
                                'success': False},
 'notforall-second-parameter-repair': {'source': 'prop refutation_parameters(t R):\n'
                                                 '    not forall a R, b {1 / 2}:\n'
                                                 '        a = a\n',
                                       'success': True},
 'iff-second-parameter': {'source': 'prop equivalent_parameters(t R):\n'
                                    '    forall a R, b {1 / 0}:\n'
                                    '        =>:\n'
                                    '            a = a\n'
                                    '        <=>:\n'
                                    '            a = a\n',
                          'success': False},
 'iff-second-parameter-repair': {'source': 'prop equivalent_parameters(t R):\n'
                                           '    forall a R, b {1 / 2}:\n'
                                           '        =>:\n'
                                           '            a = a\n'
                                           '        <=>:\n'
                                           '            a = a\n',
                                 'success': True},
 'notforall-premise-prefix': {'source': 'prop refutation_premises(t R):\n'
                                        '    not forall x R:\n'
                                        '        x > 0\n'
                                        '        1 / (x - 1) $in R\n'
                                        '        =>:\n'
                                        '            x = x\n',
                              'success': False},
 'notforall-premise-prefix-repair': {'source': 'prop refutation_premises(t R):\n'
                                               '    not forall x R:\n'
                                               '        x > 0\n'
                                               '        x - 1 != 0\n'
                                               '        1 / (x - 1) $in R\n'
                                               '        =>:\n'
                                               '            x = x\n',
                                     'success': True},
 'notforall-false-consequent-prefix': {'source': 'prop refutation_conclusions(t R):\n'
                                                 '    not forall x R:\n'
                                                 '        x > 0\n'
                                                 '        =>:\n'
                                                 '            x = 0\n'
                                                 '            1 / (x - 1) > 0\n'
                                                 '            x = x\n',
                                       'success': False},
 'notforall-false-consequent-prefix-repair': {'source': 'prop refutation_conclusions(t R):\n'
                                                        '    not forall x R:\n'
                                                        '        x > 0\n'
                                                        '        x - 1 != 0\n'
                                                        '        =>:\n'
                                                        '            x = 0\n'
                                                        '            1 / (x - 1) > 0\n'
                                                        '            x = x\n',
                                              'success': True},
 'iff-premise-prefix': {'source': 'prop equivalence_premises(t R):\n'
                                  '    forall x R:\n'
                                  '        x > 0\n'
                                  '        1 / (x - 1) $in R\n'
                                  '        =>:\n'
                                  '            x = x\n'
                                  '        <=>:\n'
                                  '            x = x\n',
                        'success': False},
 'iff-premise-prefix-repair': {'source': 'prop equivalence_premises(t R):\n'
                                         '    forall x R:\n'
                                         '        x > 0\n'
                                         '        x - 1 != 0\n'
                                         '        1 / (x - 1) $in R\n'
                                         '        =>:\n'
                                         '            x = x\n'
                                         '        <=>:\n'
                                         '            x = x\n',
                               'success': True},
 'iff-left-false-prefix': {'source': 'prop equivalence_left(t R):\n'
                                     '    forall x R:\n'
                                     '        x > 0\n'
                                     '        =>:\n'
                                     '            x = 0\n'
                                     '            1 / (x - 1) > 0\n'
                                     '            x = x\n'
                                     '        <=>:\n'
                                     '            x = x\n',
                           'success': False},
 'iff-left-false-prefix-repair': {'source': 'prop equivalence_left(t R):\n'
                                            '    forall x R:\n'
                                            '        x > 0\n'
                                            '        x - 1 != 0\n'
                                            '        =>:\n'
                                            '            x = 0\n'
                                            '            1 / (x - 1) > 0\n'
                                            '            x = x\n'
                                            '        <=>:\n'
                                            '            x = x\n',
                                  'success': True},
 'iff-right-false-left': {'source': 'prop equivalence_right(t R):\n'
                                    '    forall x R:\n'
                                    '        x > 0\n'
                                    '        =>:\n'
                                    '            x = 0\n'
                                    '        <=>:\n'
                                    '            x = x\n'
                                    '            1 / (x - 1) > 0\n'
                                    '            x = x\n',
                          'success': False},
 'iff-right-false-left-repair': {'source': 'prop equivalence_right(t R):\n'
                                           '    forall x R:\n'
                                           '        x > 0\n'
                                           '        x - 1 != 0\n'
                                           '        =>:\n'
                                           '            x = 0\n'
                                           '        <=>:\n'
                                           '            x = x\n'
                                           '            1 / (x - 1) > 0\n'
                                           '            x = x\n',
                                 'success': True},
 'unique-body-prefix': {'source': 'prop unique_body(t R):\n'
                                  '    exist! x R st {x > 0, 1 / (x - 1) > 0, x = x}\n',
                        'success': False},
 'unique-body-prefix-repair': {'source': 'prop unique_body(t R):\n'
                                         '    exist! x R st {x > 0, x - 1 != 0, 1 / (x - 1) > 0, x '
                                         '= x}\n',
                               'success': True},
 'notexist-body-prefix': {'source': 'prop absent_body(t R):\n'
                                    '    not exist x R st {x > 0, 1 / (x - 1) > 0, x = x}\n',
                          'success': False},
 'notexist-body-prefix-repair': {'source': 'prop absent_body(t R):\n'
                                           '    not exist x R st {x > 0, x - 1 != 0, 1 / (x - 1) > '
                                           '0, x = x}\n',
                                 'success': True},
 'top-exist-parameter': {'source': 'exist a R, b {1 / 0} st {a = a}\n', 'success': False},
 'top-unique-parameter': {'source': 'exist! a R, b {1 / 0} st {a = a}\n', 'success': False},
 'top-notexist-parameter': {'source': 'not exist a R, b {1 / 0} st {a = a}\n', 'success': False},
 'top-notforall-parameter': {'source': 'not forall a R, b {1 / 0}:\n    a = a\n', 'success': False},
 'top-iff-parameter': {'source': 'forall a R, b {1 / 0}:\n'
                                 '    =>:\n'
                                 '        a = a\n'
                                 '    <=>:\n'
                                 '        a = a\n',
                       'success': False},
 'false-equivalence-instance': {'source': 'prop equivalence_left(t R):\n'
                                          '    forall x R:\n'
                                          '        x > 0\n'
                                          '        x - 1 != 0\n'
                                          '        =>:\n'
                                          '            x = 0\n'
                                          '            1 / (x - 1) > 0\n'
                                          '            x = x\n'
                                          '        <=>:\n'
                                          '            x = x\n'
                                          '\n'
                                          'by def $equivalence_left(2)\n',
                                'success': False},
 'unique-definition-is-not-proof': {'source': 'prop unique_body(t R):\n'
                                              '    exist! x R st {x > 0, x - 1 != 0, 1 / (x - 1) > '
                                              '0, x = x}\n'
                                              '\n'
                                              'by def $unique_body(2)\n',
                                    'success': False},
 'nonexistence-definition-is-not-proof': {'source': 'prop absent_body(t R):\n'
                                                    '    not exist x R st {x > 0, x - 1 != 0, 1 / '
                                                    '(x - 1) > 0, x = x}\n'
                                                    '\n'
                                                    'by def $absent_body(2)\n',
                                          'success': False},
 'exist-first-parameter': {'source': 'prop first_exist_parameter(t R):\n'
                                     '    exist a {1 / 0} st {a = a}\n',
                           'success': False},
 'notforall-first-parameter': {'source': 'prop first_refutation_parameter(t R):\n'
                                         '    not forall a {1 / 0}:\n'
                                         '        a = a\n',
                               'success': False},
 'iff-first-parameter': {'source': 'prop first_equivalence_parameter(t R):\n'
                                   '    forall a {1 / 0}:\n'
                                   '        =>:\n'
                                   '            a = a\n'
                                   '        <=>:\n'
                                   '            a = a\n',
                         'success': False},
 'inference-definition': {'source': 'prop nonzero_value(x R):\n    x != 0\n', 'success': True},
 'exist-local-inference': {'source': 'prop nonzero_value(x R):\n'
                                     '    x != 0\n'
                                     '\n'
                                     'prop inferred_exist_body(t R):\n'
                                     '    exist x R st {$nonzero_value(x), 1 / (x - 1) > 0, x = '
                                     'x}\n',
                           'success': False},
 'exist-local-inference-repair': {'source': 'prop nonzero_value(x R):\n'
                                            '    x != 0\n'
                                            '\n'
                                            'prop inferred_exist_body(t R):\n'
                                            '    exist x R st {$nonzero_value(x), x - 1 != 0, 1 / '
                                            '(x - 1) > 0, x = x}\n',
                                  'success': True},
 'notforall-local-inference': {'source': 'prop nonzero_value(x R):\n'
                                         '    x != 0\n'
                                         '\n'
                                         'prop inferred_refutation_body(t R):\n'
                                         '    not forall x R:\n'
                                         '        $nonzero_value(x)\n'
                                         '        1 / (x - 1) $in R\n'
                                         '        =>:\n'
                                         '            x = x\n',
                               'success': False},
 'notforall-local-inference-repair': {'source': 'prop nonzero_value(x R):\n'
                                                '    x != 0\n'
                                                '\n'
                                                'prop inferred_refutation_body(t R):\n'
                                                '    not forall x R:\n'
                                                '        $nonzero_value(x)\n'
                                                '        x - 1 != 0\n'
                                                '        1 / (x - 1) $in R\n'
                                                '        =>:\n'
                                                '            x = x\n',
                                      'success': True},
 'iff-local-inference': {'source': 'prop nonzero_value(x R):\n'
                                   '    x != 0\n'
                                   '\n'
                                   'prop inferred_equivalence_body(t R):\n'
                                   '    forall x R:\n'
                                   '        $nonzero_value(x)\n'
                                   '        1 / (x - 1) $in R\n'
                                   '        =>:\n'
                                   '            x = x\n'
                                   '        <=>:\n'
                                   '            x = x\n',
                         'success': False},
 'iff-local-inference-repair': {'source': 'prop nonzero_value(x R):\n'
                                          '    x != 0\n'
                                          '\n'
                                          'prop inferred_equivalence_body(t R):\n'
                                          '    forall x R:\n'
                                          '        $nonzero_value(x)\n'
                                          '        x - 1 != 0\n'
                                          '        1 / (x - 1) $in R\n'
                                          '        =>:\n'
                                          '            x = x\n'
                                          '        <=>:\n'
                                          '            x = x\n',
                                'success': True},
 'top-iff-reverse-formation': {'source': 'forall x R:\n'
                                         '    =>:\n'
                                         '        x != 0\n'
                                         '    <=>:\n'
                                         '        1 / x $in R\n',
                               'success': False},
 'top-iff-reverse-formation-repair': {'source': 'forall x R:\n'
                                                '    x != 0\n'
                                                '    =>:\n'
                                                '        x != 0\n'
                                                '    <=>:\n'
                                                '        1 / x $in R\n',
                                      'success': True},
 'top-iff-nonzero-domain': {'source': 'forall x R*:\n'
                                      '    =>:\n'
                                      '        x != 0\n'
                                      '    <=>:\n'
                                      '        1 / x $in R\n',
                            'success': True}}


COMPOUND_QUANTIFIER_FORMATION_CASES = {'and-failed-inside-clause': {'source': 'prop bounded_reciprocal(t R):\n'
                                        '    exist x R st {x != 0 and 1 / x > 0}\n',
                              'success': False},
 'and-split-clauses-repair': {'source': 'prop bounded_reciprocal(t R):\n'
                                        '    exist x R st {x != 0, 1 / x > 0}\n',
                              'success': True},
 'and-complete-before-failure': {'source': 'prop and_candidates(t R):\n'
                                           '    exist x R st {x >= 0 and x <= 1, 1 / x > 0, x = '
                                           'x}\n',
                                 'success': False},
 'and-complete-before-failure-repair': {'source': 'prop and_candidates(t R):\n'
                                                  '    exist x R st {x >= 0 and x <= 1, x != 0, 1 '
                                                  '/ x > 0, x = x}\n',
                                        'success': True},
 'chain-complete-before-failure': {'source': 'prop chain_candidates(t R):\n'
                                             '    exist x R st {0 <= x <= 1, 1 / x > 0, x = x}\n',
                                   'success': False},
 'chain-complete-before-failure-repair': {'source': 'prop chain_candidates(t R):\n'
                                                    '    exist x R st {0 <= x <= 1, x != 0, 1 / x '
                                                    '> 0, x = x}\n',
                                          'success': True},
 'or-complete-before-failure': {'source': 'prop or_candidates(t R):\n'
                                          '    exist x R st {x = 0 or x = 1, 1 / x > 0, x = x}\n',
                                'success': False},
 'or-complete-before-failure-repair': {'source': 'prop or_candidates(t R):\n'
                                                 '    exist x R st {x = 0 or x = 1, x != 0, 1 / x '
                                                 '> 0, x = x}\n',
                                       'success': True},
 'mixed-or-before-failure': {'source': 'prop mixed_or_candidates(t R):\n'
                                       '    exist x R st {x = 0 and x = x or 0 < x < 1, 1 / x > 0, '
                                       'x = x}\n',
                             'success': False},
 'mixed-or-before-failure-repair': {'source': 'prop mixed_or_candidates(t R):\n'
                                              '    exist x R st {x = 0 and x = x or 0 < x < 1, x '
                                              '!= 0, 1 / x > 0, x = x}\n',
                                    'success': True},
 'chain-failed-inside-clause': {'source': 'prop chain_formation(t R):\n'
                                          '    exist x R st {x = x = 1 / x = 0}\n',
                                'success': False},
 'chain-failed-inside-clause-repair': {'source': 'prop chain_formation(t R):\n'
                                                 '    exist x R st {x != 0, x = x = 1 / x = 0}\n',
                                       'success': True},
 'or-failed-inside-clause': {'source': 'prop or_formation(t R):\n'
                                       '    exist x R st {x = x or 1 / x > 0 or x = 1}\n',
                             'success': False},
 'or-failed-inside-clause-repair': {'source': 'prop or_formation(t R):\n'
                                              '    exist x R st {x != 0, x = x or 1 / x > 0 or x = '
                                              '1}\n',
                                    'success': True},
 'nested-or-and-failure': {'source': 'prop nested_formation(t R):\n'
                                     '    exist x R st {x = x or x != 0 and 1 / x > 0 or x = 1}\n',
                           'success': False},
 'nested-or-and-failure-repair': {'source': 'prop nested_formation(t R):\n'
                                            '    exist x R st {x != 0, x = x or x != 0 and 1 / x > '
                                            '0 or x = 1}\n',
                                  'success': True},
 'unique-and-prefix': {'source': 'prop unique_compound(t R):\n'
                                 '    exist! x R st {x >= 0 and x <= 1, 1 / x > 0, x = x}\n',
                       'success': False},
 'unique-and-prefix-repair': {'source': 'prop unique_compound(t R):\n'
                                        '    exist! x R st {x >= 0 and x <= 1, x != 0, 1 / x > 0, '
                                        'x = x}\n',
                              'success': True},
 'notexist-or-prefix': {'source': 'prop no_compound(t R):\n'
                                  '    not exist x R st {x = 0 or x = 1, 1 / x > 0, x = x}\n',
                        'success': False},
 'notexist-or-prefix-repair': {'source': 'prop no_compound(t R):\n'
                                         '    not exist x R st {x = 0 or x = 1, x != 0, 1 / x > 0, '
                                         'x = x}\n',
                               'success': True},
 'notforall-chain-premise': {'source': 'prop counter_compound(t R):\n'
                                       '    not forall x R:\n'
                                       '        0 <= x <= 1\n'
                                       '        1 / x > 0\n'
                                       '        =>:\n'
                                       '            x = x\n',
                             'success': False},
 'notforall-chain-premise-repair': {'source': 'prop counter_compound(t R):\n'
                                              '    not forall x R:\n'
                                              '        0 <= x <= 1\n'
                                              '        x != 0\n'
                                              '        1 / x > 0\n'
                                              '        =>:\n'
                                              '            x = x\n',
                                    'success': True},
 'iff-or-premise': {'source': 'prop equivalent_compound(t R):\n'
                              '    forall x R:\n'
                              '        x = 0 or x = 1\n'
                              '        1 / x > 0\n'
                              '        =>:\n'
                              '            x = x\n'
                              '        <=>:\n'
                              '            x = x\n',
                    'success': False},
 'iff-or-premise-repair': {'source': 'prop equivalent_compound(t R):\n'
                                     '    forall x R:\n'
                                     '        x = 0 or x = 1\n'
                                     '        x != 0\n'
                                     '        1 / x > 0\n'
                                     '        =>:\n'
                                     '            x = x\n'
                                     '        <=>:\n'
                                     '            x = x\n',
                           'success': True},
 'forall-proof-and-premise': {'source': 'forall x R:\n'
                                        '    x >= 0 and x <= 1\n'
                                        '    1 / x > 0\n'
                                        '    =>:\n'
                                        '        x = x\n',
                              'success': False},
 'forall-proof-and-premise-repair': {'source': 'forall x R:\n'
                                               '    x >= 0 and x <= 1\n'
                                               '    x != 0\n'
                                               '    1 / x > 0\n'
                                               '    =>:\n'
                                               '        x = x\n',
                                     'success': True},
 'forall-false-and-consequent': {'source': 'prop false_and_tail(t R):\n'
                                           '    forall x R:\n'
                                           '        x >= 0\n'
                                           '        =>:\n'
                                           '            x = 0 and x = 1\n'
                                           '            1 / (x - 1) > 0\n'
                                           '            x = x\n',
                                 'success': False},
 'forall-false-and-consequent-repair': {'source': 'prop false_and_tail(t R):\n'
                                                  '    forall x R:\n'
                                                  '        x >= 0\n'
                                                  '        x - 1 != 0\n'
                                                  '        =>:\n'
                                                  '            x = 0 and x = 1\n'
                                                  '            1 / (x - 1) > 0\n'
                                                  '            x = x\n',
                                        'success': True},
 'notforall-false-or-consequent': {'source': 'prop false_or_tail(t R):\n'
                                             '    not forall x R:\n'
                                             '        x >= 0\n'
                                             '        =>:\n'
                                             '            x < 0 or x > 1\n'
                                             '            1 / (x - 1) > 0\n'
                                             '            x = x\n',
                                   'success': False},
 'notforall-false-or-consequent-repair': {'source': 'prop false_or_tail(t R):\n'
                                                    '    not forall x R:\n'
                                                    '        x >= 0\n'
                                                    '        x - 1 != 0\n'
                                                    '        =>:\n'
                                                    '            x < 0 or x > 1\n'
                                                    '            1 / (x - 1) > 0\n'
                                                    '            x = x\n',
                                          'success': True},
 'iff-false-chain-left': {'source': 'prop false_chain_left(t R):\n'
                                    '    forall x R:\n'
                                    '        x >= 0\n'
                                    '        =>:\n'
                                    '            x = 0 = 1\n'
                                    '            1 / (x - 1) > 0\n'
                                    '        <=>:\n'
                                    '            x = x\n',
                          'success': False},
 'iff-false-chain-left-repair': {'source': 'prop false_chain_left(t R):\n'
                                           '    forall x R:\n'
                                           '        x >= 0\n'
                                           '        x - 1 != 0\n'
                                           '        =>:\n'
                                           '            x = 0 = 1\n'
                                           '            1 / (x - 1) > 0\n'
                                           '        <=>:\n'
                                           '            x = x\n',
                                 'success': True},
 'iff-false-and-right': {'source': 'prop false_and_right(t R):\n'
                                   '    forall x R:\n'
                                   '        x >= 0\n'
                                   '        =>:\n'
                                   '            x = x\n'
                                   '        <=>:\n'
                                   '            x = 0 and x = 1\n'
                                   '            1 / (x - 1) > 0\n'
                                   '            x = x\n',
                         'success': False},
 'iff-false-and-right-repair': {'source': 'prop false_and_right(t R):\n'
                                          '    forall x R:\n'
                                          '        x >= 0\n'
                                          '        x - 1 != 0\n'
                                          '        =>:\n'
                                          '            x = x\n'
                                          '        <=>:\n'
                                          '            x = 0 and x = 1\n'
                                          '            1 / (x - 1) > 0\n'
                                          '            x = x\n',
                                'success': True},
 'forall-partial-and-conclusion': {'source': 'prop partial_and_tail(t R):\n'
                                             '    forall x R:\n'
                                             '        x >= 0\n'
                                             '        =>:\n'
                                             '            x != 0 and 1 / x > 0\n'
                                             '            x = x\n',
                                   'success': False},
 'forall-partial-and-conclusion-repair': {'source': 'prop partial_and_tail(t R):\n'
                                                    '    forall x R:\n'
                                                    '        x >= 0\n'
                                                    '        x != 0\n'
                                                    '        =>:\n'
                                                    '            x != 0 and 1 / x > 0\n'
                                                    '            x = x\n',
                                          'success': True},
 'iff-partial-chain-left': {'source': 'prop partial_chain_left(t R):\n'
                                      '    forall x R:\n'
                                      '        x >= 0\n'
                                      '        =>:\n'
                                      '            x = x = 1 / x = 0\n'
                                      '        <=>:\n'
                                      '            x = x\n',
                            'success': False},
 'iff-partial-chain-left-repair': {'source': 'prop partial_chain_left(t R):\n'
                                             '    forall x R:\n'
                                             '        x >= 0\n'
                                             '        x != 0\n'
                                             '        =>:\n'
                                             '            x = x = 1 / x = 0\n'
                                             '        <=>:\n'
                                             '            x = x\n',
                                   'success': True},
 'false-consequent-instance': {'source': 'prop false_and_tail(t R):\n'
                                         '    forall x R:\n'
                                         '        x >= 0\n'
                                         '        x - 1 != 0\n'
                                         '        =>:\n'
                                         '            x = 0 and x = 1\n'
                                         '            1 / (x - 1) > 0\n'
                                         '            x = x\n'
                                         '\n'
                                         'by def $false_and_tail(0)\n',
                               'success': False},
 'false-iff-instance': {'source': 'prop false_and_right(t R):\n'
                                  '    forall x R:\n'
                                  '        x >= 0\n'
                                  '        x - 1 != 0\n'
                                  '        =>:\n'
                                  '            x = x\n'
                                  '        <=>:\n'
                                  '            x = 0 and x = 1\n'
                                  '            1 / (x - 1) > 0\n'
                                  '            x = x\n'
                                  '\n'
                                  'by def $false_and_right(0)\n',
                        'success': False},
 'named-guard-definition': {'source': 'prop nonzero_value(x R):\n    x != 0\n', 'success': True},
 'and-named-local-inference': {'source': 'prop nonzero_value(x R):\n'
                                         '    x != 0\n'
                                         '\n'
                                         'prop named_guard_candidate(t R):\n'
                                         '    exist x R st {$nonzero_value(x) and x >= 0, 1 / (x - '
                                         '1) > 0, x = x}\n',
                               'success': False},
 'and-named-local-inference-repair': {'source': 'prop nonzero_value(x R):\n'
                                                '    x != 0\n'
                                                '\n'
                                                'prop named_guard_candidate(t R):\n'
                                                '    exist x R st {$nonzero_value(x) and x >= 0, x '
                                                '- 1 != 0, 1 / (x - 1) > 0, x = x}\n',
                                      'success': True},
 'chain-local-inference': {'source': 'prop chain_guard_candidate(t R):\n'
                                     '    exist x R st {0 < x <= 1, 1 / (x - 1) > 0, x = x}\n',
                           'success': False},
 'chain-local-inference-repair': {'source': 'prop chain_guard_candidate(t R):\n'
                                            '    exist x R st {0 < x <= 1, x - 1 != 0, 1 / (x - 1) '
                                            '> 0, x = x}\n',
                                  'success': True},
 'and-first-component-failure': {'source': 'prop and_first(t R):\n'
                                           '    exist x R st {1 / x > 0 and x != 0}\n',
                                 'success': False},
 'chain-first-link-failure': {'source': 'prop chain_first(t R):\n'
                                        '    exist x R st {1 / x = x = 0}\n',
                              'success': False},
 'or-first-branch-failure': {'source': 'prop or_first(t R):\n'
                                       '    exist x R st {1 / x > 0 or x = x}\n',
                             'success': False},
 'and-last-component-failure': {'source': 'prop and_last(t R):\n'
                                          '    exist x R st {x != 0 and x = x and 1 / x > 0}\n',
                                'success': False},
 'or-last-branch-failure': {'source': 'prop or_last(t R):\n'
                                      '    exist x R st {x = x or x = 0 or 1 / x > 0}\n',
                            'success': False},
 'membership-chain-prefix': {'source': 'prop membership_chain(t R):\n'
                                       '    exist S set st {1 $in S $subset R, 1 / t > 0}\n',
                             'success': False},
 'membership-chain-prefix-repair': {'source': 'prop membership_chain(t R):\n'
                                              '    exist S set st {t != 0, 1 $in S $subset R, 1 / '
                                              't > 0}\n',
                                    'success': False},
 'membership-conjunction-before-failure': {'source': 'prop membership_chain(t R):\n'
                                                     '    exist S set st {1 $in S and S $subset R, '
                                                     '1 / t > 0}\n',
                                           'success': False},
 'membership-conjunction-before-failure-repair': {'source': 'prop membership_chain(t R):\n'
                                                            '    exist S set st {t != 0, 1 $in S '
                                                            'and S $subset R, 1 / t > 0}\n',
                                                  'success': True}}


STRUCT_INTRO_DEFINITIONS = 'struct ScalarOperations:\n    unit R\n    combine fn(x, y R) R\n    <=>:\n        unit = 1\n\nstruct ScalarAction:\n    scalars &ScalarOperations\n    act fn(a, x R) R\n    <=>:\n        forall a, b, x R:\n            act(scalars.combine(a, b), x) = act(a, act(b, x))\n\nstruct ScalarIdentity<S nonempty_set>:\n    zero S\n    add fn(x, y S) S\n    <=>:\n        forall x S:\n            add(zero, x) = x\n\nstruct IdentityCarrier<S nonempty_set>:\n    scalars &ScalarIdentity<S>\n    element S\n'
STRUCT_INTRO_CASES = {
    'trusted': {'source': STRUCT_INTRO_DEFINITIONS + '\ntrust have assumed_action &ScalarOperations:\n    assumed_action.unit = 1\n', 'success': True, 'strict': False},
    'failed-trusted': {'source': STRUCT_INTRO_DEFINITIONS + '\ntrust have broken_action &ScalarOperations:\n    broken_action.unit = 1\n    1 / 0 = 0\n    broken_action.unit != 1\n', 'success': False, 'strict': False},
    'verified': {'source': STRUCT_INTRO_DEFINITIONS + '\nstruct ReadingOwnedPair:\n    first R\n    second Z\nhave owned_pair &ReadingOwnedPair = (1/2, 2)\n', 'success': True, 'strict': True},
    'template-failed': {'source': STRUCT_INTRO_DEFINITIONS + '\ntemplate<T nonempty_set>:\n    trust have template_assumed &ScalarIdentity<T>:\n        template_assumed.zero $in T\n        1 / 0 = 0\n        template_assumed.zero = template_assumed.zero\n', 'success': False, 'strict': False},
    'template-parent-failed': {'source': STRUCT_INTRO_DEFINITIONS + '\ntemplate<outer &ScalarOperations>:\n    trust have template_assumed &ScalarOperations:\n        template_assumed.unit = outer.unit\n        1 / 0 = 0\n        template_assumed.unit != outer.unit\n', 'success': False, 'strict': False},
    'chosen': {'source': STRUCT_INTRO_DEFINITIONS + '\nstruct ReadingOwnedPair:\n    first R\n    second Z\nhave owned_pair &ReadingOwnedPair = (1/2, 2)\nwitness $is_nonempty_set(&ReadingOwnedPair) from owned_pair\nhave chosen_pair &ReadingOwnedPair\n', 'success': True, 'strict': True},
    'compound-failed': {'source': STRUCT_INTRO_DEFINITIONS + '\ntrust have compound_action &ScalarOperations:\n    forall x R:\n        compound_action.combine(x, 0) = x\n    1 / 0 = 0\n    compound_action.unit = 1\n', 'success': False, 'strict': False},
    'conflicting': {'source': STRUCT_INTRO_DEFINITIONS + '\ntrust have conflicting_action &ScalarOperations:\n    conflicting_action.unit = 2\n', 'success': True, 'strict': False},
    'local-trusted': {'source': STRUCT_INTRO_DEFINITIONS + '\nsketch:\n    trust have local_assumed &ScalarOperations:\n        local_assumed.unit = 2\n    local_assumed.unit = 1\n', 'success': True, 'strict': False},
    'template-trusted': {'source': STRUCT_INTRO_DEFINITIONS + '\ntemplate<T set>:\n    trust have template_assumed &ScalarOperations:\n        template_assumed.unit = 2\n', 'success': True, 'strict': False},
    'multiple-trusted': {'source': STRUCT_INTRO_DEFINITIONS + '\ntrust have first_assumed, second_assumed &ScalarOperations:\n    first_assumed.unit = second_assumed.unit\n', 'success': True, 'strict': False},
    'strict-trusted': {'source': STRUCT_INTRO_DEFINITIONS + '\ntrust have assumed_action &ScalarOperations:\n    assumed_action.unit = 1\n', 'success': False, 'strict': True},
    'strict-template': {'source': STRUCT_INTRO_DEFINITIONS + '\ntemplate<T set>:\n    trust have template_assumed &ScalarOperations:\n        template_assumed.unit = 2\n', 'success': False, 'strict': True},
    'local-verified': {'source': STRUCT_INTRO_DEFINITIONS + '\nstruct ReadingOwnedPair:\n    first R\n    second Z\nsketch:\n    have local_owned &ReadingOwnedPair = (1/2, 2)\n    local_owned.first $in R\n', 'success': True, 'strict': True},
    'invalid-verified': {'source': STRUCT_INTRO_DEFINITIONS + '\nstruct ReadingOwnedPair:\n    first R\n    second Z\nhave invalid_owned &ReadingOwnedPair = (1, {})\n', 'success': False, 'strict': True},
    'local-failed-trusted': {'source': STRUCT_INTRO_DEFINITIONS + '\nsketch:\n    trust have local_broken &ScalarOperations:\n        local_broken.unit = 1\n        1 / 0 = 0\n        local_broken.unit != 1\n', 'success': False, 'strict': False},
}
STRUCT_INTRO_BOOK = {'01-definitions.lit': 'struct ScalarOperations:\n'
                       '    unit R\n'
                       '    combine fn(x, y R) R\n'
                       '    <=>:\n'
                       '        unit = 1\n'
                       '\n'
                       'struct ScalarAction:\n'
                       '    scalars &ScalarOperations\n'
                       '    act fn(a, x R) R\n'
                       '    <=>:\n'
                       '        forall a, b, x R:\n'
                       '            act(scalars.combine(a, b), x) = act(a, act(b, x))\n'
                       '\n'
                       'struct ScalarIdentity<S nonempty_set>:\n'
                       '    zero S\n'
                       '    add fn(x, y S) S\n'
                       '    <=>:\n'
                       '        forall x S:\n'
                       '            add(zero, x) = x\n'
                       '\n'
                       'struct IdentityCarrier<S nonempty_set>:\n'
                       '    scalars &ScalarIdentity<S>\n'
                       '    element S\n'
                       '\n'
                       'struct ReadingOwnedPair:\n'
                       '    first R\n'
                       '    second Z\n',
 '02-proofs.lit': 'trust have book_assumed &structures::ScalarOperations:\n'
                  '    book_assumed.unit = 1\n'
                  'have book_owned &structures::ReadingOwnedPair = (1/2, 2)\n'
                  'witness $is_nonempty_set(&structures::ReadingOwnedPair) from book_owned\n'
                  'have book_chosen &structures::ReadingOwnedPair\n'
                  'book_owned.first $in R\n'
                  'trust have book_broken &structures::ScalarOperations:\n'
                  '    book_broken.unit = 1\n'
                  '    1 / 0 = 0\n'
                  '    book_broken.unit != 1\n',
 'litex.config': '[export]\nstructures = "./01-definitions.lit"\nproofs = "./02-proofs.lit"\n',
 'reading-titles.json': '{\n'
                        '  "01-definitions.lit": {\n'
                        '    "zh": "结构的定义",\n'
                        '    "en": "Structure definitions"\n'
                        '  },\n'
                        '  "02-proofs.lit": {\n'
                        '    "zh": "对象与性质的来源",\n'
                        '    "en": "Origins of objects and properties"\n'
                        '  }\n'
                        '}\n'}


TEMPLATE_CONTEXT_CASES = {'guarded': {'source': 'template<S set: $is_nonempty_set(S)>:\n    have guarded S\n\\guarded<R> $in R\n\n',
             'strict': True,
             'success': True},
 'published': {'path': 'examples/stmt_nodes/definition/template_definition_facts.lit',
               'strict': True,
               'success': True},
 'domain-prefix': {'path': 'examples/test_statements/negative/def_template_stmt/retained-domain-prefix.lit',
                   'strict': True,
                   'success': False},
 'structural-parameter': {'source': 'struct ScalarOperations:\n'
                                    '    unit R\n'
                                    '    combine fn(x, y R) R\n'
                                    '    <=>:\n'
                                    '        unit = 1\n'
                                    '\n'
                                    'struct ScalarAction:\n'
                                    '    scalars &ScalarOperations\n'
                                    '    act fn(a, x R) R\n'
                                    '    <=>:\n'
                                    '        forall a, b, x R:\n'
                                    '            act(scalars.combine(a, b), x) = act(a, act(b, x))\n'
                                    '\n'
                                    'struct ScalarIdentity<S nonempty_set>:\n'
                                    '    zero S\n'
                                    '    add fn(x, y S) S\n'
                                    '    <=>:\n'
                                    '        forall x S:\n'
                                    '            add(zero, x) = x\n'
                                    '\n'
                                    'struct IdentityCarrier<S nonempty_set>:\n'
                                    '    scalars &ScalarIdentity<S>\n'
                                    '    element S\n'
                                    '\n'
                                    'template<outer &ScalarOperations>:\n'
                                    '    trust have template_assumed &ScalarOperations:\n'
                                    '        template_assumed.unit = outer.unit\n'
                                    '        1 / 0 = 0\n'
                                    '        template_assumed.unit != outer.unit\n',
                          'strict': False,
                          'success': False},
 'type-preflight': {'source': 'sketch:\n'
                              '    struct Point:\n'
                              '        x R\n'
                              '        y R\n'
                              '    have p &Point = (1, 2)\n'
                              '    p.x = p(1) = 1\n'
                              '    p.y = p(2) = 2\n',
                    'strict': True,
                    'success': True},
 'predicate': {'source': 'prop reading_template_nonzero(x R):\n'
                         '    x != 0\n'
                         '\n'
                         'template<a R: $reading_template_nonzero(a)>:\n'
                         '    have reading_inverse R = 1 / a\n',
               'strict': True,
               'success': True},
 'body-failed': {'source': 'prop reading_template_nonzero(x R):\n'
                           '    x != 0\n'
                           '\n'
                           'template<a R: $reading_template_nonzero(a)>:\n'
                           '    have reading_broken R = 1 / 0\n',
                 'strict': True,
                 'success': False},
 'body-repair': {'source': 'prop reading_template_nonzero(x R):\n'
                           '    x != 0\n'
                           '\n'
                           'template<a R: $reading_template_nonzero(a)>:\n'
                           '    have reading_broken R = 1 / a\n',
                 'strict': True,
                 'success': True},
 'premise-failed': {'source': 'prop reading_template_nonzero(x R):\n'
                              '    x != 0\n'
                              '\n'
                              'template<a R: $reading_template_nonzero(a), $is_set({1 / (a - 1)}), '
                              '$is_set({a})>:\n'
                              '    have reading_guard_prefix R = a\n',
                    'strict': True,
                    'success': False},
 'premise-repair': {'source': 'prop reading_template_nonzero(x R):\n'
                              '    x != 0\n'
                              '\n'
                              'template<a R: $reading_template_nonzero(a), a != 1, $is_set({1 / (a - 1)}), '
                              '$is_set({a})>:\n'
                              '    have reading_guard_prefix R = a\n',
                    'strict': True,
                    'success': True},
 'function-body': {'source': 'prop reading_template_nonzero(x R):\n'
                             '    x != 0\n'
                             '\n'
                             'template<a R: $reading_template_nonzero(a)>:\n'
                             '    have fn reading_shift(x R) R = x + 1 / a\n',
                   'strict': True,
                   'success': True},
 'predicate-use': {'source': 'prop reading_template_nonzero(x R):\n'
                             '    x != 0\n'
                             '\n'
                             'template<a R: $reading_template_nonzero(a)>:\n'
                             '    have reading_inverse R = 1 / a\n'
                             'by def $reading_template_nonzero(2)\n'
                             '\\reading_inverse<2> = 1 / 2\n',
                   'strict': True,
                   'success': True},
 'inconsistent': {'source': 'template<a R: a = 0, a != 0,>:\n    have reading_no_admissible R = a\n',
                  'strict': True,
                  'success': True},
 'inadmissible': {'source': 'template<a R: a = 0, a != 0,>:\n'
                            '    have reading_no_admissible R = a\n'
                            '\n'
                            '\\reading_no_admissible<0> = 0\n',
                  'strict': True,
                  'success': False},
 'structural-success': {'source': 'struct ScalarOperations:\n'
                                  '    unit R\n'
                                  '    combine fn(x, y R) R\n'
                                  '    <=>:\n'
                                  '        unit = 1\n'
                                  '\n'
                                  'template<ops &ScalarOperations: ops.unit = 1,>:\n'
                                  '    have reading_unit R = ops.unit\n',
                        'strict': True,
                        'success': True},
 'dependent': {'source': 'template<S nonempty_set, a S>:\n    have reading_selected S = a\n',
               'strict': True,
               'success': True}}
TEMPLATE_CONTEXT_BOOK = {'01-definitions.lit': 'prop reading_template_nonzero(x R):\n'
                       '    x != 0\n'
                       '\n'
                       'struct ScalarOperations:\n'
                       '    unit R\n'
                       '    combine fn(x, y R) R\n'
                       '    <=>:\n'
                       '        unit = 1\n',
 '02-templates.lit': 'template<a R: $definitions::reading_template_nonzero(a)>:\n'
                     '    have book_inverse R = 1 / a\n'
                     '\n'
                     'template<ops &definitions::ScalarOperations: ops.unit = 1,>:\n'
                     '    have book_unit R = ops.unit\n'
                     '\n'
                     'by def $definitions::reading_template_nonzero(2)\n'
                     '\n'
                     '\\book_inverse<2> = 1 / 2\n'
                     '\n'
                     'template<a R: $definitions::reading_template_nonzero(a)>:\n'
                     '    have fn book_shift(x R) R = x + 1 / a\n'
                     '\n'
                     'template<a R: $definitions::reading_template_nonzero(a), $is_set({1 / (a - 1)}), '
                     '$is_set({a})>:\n'
                     '    have book_invalid R = a\n',
 'reading-titles.json': '{\n'
                        '  "kind": "reading_titles",\n'
                        '  "sources": {\n'
                        '    "01-definitions.lit": {\n'
                        '      "en": "Definitions",\n'
                        '      "zh": "定义"\n'
                        '    },\n'
                        '    "02-templates.lit": {\n'
                        '      "en": "Families with premises",\n'
                        '      "zh": "带前提的定义族"\n'
                        '    }\n'
                        '  }\n'
                        '}\n',
 'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\ntemplates = "./02-templates.lit"\n'}



# Real strategy failures and repairs checked in one retained strict Session.
FAILED_STRATEGY_CONTEXT_CASES = {'final-conclusion-prefix': {'source': 'prop P(x R):\n'
                                       '    x = 0\n'
                                       'strategy fail_final:\n'
                                       '    ? forall x R:\n'
                                       '        x = 0\n'
                                       '        =>:\n'
                                       '            x = x\n'
                                       '            $P(x + 1)\n'
                                       '            x + 0 = x\n'
                                       '    have helper R = x\n'
                                       '    helper = x\n',
                             'strict': True,
                             'success': False},
 'body-prefix-failure': {'source': 'prop P(x R):\n'
                                   '    x = 0\n'
                                   'strategy fail_body:\n'
                                   '    ? forall x R:\n'
                                   '        x = 0\n'
                                   '        =>:\n'
                                   '            $P(x)\n'
                                   '    have local_helper R = x\n'
                                   '    local_helper = 0\n'
                                   '    7 = 8\n'
                                   '    have unchecked R = 9\n',
                         'strict': True,
                         'success': False},
 'goal-formation-before-body': {'source': 'prop P(x R):\n'
                                          '    x = 0\n'
                                          'strategy illformed:\n'
                                          '    ? forall x R:\n'
                                          '        1 / 0 = 0\n'
                                          '    1 = 1\n',
                                'strict': True,
                                'success': False},
 'empty-parameter-boundary': {'source': 'prop P(x R):\n'
                                        '    x = 0\n'
                                        'strategy empty:\n'
                                        '    ? forall x {}:\n'
                                        '        x = x\n'
                                        '    x = x\n',
                              'strict': True,
                              'success': True},
 'inferred-premise-final-failure': {'source': 'prop nonnegative(x R):\n'
                                              '    x >= 0\n'
                                              'strategy nonnegative_is_negative:\n'
                                              '    ? forall x R:\n'
                                              '        $nonnegative(x)\n'
                                              '        =>:\n'
                                              '            x >= 0\n'
                                              '            x < 0\n'
                                              '    have guarded R = x\n',
                                    'strict': True,
                                    'success': False},
 'same-name-repair': {'source': 'prop P(x R):\n'
                                '    x = 0\n'
                                'strategy fail_final:\n'
                                '    ? forall x R:\n'
                                '        x = 0\n'
                                '        =>:\n'
                                '            $P(x)\n'
                                '    by def $P(x)\n'
                                '$P(0)\n',
                      'strict': True,
                      'success': True},
 'scope-after-failure': {'source': 'prop P(x R):\n'
                                   '    x = 0\n'
                                   'strategy fail_final:\n'
                                   '    ? forall x R:\n'
                                   '        x = 0\n'
                                   '        =>:\n'
                                   '            x = x\n'
                                   '            $P(x + 1)\n'
                                   '            x + 0 = x\n'
                                   '    have helper R = x\n'
                                   '    helper = x\n'
                                   'have helper R = 1\n'
                                   'helper = 1\n',
                         'strict': True,
                         'success': False},
 'duplicate-before-body': {'source': 'prop P(x R):\n'
                                     '    x = 0\n'
                                     'strategy fail_final:\n'
                                     '    ? forall x R:\n'
                                     '        x = 0\n'
                                     '        =>:\n'
                                     '            $P(x)\n'
                                     '    by def $P(x)\n'
                                     'strategy fail_final:\n'
                                     '    ? forall x R:\n'
                                     '        x = x\n'
                                     '    7 = 8\n',
                           'strict': True,
                           'success': False},
 'canonical-final': {'strict': True,
                     'success': False,
                     'path': 'examples/test_statements/negative/def_strategy_stmt/false-strategy-body.lit'},
 'canonical-nested': {'strict': True,
                      'success': False,
                      'path': 'examples/test_statements/negative/def_strategy_stmt/false-nested-proof.lit'},
 'parse-control': {'strict': True,
                   'success': False,
                   'path': 'examples/test_statements/negative/def_strategy_stmt/strategy-must-be-universal.lit'},
 'public-tracer': {'strict': True,
                   'success': False,
                   'path': 'examples/test_statements/negative/def_strategy_stmt/retained-final-prefix.lit'},
 'scope-tracer': {'strict': True,
                  'success': False,
                  'path': 'examples/test_statements/negative/def_strategy_stmt/retained-inference-scopes.lit'}}
FAILED_STRATEGY_BOOK = {'01-predicate.lit': 'prop P(x R):\n    x = 0\n',
 '02-strategy.lit': 'strategy book_failed:\n'
                    '    ? forall x R:\n'
                    '        x = 0\n'
                    '        =>:\n'
                    '            x = x\n'
                    '            $definitions::P(x + 1)\n'
                    '            x + 0 = x\n'
                    '    have helper R = x\n'
                    '    helper = x\n'
                    '\n'
                    'have helper R = 1\n'
                    '\n'
                    'helper = 1\n'
                    '\n'
                    '$definitions::P(1)\n',
 'litex.config': '[export]\ndefinitions = "./01-predicate.lit"\nstrategies = "./02-strategy.lit"\n',
 'reading-titles.json': '{\n'
                        '  "kind": "reading_titles",\n'
                        '  "sources": {\n'
                        '    "01-predicate.lit": {\n'
                        '      "zh": "谓词定义",\n'
                        '      "en": "Predicate definition"\n'
                        '    },\n'
                        '    "02-strategy.lit": {\n'
                        '      "zh": "未完成的证明策略",\n'
                        '      "en": "An unfinished proof strategy"\n'
                        '    }\n'
                        '  }\n'
                        '}\n'}

FAILED_THEOREM_CONTEXT_CASES = {'public-compound-tracer': {'path': 'examples/test_statements/negative/def_thm_stmt/retained-compound-goal.lit', 'strict': True, 'success': False},
 'forall-final-prefix': {'source': 'prop P(x R):\n'
                                   '    x = 0\n'
                                   'thm fail_final:\n'
                                   '    ? forall x R:\n'
                                   '        x = 0\n'
                                   '        =>:\n'
                                   '            x = x\n'
                                   '            $P(x + 1)\n'
                                   '            x + 0 = x\n'
                                   '    have helper R = x\n'
                                   '    helper = x\n',
                         'strict': True,
                         'success': False},
 'same-name-repair': {'source': 'prop P(x R):\n'
                                '    x = 0\n'
                                'thm fail_final:\n'
                                '    ? forall x R:\n'
                                '        x = 0\n'
                                '        =>:\n'
                                '            $P(x)\n'
                                '    by def $P(x)\n',
                      'strict': True,
                      'success': True},
 'nonforall-final-failure': {'source': 'prop P(x R):\n'
                                       '    x = 0\n'
                                       'thm direct_failed:\n'
                                       '    ? $P(1)\n'
                                       '    have direct_helper R = 0\n'
                                       '    direct_helper = 0\n',
                             'strict': True,
                             'success': False},
 'nonforall-body-failure': {'source': 'prop P(x R):\n'
                                      '    x = 0\n'
                                      'thm direct_body_failed:\n'
                                      '    ? 1 = 1\n'
                                      '    have direct_local R = 1\n'
                                      '    direct_local = 1\n'
                                      '    1 = 2\n'
                                      '    have unreachable R = 3\n',
                            'strict': True,
                            'success': False},
 'forall-nested-body-failure': {'source': 'prop P(x R):\n'
                                          '    x = 0\n'
                                          'thm nested_failed:\n'
                                          '    ? forall x R:\n'
                                          '        x = 0\n'
                                          '        =>:\n'
                                          '            $P(x)\n'
                                          '    have nested_helper R = x\n'
                                          '    nested_helper = x\n'
                                          '    claim:\n'
                                          '        ? x = 1\n'
                                          '        x = 1\n'
                                          '    have unreachable R = x\n',
                                'strict': True,
                                'success': False},
 'inferred-premise-final-failure': {'source': 'prop P(x R):\n'
                                              '    x = 0\n'
                                              'prop nonnegative(x R):\n'
                                              '    x >= 0\n'
                                              'thm nonnegative_is_negative:\n'
                                              '    ? forall x R:\n'
                                              '        $nonnegative(x)\n'
                                              '        =>:\n'
                                              '            x >= 0\n'
                                              '            x < 0\n'
                                              '    have guarded R = x\n',
                                    'strict': True,
                                    'success': False},
 'goal-formation-before-entry': {'source': 'prop P(x R):\n'
                                           '    x = 0\n'
                                           'thm undefined_goal:\n'
                                           '    ? forall x R:\n'
                                           '        1 / 0 = x\n'
                                           '    have not_entered R = 0\n',
                                 'strict': True,
                                 'success': False},
 'nonforall-compound-final-failure': {'source': 'prop P(x R):\n'
                                                '    x = 0\n'
                                                'thm compound_failed:\n'
                                                '    ? 1 = 1 and 1 = 2\n'
                                                '    have compound_helper R = 1\n',
                                      'strict': True,
                                      'success': False},
 'nonforall-chain-final-failure': {'source': 'prop P(x R):\n'
                                             '    x = 0\n'
                                             'thm chain_failed:\n'
                                             '    ? 1 = 1 = 2\n'
                                             '    have chain_helper R = 1\n',
                                   'strict': True,
                                   'success': False},
 'nonforall-repair': {'source': 'prop P(x R):\n'
                                '    x = 0\n'
                                'thm direct_failed:\n'
                                '    ? $P(0)\n'
                                '    by def $P(0)\n',
                      'strict': True,
                      'success': True},
 'parameter-empty-carrier-positive': {'source': 'prop P(x R):\n'
                                                '    x = 0\n'
                                                'thm vacuous:\n'
                                                '    ? forall x {}:\n'
                                                '        x = 0\n',
                                      'strict': True,
                                      'success': False},
 'empty-domain-repair': {'source': 'prop P(x R):\n'
                                   '    x = 0\n'
                                   'thm vacuous:\n'
                                   '    ? forall x {}:\n'
                                   '        x = x\n',
                         'strict': True,
                         'success': True},
 'same-name-after-body-failure': {'source': 'prop P(x R):\n'
                                            '    x = 0\n'
                                            'thm direct_body_failed:\n'
                                            '    ? 1 = 1\n'
                                            '    have direct_local R = 1\n'
                                            '    direct_local = 1\n',
                                  'strict': True,
                                  'success': True},
 'canonical-universal': {'source': '# Expected rejection: false-universal-theorem\n'
                                   '# Owner: DefThmStmt\n'
                                   '\n'
                                   'thm bad:\n'
                                   '    ? forall x R:\n'
                                   '        x = 0\n',
                         'strict': True,
                         'success': False},
 'canonical-direct': {'source': '# Expected rejection: false-bodyless-theorem\n'
                                '# Owner: DefThmStmt\n'
                                '\n'
                                'thm bad:\n'
                                '    ? 1 = 2\n',
                      'strict': True,
                      'success': False},
 'unsupported-iff': {'source': '# Root quantified iff is outside the named-theorem goal contract.\n'
                               '# Both directions are true; unsupported input must still be '
                               'rejected.\n'
                               'thm equality_iff:\n'
                               '    ? forall x, y R:\n'
                               '        =>:\n'
                               '            x = y\n'
                               '        <=>:\n'
                               '            y = x\n',
                     'strict': True,
                     'success': False},
 'public-tracer': {'path': 'examples/test_statements/negative/def_thm_stmt/retained-final-prefix.lit',
                   'strict': True,
                   'success': False}}

FAILED_THEOREM_BOOK = {'reading-titles.json': '{\n'
                        '  "kind": "reading_titles",\n'
                        '  "sources": {\n'
                        '    "01-predicate.lit": {\n'
                        '      "zh": "谓词定义",\n'
                        '      "en": "Predicate definition"\n'
                        '    },\n'
                        '    "02-theorem.lit": {\n'
                        '      "zh": "定理中的局部证明",\n'
                        '      "en": "Local proof in a theorem"\n'
                        '    }\n'
                        '  }\n'
                        '}\n',
 '01-predicate.lit': 'prop P(x R):\n    x = 0\n',
 'README.md': '# Rejected theorem proof context\n'
              '\n'
              'Task-owned strict acceptance project. The first file declares P(x) iff x=0; the '
              'second checks deliberately false theorem conclusions, rollback and real definition '
              'citations. It is not a published mathematics module.\n',
 '02-theorem.lit': 'thm book_failed:\n'
                   '    ? forall x R:\n'
                   '        x = 0\n'
                   '        =>:\n'
                   '            x = x\n'
                   '            $definitions::P(x + 1)\n'
                   '            x + 0 = x\n'
                   '    have helper R = x\n'
                   '    helper = x\n'
                   '\n'
                   'have helper R = 1\n'
                   '\n'
                   'by def $definitions::P(0)\n'
                   '\n'
                   '$definitions::P(1)\n',
 'litex.config': '[export]\ndefinitions = "./01-predicate.lit"\ntheorems = "./02-theorem.lit"\n',
 'math_collections.md': '# Mathematical interfaces\n'
                        '\n'
                        '`P(x R)` means `x=0`. The attempted theorem assumes x=0 and must not '
                        'publish P(x+1). Outer helper values and P(0) are independent checked '
                        'controls. No trust or axiom is used.\n'}

PENDING_GOAL_CASES = {'theorem-direct-body': {'source': 'prop P(x R):\n'
                                   '    x = 0\n'
                                   'thm direct_body_failed:\n'
                                   '    ? 1 = 1\n'
                                   '    have direct_local R = 1\n'
                                   '    direct_local = 1\n'
                                   '    1 = 2\n'
                                   '    have unreachable R = 3\n',
                         'success': False,
                         'strict': True,
                         'pending': True,
                         'family': 'theorem'},
 'theorem-nested-body': {'source': 'prop P(x R):\n'
                                   '    x = 0\n'
                                   'thm nested_failed:\n'
                                   '    ? forall x R:\n'
                                   '        x = 0\n'
                                   '        =>:\n'
                                   '            $P(x)\n'
                                   '    have nested_helper R = x\n'
                                   '    nested_helper = x\n'
                                   '    claim:\n'
                                   '        ? x = 1\n'
                                   '        x = 1\n'
                                   '    have unreachable R = x\n',
                         'success': False,
                         'strict': True,
                         'pending': True,
                         'family': 'theorem'},
 'theorem-later-goal': {'source': 'prop P(x R):\n'
                                  '    x = 0\n'
                                  'thm fail_final:\n'
                                  '    ? forall x R:\n'
                                  '        x = 0\n'
                                  '        =>:\n'
                                  '            x = x\n'
                                  '            $P(x + 1)\n'
                                  '            x + 0 = x\n'
                                  '    have helper R = x\n'
                                  '    helper = x\n',
                        'success': False,
                        'strict': True,
                        'pending': True,
                        'family': 'theorem'},
 'theorem-final-last': {'source': 'prop P(x R):\n'
                                  '    x = 0\n'
                                  'prop nonnegative(x R):\n'
                                  '    x >= 0\n'
                                  'thm nonnegative_is_negative:\n'
                                  '    ? forall x R:\n'
                                  '        $nonnegative(x)\n'
                                  '        =>:\n'
                                  '            x >= 0\n'
                                  '            x < 0\n'
                                  '    have guarded R = x\n',
                        'success': False,
                        'strict': True,
                        'pending': False,
                        'family': 'theorem'},
 'theorem-compound-checked': {'source': 'prop P(x R):\n'
                                        '    x = 0\n'
                                        'thm compound_failed:\n'
                                        '    ? 1 = 1 and 1 = 2\n'
                                        '    have compound_helper R = 1\n',
                              'success': False,
                              'strict': True,
                              'pending': False,
                              'family': 'theorem'},
 'theorem-goal-wd': {'source': 'prop P(x R):\n'
                               '    x = 0\n'
                               'thm undefined_goal:\n'
                               '    ? forall x R:\n'
                               '        1 / 0 = x\n'
                               '    have not_entered R = 0\n',
                     'success': False,
                     'strict': True,
                     'pending': False,
                     'family': 'theorem'},
 'theorem-success': {'source': 'prop P(x R):\n'
                               '    x = 0\n'
                               'thm direct_body_failed:\n'
                               '    ? 1 = 1\n'
                               '    have direct_local R = 1\n'
                               '    direct_local = 1\n',
                     'success': True,
                     'strict': True,
                     'pending': False,
                     'family': 'theorem'},
 'theorem-unsupported': {'source': '# Root quantified iff is outside the named-theorem goal '
                                   'contract.\n'
                                   '# Both directions are true; unsupported input must still be '
                                   'rejected.\n'
                                   'thm equality_iff:\n'
                                   '    ? forall x, y R:\n'
                                   '        =>:\n'
                                   '            x = y\n'
                                   '        <=>:\n'
                                   '            y = x\n',
                         'success': False,
                         'strict': True,
                         'pending': False,
                         'family': 'theorem'},
 'strategy-body': {'source': 'prop P(x R):\n'
                             '    x = 0\n'
                             'strategy fail_body:\n'
                             '    ? forall x R:\n'
                             '        x = 0\n'
                             '        =>:\n'
                             '            $P(x)\n'
                             '    have local_helper R = x\n'
                             '    local_helper = 0\n'
                             '    7 = 8\n'
                             '    have unchecked R = 9\n',
                   'success': False,
                   'strict': True,
                   'pending': True,
                   'family': 'strategy'},
 'strategy-later-goal': {'source': 'prop P(x R):\n'
                                   '    x = 0\n'
                                   'strategy fail_final:\n'
                                   '    ? forall x R:\n'
                                   '        x = 0\n'
                                   '        =>:\n'
                                   '            x = x\n'
                                   '            $P(x + 1)\n'
                                   '            x + 0 = x\n'
                                   '    have helper R = x\n'
                                   '    helper = x\n',
                         'success': False,
                         'strict': True,
                         'pending': True,
                         'family': 'strategy'},
 'strategy-wd': {'source': 'prop P(x R):\n'
                           '    x = 0\n'
                           'strategy illformed:\n'
                           '    ? forall x R:\n'
                           '        1 / 0 = 0\n'
                           '    1 = 1\n',
                 'success': False,
                 'strict': True,
                 'pending': False,
                 'family': 'strategy'},
 'strategy-success': {'source': 'prop P(x R):\n'
                                '    x = 0\n'
                                'strategy fail_final:\n'
                                '    ? forall x R:\n'
                                '        x = 0\n'
                                '        =>:\n'
                                '            $P(x)\n'
                                '    by def $P(x)\n'
                                '$P(0)\n',
                      'success': True,
                      'strict': True,
                      'pending': False,
                      'family': 'strategy'},
 'claim-direct-body': {'source': 'claim:\n'
                                 '    ? 1 = 1\n'
                                 '    have claim_inner R = 2\n'
                                 '    claim_inner = 2\n'
                                 '    2 = 3\n'
                                 '    4 = 4\n',
                       'success': False,
                       'strict': True,
                       'pending': True,
                       'family': 'claim'},
 'claim-quantified-body': {'source': 'claim:\n'
                                     '    ? forall x R:\n'
                                     '        x > 0\n'
                                     '        =>:\n'
                                     '            x >= 0\n'
                                     '    x > 0\n'
                                     '    2 = 3\n'
                                     '    x >= 0\n',
                           'success': False,
                           'strict': True,
                           'pending': True,
                           'family': 'claim'},
 'claim-nested-body': {'source': 'claim:\n'
                                 '    ? forall outer_x R:\n'
                                 '        outer_x > 0\n'
                                 '        =>:\n'
                                 '            outer_x >= 0\n'
                                 '    claim:\n'
                                 '        ? forall inner_y R:\n'
                                 '            inner_y < 0\n'
                                 '            =>:\n'
                                 '                inner_y <= 0\n'
                                 '        outer_x > 0\n'
                                 '        inner_y < 0\n'
                                 '        2 = 3\n'
                                 '    outer_x >= 0\n',
                       'success': False,
                       'strict': True,
                       'pending': True,
                       'family': 'claim'},
 'claim-final-last': {'source': 'claim:\n'
                                '    ? forall t R:\n'
                                '        t = t\n'
                                '        t >= 0\n'
                                '    t = t\n',
                      'success': False,
                      'strict': True,
                      'pending': False,
                      'family': 'claim'},
 'claim-wd': {'source': 'claim:\n    ? 1 / 0 = 0\n    1 = 1\n',
              'success': False,
              'strict': True,
              'pending': False,
              'family': 'claim'},
 'claim-success': {'source': 'claim:\n'
                             '    ? 1 = 1\n'
                             '    have success_inner R = 2\n'
                             '    success_inner = 2\n',
                   'success': True,
                   'strict': True,
                   'pending': False,
                   'family': 'claim'},
 'contra-assumption': {'source': '# Expected rejection: retained-assumption-body\n'
                                 '# Before: this exact input discarded the reversed assumption and '
                                 'detached scope.\n'
                                 '# by contra:\n'
                                 '#     ? not $narrow(2)\n'
                                 '#     2 > 0\n'
                                 '#     7 = 8\n'
                                 '#     have unexecuted R = 9\n'
                                 '#     impossible 2 < 1\n'
                                 '# Now: the assumption narrow(2), its actual consequences and the '
                                 'first checked\n'
                                 '# body statement remain local; the failed equality stops the '
                                 'remaining steps.\n'
                                 'prop narrow(x R):\n'
                                 '    x > 0\n'
                                 '    x < 1\n'
                                 '\n'
                                 'by contra:\n'
                                 '    ? not $narrow(2)\n'
                                 '    2 > 0\n'
                                 '    7 = 8\n'
                                 '    have unexecuted R = 9\n'
                                 '    impossible 2 < 1\n'
                                 '# Evidence: target/release/litex -strict -lang en -f '
                                 'examples/test_statements/negative/by_contra_stmt/retained-assumption-body.lit\n'
                                 '# Expected: exit 1, proof_body at 7 = 8 (step_index 1), no outer '
                                 'target.\n'
                                 '# Producer: tests/reading_failed_contradictions.rs; consumer: '
                                 'failed-contra-context.cjs.\n',
                       'success': False,
                       'strict': True,
                       'pending': False,
                       'family': 'control'},
 'case-assumption': {'source': "# Before: the same case's assumption and successful prefix were "
                               'discarded.\n'
                               '#     case 0 = 0:\n'
                               '#         3 = 3\n'
                               '#         2 = 3\n'
                               '# Reading now retains that local assumption, accepted prefix and '
                               'failure.\n'
                               '# Expected: strict CLI exit 1, proof_body, branch 0, step 1; no '
                               'outer conclusion.\n'
                               '# Run: target/release/litex -strict -lang en -f '
                               'examples/test_statements/negative/by_cases_stmt/failed-body-context.lit\n'
                               'by cases:\n'
                               '    ? 0 = 0\n'
                               '    case 0 = 0:\n'
                               '        3 = 3\n'
                               '        2 = 3\n'
                               '    case 0 != 0:\n'
                               '        0 = 0\n',
                     'success': False,
                     'strict': True,
                     'pending': False,
                     'family': 'control'},
 'claim-multiple-pending': {'source': 'prop P(x R):\n'
                                      '    x = 0\n'
                                      'claim:\n'
                                      '    ? forall x R:\n'
                                      '        x = 0\n'
                                      '        =>:\n'
                                      '            x = x\n'
                                      '            $P(x + 1)\n'
                                      '            x + 0 = x\n'
                                      '            x * 1 = x\n'
                                      '    have helper R = x\n'
                                      '    helper = x\n',
                            'strict': True,
                            'success': False,
                            'pending': True,
                            'family': 'claim'},
 'public-tracer': {'strict': True,
                   'success': False,
                   'pending': True,
                   'family': 'theorem',
                   'path': 'examples/test_statements/negative/def_thm_stmt/pending-goal-after-body-failure.lit'},
 'repaired-tracer': {'source': 'thm body_stops_before_goal:\n'
                               '    ? 1 = 1\n'
                               '    have helper R = 1\n'
                               '    helper = 1\n',
                     'strict': True,
                     'success': True,
                     'pending': False,
                     'family': 'theorem'}}

REGISTRATION_FAILURE_CASES = {'reflexive-failed': {'path': 'examples/test_statements/negative/register_reflexive_prop_stmt/false-shaped-law.lit',
                      'success': False,
                      'strict': True},
 'reflexive-positive': {'path': 'examples/test_statements/register_reflexive_prop_stmt.lit',
                        'success': True,
                        'strict': True},
 'reflexive-wrong-law-shape': {'path': 'examples/test_statements/negative/register_reflexive_prop_stmt/wrong-law-shape.lit',
                               'success': False,
                               'strict': True},
 'reflexive-reflexive-carrier-R': {'path': 'examples/test_statements/negative/register_reflexive_prop_stmt/reflexive-carrier-R.lit',
                                   'success': False,
                                   'strict': True},
 'reflexive-extra-registration-proof': {'path': 'examples/test_statements/negative/register_reflexive_prop_stmt/extra-registration-proof.lit',
                                        'success': False,
                                        'strict': True},
 'symmetric-failed': {'path': 'examples/test_statements/negative/register_symmetric_prop_stmt/false-shaped-law.lit',
                      'success': False,
                      'strict': True},
 'symmetric-positive': {'path': 'examples/test_statements/register_symmetric_prop_stmt.lit',
                        'success': True,
                        'strict': True},
 'symmetric-wrong-law-shape': {'path': 'examples/test_statements/negative/register_symmetric_prop_stmt/wrong-law-shape.lit',
                               'success': False,
                               'strict': True},
 'symmetric-symmetric-carrier-R': {'path': 'examples/test_statements/negative/register_symmetric_prop_stmt/symmetric-carrier-R.lit',
                                   'success': False,
                                   'strict': True},
 'symmetric-extra-registration-proof': {'path': 'examples/test_statements/negative/register_symmetric_prop_stmt/extra-registration-proof.lit',
                                        'success': False,
                                        'strict': True},
 'transitive-failed': {'path': 'examples/test_statements/negative/register_transitive_prop_stmt/false-shaped-law.lit',
                       'success': False,
                       'strict': True},
 'transitive-positive': {'path': 'examples/test_statements/register_transitive_prop_stmt.lit',
                         'success': True,
                         'strict': True},
 'transitive-wrong-law-shape': {'path': 'examples/test_statements/negative/register_transitive_prop_stmt/wrong-law-shape.lit',
                                'success': False,
                                'strict': True},
 'transitive-transitive-carrier-R': {'path': 'examples/test_statements/negative/register_transitive_prop_stmt/transitive-carrier-R.lit',
                                     'success': False,
                                     'strict': True},
 'transitive-extra-registration-proof': {'path': 'examples/test_statements/negative/register_transitive_prop_stmt/extra-registration-proof.lit',
                                         'success': False,
                                         'strict': True},
 'nested-failed': {'source': 'prop different(x, y set):\n'
                             '    x != y\n'
                             'claim:\n'
                             '    ? 1 = 1\n'
                             '    # 局部检查，不发布这里采用的条件。\n'
                             '    register transitive:\n'
                             '        ? forall x, y, z set:\n'
                             '            $different(x, y)\n'
                             '            $different(y, z)\n'
                             '            =>:\n'
                             '                $different(x, z)\n',
                   'success': False,
                   'strict': True},
 'cyclic-failed': {'source': 'prop ordered_three(x, y, z set):\n'
                             '    x = {}\n'
                             '    y = {1}\n'
                             '    z = {2}\n'
                             'register symmetric:\n'
                             '    ? forall x, y, z set:\n'
                             '        $ordered_three(x, y, z)\n'
                             '        =>:\n'
                             '            $ordered_three(y, z, x)\n',
                   'success': False,
                   'strict': True},
 'domain-requirement': {'source': 'prop real_same(x, y R):\n'
                       '    x = y\n'
                       'register reflexive:\n'
                       '    ? forall x set:\n'
                       '        $real_same(x, x)\n',
             'success': False,
             'strict': True},
 'wrong-arity': {'source': 'prop ordered_three(x, y, z set):\n'
                           '    x = {}\n'
                           '    y = {1}\n'
                           '    z = {2}\n'
                           'register symmetric:\n'
                           '    ? forall x, y set:\n'
                           '        $ordered_three(x, y)\n'
                           '        =>:\n'
                           '            $ordered_three(y, x)\n',
                 'success': False,
                 'strict': True},
 'public-tracer': {'path': 'examples/test_statements/negative/register_transitive_prop_stmt/retained-law-context.lit',
                   'success': False,
                   'strict': True},
 'canonical-routes': {'source': 'have source_anchor R = 0\n'
                                'prop same(x, y set):\n'
                                '    x = y\n'
                                'prop below(x, y set):\n'
                                '    x $in R\n'
                                '    y $in R\n'
                                '    x <= y\n'
                                'claim:\n'
                                '    ? forall x, y, z set:\n'
                                '        $below(x, y)\n'
                                '        $below(y, z)\n'
                                '        =>:\n'
                                '            $below(x, z)\n'
                                '    x <= y <= z\n'
                                '    by def $below(x, z)\n'
                                'register transitive:\n'
                                '    ? forall x, y, z set:\n'
                                '        $below(x, y)\n'
                                '        $below(y, z)\n'
                                '        =>:\n'
                                '            $below(x, z)\n'
                                'forall a, b, c R:\n'
                                '    $below(a, b)\n'
                                '    $below(b, c)\n'
                                '    =>:\n'
                                '        $below(a, c)\n'
                                'register symmetric:\n'
                                '    ? forall x, y set:\n'
                                '        $same(x, y)\n'
                                '        =>:\n'
                                '            $same(y, x)\n'
                                'forall a, b set:\n'
                                '    $same(a, b)\n'
                                '    =>:\n'
                                '        $same(b, a)\n'
                                'register reflexive:\n'
                                '    ? forall x set:\n'
                                '        $same(x, x)\n'
                                'forall a set:\n'
                                '    $same(a, a)\n',
                      'success': True,
                      'strict': True}}

REGISTRATION_FAILURE_BOOK = {'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\nlaws = "./02-laws.lit"\n',
 'reading-titles.json': '{"kind": "reading_titles", "sources": {"definitions": {"zh": "关系定义", "en": "A '
                        'relation"}, "laws": {"zh": "检查关系的性质", "en": "Checking relation properties"}}}',
 '01-definitions.lit': 'prop different(x, y set):\n    x != y\n',
 '02-laws.lit': 'register transitive:\n'
                '    ? forall x, y, z set:\n'
                '        $definitions::different(x, y)\n'
                '        $definitions::different(y, z)\n'
                '        =>:\n'
                '            $definitions::different(x, z)\n'}

TRANSITIVITY_APPLICATION_CASES = {'registered': {'source': 'prop below(x, y set):\n'
                          '    x $in R\n'
                          '    y $in R\n'
                          '    x <= y\n'
                          'claim:\n'
                          '    ? forall x, y, z set:\n'
                          '        $below(x, y)\n'
                          '        $below(y, z)\n'
                          '        =>:\n'
                          '            $below(x, z)\n'
                          '    x <= y <= z\n'
                          '    by def $below(x, z)\n'
                          'register transitive:\n'
                          '    ? forall x, y, z set:\n'
                          '        $below(x, y)\n'
                          '        $below(y, z)\n'
                          '        =>:\n'
                          '            $below(x, z)\n'
                          'forall a, b, c R:\n'
                          '    $below(a, b)\n'
                          '    b <= c\n'
                          '    =>:\n'
                          '        $below(a, c)\n',
                'success': True,
                'strict': True},
 'multiple': {'source': 'prop below(x, y set):\n'
                        '    x $in R\n'
                        '    y $in R\n'
                        '    x <= y\n'
                        'claim:\n'
                        '    ? forall x, y, z set:\n'
                        '        $below(x, y)\n'
                        '        $below(y, z)\n'
                        '        =>:\n'
                        '            $below(x, z)\n'
                        '    x <= y <= z\n'
                        '    by def $below(x, z)\n'
                        'register transitive:\n'
                        '    ? forall x, y, z set:\n'
                        '        $below(x, y)\n'
                        '        $below(y, z)\n'
                        '        =>:\n'
                        '            $below(x, z)\n'
                        'forall a, b, c, d R:\n'
                        '    $below(a, b)\n'
                        '    b <= c\n'
                        '    b <= d\n'
                        '    =>:\n'
                        '        $below(a, c)\n'
                        '        $below(a, d)\n',
              'success': True,
              'strict': True},
 'missing-right': {'source': 'prop below(x, y set):\n'
                             '    x $in R\n'
                             '    y $in R\n'
                             '    x <= y\n'
                             'claim:\n'
                             '    ? forall x, y, z set:\n'
                             '        $below(x, y)\n'
                             '        $below(y, z)\n'
                             '        =>:\n'
                             '            $below(x, z)\n'
                             '    x <= y <= z\n'
                             '    by def $below(x, z)\n'
                             'register transitive:\n'
                             '    ? forall x, y, z set:\n'
                             '        $below(x, y)\n'
                             '        $below(y, z)\n'
                             '        =>:\n'
                             '            $below(x, z)\n'
                             'forall a, b, c R:\n'
                             '    $below(a, b)\n'
                             '    =>:\n'
                             '        $below(a, c)\n',
                   'success': False,
                   'strict': True},
 'local-prefix': {'source': 'prop below(x, y set):\n'
                            '    x $in R\n'
                            '    y $in R\n'
                            '    x <= y\n'
                            'claim:\n'
                            '    ? forall x, y, z set:\n'
                            '        $below(x, y)\n'
                            '        $below(y, z)\n'
                            '        =>:\n'
                            '            $below(x, z)\n'
                            '    x <= y <= z\n'
                            '    by def $below(x, z)\n'
                            'register transitive:\n'
                            '    ? forall x, y, z set:\n'
                            '        $below(x, y)\n'
                            '        $below(y, z)\n'
                            '        =>:\n'
                            '            $below(x, z)\n'
                            'thm unfinished_bound:\n'
                            '    ? forall a, b, c R:\n'
                            '        $below(a, b)\n'
                            '        b <= c\n'
                            '        =>:\n'
                            '            $below(a, c)\n'
                            '            a = c\n',
                  'success': False,
                  'strict': True},
 'without-registration': {'source': 'prop below(x, y set):\n'
                                    '    x $in R\n'
                                    '    y $in R\n'
                                    '    x <= y\n'
                                    'claim:\n'
                                    '    ? forall x, y, z set:\n'
                                    '        $below(x, y)\n'
                                    '        $below(y, z)\n'
                                    '        =>:\n'
                                    '            $below(x, z)\n'
                                    '    x <= y <= z\n'
                                    '    by def $below(x, z)\n'
                                    'forall a, b, c R:\n'
                                    '    $below(a, b)\n'
                                    '    b <= c\n'
                                    '    =>:\n'
                                    '        $below(a, c)\n',
                          'success': False,
                          'strict': True},
 'order-le': {'source': 'forall x R:\n    x <= 900\n    =>:\n        x <= 1070\n',
              'success': True,
              'strict': True},
 'order-lt': {'source': 'forall x R:\n    x < 900\n    =>:\n        x < 1070\n',
              'success': True,
              'strict': True},
 'order-ge': {'source': 'forall x R:\n    x >= 1260\n    =>:\n        x >= 1250\n',
              'success': True,
              'strict': True},
 'order-gt': {'source': 'forall x R:\n    x > 1260\n    =>:\n        x > 1250\n',
              'success': True,
              'strict': True},
 'closed-order': {'source': '1 <= 2\n', 'success': True, 'strict': True},
 'false-order': {'source': 'forall x R:\n    x <= 900\n    =>:\n        x <= 899\n',
                 'success': False,
                 'strict': True},
 'definition-control': {'source': 'have source_anchor R = 0\n'
                                  'prop same(x, y set):\n'
                                  '    x = y\n'
                                  'prop below(x, y set):\n'
                                  '    x $in R\n'
                                  '    y $in R\n'
                                  '    x <= y\n'
                                  'claim:\n'
                                  '    ? forall x, y, z set:\n'
                                  '        $below(x, y)\n'
                                  '        $below(y, z)\n'
                                  '        =>:\n'
                                  '            $below(x, z)\n'
                                  '    x <= y <= z\n'
                                  '    by def $below(x, z)\n'
                                  'register transitive:\n'
                                  '    ? forall x, y, z set:\n'
                                  '        $below(x, y)\n'
                                  '        $below(y, z)\n'
                                  '        =>:\n'
                                  '            $below(x, z)\n'
                                  'forall a, b, c R:\n'
                                  '    $below(a, b)\n'
                                  '    $below(b, c)\n'
                                  '    =>:\n'
                                  '        $below(a, c)\n'
                                  'register symmetric:\n'
                                  '    ? forall x, y set:\n'
                                  '        $same(x, y)\n'
                                  '        =>:\n'
                                  '            $same(y, x)\n'
                                  'forall a, b set:\n'
                                  '    $same(a, b)\n'
                                  '    =>:\n'
                                  '        $same(b, a)\n'
                                  'register reflexive:\n'
                                  '    ? forall x set:\n'
                                  '        $same(x, x)\n'
                                  'forall a set:\n'
                                  '    $same(a, a)\n',
                        'success': True,
                        'strict': True},
 'public-tracer': {'success': True,
                   'strict': True,
                   'path': 'examples/proof_nodes/atomic/by_known_rewrite/registered_transitivity_application.lit'},
 'global-left': {'source': 'prop below(x, y set):\n'
                           '    x $in R\n'
                           '    y $in R\n'
                           '    x <= y\n'
                           'claim:\n'
                           '    ? forall x, y, z set:\n'
                           '        $below(x, y)\n'
                           '        $below(y, z)\n'
                           '        =>:\n'
                           '            $below(x, z)\n'
                           '    x <= y <= z\n'
                           '    by def $below(x, z)\n'
                           'register transitive:\n'
                           '    ? forall x, y, z set:\n'
                           '        $below(x, y)\n'
                           '        $below(y, z)\n'
                           '        =>:\n'
                           '            $below(x, z)\n'
                           'have fixed_left R = 0\n'
                           'have middle R = 1\n'
                           'by def $below(fixed_left, middle)\n'
                           'forall c R:\n'
                           '    middle <= c\n'
                           '    =>:\n'
                           '        $below(fixed_left, c)\n',
                 'success': True,
                 'strict': True},
 'inferred-left': {'source': 'forall x, y R:\n    x <= y <= 900\n    =>:\n        x <= 1070\n',
                   'success': True,
                   'strict': True},
 'mixed-order-boundary': {'source': 'forall x R:\n    x < 900\n    =>:\n        x <= 1070\n',
                          'success': False,
                          'strict': True}}

TRANSITIVITY_APPLICATION_BOOK = {'litex.config': '[export]\ndefinitions = "./01-relation.lit"\napplications = "./02-applications.lit"\n',
 'reading-titles.json': '{"kind": "reading_titles", "sources": {"definitions": {"zh": "关系与传递性", "en": "A '
                        'transitive relation"}, "applications": {"zh": "应用传递性", "en": "Applying '
                        'transitivity"}}}',
 '01-relation.lit': 'prop below(x, y set):\n    x $in R\n    y $in R\n    x <= y\n',
 '02-applications.lit': 'claim:\n'
                        '    ? forall x, y, z set:\n'
                        '        $definitions::below(x, y)\n'
                        '        $definitions::below(y, z)\n'
                        '        =>:\n'
                        '            $definitions::below(x, z)\n'
                        '    x <= y <= z\n'
                        '    by def $definitions::below(x, z)\n'
                        'register transitive:\n'
                        '    ? forall x, y, z set:\n'
                        '        $definitions::below(x, y)\n'
                        '        $definitions::below(y, z)\n'
                        '        =>:\n'
                        '            $definitions::below(x, z)\n'
                        'forall a, b, c R:\n'
                        '    $definitions::below(a, b)\n'
                        '    b <= c\n'
                        '    =>:\n'
                        '        $definitions::below(a, c)\n'}

TUPLE_COORDINATE_CASES = {
    'direct': ('have p cart(R, R) = (1, 2)\np(1) + p(2) = 3\n', True),
    'symbolic': ('forall a, b R, q cart(R, R):\n    q = (a, b)\n    =>:\n        q(1) = a\n        q(2) = b\n', True),
    'reversed': ('forall a, b R, q cart(R, R):\n    (a, b) = q\n    =>:\n        q(1) = a\n        q(2) = b\n', True),
    'conjunction': ('forall q cart(R, R):\n    q = (1, 2) and 1 = 1\n    =>:\n        q(1) = 1\n        q(2) = 2\n', True),
    'nested-boundary': ('let pair = ((1, 2), 3)\n', True),
    'nested-step': ('let pair = ((1, 2), 3)\npair(1) = (1, 2)\n', True),
    'alias-boundary': ('have p cart(R, R) = (1, 2)\nlet alias = p\n', True),
    'singleton': ('let singleton = (7,)\n', True),
    'empty': ('let empty = tuple()\n', True),
    'wrong-coordinate': ('have p cart(R, R) = (1, 2)\np(1) = 2\n', False),
    'index-zero': ('have p cart(R, R) = (1, 2)\np(0) = 0\n', False),
    'index-outside': ('have p cart(R, R) = (1, 2)\np(3) = 0\n', False),
    'failed-scope': ('claim:\n    ? 1 = 2\n    have doomed cart(R, R) = (1, 2)\n', False),
}
TUPLE_COORDINATE_BOOK = {
    '01-points.lit': 'have point cart(R, R) = (1, 2)\n',
    '02-coordinates.lit': 'release obj def points::point\npoints::point(1) + points::point(2) = 3\n',
    'litex.config': '[export]\npoints = "./01-points.lit"\ncoordinates = "./02-coordinates.lit"\n',
}

NUMERIC_REWRITE_CASES = {'numbers': {'source': '# Node: equal.ByBuiltinRewrite.ClosedNumericEqualSubstitution\n'
                       '# Run: litex -f '
                       'examples/proof_nodes/equal/by_builtin_rewrite/closed_numeric_equal_substitution.lit\n'
                       '\n'
                       'have a R = 10\n'
                       'have b R = 20\n'
                       'a + b = 30\n',
             'success': True},
 'tuple': {'source': 'have p cart(R, R) = (1, 2)\np(1) + p(2) = 3\n', 'success': True},
 'both-sides': {'source': 'have numeric_left R = 10\n'
                          '\n'
                          'have numeric_right R = 20\n'
                          '\n'
                          'numeric_left + 1 = numeric_right - 9\n'
                          '\n',
                'success': True},
 'reversed-source': {'source': 'forall numeric_t R:\n'
                               '    2 = numeric_t\n'
                               '    =>:\n'
                               '        numeric_t + 1 = 3\n'
                               '\n',
                     'success': True},
 'chain': {'source': 'have numeric_left R = 10\n\nnumeric_left + 1 = 11 = numeric_left + 1\n\n',
           'success': True},
 'failed-local': {'source': 'thm stopped_numeric:\n'
                            '    ? 1 = 2\n'
                            '    have numeric_hidden R = 10\n'
                            '    numeric_hidden + 1 = 11\n'
                            '\n',
                  'success': False},
 'missing-value': {'source': 'have numeric_free R\n\nnumeric_free + 1 = 11\n\n', 'success': False},
 'wrong-result': {'source': 'have numeric_left R = 10\n\nnumeric_left + 1 = 12\n\n', 'success': False},
 'undefined-division': {'source': 'have numeric_left R = 10\n\n1 / (numeric_left - 10) = 0\n\n',
                        'success': False},
 'local': {'source': 'claim:\n'
                     '    ? forall numeric_u R:\n'
                     '        numeric_u = 10\n'
                     '        =>:\n'
                     '            numeric_u + 1 = 11\n'
                     '    numeric_u + 1 = 11\n'
                     '\n',
           'success': True},
 'congruence-control': {'source': 'forall numeric_u, numeric_x R:\n'
                                  '    numeric_u = 1\n'
                                  '    =>:\n'
                                  '        numeric_u + numeric_x = 1 + numeric_x\n'
                                  '\n',
                        'success': True},
 'whole-subterm': {'source': 'have numeric_angle R = 0\n'
                             '\n'
                             'cos(numeric_angle) = cos(0) = 1\n'
                             '\n'
                             'cos(numeric_angle) + 2 = 3\n'
                             '\n',
                   'success': True},
 'calculation-control': {'source': '1 + 2 = 3\n\n', 'success': True},
 'arithmetic-ops': {'source': '# Node: equal.ByBuiltinRewrite.ClosedNumericEqualSubstitution '
                              '(arithmetic ops)\n'
                              '# Store / rewrite when the closed representative uses abs / min / max / '
                              'floor / sign.\n'
                              '# Run: litex -f '
                              'examples/proof_nodes/equal/by_builtin_rewrite/closed_numeric_equal_substitution_arithmetic_ops.lit\n'
                              '\n'
                              'have a R = |-3|\n'
                              'a = 3\n'
                              '\n'
                              'have b R = min(1, 2)\n'
                              'b + 1 = 2\n'
                              '\n'
                              'have c R = max(floor(2.5), sign(-1))\n'
                              'c = 2\n',
                    'success': True},
 'object-definition-control': {'source': 'have fn reciprocal(x R: x != 0) R = 1 / x\n'
                                         'reciprocal(2) = 1 / 2\n',
                               'success': True},
 'theorem-control': {'source': '# Stmt: By.ByThmStmt → exec_by_thm_stmt\n'
                               '# Run: litex -f examples/stmt_nodes/by/by_thm.lit\n'
                               '\n'
                               'thm zero_sides:\n'
                               '    ? forall x R:\n'
                               '        x + 0 = x\n'
                               '        0 + x = x\n'
                               '    x + 0 = x\n'
                               '    0 + x = x\n'
                               '\n'
                               'by thm zero_sides(2) => 2 + 0 = 2\n',
                     'success': True}}

UNEXECUTED_LOOP_CASES = {'enum-empty': {'source': 'by enumerate finite_set:\n'
                          '    ? forall x {}:\n'
                          '        0 = x = 1\n'
                          '    0 = x = 1\n',
                'success': True},
 'range-empty': {'source': 'by for:\n'
                           '    ? forall n range(2, 2):\n'
                           '        2 % n != 0\n'
                           '    2 % n != 0\n',
                 'success': True},
 'nested-body': {'source': 'by enumerate finite_set:\n'
                           '    ? forall unused {}:\n'
                           '        unused = unused\n'
                           '    have never_object R = 1 / 0\n'
                           '    prop never_predicate(y R):\n'
                           '        y >= 0\n'
                           '    have fn never_function(y R) R = y + 1\n'
                           '    claim:\n'
                           '        ? 1 = 2\n'
                           '        1 = 2\n'
                           '    by for:\n'
                           '        ? forall k range(0, 1):\n'
                           '            k = k\n'
                           '        1 = 2\n',
                 'success': True},
 'all-skipped': {'source': 'by enumerate finite_set:\n'
                           '    ? forall skipped_n {0, 1}:\n'
                           '        skipped_n < 0\n'
                           '        =>:\n'
                           '            skipped_n = 2\n'
                           '    1 = 2\n',
                 'success': True},
 'range-all-skipped': {'source': 'by for:\n'
                                 '    ? forall skipped_k range(0, 2):\n'
                                 '        skipped_k < 0\n'
                                 '        =>:\n'
                                 '            skipped_k = 9\n'
                                 '    1 = 2\n',
                       'success': True},
 'dependent-range-domain-boundary': {'source': 'by enumerate finite_set:\n'
                                               '    ? forall outer_n {1, 2}:\n'
                                               '        outer_n = outer_n\n'
                                               '    by for:\n'
                                               '        ? forall inner_k range(outer_n, outer_n):\n'
                                               '            1 = 2\n'
                                               '        1 = 2\n',
                                     'success': False},
 'repeated-empty': {'source': 'by enumerate finite_set:\n'
                              '    ? forall outer_n {1, 2}:\n'
                              '        outer_n = outer_n\n'
                              '    by for:\n'
                              '        ? forall inner_k range(2, 2):\n'
                              '            1 = 2\n'
                              '        1 = 2\n',
                    'success': True},
 'failed-outer': {'source': 'thm stopped_empty_loop:\n'
                            '    ? 1 = 2\n'
                            '    by enumerate finite_set:\n'
                            '        ? forall local_empty {}:\n'
                            '            1 = 2\n'
                            '        1 = 2\n',
                  'success': False},
 'later-empty-domain': {'source': 'by enumerate finite_set:\n'
                                  '    ? forall seed {1, 2}, missing {}:\n'
                                  '        seed = seed\n'
                                  '    1 / 0 = 0\n',
                        'success': True},
 'nonempty-failure': {'source': 'by enumerate finite_set:\n'
                                '    ? forall checked_n {0}:\n'
                                '        checked_n = checked_n\n'
                                '    1 = 2\n',
                      'success': False},
 'no-false-publication': {'source': '1 = 2\n', 'success': False},
 'ordinary-enumeration': {'source': '# Stmt: ByEnumerateFiniteSetStmt\n'
                                    '# AST: Stmt::By::ByEnumerateFiniteSetStmt\n'
                                    '# Run all scenarios and boundaries: python3 '
                                    'examples/test_statements/run.py --leaf '
                                    'ByEnumerateFiniteSetStmt\n'
                                    '\n'
                                    '# case: two-elements\n'
                                    'by enumerate finite_set:\n'
                                    '    ? forall x {1, 2}:\n'
                                    '        x > 0\n'
                                    '    x > 0\n'
                                    '\n'
                                    '# case: two-independent-domains\n'
                                    'by enumerate finite_set:\n'
                                    '    ? forall x {1, 2}, y {3, 4}:\n'
                                    '        x < y\n'
                                    '    x < y\n'
                                    '\n'
                                    '# case: singleton-and-empty\n'
                                    'by enumerate finite_set:\n'
                                    '    ? forall x {0}:\n'
                                    '        x = 0\n'
                                    '    x = 0\n'
                                    'by enumerate finite_set:\n'
                                    '    ? forall x {}:\n'
                                    '        x = x\n'
                                    '    x = x\n'
                                    '\n'
                                    '# case: constant-proof-body\n'
                                    'by enumerate finite_set:\n'
                                    '    ? forall n {0, 1}:\n'
                                    '        n = n\n'
                                    '    1 = 1\n'
                                    '\n'
                                    '# case: conditional-nested-binder-body\n'
                                    'prop enum_positive(x R):\n'
                                    '    x > 0\n'
                                    'by enumerate finite_set:\n'
                                    '    ? forall n {0, 1, 2}:\n'
                                    '        n > 0\n'
                                    '        =>:\n'
                                    '            n != 0\n'
                                    '    by def $enum_positive(n)\n',
                          'success': True},
 'ordinary-for': {'source': '# Stmt: By.ByForStmt → exec_by_for_stmt\n'
                            '# Run: litex -f examples/stmt_nodes/by/by_for.lit\n'
                            '\n'
                            'by for:\n'
                            '    ? forall n range(0, 3) => n < 3\n'
                            '    n < 3\n',
                  'success': True},
 'goal-wd-failure': {'source': 'by enumerate finite_set:\n'
                               '    ? forall w {}:\n'
                               '        1 / 0 = 0\n'
                               '    1 = 2\n',
                     'success': False},
 'failed-body-suffix': {'source': 'by enumerate finite_set:\n'
                                  '    ? forall n {0}:\n'
                                  '        n = n\n'
                                  '    1 = 2\n'
                                  '    1 = 1\n',
                        'success': False},
 'false-after-empty': {'source': 'by enumerate finite_set:\n'
                                 '    ? forall x {}:\n'
                                 '        0 = x = 1\n'
                                 '    0 = x = 1\n'
                                 '1 = 2\n',
                       'success': False},
 'unicode-source': {'source': '# 空集中的对象；this source checks byte positions.\n'
                              'by enumerate finite_set:\n'
                              '    ? forall x {}:\n'
                              '        0 = x = 1\n'
                              '    0 = x = 1\n',
                    'success': True}}

UNEXECUTED_LOOP_BOOK = {'01-real.lit': '# Stmt: By.ByForStmt → exec_by_for_stmt\n'
                '# Run: litex -f examples/stmt_nodes/by/by_for.lit\n'
                '\n'
                'by for:\n'
                '    ? forall n range(0, 3) => n < 3\n'
                '    n < 3\n',
 '02-empty.lit': 'by enumerate finite_set:\n'
                 '    ? forall x {}:\n'
                 '        0 = x = 1\n'
                 '    0 = x = 1\n'
                 '\n'
                 'by for:\n'
                 '    ? forall skipped_k range(0, 2):\n'
                 '        skipped_k < 0\n'
                 '        =>:\n'
                 '            skipped_k = 9\n'
                 '    1 = 2\n',
 'litex.config': '[export]\nreal = "./01-real.lit"\nempty = "./02-empty.lit"\n'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/release/litex')
    parser.add_argument('--lessons', action='store_true', help='Also verify the bilingual lessons and their concrete repair exercises.')
    parser.add_argument('--correspondence', action='store_true', help='Also export the four atomic proof routes and named strategy examples.')
    parser.add_argument('--definitions', action='store_true', help='Also export definition applications, tuple properties and rejection controls.')
    parser.add_argument('--definition-scopes', action='store_true', help='Export maintained builtin/user definition proofs and ordinary-rule controls for scoped requirement citations.')
    parser.add_argument('--glossary', action='store_true', help='Also export mathematical language-reference hover cases.')
    parser.add_argument('--forall-equality-symmetry', action='store_true', help='Export actual universal instantiation followed by equality symmetry, controls and a qualified two-source book.')
    parser.add_argument('--theorems', action='store_true', help='Also export actual theorem applications and their rejection control.')
    parser.add_argument('--logic', action='store_true', help='Also export local assumptions, case scopes and block conclusions from public proofs.')
    parser.add_argument('--processes', action='store_true', help='Also export induction stages, enumeration assignments and witness obligations.')
    parser.add_argument('--introductions', action='store_true', help='Also export object introductions, existential elimination and their boundaries.')
    parser.add_argument('--functions', action='store_true', help='Also export function and algorithm definitions, obligations and rejection boundaries.')
    parser.add_argument('--expansions', action='store_true', help='Also export extensionality, explicit definition release and range expansion.')
    parser.add_argument('--state-changes', action='store_true', help='Also export checked registrations, explicit assumptions and scratch scopes, including strict-policy boundaries.')
    parser.add_argument('--interfaces', action='store_true', help='Also export six mathematical interface definitions and their actual native publication/proof boundaries.')
    parser.add_argument('--foundations-eval', action='store_true', help='Also export foundational principle applications and exact evaluation traces, including native rejections.')
    parser.add_argument('--empty-domains', action='store_true', help='Also export real vacuous universals, non-publication and WD boundaries.')
    parser.add_argument('--equivalences', action='store_true', help='Also export both quantified-equivalence directions, partial failures and WD boundaries.')
    parser.add_argument('--failed-introductions', action='store_true', help='Export actual partial object-introduction and witness-source failure records.')
    parser.add_argument('--declaration-status', action='store_true', help='Export attempted, completed and scoped declaration hover controls.')
    parser.add_argument('--quantifier-formation', action='store_true', help='Export retained forall proof-introduction and formation-only failures, including a false consequent and actual local inference.')
    parser.add_argument('--failed-interfaces', action='store_true', help='Export actual failed prop/struct/template stage prefixes and local scopes.')
    parser.add_argument('--failed-contra', action='store_true', help='Export actual retained failed contradiction assumptions, body prefixes and closing sides.')
    parser.add_argument('--failed-theorems', action='store_true', help='Export actual failed theorem preparation, argument, domain, premise and selection records.')
    parser.add_argument('--failed-definitions', action='store_true', help='Also export actual failed definition requirement prefixes, scopes and unexecuted conditions.')
    parser.add_argument('--whole-chain-forall', action='store_true', help='Also export whole-chain universal applications, actual matches/WD and rejection boundaries.')
    parser.add_argument('--failed-chain-proofs', action='store_true', help='Also export actual partial chain proofs, failed adjacent checks and unchecked suffix boundaries.')
    parser.add_argument('--local-source-equalities', action='store_true', help='Also export checked local equality clauses, closing checks and non-proof boundaries.')
    parser.add_argument('--failed-universal-context', action='store_true', help='Also export actual failed universal contexts, checked prefixes and boundaries.')
    parser.add_argument('--failed-claim-context', action='store_true', help='Also export retained failed claim scopes, assumptions and completed-stage prefixes.')
    parser.add_argument('--inferred-rules', action='store_true', help='Also export actual inference rule sources, conclusions and checked side conditions.')
    parser.add_argument('--tuple-coordinates', action='store_true', help='Export actual one-layer tuple coordinate inference, local/reversed/empty/alias boundaries and a qualified two-source book.')
    parser.add_argument('--numeric-rewrites', action='store_true', help='Export actual closed-numeric equality rewrites, residual proofs, local/chain/route controls and a qualified two-source book.')
    parser.add_argument('--unexecuted-loops', action='store_true', help='Export actual empty/all-skipped enumeration bodies, nested/repeated/local histories and rejection controls.')
    parser.add_argument('--case-consequences', action='store_true', help='Also export successful case-target inference batches and outer-publication boundaries.')
    parser.add_argument('--completed-case-prefix', action='store_true', help='Also export actual completed case prefixes, coverage and closing-target prefixes before later failures.')
    parser.add_argument('--failed-case-context', action='store_true', help='Also export actual failed case assumptions, completed body prefixes, nested scopes and non-leakage boundaries.')
    parser.add_argument('--failed-headers', action='store_true', help='Also export rejected statement headers, exact body failures, parse boundaries and successful controls.')
    parser.add_argument('--function-properties', action='store_true', help='Also export exact function interfaces, all relevant return guarantees, retained call layers and rejection boundaries.')
    parser.add_argument('--matrix-membership', action='store_true', help='Also export native matrix function interfaces, all five scalar-evidence families and rejection boundaries.')
    parser.add_argument('--function-membership', action='store_true', help='Also export ordinary complete-domain membership, Cartesian coordinates and search boundaries.')
    parser.add_argument('--function-domains', action='store_true', help='Also export actual complete function interfaces, theorem-domain comparisons and failure boundaries.')
    parser.add_argument('--connectives', action='store_true', help='Also export actual conjunction/disjunction branches, rules, citations, scopes and rejection boundaries.')
    parser.add_argument('--counterexamples', action='store_true', help='Also export counterexample proofs of negated universals and their actual inferred existentials.')
    parser.add_argument('--objects', action='store_true', help='Also export native object-operation help and domain controls.')
    parser.add_argument('--contexts', action='store_true', help='Also export AST-owned expression-position help.')
    parser.add_argument('--multivariable', action='store_true', help='Also export multivariable expression help and domain controls.')
    parser.add_argument('--symbols', action='store_true', help='Also export postfix and structural-symbol help controls.')
    parser.add_argument('--repeated', action='store_true', help='Also export repeated-expression anchors and mixed-role brace controls.')
    parser.add_argument('--builtin-references', action='store_true', help='Also execute and export each authored builtin-theorem help example.')
    parser.add_argument('--failed-strategy-context', action='store_true', help='Export retained failed strategy scopes, actual checked prefixes, controls and a qualified two-source book.')
    parser.add_argument('--failed-theorem-context', action='store_true', help='Export actual rejected universal/direct theorem histories, checked prefixes, local inference and a qualified two-source book.')
    parser.add_argument('--transitivity-applications', action='store_true', help='Export actual registered and builtin transitivity, residual proofs and missing-premise/registration controls.')
    parser.add_argument('--registration-failures', action='store_true', help='Export actual failed relation-law contexts and pre-entry boundaries, with a qualified two-source book.')
    parser.add_argument('--pending-goals', action='store_true', help='Export actual unchecked local goals after stopped proof bodies or earlier goal failures, with role and recovery controls.')
    parser.add_argument('--strategy-body', action='store_true', help='Export actual nested strategy source steps and local-scope failure boundaries.')
    parser.add_argument('--statement-kinds', action='store_true', help='Export the canonical positive file for each live statement manifest entry, preserving its strict policy.')
    parser.add_argument('--template-contexts', action='store_true', help='Export actual template parameter/guard assumptions, local consequences, conditional publication and failure-prefix boundaries.')
    parser.add_argument('--struct-introduction-history', action='store_true', help='Export actual trusted, verified and temporary structure origins, with a two-source failure book.')
    parser.add_argument('--trust-have-history', action='store_true', help='Export explicit-assumption formation prefixes, rollback and strict-policy controls.')
    parser.add_argument('--peer-quantifier-formation', action='store_true', help='Export actual exist/exist!/not-exist/not-forall/iff formation prefixes and truth boundaries.')
    parser.add_argument('--automatic-struct-origins', action='store_true', help='Export scoped automatic struct origins and excluded formation/preflight controls.')
    parser.add_argument('--struct-expansion', action='store_true', help='Export actual nested/parameterized structure expansions and a two-source qualified book.')
    parser.add_argument('--atomic-fact-formation', action='store_true', help='Export atomic formation stages, exact goal rows, nested proof failures and truth/parse controls.')
    parser.add_argument('--compound-fact-formation', action='store_true', help='Export ordinary compound WD, proved prefixes, nested failures and truth-search boundaries.')
    parser.add_argument('--compound-quantifier-formation', action='store_true', help='Export actual complete and partial and/chain/or formation histories and adoption boundaries.')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    report = {}
    if args.definition_scopes:
        paths = {path.stem: path for path in sorted((ROOT / 'examples/proof_nodes/atomic/by_definition').glob('*.lit'))}
        paths['canonical-by-def'] = ROOT / 'examples/test_statements/by_def_stmt.lit'
        paths['ordinary-builtin'] = ROOT / CORRESPONDENCE_CASES['strategy'][0]
        for name, path in paths.items():
            source = path.read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-json', '-lang', 'en', '-f', str(path)], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != 0 or bundle.get('run_result') != 'success' or len(bundle['sources']) != 1 or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f'{name}: unexpected definition-scope source result\n{run.stderr}')
            (args.output / f'definition-scope-{name}.json').write_text(run.stdout)
            report[f'definition-scope-{name}'] = {'exit': run.returncode, 'run_result': 'success', 'strict': True, 'source': str(path.relative_to(ROOT))}
        project = args.output / 'definition-scope-book-source'
        project.mkdir(exist_ok=True)
        book_files = {
            'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\napplications = "./02-applications.lit"\n',
            '01-definitions.lit': (ROOT / 'examples/test_statements/by_def_stmt.lit').read_text() + '\n' + (ROOT / 'examples/test_statements/release_thm_stmt.lit').read_text(),
            '02-applications.lit': 'by def:\n    ? $definitions::def_zero(0)\n\nrelease thm definitions::release_one\n',
            'reading-titles.json': json.dumps({'kind': 'reading_titles', 'sources': {'definitions': {'zh': '定义中的局部证明', 'en': 'Local proofs within definitions'}, 'applications': {'zh': '应用定义与定理', 'en': 'Applying definitions and theorems'}}}, ensure_ascii=False),
        }
        for name, source in book_files.items():
            (project / name).write_text(source)
        exported = args.output / 'definition-scope-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 0 or bundle.get('run_result') != 'success' or len(bundle['sources']) != 2:
            raise RuntimeError(f'definition-scope-book: unexpected result\n{run.stderr}')
        report['definition-scope-book'] = {'exit': run.returncode, 'run_result': 'success', 'sources': 2, 'strict': True}
    if args.transitivity_applications:
        for name, case in TRANSITIVITY_APPLICATION_CASES.items():
            source = case.get('source') or (ROOT / case['path']).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-json', '-lang', 'en', '-e', source], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f'{name}: unexpected transitivity result\n{run.stderr}')
            (args.output / f'transitivity-{name}.json').write_text(run.stdout)
            report[f'transitivity-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': True}
        project = args.output / 'transitivity-book-source'
        project.mkdir(exist_ok=True)
        for name, source in TRANSITIVITY_APPLICATION_BOOK.items():
            (project / name).write_text(source)
        exported = args.output / 'transitivity-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 0 or bundle.get('run_result') != 'success' or [item['content'] for item in bundle['sources']] != [value for key, value in TRANSITIVITY_APPLICATION_BOOK.items() if key.endswith('.lit')]:
            raise RuntimeError(f'transitivity book: unexpected result or source mismatch\n{run.stderr}')
        report['transitivity-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2, 'strict': True}
    if args.registration_failures:
        for name, case in REGISTRATION_FAILURE_CASES.items():
            source = case.get('source') or (ROOT / case['path']).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-json', '-lang', 'en', '-e', source], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f'{name}: unexpected registration result\n{run.stderr}')
            (args.output / f'registration-{name}.json').write_text(run.stdout)
            report[f'registration-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': True}
        project = args.output / 'registration-book-source'
        project.mkdir(exist_ok=True)
        for name, source in REGISTRATION_FAILURE_BOOK.items():
            (project / name).write_text(source)
        exported = args.output / 'registration-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 1 or bundle.get('run_result') != 'failure' or [item['content'] for item in bundle['sources']] != [value for key, value in REGISTRATION_FAILURE_BOOK.items() if key.endswith('.lit')]:
            raise RuntimeError(f'registration book: unexpected result or source mismatch\n{run.stderr}')
        report['registration-book'] = {'exit': 1, 'run_result': 'failure', 'sources': 2, 'strict': True}
    if args.pending_goals:
        for name, case in PENDING_GOAL_CASES.items():
            source = case.get('source') or (ROOT / case['path']).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-json', '-lang', 'en', '-e', source], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f'{name}: unexpected pending-goal source result\n{run.stderr}')
            (args.output / f'pending-goal-{name}.json').write_text(run.stdout)
            report[f'pending-goal-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': True}
        project = args.output / 'pending-goal-book-source'
        project.mkdir(exist_ok=True)
        for name, source in FAILED_THEOREM_BOOK.items():
            (project / name).write_text(source)
        exported = args.output / 'pending-goal-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 1 or bundle.get('run_result') != 'failure' or len(bundle['sources']) != 2:
            raise RuntimeError(f'pending-goal book: unexpected result or source mismatch\n{run.stderr}')
        report['pending-goal-book'] = {'exit': 1, 'run_result': 'failure', 'sources': 2, 'strict': True}
    if args.failed_theorem_context:
        for name, case in FAILED_THEOREM_CONTEXT_CASES.items():
            source = case.get('source') or (ROOT / case['path']).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-json', '-lang', 'en', '-e', source], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != ('success' if case['success'] else 'failure') or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f'{name}: unexpected theorem-context result\n{run.stderr}')
            (args.output / f'failed-theorem-{name}.json').write_text(run.stdout)
            report[f'failed-theorem-{name}'] = {'exit': run.returncode, 'run_result': bundle['run_result'], 'strict': True}
        project = args.output / 'failed-theorem-book-source'
        project.mkdir(exist_ok=True)
        for name, source in FAILED_THEOREM_BOOK.items():
            (project / name).write_text(source)
        exported = args.output / 'failed-theorem-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 1 or bundle.get('run_result') != 'failure' or [item['content'] for item in bundle['sources']] != [value for key, value in FAILED_THEOREM_BOOK.items() if key.endswith('.lit')]:
            raise RuntimeError(f'failed-theorem book: unexpected result or source mismatch\n{run.stderr}')
        report['failed-theorem-book'] = {'exit': 1, 'run_result': 'failure', 'sources': 2, 'strict': True}
    if args.failed_strategy_context:
        for name, case in FAILED_STRATEGY_CONTEXT_CASES.items():
            source = case.get('source') or (ROOT / case['path']).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-json', '-lang', 'en', '-e', source], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != ('success' if case['success'] else 'failure') or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f'{name}: unexpected strategy-context result\n{run.stderr}')
            (args.output / f'failed-strategy-{name}.json').write_text(run.stdout)
            report[f'failed-strategy-{name}'] = {'exit': run.returncode, 'run_result': bundle['run_result'], 'strict': True}
        project = args.output / 'failed-strategy-book-source'
        project.mkdir(exist_ok=True)
        for name, source in FAILED_STRATEGY_BOOK.items():
            (project / name).write_text(source)
        exported = args.output / 'failed-strategy-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 1 or bundle.get('run_result') != 'failure' or [item['content'] for item in bundle['sources']] != [value for key, value in FAILED_STRATEGY_BOOK.items() if key.endswith('.lit')]:
            raise RuntimeError(f'failed-strategy book: unexpected result or source mismatch\n{run.stderr}')
        report['failed-strategy-book'] = {'exit': 1, 'run_result': 'failure', 'sources': 2, 'strict': True}
    if args.statement_kinds or args.strategy_body:
        manifest = json.loads((ROOT / 'examples/test_statements/manifest.json').read_text())
        for row in manifest['statements']:
            if not args.statement_kinds and row['leaf'] != 'DefStrategyStmt':
                continue
            source = (ROOT / 'examples/test_statements' / row['file']).read_text()
            command = [str(args.binary.resolve()), '-reading', '-json', '-lang', 'en']
            if row['file_strict']:
                command.append('-strict')
            run = subprocess.run(command + ['-e', source], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != 0 or bundle.get('run_result') != 'success' or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f"{row['leaf']}: canonical statement input failed\n{run.stderr}")
            name = 'kind-' + row['leaf']
            (args.output / f'{name}.json').write_text(run.stdout)
            report[name] = {'exit': 0, 'run_result': 'success', 'strict': row['file_strict'], 'source': row['file']}
    if args.strategy_body:
        cases = {
            'nested': ('examples/stmt_nodes/definition/strategy_nested_proof.lit', True),
            'reading-tracer': ('examples/reading/strategy_body_steps.lit', True),
            'false-body': ('examples/test_statements/negative/def_strategy_stmt/false-strategy-body.lit', False),
            'false-nested': ('examples/test_statements/negative/def_strategy_stmt/false-nested-proof.lit', False),
            'parse-control': ('examples/test_statements/negative/def_strategy_stmt/strategy-must-be-universal.lit', False),
        }
        for name, (relative, success) in cases.items():
            source = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', source], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != (0 if success else 1) or bundle.get('run_result') != ('success' if success else 'failure') or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f'{name}: unexpected strategy-source result\n{run.stderr}')
            (args.output / f'strategy-source-{name}.json').write_text(run.stdout)
            report[f'strategy-source-{name}'] = {'exit': run.returncode, 'run_result': bundle['run_result'], 'source': relative}
        project = args.output / 'strategy-source-book-source'
        project.mkdir(exist_ok=True)
        sources = {
            '01-predicate.lit': 'prop same(x R):\n    x = 0\n',
            '02-strategy.lit': (
                'strategy use_same:\n'
                '    ? forall x R:\n'
                '        x = 0\n'
                '        =>:\n'
                '            $definitions::same(x)\n'
                '    have helper R = x\n'
                '    claim:\n'
                '        ? helper = 0\n'
                '        helper = 0\n'
                '    witness exist u R st {u = helper} from helper\n'
                '    obtain u from exist u R st {u = helper}\n'
                '    by def $definitions::same(x)\n\n'
                '$definitions::same(0)\n\n'
                'have helper R = 1\n\n'
                'helper = 1\n'
            ),
        }
        for name, source in sources.items():
            (project / name).write_text(source)
        (project / 'litex.config').write_text('[export]\ndefinitions = "./01-predicate.lit"\nstrategies = "./02-strategy.lit"\n')
        (project / 'reading-titles.json').write_text(json.dumps({'kind': 'reading_titles', 'sources': {
            '01-predicate.lit': {'zh': '谓词', 'en': 'Predicates'},
            '02-strategy.lit': {'zh': '证明策略', 'en': 'Proof strategies'},
        }}, ensure_ascii=False, indent=2) + '\n')
        exported = args.output / 'strategy-source-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 0 or bundle.get('run_result') != 'success' or [s['content'] for s in bundle['sources']] != list(sources.values()):
            raise RuntimeError(f'strategy-source book: unexpected result or source mismatch\n{run.stderr}')
        report['strategy-source-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2, 'strict': True}
    if args.template_contexts:
        for name, case in TEMPLATE_CONTEXT_CASES.items():
            source = case.get('source') or (ROOT / case['path']).read_text()
            command = [str(args.binary.resolve()), '-reading', '-json', '-lang', 'en']
            if case['strict']:
                command.append('-strict')
            run = subprocess.run(command + ['-e', source], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != source:
                raise RuntimeError(f'{name}: unexpected template-context result\n{run.stderr}')
            (args.output / f'template-context-{name}.json').write_text(run.stdout)
            report[f'template-context-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': case['strict']}
        project = args.output / 'template-context-book-source'
        project.mkdir(exist_ok=True)
        for name, source in TEMPLATE_CONTEXT_BOOK.items():
            (project / name).write_text(source)
        exported = args.output / 'template-context-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 1 or bundle['run_result'] != 'failure' or len(bundle['sources']) != 2:
            raise RuntimeError(f'template-context book lost its actual failure: {run.stderr}')
        report['template-context-book'] = {'exit': 1, 'run_result': 'failure', 'sources': 2, 'strict': True}
    if args.automatic_struct_origins:
        for name, case in AUTOMATIC_STRUCT_ORIGIN_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict',
                                  '-lang', 'en', '-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected automatic structure result\n{run.stderr}')
            (args.output / f'auto-struct-{name}.json').write_text(run.stdout)
            report[f'auto-struct-{name}'] = {'exit': run.returncode, 'run_result': expected}
        project = args.output / 'automatic-struct-book-source'
        project.mkdir(exist_ok=True)
        for name, content in AUTOMATIC_STRUCT_ORIGIN_BOOK.items():
            (project / name).write_text(content)
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en',
                              '-export', str(args.output / 'automatic-struct-book'), '-r', str(project)], capture_output=True, text=True)
        if run.returncode != 0:
            raise RuntimeError(f'automatic structure book: unexpected export result\n{run.stderr}')
        report['automatic-struct-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2}
    if args.struct_expansion:
        nested = None
        for name, (relative, success) in STRUCT_EXPANSION_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict',
                                  '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if success else 'failure'
            if run.returncode != (0 if success else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected structure expansion result\n{run.stderr}')
            (args.output / f'struct-expansion-{name}.json').write_text(run.stdout)
            report[f'struct-expansion-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected}
            if name == 'nested':
                nested = bundle
        # Stmt.source_text can be a display header. Only the original UTF-8
        # source and recorded byte spans retain complete authored definitions.
        source = nested['sources'][0]['content'].encode()
        top = [statement for statement in nested['statements'] if not statement.get('parent_statement_id')]
        raw = lambda statement: source[statement['start_byte']:statement['end_byte']].decode().strip()
        definitions = [raw(statement) for statement in top if statement['statement_kind'].endswith('DefStructStmt')]
        claims = [raw(statement).replace('&ScalarAction', '&structures::ScalarAction').replace('&IdentityCarrier<', '&structures::IdentityCarrier<')
                  for statement in top if statement['statement_kind'].endswith('ClaimStmt')]
        if len(definitions) != 4 or len(claims) != 3:
            raise RuntimeError('structure example changed its source boundaries')
        project = args.output / 'struct-expansion-book-source'
        project.mkdir(exist_ok=True)
        (project / '01-definitions.lit').write_text('\n\n'.join(definitions) + '\n')
        (project / '02-proofs.lit').write_text('\n\n'.join(claims) + '\n')
        (project / 'litex.config').write_text('[export]\nstructures = "./01-definitions.lit"\nproofs = "./02-proofs.lit"\n')
        (project / 'reading-titles.json').write_text(json.dumps({'kind': 'reading_titles', 'sources': {
            '01-definitions.lit': {'zh': '结构定义', 'en': 'Structural definitions'},
            '02-proofs.lit': {'zh': '结构性质的使用', 'en': 'Using structural properties'}}}, ensure_ascii=False) + '\n')
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en',
                              '-export', str(args.output / 'struct-expansion-book'), '-r', str(project)], capture_output=True, text=True)
        if run.returncode != 0:
            raise RuntimeError(f'structure book: unexpected export result\n{run.stderr}')
        report['struct-expansion-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2}
    if args.atomic_fact_formation:
        for name, case in ATOMIC_FACT_FORMATION_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict',
                                  '-lang', 'en', '-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected atomic formation result\n{run.stderr}')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != case['source']:
                raise RuntimeError(f'{name}: atomic formation source mismatch')
            (args.output / f'atomic-{name}.json').write_text(run.stdout)
            report[f'atomic-{name}'] = {'exit': run.returncode, 'run_result': expected}
    if args.compound_fact_formation:
        for name, case in COMPOUND_FACT_FORMATION_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict',
                                  '-lang', 'en', '-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected ordinary compound result\n{run.stderr}')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != case['source']:
                raise RuntimeError(f'{name}: ordinary compound source mismatch')
            (args.output / f'fact-formation-{name}.json').write_text(run.stdout)
            report[f'fact-formation-{name}'] = {'exit': run.returncode, 'run_result': expected}
        project = args.output / 'fact-formation-book-source'
        project.mkdir(exist_ok=True)
        files = {
            '01-definitions.lit': 'prop reading_positive(x R):\n    x > 0\n',
            '02-attempt.lit': '$definitions::reading_positive(-1) or 1 / 0 = 0 or 1 = 1\n',
            'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\nattempt = "./02-attempt.lit"\n',
            'reading-titles.json': json.dumps({'kind': 'reading_titles', 'sources': {
                '01-definitions.lit': {'zh': '正数条件', 'en': 'A positive condition'},
                '02-attempt.lit': {'zh': '析取的表达式检查', 'en': 'Formation of a disjunction'}}}, ensure_ascii=False),
            'README.md': '# Ordinary compound reading probe\n\nThe first source defines positivity. The second fails expression formation in the middle alternative. Neither the false first predicate instance nor the true last equality bypasses the failed denominator check.\n',
            'math_collections.md': '# Mathematical interfaces\n\n`reading_positive(x R)` requires x > 0. Its instance at -1 is well-formed but false. The rejected disjunction publishes no whole fact, branch fact or inferred consequence.\n',
        }
        for name, content in files.items():
            (project / name).write_text(content)
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en',
                              '-export', str(args.output / 'fact-formation-book'), '-r', str(project)],
                             capture_output=True, text=True)
        if run.returncode != 1:
            raise RuntimeError(f'fact-formation-book: unexpected export result\n{run.stderr}')
        bundle = json.loads((args.output / 'fact-formation-book' / 'reading.json').read_text())
        if bundle.get('run_result') != 'failure' or len(bundle.get('sources', [])) != 2:
            raise RuntimeError('fact-formation-book: source or result mismatch')
        report['fact-formation-book'] = {'exit': run.returncode, 'run_result': 'failure', 'sources': 2}
    if args.compound_quantifier_formation:
        for name, case in COMPOUND_QUANTIFIER_FORMATION_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict',
                                  '-lang', 'en', '-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected compound formation result\n{run.stderr}')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != case['source']:
                raise RuntimeError(f'{name}: compound formation source mismatch')
            (args.output / f'compound-{name}.json').write_text(run.stdout)
            report[f'compound-{name}'] = {'exit': run.returncode, 'run_result': expected}
    if args.peer_quantifier_formation:
        for name, case in PEER_QUANTIFIER_FORMATION_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict',
                                  '-lang', 'en', '-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected peer formation result\n{run.stderr}')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != case['source']:
                raise RuntimeError(f'{name}: peer formation source mismatch')
            (args.output / f'peer-{name}.json').write_text(run.stdout)
            report[f'peer-{name}'] = {'exit': run.returncode, 'run_result': expected}
    if args.struct_introduction_history:
        for name, case in STRUCT_INTRO_CASES.items():
            command = [str(args.binary.resolve()), '-reading', '-json', '-lang', 'en']
            if case['strict']:
                command.append('-strict')
            run = subprocess.run(command + ['-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != case['source']:
                raise RuntimeError(f'{name}: unexpected structural introduction result\n{run.stderr}')
            (args.output / f'struct-introduction-{name}.json').write_text(run.stdout)
            report[f'struct-introduction-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': case['strict']}
        project = args.output / 'struct-introduction-book-source'
        project.mkdir(exist_ok=True)
        for name, source in STRUCT_INTRO_BOOK.items():
            (project / name).write_text(source)
        exported = args.output / 'struct-introduction-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        bundle = json.loads((exported / 'reading.json').read_text())
        if run.returncode != 1 or bundle['run_result'] != 'failure' or len(bundle['sources']) != 2:
            raise RuntimeError(f'structural introduction book lost its actual failure: {run.stderr}')
        report['struct-introduction-book'] = {'exit': run.returncode, 'run_result': 'failure', 'sources': 2, 'strict': False}
    if args.trust_have_history:
        for name, case in TRUST_HAVE_HISTORY_CASES.items():
            command = [str(args.binary.resolve()), '-reading', '-json', '-lang', 'en']
            if case['strict']:
                command.append('-strict')
            run = subprocess.run(command + ['-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected trust-have formation result\n{run.stderr}')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != case['source']:
                raise RuntimeError(f'{name}: trust-have source mismatch')
            (args.output / f'trust-have-{name}.json').write_text(run.stdout)
            report[f'trust-have-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': case['strict']}
    if args.trust_have_history:
        project = args.output / 'trust-have-book-source'
        project.mkdir(exist_ok=True)
        files = {
            '01-definitions.lit': 'prop nonzero(x R):\n    x != 0\n',
            '02-instance.lit': 'by def $definitions::nonzero(2)\n',
            '03-assumptions.lit': 'trust have local_a R:\n    $definitions::nonzero(2)\n    1 / local_a $in R\n    local_a = local_a\n',
            'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\ninstance = "./02-instance.lit"\nassumptions = "./03-assumptions.lit"\n',
            'README.md': '# Assumption formation reading probe\n\nA nonzero predicate is defined and its instance at2 is proved. The last explicit-assumption declaration intentionally fails before storing any body assumption. Checking predicate formation does not prove its instance.\n',
            'math_collections.md': '# Mathematical interfaces\n\n`nonzero(x R)` is equivalent to x !=0 in its declared domain. Its by-definition instance is distinct from the last attempted declaration, whose formation checks establish no body fact.\n',
        }
        for name, content in files.items():
            (project / name).write_text(content)
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-lang', 'en',
                              '-export', str(args.output / 'trust-have-book'), '-r', str(project)],
                             capture_output=True, text=True)
        if run.returncode != 1:
            raise RuntimeError(f'trust-have-book: unexpected export result\n{run.stderr}')
        bundle = json.loads((args.output / 'trust-have-book' / 'reading.json').read_text())
        if bundle.get('run_result') != 'failure' or len(bundle.get('sources', [])) != 3:
            raise RuntimeError('trust-have-book: source or result mismatch')
        report['trust-have-book'] = {'exit': run.returncode, 'run_result': 'failure', 'sources': 3}
    if args.compound_quantifier_formation:
        project = args.output / 'compound-book-source'
        project.mkdir(exist_ok=True)
        files = {
            '01-definitions.lit': 'prop nonzero_value(x R):\n    x != 0\n',
            '02-instance.lit': 'by def $definitions::nonzero_value(2)\n',
            '03-candidates.lit': 'prop book_candidate(t R):\n    exist x R st {$definitions::nonzero_value(x) and x >= 0, 1 / (x - 1) > 0, x = x}\n',
            'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\ninstance = "./02-instance.lit"\ncandidate = "./03-candidates.lit"\n',
            'reading-titles.json': json.dumps({'kind': 'reading_titles', 'sources': {
                '01-definitions.lit': {'zh': '非零条件', 'en': 'A nonzero condition'},
                '02-instance.lit': {'zh': '按定义证明', 'en': 'Proof by definition'},
                '03-candidates.lit': {'zh': '复合条件的检查', 'en': 'Compound candidate conditions'}}}, ensure_ascii=False),
            'README.md': '# Compound candidate formation reading probe\n\nThe first source defines a nonzero condition. The second proves its instance at2. The last declaration intentionally fails formation after a locally adopted conjunction; that local assumption supplies no existence witness or published conclusion.\n',
            'math_collections.md': '# Mathematical interfaces\n\n`nonzero_value(x R)` is equivalent to x !=0 within its declared domain. The last existential condition has an unrestricted denominator x-1. Its locally adopted conjunction stores its atomic components. Only the actual predicate component supplies the local nonzero consequence; neither alternative branches nor formation-only clauses become assumptions.\n',
        }
        for name, content in files.items():
            (project / name).write_text(content)
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en',
                              '-export', str(args.output / 'compound-book'), '-r', str(project)],
                             capture_output=True, text=True)
        if run.returncode != 1:
            raise RuntimeError(f'compound-book: unexpected export result\n{run.stderr}')
        bundle = json.loads((args.output / 'compound-book' / 'reading.json').read_text())
        if bundle.get('run_result') != 'failure' or len(bundle.get('sources', [])) != 3:
            raise RuntimeError('compound-book: source or result mismatch')
        report['compound-book'] = {'exit': run.returncode, 'run_result': 'failure', 'sources': 3}
    if args.peer_quantifier_formation:
        project = args.output / 'peer-book-source'
        project.mkdir(exist_ok=True)
        files = {
            '01-definitions.lit': 'prop nonzero_value(x R):\n    x != 0\n',
            '02-instance.lit': 'by def $definitions::nonzero_value(2)\n',
            '03-candidates.lit': 'prop book_candidate(t R):\n    exist x R st {$definitions::nonzero_value(2), 1 / (x - 1) > 0, x = x}\n',
            'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\ninstance = "./02-instance.lit"\ncandidate = "./03-candidates.lit"\n',
            'reading-titles.json': json.dumps({'kind': 'reading_titles', 'sources': {
                '01-definitions.lit': {'zh': '非零条件', 'en': 'A nonzero condition'},
                '02-instance.lit': {'zh': '按定义证明', 'en': 'Proof by definition'},
                '03-candidates.lit': {'zh': '候选条件的检查', 'en': 'Checking candidate conditions'}}}, ensure_ascii=False),
            'README.md': '# Candidate formation reading probe\n\nThe first source defines a nonzero condition. The second proves its instance at2. The last declaration intentionally fails formation after a local candidate assumption; that local assumption supplies no existence witness or published conclusion.\n',
            'math_collections.md': '# Mathematical interfaces\n\n`nonzero_value(x R)` is equivalent to x !=0 within its declared domain. The last existential condition has an unrestricted denominator x-1. Its locally assumed predicate instance supplies only the retained consequences of that assumption.\n',
        }
        for name, content in files.items():
            (project / name).write_text(content)
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en',
                              '-export', str(args.output / 'peer-book'), '-r', str(project)],
                             capture_output=True, text=True)
        if run.returncode != 1:
            raise RuntimeError(f'peer-book: unexpected export result\n{run.stderr}')
        bundle = json.loads((args.output / 'peer-book' / 'reading.json').read_text())
        if bundle.get('run_result') != 'failure' or len(bundle.get('sources', [])) != 3:
            raise RuntimeError('peer-book: source or result mismatch')
        report['peer-book'] = {'exit': run.returncode, 'run_result': 'failure', 'sources': 3}
    if args.quantifier_formation:
        for name, (content, succeeds) in QUANTIFIER_FORMATION_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected quantified check\n{run.stderr}')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != content:
                raise RuntimeError(f'{name}: quantified source snapshot mismatch')
            (args.output / f'quantifier-{name}.json').write_text(run.stdout)
            report[f'quantifier-{name}'] = {'exit': run.returncode, 'run_result': expected}
    if args.quantifier_formation:
        project = args.output / 'quantifier-book-source'
        project.mkdir(exist_ok=True)
        files = {
            '01-definitions.lit': QUANTIFIER_FORMATION_CASES['real-quotient-definition-repair'][0] + '\n',
            '02-instance.lit': 'by def $definitions::quotients_are_real(2)\n',
            '03-universal.lit': 'forall x R:\n    $definitions::quotients_are_real(2)\n    1 / (x - 1) > 0\n    =>:\n        x = x\n',
            'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\ninstance = "./02-instance.lit"\napplication = "./03-universal.lit"\n',
            'README.md': '# Quantified formation reading probe\n\nThe definition requires a nonzero real denominator. The second source proves the instance at2. The last source intentionally fails at x-1; a premise about denominator2 does not imply x !=1. No outer universal conclusion is published.\n',
            'math_collections.md': '# Mathematical interfaces\n\n`quotients_are_real(a R)` requires a !=0 and every real quotient x/a to be real. The checked instance uses a=2. The last attempted universal retains its scoped assumptions and fails expression formation.\n',
        }
        for name, content in files.items():
            (project / name).write_text(content)
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en',
                              '-export', str(args.output / 'quantifier-book'), '-r', str(project)],
                             capture_output=True, text=True)
        if run.returncode != 1:
            raise RuntimeError(f'quantifier-book: unexpected export result\n{run.stderr}')
        bundle = json.loads((args.output / 'quantifier-book' / 'reading.json').read_text())
        if bundle.get('run_result') != 'failure' or len(bundle.get('sources', [])) != 3:
            raise RuntimeError('quantifier-book: source or result mismatch')
        report['quantifier-book'] = {'exit': run.returncode, 'run_result': 'failure', 'sources': 3}
    if args.failed_interfaces:
        for name, (content, succeeds) in FAILED_INTERFACE_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected definition check\n{run.stderr}')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != content:
                raise RuntimeError(f'{name}: definition source snapshot mismatch')
            (args.output / f'failed-interface-{name}.json').write_text(run.stdout)
            report[f'failed-interface-{name}'] = {'exit': run.returncode, 'run_result': expected}
    if args.failed_interfaces:
        project = args.output / 'failed-interface-book-source'
        project.mkdir(exist_ok=True)
        files = {'01-definitions.lit': 'prop def_nonzero(t R):\n    t != 0\n', '02-instance.lit': 'by def $definitions::def_nonzero(2)\n', '03-definition.lit': 'prop inferred_guard(x R):\n    $definitions::def_nonzero(x)\n    1 / (x - 1) $in R\n    x = x\n', 'litex.config': '[export]\ndefinitions = "./01-definitions.lit"\ninstance = "./02-instance.lit"\napplication = "./03-definition.lit"\n', 'README.md': '# Definition-check reading probe\n\nThe first export defines nonzero, the second checks its instance at2, and the last intentionally fails a reciprocal formation condition. Local assumptions and their consequences are not a published definition or a proof for arbitrary arguments.\n', 'math_collections.md': '# Mathematical interfaces\n\n`def_nonzero(t R)` means `t !=0`. The attempted `inferred_guard(x R)` assumes nonzero x, which does not imply `x !=1`. Its quotient cannot be formed and the definition is not published.\n'}
        for name, content in files.items():
            (project / name).write_text(content)
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en',
                              '-export', str(args.output / 'failed-interface-book'), '-r', str(project)],
                             capture_output=True, text=True)
        if run.returncode != 1:
            raise RuntimeError(f'failed-interface-book: unexpected export result\n{run.stderr}')
        bundle = json.loads((args.output / 'failed-interface-book' / 'reading.json').read_text())
        if bundle.get('run_result') != 'failure' or len(bundle.get('sources', [])) != 3:
            raise RuntimeError('failed-interface-book: source or result mismatch')
        report['failed-interface-book'] = {'exit': run.returncode, 'run_result': 'failure', 'sources': 3}
    if args.declaration_status:
        cases = {
            'failed-objects': ('have a, b, c N = 1, -1, 2\n', False),
            'completed-objects': ('have a, b, c N = 1, 2, 2\n', True),
            'failed-function-domain': ((ROOT / FUNCTION_CASES['wrong-codomain'][0]).read_text(), False),
            'failed-function-body': ((ROOT / FUNCTION_CASES['ill-defined'][0]).read_text(), False),
            'failed-theorem': ((ROOT / INTERFACE_CASES['theorem-false-bodyless-theorem'][0]).read_text(), False),
            'failed-strategy': ((ROOT / INTERFACE_CASES['strategy-false-strategy-body'][0]).read_text(), False),
            'failed-caller': ((ROOT / INTERFACE_CASES['prop-wrong-predicate-carrier'][0]).read_text(), False),
            'local-in-failed-proof': FAILED_CONTRA_CASES['closing-after-prefix'],
            'repeated': ((ROOT / INTRODUCTION_CASES['repeated'][0]).read_text(), True),
        }
        for name, (content, succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected declaration result\n{run.stderr}')
            if len(bundle.get('sources', [])) != 1 or bundle['sources'][0].get('content') != content:
                raise RuntimeError(f'{name}: declaration source snapshot mismatch')
            (args.output / f'declaration-{name}.json').write_text(run.stdout)
            report[f'declaration-{name}'] = {'exit': run.returncode, 'run_result': expected}
    if args.function_properties:
        cases = dict(FUNCTION_PROPERTY_INLINE_CASES)
        cases['aliased-nested-tracer'] = ((ROOT / 'examples/proof_nodes/atomic/by_known_special_property/function_return_interface_layers.lit').read_text(), True)
        for name, (content, succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected function-property result\n{run.stderr}')
            if not any(s.get('content') == content for s in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: function-property source snapshot mismatch')
            (args.output / f'function-property-{name}.json').write_text(run.stdout)
            report[f'function-property-{name}'] = {'source': '<session-verified fixture>', 'exit': run.returncode, 'run_result': expected}
    if args.matrix_membership:
        cases = dict(MATRIX_MEMBERSHIP_INLINE_CASES)
        cases['matrix-space-functions'] = ((ROOT / 'examples/test_objs/matrix_fn_space.lit').read_text(), True)
        for name, (content, succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected matrix-membership result\n{run.stderr}')
            if not any(s.get('content') == content for s in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: matrix-membership source snapshot mismatch')
            (args.output / f'matrix-membership-{name}.json').write_text(run.stdout)
            report[f'matrix-membership-{name}'] = {'source': '<session-verified fixture>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_introductions:
        for name, (content, succeeds) in FAILED_INTRODUCTION_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected object-introduction result\n{run.stderr}')
            (args.output / f'failed-introduction-{name}.json').write_text(run.stdout)
            report[f'failed-introduction-{name}'] = {'source': '<session-and-public-source-baseline>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_contra:
        for name, (content, succeeds) in FAILED_CONTRA_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected contradiction result\n{run.stderr}')
            (args.output / f'failed-contra-{name}.json').write_text(run.stdout)
            report[f'failed-contra-{name}'] = {'source': '<session-verified>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_theorems:
        for name, (content, succeeds) in FAILED_THEOREM_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected theorem invocation result\n{run.stderr}')
            (args.output / f'failed-theorem-{name}.json').write_text(run.stdout)
            report[f'failed-theorem-{name}'] = {'source': '<session-verified>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_definitions:
        for name, (content, succeeds) in FAILED_DEFINITION_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected failed-definition result\n{run.stderr}')
            (args.output / f'failed-definition-{name}.json').write_text(run.stdout)
            report[f'failed-definition-{name}'] = {'source': '<session-verified>', 'exit': run.returncode, 'run_result': expected}
    if args.whole_chain_forall:
        for name, (content, succeeds) in WHOLE_CHAIN_FORALL_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected whole-chain result\n{run.stderr}')
            (args.output / f'whole-chain-{name}.json').write_text(run.stdout)
            report[f'whole-chain-{name}'] = {'source': '<session-verified>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_chain_proofs:
        for name, (content, succeeds) in FAILED_CHAIN_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected failed-chain result\n{run.stderr}')
            (args.output / f'failed-chain-{name}.json').write_text(run.stdout)
            report[f'failed-chain-{name}'] = {'source': '<session-verified>', 'exit': run.returncode, 'run_result': expected}
    if args.local_source_equalities:
        for name, (content, succeeds) in LOCAL_SOURCE_EQUALITY_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected local equality result\n{run.stderr}')
            (args.output / f'local-equality-{name}.json').write_text(run.stdout)
            report[f'local-equality-{name}'] = {'source': '<session-verified>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_universal_context:
        cases = dict(FAILED_UNIVERSAL_INLINE_CASES)
        cases['canonical'] = ((ROOT / 'examples/test_statements/negative/fact/retained-universal-context.lit').read_text(), False)
        for name, (content, succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected failed-universal result\n{run.stderr}')
            (args.output / f'failed-universal-{name}.json').write_text(run.stdout)
            report[f'failed-universal-{name}'] = {'source': '<session-verified>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_claim_context:
        cases = {name: ((ROOT / relative).read_text(), succeeds)
                 for name, (relative, succeeds) in FAILED_CLAIM_CASES.items()}
        cases.update(FAILED_CLAIM_INLINE_CASES)
        for name, (content, succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(
                    item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected failed-claim result\n{run.stderr}')
            (args.output / f'failed-claim-{name}.json').write_text(run.stdout)
            report[f'failed-claim-{name}'] = {'source': FAILED_CLAIM_CASES.get(name, ('<session-verified>',))[0],
                                           'exit': run.returncode, 'run_result': expected}
    if args.inferred_rules:
        for name, relative in INFERRED_RULE_CASES.items():
            source = ROOT / relative
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-f', str(source)], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != 0 or bundle.get('run_result') != 'success' or not any(
                    item.get('content') == source.read_text() for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: unexpected inference result\n{run.stderr}')
            (args.output / f'inferred-rule-{name}.json').write_text(run.stdout)
            report[f'inferred-rule-{name}'] = {'source': relative, 'exit': 0, 'run_result': 'success'}
    if args.case_consequences:
        for name, (content, succeeds) in CASE_CONSEQUENCES_INLINE_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected case-consequence result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: case-consequence source snapshot mismatch')
            (args.output / f'case-prefix-{name}.json').write_text(run.stdout)
            report[f'case-prefix-{name}'] = {'source': '<session-verified fixture>', 'exit': run.returncode, 'run_result': expected}
    if args.completed_case_prefix:
        cases = dict(COMPLETED_CASE_PREFIX_INLINE_CASES)
        cases['canonical'] = ((ROOT / 'examples/test_statements/negative/by_cases_stmt/completed-branch-before-failure.lit').read_text(), False)
        for name, (content, succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected completed-case prefix result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: completed-case source snapshot mismatch')
            (args.output / f'case-prefix-{name}.json').write_text(run.stdout)
            report[f'case-prefix-{name}'] = {'source': '<session-verified fixture>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_case_context:
        cases = dict(FAILED_CASE_CONTEXT_INLINE_CASES)
        cases['canonical-prefix'] = ((ROOT / 'examples/test_statements/negative/by_cases_stmt/failed-body-context.lit').read_text(), False)
        for name, (content, succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected failed-case context result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: failed-case source snapshot mismatch')
            (args.output / f'failed-case-{name}.json').write_text(run.stdout)
            report[f'failed-case-{name}'] = {'source': '<session-verified fixture>', 'exit': run.returncode, 'run_result': expected}
    if args.failed_headers:
        cases = {name: ((ROOT / source).read_text(), succeeds, source)
                 for name, (source, succeeds) in FAILED_HEADER_CASES.items()}
        cases.update({name: (content, succeeds, '<session-verified fixture>')
                      for name, (content, succeeds) in FAILED_HEADER_INLINE_CASES.items()})
        for name, (content, succeeds, source) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected failed-header result\n{run.stderr}')
            if not any(s.get('content') == content for s in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: failed-header source snapshot mismatch')
            (args.output / f'failed-header-{name}.json').write_text(run.stdout)
            report[f'failed-header-{name}'] = {'source': source, 'exit': run.returncode, 'run_result': expected}
    if args.function_membership:
        cases = {name: ((ROOT / source).read_text(), succeeds, source)
                 for name, (source, succeeds) in FUNCTION_MEMBERSHIP_CASES.items()}
        cases.update({name: (content, succeeds, '<session-verified fixture>')
                      for name, (content, succeeds) in FUNCTION_MEMBERSHIP_INLINE_CASES.items()})
        for name, (content, succeeds, source) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected function-membership result\n{run.stderr}')
            if not any(s.get('content') == content for s in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: function-membership source snapshot mismatch')
            (args.output / f'function-membership-{name}.json').write_text(run.stdout)
            report[f'function-membership-{name}'] = {'source': source, 'exit': run.returncode, 'run_result': expected}
    if args.function_domains:
        cases = {name: ((ROOT / source).read_text(), succeeds, source)
                 for name, (source, succeeds) in FUNCTION_DOMAIN_CASES.items()}
        cases.update({name: (content, succeeds, '<session-verified fixture>')
                      for name, (content, succeeds) in FUNCTION_DOMAIN_INLINE_CASES.items()})
        for name, (content, succeeds, source) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected function-domain result\n{run.stderr}')
            if not any(s.get('content') == content for s in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: function-domain source snapshot mismatch')
            (args.output / f'function-domain-{name}.json').write_text(run.stdout)
            report[f'function-domain-{name}'] = {'source': source, 'exit': run.returncode, 'run_result': expected}
    if args.connectives:
        cases = {name: ((ROOT / source).read_text(), succeeds, source)
                 for name, (source, succeeds) in CONNECTIVE_CASES.items()}
        cases.update({name: (content, succeeds, '<session-verified fixture>')
                      for name, (content, succeeds) in CONNECTIVE_INLINE_CASES.items()})
        for name, (content, succeeds, source) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected connective result\n{run.stderr}')
            if not any(s.get('content') == content for s in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: connective source snapshot mismatch')
            (args.output / f'connective-{name}.json').write_text(run.stdout)
            report[f'connective-{name}'] = {'source': source, 'exit': run.returncode, 'run_result': expected}
    if args.counterexamples:
        cases = [(name, (ROOT / relative).read_text(), succeeds, relative)
                 for name, (relative, succeeds) in COUNTEREXAMPLE_CASES.items()]
        cases += [(name, content, succeeds, '<inline: Session-checked counterexample>')
                  for name, (content, succeeds) in COUNTEREXAMPLE_INLINE_CASES.items()]
        for name, content, succeeds, source in cases:
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: counterexample source/result mismatch\n{run.stderr}')
            (args.output / f'not-forall-{name}.json').write_text(run.stdout)
            report[f'not-forall-{name}'] = {'source': source, 'strict': True, 'exit': run.returncode, 'run_result': expected}
    if args.equivalences:
        cases = [(name, (ROOT / relative).read_text(), succeeds, relative)
                 for name, (relative, succeeds) in EQUIVALENCE_CASES.items()]
        cases += [(name, content, succeeds, '<inline: Session-checked equivalence>')
                  for name, (content, succeeds) in EQUIVALENCE_INLINE_CASES.items()]
        for name, content, succeeds, source in cases:
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(item.get('content') == content for item in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: equivalence source/result mismatch\n{run.stderr}')
            (args.output / f'iff-{name}.json').write_text(run.stdout)
            report[f'iff-{name}'] = {'source': source, 'strict': True, 'exit': run.returncode, 'run_result': expected}
    if args.empty_domains:
        for name, (relative, succeeds) in EMPTY_DOMAIN_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: empty-domain source/result mismatch\n{run.stderr}')
            (args.output / f'empty-domain-{name}.json').write_text(run.stdout)
            report[f'empty-domain-{name}'] = {'source': relative, 'strict': True, 'exit': run.returncode, 'run_result': expected}
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', EMPTY_DOMAIN_LATER_GROUP], capture_output=True, text=True)
        bundle = json.loads(run.stdout)
        if run.returncode != 0 or bundle.get('run_result') != 'success' or not any(source.get('content') == EMPTY_DOMAIN_LATER_GROUP for source in bundle.get('sources', [])):
            raise RuntimeError(f'later empty group: source/result mismatch\n{run.stderr}')
        (args.output / 'empty-domain-later-group.json').write_text(run.stdout)
        report['empty-domain-later-group'] = {'source': '<inline: earlier real parameter, later empty carrier>', 'strict': True, 'exit': 0, 'run_result': 'success'}
    if args.foundations_eval:
        for name, (relative, succeeds, strict) in FOUNDATION_EVAL_CASES.items():
            content = (ROOT / relative).read_text()
            command = [str(args.binary.resolve()), '-reading', '-json', '-lang', 'en', '-e', content]
            if strict:
                command.insert(3, '-strict')
            run = subprocess.run(command, capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected foundation/evaluation result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: foundation/evaluation source snapshot mismatch')
            (args.output / f'foundation-eval-{name}.json').write_text(run.stdout)
            report[f'foundation-eval-{name}'] = {'source': relative, 'strict': strict,
                                              'exit': run.returncode, 'run_result': expected,
                                              'diagnostic_phases': sorted({d.get('phase', 'unspecified') for d in bundle['diagnostics']})}
        for name, (relative, content) in EVAL_NATIVE_TRACERS.items():
            if '"'+content+'"' not in (ROOT / relative).read_text():
                raise RuntimeError(f'{name}: native regression source no longer matches')
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict',
                                  '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            if run.returncode != 0 or bundle.get('run_result') != 'success':
                raise RuntimeError(f'{name}: unexpected native evaluation result\n{run.stderr}')
            (args.output / f'foundation-eval-{name}.json').write_text(run.stdout)
            report[f'foundation-eval-{name}'] = {'source': relative, 'nativeRegression': True,
                                              'strict': True, 'exit': 0, 'run_result': 'success',
                                              'diagnostic_phases': []}
    if args.interfaces:
        for name, (relative, succeeds, strict) in INTERFACE_CASES.items():
            content = (ROOT / relative).read_text()
            command = [str(args.binary.resolve()), '-reading', '-json', '-lang', 'en', '-e', content]
            if strict:
                command.insert(3, '-strict')
            run = subprocess.run(command, capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected mathematical-interface result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: mathematical-interface source snapshot mismatch')
            (args.output / f'interface-{name}.json').write_text(run.stdout)
            report[f'interface-{name}'] = {'source': relative, 'strict': strict,
                                         'exit': run.returncode, 'run_result': expected,
                                         'diagnostic_phases': sorted({d.get('phase', 'unspecified') for d in bundle['diagnostics']})}
    if args.state_changes:
        for name, (relative, succeeds, strict) in STATE_CHANGE_CASES.items():
            content = (ROOT / relative).read_text()
            if name == 'trust-have-release':
                # Same-context Session checked: retain the original trust origin
                # when releasing its definition, without claiming a proof.
                content += '\nrelease obj def trusted_a\n'
            command = [str(args.binary.resolve()), '-reading', '-json', '-lang', 'en', '-e', content]
            if strict:
                command.insert(3, '-strict')
            run = subprocess.run(command, capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected context-change result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: context-change source snapshot mismatch')
            (args.output / f'context-change-{name}.json').write_text(run.stdout)
            report[f'context-change-{name}'] = {'source': relative, 'strict': strict,
                                              'variation': 'append release obj def trusted_a' if name == 'trust-have-release' else None,
                                              'exit': run.returncode, 'run_result': expected,
                                              'diagnostic_phases': sorted({d.get('phase', 'unspecified') for d in bundle['diagnostics']})}
    if args.expansions:
        for name, (relative, succeeds) in EXPANSION_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected extensionality/release result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: extensionality/release source snapshot mismatch')
            parse_rejection = any(diagnostic.get('phase') == 'parse' for diagnostic in bundle.get('diagnostics', []))
            if not succeeds and not parse_rejection and not any(statement.get('status') == 'rejected' for statement in bundle.get('statements', [])):
                raise RuntimeError(f'{name}: expected an actual rejected statement or parse diagnostic')
            (args.output / f'expansion-{name}.json').write_text(run.stdout)
            report[f'expansion-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected,
                                         'failure_phase': 'parse' if parse_rejection else ('verification' if not succeeds else None)}
    if args.functions:
        for name, (relative, succeeds) in FUNCTION_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected function-definition result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: function-definition source snapshot mismatch')
            parse_rejection = any(diagnostic.get('phase') == 'parse' for diagnostic in bundle.get('diagnostics', []))
            if not succeeds and not parse_rejection and not any(statement.get('status') == 'rejected' for statement in bundle.get('statements', [])):
                raise RuntimeError(f'{name}: expected an actual rejected statement or parse diagnostic')
            (args.output / f'function-{name}.json').write_text(run.stdout)
            report[f'function-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected,
                                        'failure_phase': 'parse' if parse_rejection else ('verification' if not succeeds else None)}
    if args.introductions:
        for name, (relative, succeeds) in INTRODUCTION_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected object-introduction result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: object-introduction source snapshot mismatch')
            parse_rejection = any(diagnostic.get('phase') == 'parse' for diagnostic in bundle.get('diagnostics', []))
            if not succeeds and not parse_rejection and not any(statement.get('status') == 'rejected' for statement in bundle.get('statements', [])):
                raise RuntimeError(f'{name}: expected an actual rejected statement or parse diagnostic')
            (args.output / f'intro-{name}.json').write_text(run.stdout)
            report[f'intro-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected,
                                     'failure_phase': 'parse' if parse_rejection else ('verification' if not succeeds else None)}
    if args.processes:
        for name, (relative, succeeds) in PROCESS_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected proof-process result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: proof-process source snapshot mismatch')
            if not succeeds and not any(statement.get('status') == 'rejected' for statement in bundle.get('statements', [])):
                raise RuntimeError(f'{name}: expected an actual rejected statement')
            (args.output / f'process-{name}.json').write_text(run.stdout)
            report[f'process-{name}'] = {'source': relative, 'exit': run.returncode, 'run_result': expected}
    if args.logic:
        for name, (relative, succeeds) in LOGICAL_CASES.items():
            content = (ROOT / relative).read_text()
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected:
                raise RuntimeError(f'{name}: unexpected logical proof result\n{run.stderr}')
            if not any(source.get('content') == content for source in bundle.get('sources', [])):
                raise RuntimeError(f'{name}: logical source snapshot mismatch')
            (args.output / f'{name}.json').write_text(run.stdout)
            report[name] = {'source': relative, 'exit': run.returncode, 'run_result': expected}
    if args.builtin_references:
        cards=json.loads((ROOT/'src/reading/language_reference.json').read_text())['builtin_theorems']
        cases={identity:(card['example'],True) for identity,card in cards.items()}
        cases.update({name:(content,False) for name,content in BUILTIN_REFERENCE_REJECTIONS.items()})
        for identity,(content,succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json',
                                  '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True, timeout=120)
            bundle=json.loads(run.stdout)
            expected='success' if succeeds else 'failure'
            if run.returncode!=(0 if succeeds else 1) or bundle.get('run_result')!=expected:
                raise RuntimeError(f'{identity}: unexpected builtin-reference result\n{run.stderr}')
            if not any(source.get('content')==content for source in bundle.get('sources',[])):
                raise RuntimeError(f'{identity}: builtin reference source snapshot mismatch')
            if not succeeds:
                if not any(statement.get('status')=='rejected' and statement.get('statement_kind','').endswith(('ReleaseThmStmt','ByThmStmt')) for statement in bundle.get('statements',[])):
                    raise RuntimeError(f'{identity}: expected a parsed, rejected theorem call, not a parse error')
                if not any(symbol.get('kind')=='builtin_theorem' and symbol.get('builtin_theorem',{}).get('type')=='BuiltinTheoremId' for symbol in bundle.get('symbols',[])):
                    raise RuntimeError(f'{identity}: rejected theorem has no native declaration identity')
            (args.output/f'builtin-reference-{identity}.json').write_text(run.stdout)
            report[f'builtin-reference-{identity}']={'exit':run.returncode,'run_result':expected,'exactHelpExample':succeeds}
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
    if args.forall_equality_symmetry:
        for name, case in FORALL_EQUALITY_SYMMETRY_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != case['source']:
                raise RuntimeError(f'{name}: unexpected forall equality symmetry result\n{run.stderr}')
            (args.output / f'symmetry-{name}.json').write_text(run.stdout)
            report[f'symmetry-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': True}
        project = args.output / 'forall-symmetry-book-source'
        project.mkdir(exist_ok=True)
        for name, source in FORALL_EQUALITY_SYMMETRY_BOOK.items():
            (project / name).write_text(source)
        exported = args.output / 'forall-symmetry-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        if run.returncode != 0:
            raise RuntimeError(f'forall symmetry book: export failed\n{run.stderr}')
        bundle = json.loads((exported / 'reading.json').read_text())
        if bundle.get('run_result') != 'success' or [item['content'] for item in bundle['sources']] != [value for name, value in FORALL_EQUALITY_SYMMETRY_BOOK.items() if name.endswith('.lit')]:
            raise RuntimeError('forall symmetry book: unexpected result or source mismatch')
        report['forall-symmetry-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2, 'strict': True}
    if args.unexecuted_loops:
        for name, case in UNEXECUTED_LOOP_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != case['source']:
                raise RuntimeError(f'{name}: unexpected unexecuted-loop result\n{run.stderr}')
            (args.output / f'unexecuted-loop-{name}.json').write_text(run.stdout)
            report[f'unexecuted-loop-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': True}
        project = args.output / 'unexecuted-loop-book-source'
        project.mkdir(exist_ok=True)
        for name, content in UNEXECUTED_LOOP_BOOK.items():
            (project / name).write_text(content)
        exported = args.output / 'unexecuted-loop-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        if run.returncode != 0:
            raise RuntimeError(f'numeric rewrite book: export failed\n{run.stderr}')
        bundle = json.loads((exported / 'reading.json').read_text())
        if bundle.get('run_result') != 'success' or [item['content'] for item in bundle['sources']] != [content for name, content in UNEXECUTED_LOOP_BOOK.items() if name.endswith('.lit')]:
            raise RuntimeError('numeric rewrite book: unexpected result or source mismatch')
        report['unexecuted-loop-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2, 'strict': True}
    if args.numeric_rewrites:
        for name, case in NUMERIC_REWRITE_CASES.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', case['source']], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if case['success'] else 'failure'
            if run.returncode != (0 if case['success'] else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != case['source']:
                raise RuntimeError(f'{name}: unexpected numeric-rewrite result\n{run.stderr}')
            (args.output / f'numeric-rewrite-{name}.json').write_text(run.stdout)
            report[f'numeric-rewrite-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': True}
        project = args.output / 'numeric-rewrite-book-source'
        project.mkdir(exist_ok=True)
        for name, content in TUPLE_COORDINATE_BOOK.items():
            (project / name).write_text(content)
        exported = args.output / 'numeric-rewrite-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        if run.returncode != 0:
            raise RuntimeError(f'numeric rewrite book: export failed\n{run.stderr}')
        bundle = json.loads((exported / 'reading.json').read_text())
        if bundle.get('run_result') != 'success' or [item['content'] for item in bundle['sources']] != [content for name, content in TUPLE_COORDINATE_BOOK.items() if name.endswith('.lit')]:
            raise RuntimeError('numeric rewrite book: unexpected result or source mismatch')
        report['numeric-rewrite-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2, 'strict': True}
    if args.tuple_coordinates:
        cases = {'public': ((ROOT / 'examples/infer/equal/tuple_coordinates.lit').read_text(), True), **TUPLE_COORDINATE_CASES}
        for name, (content, succeeds) in cases.items():
            run = subprocess.run([str(args.binary.resolve()), '-reading', '-json', '-strict', '-lang', 'en', '-e', content], capture_output=True, text=True)
            bundle = json.loads(run.stdout)
            expected = 'success' if succeeds else 'failure'
            if run.returncode != (0 if succeeds else 1) or bundle.get('run_result') != expected or bundle['sources'][0]['content'] != content:
                raise RuntimeError(f'{name}: unexpected tuple-coordinate result\n{run.stderr}')
            (args.output / f'tuple-coordinate-{name}.json').write_text(run.stdout)
            report[f'tuple-coordinate-{name}'] = {'exit': run.returncode, 'run_result': expected, 'strict': True}
        project = args.output / 'tuple-coordinate-book-source'
        project.mkdir(exist_ok=True)
        for name, content in TUPLE_COORDINATE_BOOK.items():
            (project / name).write_text(content)
        exported = args.output / 'tuple-coordinate-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        if run.returncode != 0:
            raise RuntimeError(f'tuple-coordinate book: export failed\n{run.stderr}')
        bundle = json.loads((exported / 'reading.json').read_text())
        if bundle.get('run_result') != 'success' or [item['content'] for item in bundle['sources']] != [content for name, content in TUPLE_COORDINATE_BOOK.items() if name.endswith('.lit')]:
            raise RuntimeError('tuple-coordinate book: unexpected result or source mismatch')
        report['tuple-coordinate-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2, 'strict': True}
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
        # Qualified, nested and repeated applications, accepted in one strict
        # Session before this reproducible export was added.
        project = args.output / 'theorem-group-book-source'
        project.mkdir(exist_ok=True)
        book_sources = {
            '01-theorems.lit': (ROOT / THEOREM_CASES['canonical']).read_text(),
            '02-uses.lit': ('release thm theorems::release_sides(2)\n\n'
                            'claim:\n'
                            '    ? 4 + 0 = 4\n'
                            '    release thm theorems::release_sides(4)\n\n'
                            'release thm theorems::release_sides(2)\n'
                            '0 + 2 = 2\n'),
        }
        for name, source in book_sources.items():
            (project / name).write_text(source)
        (project / 'litex.config').write_text('[export]\ntheorems = "./01-theorems.lit"\nuses = "./02-uses.lit"\n')
        exported = args.output / 'theorem-group-book'
        run = subprocess.run([str(args.binary.resolve()), '-reading', '-strict', '-lang', 'en', '-r', str(project), '-export', str(exported)], capture_output=True, text=True)
        if run.returncode != 0:
            raise RuntimeError(f'theorem group book: export failed\n{run.stderr}')
        bundle = json.loads((exported / 'reading.json').read_text())
        if bundle.get('run_result') != 'success' or [item['content'] for item in bundle['sources']] != list(book_sources.values()):
            raise RuntimeError('theorem group book: unexpected result or source mismatch')
        report['theorem-group-book'] = {'exit': 0, 'run_result': 'success', 'sources': 2, 'strict': True}
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
