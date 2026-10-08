//! Generated equality builtin-rule detailed projection.
use super::log_algebra_base::project_log_algebra_base;
use super::store::project_verify_facts;
use super::verify::project_verify_fact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
use crate::json_output::helper::{object_for, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::Runtime;

pub(super) fn project_equality_builtin_rule(rule: &EqualitySearchProofByBuiltinRule, runtime: &Runtime) -> JsonValue {
    match rule {
        EqualitySearchProofByBuiltinRule::ScalarExtra(p) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_extra::ScalarExtraEqualityProof as P;
            let mut entries=vec![("type",string("builtin_rule")),("rule",string(p.rule_id()))];
            match p {
                P::SqrtProductFromKnownArgument(p) => {
                    entries.push(("argument_equality",super::searched::project_equal_searched(&p.argument_equality,runtime)));
                },
                P::SqrtQuotientFromKnownArgument(p) => {
                    entries.push(("argument_equality",super::searched::project_equal_searched(&p.argument_equality,runtime)));
                },
                P::ArcsinFromKnownSine(p) => {
                    entries.push(("principal_bounds",project_verify_facts(&p.principal_bounds,runtime)));
                    entries.push(("sine_equality",super::searched::project_equal_searched(&p.sine_equality,runtime)));
                },
                P::RealLogFromKnownPower(p) => {
                    entries.push(("base_guard",project_log_algebra_base(&p.base_guard,runtime)));
                    entries.push(("exponent_real",project_verify_fact(&p.exponent_real,runtime)));
                    entries.push(("power_equality",super::searched::project_equal_searched(&p.power_equality,runtime)));
                },
                P::PositivePowerLogInverse(p) => {
                    entries.push(("base_guard",project_log_algebra_base(&p.base_guard,runtime)));
                },
                P::PositivePowerReciprocalRoot(p) => {
                    entries.push(("base_positive",project_verify_fact(&p.base_positive,runtime)));
                    entries.push(("exponent_positive_natural",project_verify_fact(&p.exponent_positive_natural,runtime)));
                },
                P::PositiveIntegerPowerInjective(p) => {
                    entries.push(("left_positive",project_verify_fact(&p.left_positive,runtime)));
                    entries.push(("right_positive",project_verify_fact(&p.right_positive,runtime)));
                    entries.push(("exponent_integer",project_verify_fact(&p.exponent_integer,runtime)));
                    entries.push(("exponent_nonzero",project_verify_fact(&p.exponent_nonzero,runtime)));
                    entries.push(("power_equality",super::searched::project_equal_searched(&p.power_equality,runtime)));
                },
                P::NestedRemainderUnit(_) => {
                },
            }
            object_for(runtime,entries)
        },

        EqualitySearchProofByBuiltinRule::IntegerInterval(p) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_integer_interval::{IntegerIntervalEqualityProof as P,IntegerBoundaryProof as B};
            let mut entries=vec![("type",string("builtin_rule")),("rule",string(p.rule_id()))];
            let (variable,boundary)=match p {
                P::SingletonAtLower(p)=>{
                    entries.push(("lower_weak",super::searched::project_known_premise(&p.lower_weak,runtime)));
                    entries.push(("upper_strict",super::searched::project_known_premise(&p.upper_strict,runtime)));
                    (&p.variable_integer,&p.boundary_integer)
                },
                P::SingletonAtUpper(p)=>{
                    entries.push(("lower_strict",super::searched::project_known_premise(&p.lower_strict,runtime)));
                    entries.push(("upper_weak",super::searched::project_known_premise(&p.upper_weak,runtime)));
                    (&p.variable_integer,&p.boundary_integer)
                },
            };
            entries.push(("variable_integer",project_verify_fact(variable,runtime)));
            entries.push(("boundary_integer",match boundary {
                B::Membership(p)=>project_verify_fact(p,runtime),
                B::Successor{predecessor,predecessor_integer}=>object_for(runtime,vec![("type",string("integer_successor")),("predecessor",string(predecessor.readable_string())),("predecessor_integer",project_verify_fact(predecessor_integer,runtime))]),
            }));
            object_for(runtime,entries)
        },

        EqualitySearchProofByBuiltinRule::FactorialPredecessor(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FactorialPredecessor")),
            ("positive_natural", project_verify_fact(&p.positive_natural, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::ExponentialLogarithmIdentity(p) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_exponential_logarithm_identities::ExponentialLogarithmIdentityProof as P;
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string(p.rule_id()))];
            match p {
                P::ExpDifference(_) => {
                },
                P::LnProduct(_) => {
                },
                P::LnQuotient(_) => {
                },
                P::ExpInjective(p) => {
                    entries.push(("left_real", project_verify_fact(&p.left_real, runtime)));
                    entries.push(("right_real", project_verify_fact(&p.right_real, runtime)));
                    entries.push(("image_equality", super::searched::project_equal_searched(&p.image_equality, runtime)));
                },
                P::LnInjective(p) => {
                    entries.push(("left_positive", project_verify_fact(&p.left_positive, runtime)));
                    entries.push(("right_positive", project_verify_fact(&p.right_positive, runtime)));
                    entries.push(("image_equality", super::searched::project_equal_searched(&p.image_equality, runtime)));
                },
                P::LogFromKnownPower(p) => {
                    entries.push(("base_proof", project_log_algebra_base(&p.base_proof, runtime)));
                    entries.push(("exponent_integer", project_verify_fact(&p.exponent_integer, runtime)));
                    entries.push(("power_equality", super::searched::project_equal_searched(&p.power_equality, runtime)));
                },
                P::PowerFromKnownLog(p) => {
                    entries.push(("base_proof", project_log_algebra_base(&p.base_proof, runtime)));
                    entries.push(("argument_positive", project_verify_fact(&p.argument_positive, runtime)));
                    entries.push(("exponent_integer", project_verify_fact(&p.exponent_integer, runtime)));
                    entries.push(("logarithm_equality", super::searched::project_equal_searched(&p.logarithm_equality, runtime)));
                },
            }
            object_for(runtime, entries)
        },

        EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(p) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_division_relations::ScalarDivisionRelationProof as P;
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string(p.rule_id()))];
            match p {
                P::ProductFromDivision(p) => {
                    entries.push(("division_equation", project_verify_fact(&p.division_equation, runtime)));
                },
                P::DivisionFromProduct(p) => {
                    entries.push(("product_equation", project_verify_fact(&p.product_equation, runtime)));
                },
            }
            object_for(runtime, entries)
        },

        EqualitySearchProofByBuiltinRule::GcdCommonDivisor(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("GcdCommonDivisor")),
            ("divisor_positive", project_verify_fact(&p.divisor_positive, runtime)),
            ("first_divisibility", project_verify_fact(&p.first_divisibility, runtime)),
            ("second_divisibility", project_verify_fact(&p.second_divisibility, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::LcmCommonMultiple(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("LcmCommonMultiple")),
            ("first_positive", project_verify_fact(&p.first_positive, runtime)),
            ("second_positive", project_verify_fact(&p.second_positive, runtime)),
            ("first_divisibility", project_verify_fact(&p.first_divisibility, runtime)),
            ("second_divisibility", project_verify_fact(&p.second_divisibility, runtime)),
        ]),

        EqualitySearchProofByBuiltinRule::TanQuotientDefinition(_) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("TanQuotientDefinition"))]),
        EqualitySearchProofByBuiltinRule::CotQuotientDefinition(_) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("CotQuotientDefinition"))]),
        EqualitySearchProofByBuiltinRule::GcdEuclideanStep(_) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("GcdEuclideanStep"))]),
        EqualitySearchProofByBuiltinRule::LcmLeftAbsDivisibility(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("LcmLeftAbsDivisibility")),
        ]),
        EqualitySearchProofByBuiltinRule::LcmRightAbsDivisibility(_) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("LcmRightAbsDivisibility")),
        ]),
        EqualitySearchProofByBuiltinRule::FiniteSetProductReindex(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FiniteSetProductReindex")),
            ("bijection", project_verify_fact(&p.bijection, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::FiniteSetReduceReindex(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FiniteSetReduceReindex")),
            ("operator_match", super::reduce_rules::project_match(&p.operator_match, runtime)),
            ("seed_match", super::reduce_rules::project_match(&p.seed_match, runtime)),
            ("bijection", project_verify_fact(&p.bijection, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::RangeSize(p) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("RangeSize")),("start_natural",project_verify_fact(&p.start_natural,runtime)),("end_natural",project_verify_fact(&p.end_natural,runtime)),("endpoint_order",project_verify_fact(&p.endpoint_order,runtime))]),
        EqualitySearchProofByBuiltinRule::ClosedRangeSize(p) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("ClosedRangeSize")),("start_natural",project_verify_fact(&p.start_natural,runtime)),("end_natural",project_verify_fact(&p.end_natural,runtime)),("endpoint_order",project_verify_fact(&p.endpoint_order,runtime))]),
        EqualitySearchProofByBuiltinRule::FactorialDivisibility(p) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("FactorialDivisibility")),("earlier_natural",project_verify_fact(&p.earlier_natural,runtime)),("later_natural",project_verify_fact(&p.later_natural,runtime)),("order",project_verify_fact(&p.order,runtime))]),
        EqualitySearchProofByBuiltinRule::EuclideanRemainder(p) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("EuclideanRemainder")),("domains",project_verify_facts(&p.domains,runtime)),("remainder_bound",project_verify_fact(&p.remainder_bound,runtime)),("decomposition",super::searched::project_equal_searched(&p.decomposition,runtime))]),

        EqualitySearchProofByBuiltinRule::ReduceFirstStep(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("ReduceFirstStep")),
            ("nonempty", super::reduce_rules::project_nonempty(&p.nonempty, runtime)),
            ("matches", super::reduce_rules::project_matches(&p.matches, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::ReduceTranslation(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("ReduceTranslation")),
            ("shift", string(p.shift.readable_string())), ("matches", super::reduce_rules::project_matches(&p.matches, runtime)),
            ("parameter", string(p.parameter.to_string())),
            ("assumptions", JsonValue::Array(p.assumptions.iter().map(|a| string(a.readable_string())).collect())),
            ("function_expansions", super::aggregate_identity::project_expansions(&p.function_expansions, runtime)),
            ("pointwise", super::reduce_rules::project_match(&p.pointwise, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::ReducePointwise(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("ReducePointwise")),
            ("matches", super::reduce_rules::project_matches(&p.matches, runtime)),
            ("certificate", super::reduce_rules::project_pointwise_certificate(&p.certificate, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::CartesianSize(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("CartesianSize")),
            ("factor_finiteness", project_verify_facts(&p.factor_finiteness, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::ReducePartition(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("ReducePartition")),
            ("bounds", project_verify_facts(&p.bounds, runtime)),
            ("matches", project_verify_facts(&p.matches, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::ReduceLastStep(p)=>object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("ReduceLastStep")),("nonempty",project_verify_fact(&p.nonempty,runtime)),("endpoint",project_verify_fact(&p.endpoint,runtime)),("result",project_verify_fact(&p.result,runtime))]),
        EqualitySearchProofByBuiltinRule::FiniteMapSize(p) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string(p.rule_id())),("certificate",super::searched::project_known_premise(p.certificate(),runtime))]),
        EqualitySearchProofByBuiltinRule::ReduceProduct(_) => object_for(runtime,vec![("type",string("builtin_rule")),("rule",string("ReduceProduct"))]),
        EqualitySearchProofByBuiltinRule::ElementaryArithmetic(p) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof as P;
            let mut entries=vec![("type",string("builtin_rule")),("rule",string(p.rule_id()))];
            match p {
                P::SqrtSquareNonpositive(p) => entries.push(("nonpositive_argument",project_verify_fact(&p.nonpositive_argument,runtime))),
                P::ModNegation {requirements} | P::ModNaturalPower {requirements} => entries.push(("requirements",project_verify_facts(requirements,runtime))),
                P::PositivePowerZero {premise,requirements} | P::PositivePowerCancellation {premise,requirements} | P::SqrtKnownSquare {premise,requirements} => {
                    entries.push(("premise",super::searched::project_equal_searched(premise,runtime)));
                    entries.push(("requirements",project_verify_facts(requirements,runtime)));
                }, P::AbsEvenPower => {},
            }
            object_for(runtime,entries)
        },
        EqualitySearchProofByBuiltinRule::TrigComplexIdentity(p) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof as P;
            let mut entries=vec![("type",string("builtin_rule")),("rule",string(p.rule_id()))];
            match p {
                P::SinThreeAngleSum(p) => {
                    entries.push(("first",string(p.first.readable_string())));
                    entries.push(("second",string(p.second.readable_string())));
                    entries.push(("third",string(p.third.readable_string())));
                },
                P::TanAddition(_) => {},
                P::ComplexModulusCoordinates(_) | P::RealPartQuotient(_) | P::ImaginaryPartQuotient(_) => {},
                P::TanCotProduct(p) => entries.push(("angle", string(p.angle.readable_string()))),
                P::TanSquareReciprocalCosine(p) => entries.push(("angle", string(p.angle.readable_string()))),
                P::CosDoubleAngle(p) => {
                    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::CosDoubleAngleForm as F;
                    entries.push(("angle", string(p.angle.readable_string())));
                    entries.push(("form", string(match p.form {
                        F::CosineSquareMinusSineSquare => "cosine_square_minus_sine_square",
                        F::OneMinusTwiceSineSquare => "one_minus_twice_sine_square",
                        F::TwiceCosineSquareMinusOne => "twice_cosine_square_minus_one",
                    })));
                },
                P::SinPiReflection(p) => entries.push(("angle", string(p.angle.readable_string()))),
                P::CosPiReflection(p) => entries.push(("angle", string(p.angle.readable_string()))),
                P::SinHalfPiReflection(p) => entries.push(("angle", string(p.angle.readable_string()))),
                P::CosHalfPiReflection(p) => entries.push(("angle", string(p.angle.readable_string()))),
                P::PeriodicTrig(p) => {
                    entries.push(("coefficient", string(p.coefficient.readable_string())));
                    entries.push(("integer_requirements", project_verify_facts(&p.integer_requirements, runtime)));
                    entries.push(("value", string(p.value.readable_string())));
                },
                P::NumericComplexModulus(p) => {
                    entries.push(("real", string(p.real.readable_string())));
                    entries.push(("imaginary", string(p.imaginary.readable_string())));
                    entries.push(("squared_modulus", string(p.squared_modulus.readable_string())));
                    entries.push(("value", string(p.value.readable_string())));
                },
                P::ComplexPowerCoordinates {natural} => entries.push(("natural",project_verify_fact(natural,runtime))),
                P::ComplexModulusZero {premise,complex} => {
                    entries.push(("premise",super::searched::project_equal_searched(premise,runtime)));
                    entries.push(("complex",project_verify_fact(complex,runtime)));
                }, P::ComplexCoordinatesEqual {real,imaginary,domains} => {
                    entries.push(("real",super::searched::project_equal_searched(real,runtime)));
                    entries.push(("imaginary",super::searched::project_equal_searched(imaginary,runtime)));
                    entries.push(("domains",project_verify_facts(domains,runtime)));
                },
                P::SinHalfPiShift(_) | P::CosHalfPiShift(_) | P::SinNegation | P::CosNegation
                | P::SinPiShift | P::CosPiShift | P::SinDoubleAngle | P::SinDifference | P::CosDifference
                | P::ComplexModulusProduct | P::ComplexReconstruction | P::RealPartAddition
                | P::ImaginaryPartAddition | P::RealPartSubtraction | P::ImaginaryPartSubtraction => {},
            }
            object_for(runtime,entries)
        },
        EqualitySearchProofByBuiltinRule::IntegerRangeBuilder(p) => object_for(runtime,vec![
            ("type",string("builtin_rule")),("rule",string(p.rule_id())),
        ]),
        EqualitySearchProofByBuiltinRule::ScalarIdentity(p) => {
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof as P;
            let mut entries=vec![("type",string("builtin_rule")),("rule",string(p.rule_id()))];
            match p {
                P::FiniteSetMaxSelection(p) => {
                    entries.push(("selected_index", JsonValue::Number(p.selected_index as f64)));
                    entries.push(("selected_member", string(p.selected_member.readable_string())));
                    entries.push(("comparisons", project_extremum_comparisons(&p.comparisons, runtime)));
                },
                P::FiniteSetMinSelection(p) => {
                    entries.push(("selected_index", JsonValue::Number(p.selected_index as f64)));
                    entries.push(("selected_member", string(p.selected_member.readable_string())));
                    entries.push(("comparisons", project_extremum_comparisons(&p.comparisons, runtime)));
                },
                P::SignZeroReflection(p) => {
                    entries.push(("real_proof", project_verify_fact(&p.real_proof, runtime)));
                    entries.push(("premise_proof", super::searched::project_equal_searched(&p.premise_proof, runtime)));
                },
                P::AbsZeroArgument(p) => {
                    entries.push(("premise_proof", super::searched::project_equal_searched(&p.premise_proof,runtime)));
                    entries.push(("real_proof", project_verify_fact(&p.real_proof,runtime)));
                },
                P::FloorIntegerTranslation(p) => entries.push(("integer_proof",project_verify_fact(&p.integer_proof,runtime))),
                P::CeilIntegerTranslation(p) => entries.push(("integer_proof",project_verify_fact(&p.integer_proof,runtime))),
                P::AbsDifferenceSymmetry(_) | P::FloorNegation(_) | P::CeilNegation(_) | P::MinMaxAbsorption(_) | P::MaxMinAbsorption(_) | P::LcmZero(_) => {},
            }
            object_for(runtime,entries)
        },
        EqualitySearchProofByBuiltinRule::AggregateIdentity(p) => super::aggregate_identity::project_aggregate_identity(p, runtime),
        EqualitySearchProofByBuiltinRule::AggregateCalculation(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("AggregateCalculation")),
            ("rewritten_left", string(p.rewritten_left.readable_string())), ("left_value", string(p.left_value.readable_string())),
            ("rewritten_right", string(p.rewritten_right.readable_string())), ("right_value", string(p.right_value.readable_string())),
            ("cited_equal_fact_ids", super::aggregate_evaluation::cites(&p.cited_equal_fact_ids)),
            ("aggregate_evaluations", super::aggregate_evaluation::project_aggregate_evaluations(&p.aggregate_evaluations, runtime)),
            ("function_evaluations", super::aggregate_evaluation::project_function_evaluations(&p.function_evaluations, runtime)),
            ("algo_evaluations", super::aggregate_evaluation::project_algo_evaluations(&p.algo_evaluations, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::Calculation(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("Calculation"))];
            let mode = match p {
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation::ClosedRational { left_normal, right_normal } => {
                    entries.push(("left_normal", string(left_normal.clone())));
                    entries.push(("right_normal", string(right_normal.clone())));
                    "closed_rational"
                },
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation::ClosedDecimal { .. } => "closed_decimal",
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation::Rational {} => "rational",
                crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::search_equal_fact_builtin_rule_result::EqualitySearchProofByCalculation::Complex {} => "complex_imaginary_unit",
            };
            entries.push(("mode", string(mode)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SinArcsinLeftInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinArcsinLeftInverse"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CosArccosLeftInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CosArccosLeftInverse"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::TanArctanLeftInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("TanArctanLeftInverse"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CotArccotLeftInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CotArccotLeftInverse"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArcsinSinRightInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArcsinSinRightInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArccosCosRightInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccosCosRightInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArctanTanRightInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArctanTanRightInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArccotCotRightInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccotCotRightInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArcsinExactZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArcsinExactOne"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArcsinExactNegOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArcsinExactNegOne"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArccosExactOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccosExactOne"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArccosExactZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccosExactZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArccosExactNegOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccosExactNegOne"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArctanExactZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArctanExactZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ArccotExactZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ArccotExactZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::NegativeIntegerPowerReciprocal(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("NegativeIntegerPowerReciprocal")),
            ("base_numeric", project_verify_fact(&p.base_numeric, runtime)),
            ("exponent_integer", project_verify_fact(&p.exponent_integer, runtime)),
            ("base_nonzero", project_verify_fact(&p.base_nonzero, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::PowerProductSameBase(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerProductSameBase"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::PowerOfPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerOfPower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::PowerOfProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerOfProduct"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReciprocalAsNegOnePower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReciprocalAsNegOnePower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::QuotientAsMulNegOnePower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("QuotientAsMulNegOnePower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::OneToAnyPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("OneToAnyPower"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ZeroToPosNatPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ZeroToPosNatPower"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtSquare(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtSquare"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtOne"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtOfSquare(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtOfSquare"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtProduct"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtQuotient(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtQuotient"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::AbsOfNegation(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsOfNegation"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::AbsProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsProduct"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::AbsSquare(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsSquare"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LogBaseSelf(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogBaseSelf"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LogOfOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogOfOne"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LogOfPowerSameBase(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LogOfPowerSameBase"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LogArgPower(p) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("rule", string("LogArgPower")),
                ("base_proof", project_log_algebra_base(&p.base_proof, runtime)),
                ("argument_positive_proof", project_verify_fact(&p.argument_positive_proof, runtime)),
            ])
        },
        EqualitySearchProofByBuiltinRule::LogProduct(p) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("rule", string("LogProduct")),
                ("base_proof", project_log_algebra_base(&p.base_proof, runtime)),
                ("left_argument_positive_proof", project_verify_fact(&p.left_argument_positive_proof, runtime)),
                ("right_argument_positive_proof", project_verify_fact(&p.right_argument_positive_proof, runtime)),
            ])
        },
        EqualitySearchProofByBuiltinRule::LogQuotient(p) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("rule", string("LogQuotient")),
                ("base_proof", project_log_algebra_base(&p.base_proof, runtime)),
                ("numerator_positive_proof", project_verify_fact(&p.numerator_positive_proof, runtime)),
                ("denominator_positive_proof", project_verify_fact(&p.denominator_positive_proof, runtime)),
            ])
        },
        EqualitySearchProofByBuiltinRule::LogReciprocal(p) => {
            object_for(runtime, vec![
                ("type", string("builtin_rule")), ("rule", string("LogReciprocal")),
                ("base_proof", project_log_algebra_base(&p.base_proof, runtime)),
                ("argument_positive_proof", project_verify_fact(&p.argument_positive_proof, runtime)),
            ])
        },
        EqualitySearchProofByBuiltinRule::LogChangeOfBase(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("LogChangeOfBase")),
            ("base_proof", project_log_algebra_base(&p.base_proof, runtime)),
            ("chosen_base_proof", project_log_algebra_base(&p.chosen_base_proof, runtime)),
            ("argument_positive_proof", project_verify_fact(&p.argument_positive_proof, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::ZeroMod(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ZeroMod"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ModOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModOne"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::OneModAtLeastTwo(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("OneModAtLeastTwo"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::NestedSameModAbsorption(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("NestedSameModAbsorption"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ModCompatibleSmallerModulus(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModCompatibleSmallerModulus"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MinIdempotent(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinIdempotent"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MaxIdempotent(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MaxIdempotent"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MinCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinCommutative"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MaxCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MaxCommutative"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::AbsAbsAbsorption(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsAbsAbsorption"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ExpOfLn(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ExpOfLn"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LnOfExp(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LnOfExp"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FloorOfInteger(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FloorOfInteger"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CeilOfInteger(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CeilOfInteger"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ModSelfZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModSelfZero"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FloorOfCeilOfInteger(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FloorOfCeilOfInteger"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CeilOfFloorOfInteger(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CeilOfFloorOfInteger"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SqrtOfSquareEqualsAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SqrtOfSquareEqualsAbs"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::QuotByOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("QuotByOne"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::QuotSelfOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("QuotSelfOne"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LcmCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LcmCommutative"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LcmIdempotentAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LcmIdempotentAbs"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::GcdCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdCommutative"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::GcdIdempotentAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdIdempotentAbs"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::GcdRightZeroAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdRightZeroAbs"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::GcdLeftZeroAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdLeftZeroAbs"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FactorialSuccessor(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FactorialSuccessor"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsNonnegEqualsSelf"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::AbsNonposEqualsNegation(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsNonposEqualsNegation"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SignOfPositive(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignOfPositive"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SignOfNegative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignOfNegative"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MaxRightWhenLessEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MaxRightWhenLessEqual"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MaxLeftWhenLessEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MaxLeftWhenLessEqual"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MinLeftWhenLessEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinLeftWhenLessEqual"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MinRightWhenLessEqual(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinRightWhenLessEqual"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::GcdDividesArgument(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("GcdDividesArgument"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ProductModFactorZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ProductModFactorZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EqualityFromTwoSidedWeakOrder"))];
            entries.push(("left_le_right_proof", super::searched::project_known_premise(&p.left_le_right_proof, runtime)));
            entries.push(("right_le_left_proof", super::searched::project_known_premise(&p.right_le_left_proof, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::DiffZeroFromEqualOperands(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("DiffZeroFromEqualOperands"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EqualFromKnownDifferenceZero"))];
            entries.push(("cite_fact_id", string(p.cite_fact_id.to_string())));
            if let Some(fact) = runtime.fact_by_id_in_stack(p.cite_fact_id) { entries.push(("cite", string(fact.readable_string()))); }
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ZeroProductCancel(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ZeroProductCancel"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SignOfNegation(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignOfNegation"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SignTimesAbsEqualsArg(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignTimesAbsEqualsArg"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::AbsEqualsSignTimesArg(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("AbsEqualsSignTimesArg"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SignOfProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SignOfProduct"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SubtractionFromKnownAddition"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::QuotEuclideanDecomposition(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("QuotEuclideanDecomposition"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ModDividendMinusRemainderZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModDividendMinusRemainderZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SquareSumComponentZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SquareSumComponentZero"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::MinusOneOddNaturalPower(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("MinusOneOddNaturalPower"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LcmGcdProductAbs(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LcmGcdProductAbs"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::UnionEmptyRight(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionEmptyRight"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::UnionEmptyLeft(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionEmptyLeft"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectEmptyRight(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectEmptyRight"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectEmptyLeft(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectEmptyLeft"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusSelfEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusSelfEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusEmptyRight(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusEmptyRight"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusEmptyLeft(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusEmptyLeft"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::UnionCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionCommutative"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectCommutative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectCommutative"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::UnionIdempotent(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionIdempotent"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectIdempotent(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectIdempotent"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectFromSubset(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectFromSubset"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::EmptySetFromNotNonempty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EmptySetFromNotNonempty"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::PowerSetFiniteSetSize(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerSetFiniteSetSize"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::UnionAssociative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionAssociative"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectAssociative(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectAssociative"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectUnionDistributive(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectUnionDistributive"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusUnionDeMorgan(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusUnionDeMorgan"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusIntersectDeMorgan(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusIntersectDeMorgan"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IntersectSetMinusSelfEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IntersectSetMinusSelfEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetProductEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetProductEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetReduceEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetReduceEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReduceEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReduceEmpty"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SumEmptyRange(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SumEmptyRange"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ProductEmptyRange(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ProductEmptyRange"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::UnionAbsorptionFromSubset(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionAbsorptionFromSubset"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusRecoversSubset(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusRecoversSubset"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::EmptySetFromSizeZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EmptySetFromSizeZero"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetEqualFromSubsetSize(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")),
            ("rule", string("FiniteSetEqualFromSubsetSize")),
            ("size_equal_proof", project_verify_fact(&p.size_equal_proof, runtime)),
            ("subset_proof", project_verify_fact(&p.subset_proof, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::FiniteSetSizeSetMinus(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSizeSetMinus"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSizeUnion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSizeUnion"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ClosedRangeSingletonListSet(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ClosedRangeSingletonListSet"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SumSingleTerm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SumSingleTerm"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ProductSingleTerm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ProductSingleTerm"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReduceAddZeroEqualsSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReduceAddZeroEqualsSum"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetReduceAddZeroEqualsSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetReduceAddZeroEqualsSum"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::PowOfLogInverse(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowOfLogInverse"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::UnionSetMinusDecomposition(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionSetMinusDecomposition"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusIntersectSelf(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusIntersectSelf"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfImaginaryUnit(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfImaginaryUnit"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfImaginaryUnit(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfImaginaryUnit"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfRealEmbedding(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfRealEmbedding"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealEmbedding(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfRealEmbedding"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfRealPlusI(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfRealPlusI"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusI(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfRealPlusI"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImaginaryUnit(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ComplexAbsOfImaginaryUnit"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ModNestedDivisibleAbsorption(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ModNestedDivisibleAbsorption"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SumSplitLastTerm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SumSplitLastTerm"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ProductSplitLastTerm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ProductSplitLastTerm"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumListExpansion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumListExpansion"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetProductListExpansion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetProductListExpansion"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LnAsEulerLog(_) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("LnAsEulerLog"))]),
        EqualitySearchProofByBuiltinRule::ExpAsEulerPower(_) => object_for(runtime, vec![("type", string("builtin_rule")), ("rule", string("ExpAsEulerPower"))]),
        EqualitySearchProofByBuiltinRule::EulerEqualsExpOne(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("EulerEqualsExpOne"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LnOfEuler(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("LnOfEuler"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfReal(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfReal"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfReal(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfReal"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReOfRealPlusImagScaled(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfRealPlusImagScaled"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfRealPlusImagScaled(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfRealPlusImagScaled"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfNonnegReal(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ComplexAbsOfNonnegReal"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsOfImagScaled(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ComplexAbsOfImagScaled"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ClosedRangeLiteralExpansion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ClosedRangeLiteralExpansion"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::RangeLiteralExpansion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("RangeLiteralExpansion"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::PowerSetOfEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerSetOfEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::PowerSetOfSingleton(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PowerSetOfSingleton"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FamilyUnionOfEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FamilyUnionOfEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FamilyUnionOfSingleton(p) => {
            let entries = vec![("type", string("builtin_rule")), ("rule", string("FamilyUnionOfSingleton")),
                ];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FamilyUnionOfPowerSet(p) => {
            let entries = vec![("type", string("builtin_rule")), ("rule", string("FamilyUnionOfPowerSet")),
                ];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CartWithEmptyFactor(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CartWithEmptyFactor"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::UnionOverIntersectDistributive(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("UnionOverIntersectDistributive"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetMinusChainToUnion(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetMinusChainToUnion"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FnRangeOfConstantAnonymousFn"))];
            entries.push(("source", super::function_domain::project_source(&p.source, runtime)));
            entries.push(("domain_comparison", super::function_domain::project_domain_nonempty(&p.domain_nonempty, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FnRangeOfEmptyDomain(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("FnRangeOfEmptyDomain")),
            ("source", super::function_domain::project_source(&p.source, runtime)),
            ("domain_comparison", super::function_domain::project_domain_empty(&p.domain_empty, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::EmptyFunctionGraph(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("EmptyFunctionGraph")),
            ("source", super::function_domain::project_source(&p.source, runtime)),
            ("domain_comparison", super::function_domain::project_domain_empty(&p.domain_empty, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::EmptyDomainFunctionSpaceSingleton(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("EmptyDomainFunctionSpaceSingleton")),
            ("return_space", string(p.source_space.readable_string())),
            ("source_signature", string(crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(p.signature.clone())).readable_string())),
            ("domain_comparison", super::function_domain::project_domain_empty(&p.domain_empty, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::SeqEqualsFnOnNPos(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SeqEqualsFnOnNPos"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSeqEqualsFnOnOneBasedDomain(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSeqEqualsFnOnOneBasedDomain"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IndexUnionEmptyIndex(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IndexUnionEmptyIndex"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IndexIntersectEmptyIndex(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IndexIntersectEmptyIndex"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IndexCartEmptyIndex(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IndexCartEmptyIndex"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::IndexUnionSingleton(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("IndexUnionSingleton"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSeqZeroEqualsFnOnEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSeqZeroEqualsFnOnEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SetBuilderObviouslyEmpty(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SetBuilderObviouslyEmpty"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ComplexAbsSquaredOfRectForm(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ComplexAbsSquaredOfRectForm"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ExpOfSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ExpOfSum"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::LogBasePower(p) => object_for(runtime, vec![
            ("type", string("builtin_rule")), ("rule", string("LogBasePower")),
            ("base_proof", project_log_algebra_base(&p.base_proof, runtime)),
            ("exponent_real", project_verify_fact(&p.exponent_real, runtime)),
            ("exponent_nonzero", project_verify_fact(&p.exponent_nonzero, runtime)),
            ("argument_positive_proof", project_verify_fact(&p.argument_positive_proof, runtime)),
        ]),
        EqualitySearchProofByBuiltinRule::ReOfProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReOfProduct"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ImgOfProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ImgOfProduct"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SinOfSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinOfSum"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CosOfSum(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CosOfSum"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::ReduceSingleTermWithAddZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("ReduceSingleTermWithAddZero"))];
            entries.push(("proof_of_requirement_facts", project_verify_facts(&p.proof_of_requirement_facts, runtime)));
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumFubiniSwap(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumFubiniSwap"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::FiniteSetSumOverCartesianProduct(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("FiniteSetSumOverCartesianProduct"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SinOfZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinOfZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CosOfZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CosOfZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::TanOfZero(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("TanOfZero"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SinOfHalfPi(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinOfHalfPi"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CosOfPi(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CosOfPi"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::SinOfPi(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("SinOfPi"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::CotOfHalfPi(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("CotOfHalfPi"))];
            let _ = p;
            object_for(runtime, entries)
        },
        EqualitySearchProofByBuiltinRule::PythagoreanIdentity(p) => {
            let mut entries = vec![("type", string("builtin_rule")), ("rule", string("PythagoreanIdentity"))];
            let _ = p;
            object_for(runtime, entries)
        },
    }
}

fn project_extremum_comparisons(
    comparisons: &[crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ExactExtremumComparison],
    runtime: &Runtime,
) -> JsonValue {
    use crate::rational_expression::NumberCompareResult;
    let mut values = Vec::new();
    for comparison in comparisons {
        let ordering = match comparison.ordering {
            NumberCompareResult::Less => "less",
            NumberCompareResult::Equal => "equal",
            NumberCompareResult::Greater => "greater",
        };
        values.push(object_for(runtime, vec![
            ("member", string(comparison.member.readable_string())),
            ("member_normal", string(comparison.member_normal.readable_string())),
            ("selected_normal", string(comparison.selected_normal.readable_string())),
            ("ordering", string(ordering)),
        ]));
    }
    JsonValue::Array(values)
}
