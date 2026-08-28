//! Direct compilation diagnostics and algebraic normalization evidence.

use super::super::*;

pub(in super::super) fn describe_success_fact_result_for_direct_compilation_audit(
    result: &SuccessFactStmtResult,
) -> String {
    let proof = match result.proof() {
        SuccessFactProofResult::BuiltinRule(proof) => format!(
            "BuiltinRule evidence={:?}, subgoals={}",
            proof.evidence,
            proof.subgoals.len()
        ),
        SuccessFactProofResult::BuiltinStrategy(proof) => format!(
            "BuiltinStrategy evidence={:?}, subgoals={}",
            proof.evidence,
            proof.subgoals.len()
        ),
        SuccessFactProofResult::StoredFactCitation(_) => "StoredFactCitation".to_string(),
        SuccessFactProofResult::KnownForallInstantiation(_) => {
            "KnownForallInstantiation".to_string()
        }
        SuccessFactProofResult::DefinitionReduction(_) => "DefinitionReduction".to_string(),
        SuccessFactProofResult::CheckedFunctionDefinitionReduction(_) => {
            "CheckedFunctionDefinitionReduction".to_string()
        }
        SuccessFactProofResult::DiagnosticOnly(_) => "DiagnosticOnly".to_string(),
        SuccessFactProofResult::CombinedProofs(proof) => {
            format!(
                "CombinedProofs primary={}, steps={}",
                proof.primary.is_some(),
                proof.steps.len()
            )
        }
        SuccessFactProofResult::ForallProof(proof) => {
            let assumption_rules = proof
                .assumption_infers
                .rule_applications
                .iter()
                .map(|application| infer_rule_name(&application.rule))
                .collect::<Vec<_>>();
            let conclusion_shapes = proof
                .proves
                .iter()
                .map(|proved| {
                    proved
                        .result
                        .factual_success()
                        .map(|result| match result.proof() {
                            SuccessFactProofResult::BuiltinRule(proof) => format!(
                                "BuiltinRule({:?}, subgoals={})",
                                proof.evidence,
                                proof.subgoals.len()
                            ),
                            SuccessFactProofResult::BuiltinStrategy(proof) => format!(
                                "BuiltinStrategy({:?}, subgoals={})",
                                proof.evidence,
                                proof.subgoals.len()
                            ),
                            SuccessFactProofResult::StoredFactCitation(_) => {
                                "StoredFactCitation".to_string()
                            }
                            SuccessFactProofResult::KnownForallInstantiation(_) => {
                                "KnownForallInstantiation".to_string()
                            }
                            SuccessFactProofResult::DefinitionReduction(_) => {
                                "DefinitionReduction".to_string()
                            }
                            SuccessFactProofResult::CheckedFunctionDefinitionReduction(_) => {
                                "CheckedFunctionDefinitionReduction".to_string()
                            }
                            SuccessFactProofResult::DiagnosticOnly(_) => {
                                "DiagnosticOnly".to_string()
                            }
                            SuccessFactProofResult::CombinedProofs(proof) => {
                                format!(
                                    "CombinedProofs(primary={}, steps={})",
                                    proof.primary.is_some(),
                                    proof.steps.len()
                                )
                            }
                            SuccessFactProofResult::ForallProof(_) => {
                                "NestedForallProof".to_string()
                            }
                            SuccessFactProofResult::Transform(_) => "Transform".to_string(),
                            SuccessFactProofResult::Reuse(_) => "Reuse".to_string(),
                        })
                        .unwrap_or_else(|| "NonFactual".to_string())
                })
                .collect::<Vec<_>>();
            format!(
                "ForallProof parameter_stores={}, assumption_rules={assumption_rules:?}, conclusions={conclusion_shapes:?}",
                proof.assumption_infers.store_fact_outputs.len(),
            )
        }
        SuccessFactProofResult::Transform(_) => "Transform".to_string(),
        SuccessFactProofResult::Reuse(_) => "Reuse".to_string(),
    };
    format!(
        "{proof}; infer_rules={}, stores={}",
        result.store.infers.rule_applications.len(),
        result.store.infers.store_fact_outputs.len()
    )
}

/// Keep direct builtin coverage compile-time exhaustive. Returning `None`
/// means the evidence has a direct Result consumer above. A named limitation
/// is an intentional fail-closed boundary, never permission to fall through
/// to a generic or diagnostic proof builder. Adding a new `BuiltinRuleEvidence` variant
/// therefore requires an explicit compiler decision here.
pub(in super::super) fn direct_builtin_rule_compiler_limitation(
    evidence: &BuiltinRuleEvidence,
) -> Option<String> {
    match evidence {
        BuiltinRuleEvidence::Uncatalogued(rule) => Some(format!(
            "builtin rule `{}` has no reviewed ToLean mapping",
            rule.rule_id()
        )),
        BuiltinRuleEvidence::MatrixExpressionMembership(_) => Some(
            "StmtResultToLeanCompiler does not yet represent native matrix expressions in the Lean target ABI".to_string(),
        ),
        BuiltinRuleEvidence::DivNotEqualZero(_) => Some(
            "StmtResultToLeanCompiler cannot yet replay builtin rule `nonzero.div` until Litex.Same has a reviewed numeric-observation elimination theorem".to_string(),
        ),
        BuiltinRuleEvidence::Nonzero(rule) => Some(match rule {
            NonzeroBuiltinRule::Mul => {
                "StmtResultToLeanCompiler cannot yet replay builtin rule `nonzero.mul` until Litex.Same has a reviewed numeric-observation elimination theorem".to_string()
            }
        }),
        BuiltinRuleEvidence::NotEqualFromStrictOrder => Some(
            "StmtResultToLeanCompiler cannot yet replay strict-order inequality until Litex.Same has a reviewed numeric-observation elimination theorem".to_string(),
        ),
        BuiltinRuleEvidence::DefinitionProjection(_)
        | BuiltinRuleEvidence::SetBuilderMembership(_)
        | BuiltinRuleEvidence::FunctionSetMembership(_)
        | BuiltinRuleEvidence::TupleCartesianMembership(_)
        | BuiltinRuleEvidence::IntegerRangeSumPointwiseOrder(_)
        | BuiltinRuleEvidence::RefinedNumericMembership(_)
        | BuiltinRuleEvidence::ClosedNumericMembership(_)
        | BuiltinRuleEvidence::ClosedNumericNonmembership(_)
        | BuiltinRuleEvidence::ClosedNumericComparison(_)
        | BuiltinRuleEvidence::OrderReflexivity(_)
        | BuiltinRuleEvidence::RuntimeResolvedNumericComparison(_)
        | BuiltinRuleEvidence::RegisteredReflexivePredicate(_)
        | BuiltinRuleEvidence::RegisteredSymmetricPredicate(_)
        | BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(_)
        | BuiltinRuleEvidence::ObjectReflexivity(_)
        | BuiltinRuleEvidence::RationalNormalization(_)
        | BuiltinRuleEvidence::RationalAlgebraicNormalization(_)
        | BuiltinRuleEvidence::ComplexAlgebraicNormalization(_)
        | BuiltinRuleEvidence::AbsoluteValue(_)
        | BuiltinRuleEvidence::Extrema(_)
        | BuiltinRuleEvidence::Aggregate(_)
        | BuiltinRuleEvidence::StructuralDefinitionCongruence(_)
        | BuiltinRuleEvidence::StructuralKnownEqualityCongruence(_)
        | BuiltinRuleEvidence::IntegralPolynomialNormalization(_)
        | BuiltinRuleEvidence::StandardSetNonempty(_)
        | BuiltinRuleEvidence::LiteralSetNonempty
        | BuiltinRuleEvidence::SetBuilderSubsetBase
        | BuiltinRuleEvidence::DisjunctionIntroduction(_)
        | BuiltinRuleEvidence::FunctionApplicationReturnMembership(_)
        | BuiltinRuleEvidence::KnownEqualityPath(_)
        | BuiltinRuleEvidence::Arithmetic(_)
        | BuiltinRuleEvidence::IntegerMembershipClosure(_)
        | BuiltinRuleEvidence::IntegerRangeSumMembership
        | BuiltinRuleEvidence::NaturalMembershipClosure(_)
        | BuiltinRuleEvidence::RationalMembershipClosure(_)
        | BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(_)
        | BuiltinRuleEvidence::RealArithmeticMembershipClosure(_)
        | BuiltinRuleEvidence::NativeConstantMembership(_)
        | BuiltinRuleEvidence::NotEqualSymmetry
        | BuiltinRuleEvidence::SetRelationDuality(_)
        | BuiltinRuleEvidence::Set(_)
        | BuiltinRuleEvidence::FiniteSet(_)
        | BuiltinRuleEvidence::ListSetMembership(_)
        | BuiltinRuleEvidence::TupleLiteralShape
        | BuiltinRuleEvidence::PrimeU64Reflection
        | BuiltinRuleEvidence::CoprimeNaturalReflection
        | BuiltinRuleEvidence::StandardSetMembershipProjection
        | BuiltinRuleEvidence::StandardSetSubset => None,
        BuiltinRuleEvidence::LiteralSetSubset => None,
    }
}

pub(in super::super) fn validate_complex_algebraic_normalization_builtin_rule_evidence(
    target: &Fact,
    evidence: &ComplexAlgebraicNormalizationBuiltinRuleEvidence,
) -> Result<(), String> {
    if evidence.expected_target.to_string() != target.to_string() {
        return Err("complex-algebraic-normalization evidence changed its target".into());
    }
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
        return Err("complex-algebraic-normalization evidence targets a non-equality fact".into());
    };
    if !objs_equal_by_complex_rational_expression_evaluation(&equality.left, &equality.right) {
        return Err(
            "complex-algebraic-normalization evidence does not reproduce its exact equality".into(),
        );
    }
    let zero: Obj = Number::new("0".to_string()).into();
    let reproduced_nonzero_premises =
        complex_algebraic_normalization_nonzero_requirements(&equality.left, &equality.right)
            .into_iter()
            .map(|object| {
                Fact::from(AtomicFact::NotEqualFact(NotEqualFact::new(
                    object,
                    zero.clone(),
                    equality.line_file.clone(),
                )))
            })
            .collect::<Vec<_>>();
    if reproduced_nonzero_premises.len() != evidence.expected_nonzero_premises.len()
        || reproduced_nonzero_premises
            .iter()
            .zip(evidence.expected_nonzero_premises.iter())
            .any(|(reproduced, retained)| reproduced.to_string() != retained.to_string())
    {
        return Err(
            "complex-algebraic-normalization evidence changed its ordered nonzero premises".into(),
        );
    }
    Ok(())
}

pub(in super::super) fn validate_rational_algebraic_normalization_builtin_rule_evidence(
    target: &Fact,
    evidence: &RationalAlgebraicNormalizationBuiltinRuleEvidence,
) -> Result<(), String> {
    if evidence.expected_target.to_string() != target.to_string() {
        return Err("rational-algebraic-normalization evidence changed its target".into());
    }
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
        return Err("rational-algebraic-normalization evidence targets a non-equality fact".into());
    };
    if !objs_equal_by_rational_expression_evaluation(&equality.left, &equality.right) {
        return Err(
            "rational-algebraic-normalization evidence does not reproduce its exact equality"
                .into(),
        );
    }
    let zero: Obj = Number::new("0".to_string()).into();
    let reproduced_nonzero_premises =
        algebraic_normalization_nonzero_requirements(&equality.left, &equality.right)
            .into_iter()
            .map(|object| {
                Fact::from(AtomicFact::NotEqualFact(NotEqualFact::new(
                    object,
                    zero.clone(),
                    equality.line_file.clone(),
                )))
            })
            .collect::<Vec<_>>();
    if reproduced_nonzero_premises.len() != evidence.expected_nonzero_premises.len()
        || reproduced_nonzero_premises
            .iter()
            .zip(evidence.expected_nonzero_premises.iter())
            .any(|(reproduced, retained)| reproduced.to_string() != retained.to_string())
    {
        return Err(
            "rational-algebraic-normalization evidence changed its ordered nonzero premises".into(),
        );
    }
    Ok(())
}
