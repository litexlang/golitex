use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourcePosition, SourceOwner};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::VerifyEqualitySuccess;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_elementary_arithmetic::ElementaryArithmeticProof;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_equality_result(
        &self,
        result: &VerifyEqualityResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        match result {
            VerifyEqualityResult::Success(success) => {
                self.compile_equality_success(success, position)
            }
            VerifyEqualityResult::Failed(_) => Err(LeanCompileError::new(
                "Equality/Failed",
                "Failed verification is not proof evidence.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_equality_success(
        &self,
        success: &VerifyEqualitySuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let bindings =
            self.compile_equal_wd_locals(&success.fact, &success.well_defined_proof, position)?;
        let locals = SourcePosition::new(
            position.parent,
            SourceOwner::EqualWDLocals(&success.well_defined_proof, 2),
            2,
        );
        let formed = SourcePosition {
            parent: Some(&locals),
            before: 2,
            ..*position
        };
        let position = &formed;
        let left = self.compile_object_reference(&success.fact.left, position)?;
        let right = self.compile_object_reference(&success.fact.right, position)?;
        let proof = self.compile_equality_search_with_parent_wd(
            &success.fact,
            &success.searched_proof,
            Some(&success.well_defined_proof),
            position,
        )?;
        Ok((
            Self::scope_equal_wd(format!("Litex.Same {left} {right}"), &bindings),
            Self::scope_equal_wd_proof(format!("Litex.Same {left} {right}"), proof, &bindings),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_equal_wd_locals(
        &self,
        fact: &EqualFact,
        wd: &EqualFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut bindings = Vec::new();
        for (index, (object, child)) in [(&fact.left, &wd.left), (&fact.right, &wd.right)]
            .into_iter()
            .enumerate()
        {
            ensure_object(object, child)?;
            let prior =
                SourcePosition::new(Some(position), SourceOwner::EqualWDLocals(wd, index), index);
            let term = self.compile_wd(child, &prior)?;
            if !matches!(
                object,
                Obj::Identifier(_) | Obj::Literal(_) | Obj::StandardSet(_)
            ) {
                bindings.push(format!(
                    "let {} := {term}",
                    prior.equal_wd_child_name(index)
                ));
            }
        }
        Ok(bindings)
    }

    pub(in crate::compile_to_lean) fn scope_equal_wd(term: String, bindings: &[String]) -> String {
        if bindings.is_empty() {
            term
        } else {
            format!(
                "(by\n  {}\n  exact {})",
                bindings.join("\n").replace('\n', "\n  "),
                term.replace('\n', "\n  ")
            )
        }
    }

    pub(in crate::compile_to_lean) fn scope_equal_wd_proof(
        proposition: String,
        proof: String,
        bindings: &[String],
    ) -> String {
        if !bindings.iter().any(|binding| {
            let name = binding
                .strip_prefix("let ")
                .unwrap()
                .split_whitespace()
                .next()
                .unwrap();
            proof
                .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .any(|token| token == name)
        }) {
            return proof;
        }
        // A proof can be the receiver of .trans, with no expected type yet.
        // Term lets and an explicit inner type remain inferable in that position.
        format!(
            "({};\n(show {proposition} from {proof}))",
            bindings.join(";\n")
        )
    }

    pub(in crate::compile_to_lean) fn compile_equality_search(
        &self,
        fact: &EqualFact,
        proof: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_equality_search_with_parent_wd(fact, proof, None, position)
    }

    pub(in crate::compile_to_lean) fn compile_equality_search_with_parent_wd(
        &self,
        fact: &EqualFact,
        proof: &EqualFactSearchedProof,
        parent_wd: Option<&EqualFactWellDefinedProof>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        // Both parent-WD callers have already compiled and matched the original
        // endpoint certificates. Bare searched proofs still need these checks.
        if parent_wd.is_none() {
            self.compile_object_reference(&fact.left, position)?;
            // Identical ASTs at this same cursor resolve the same original
            // producer. Keep the full second check when only their IR agrees.
            if fact.left != fact.right {
                self.compile_object_reference(&fact.right, position)?;
            }
        }
        let proof = match proof {
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_)) => {
                if fact.left.ir() != fact.right.ir() {
                    return Err(LeanCompileError::new(
                        "SameIr",
                        "Identity evidence has different endpoints.",
                    ));
                }
                // Endpoint formation has already consumed its original WD.
                // Infer only M.Value from the equality's expected type, avoiding
                // a second copy of the complete object and its certificates.
                "(show @Eq M.Value _ _ from Eq.refl _)".to_string()
            }
            EqualFactSearchedProof::ByTheyAreTheSame(
                proof @ TheyAreTheSameProof::SameFreeParamShape(_),
            ) => self.compile_identity(&fact.left, &fact.right, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::TrigComplexIdentity(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof::PeriodicTrig(p))) => self.compile_periodic_trig(fact, p, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SinArcsinLeftInverse(_)) => self.compile_trig_left_inverse(fact, "Sin", "Arcsin", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::CosArccosLeftInverse(_)) => self.compile_trig_left_inverse(fact, "Cos", "Arccos", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::TanArctanLeftInverse(_)) => self.compile_trig_left_inverse(fact, "Tan", "Arctan", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::CotArccotLeftInverse(_)) => self.compile_trig_left_inverse(fact, "Cot", "Arccot", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArcsinExactZero(_)) => self.compile_inverse_trig_exact(fact, "Arcsin", 0, None, "Real.arcsin_zero", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArcsinExactOne(_)) => self.compile_inverse_trig_exact(fact, "Arcsin", 1, Some((1, 2)), "Real.arcsin_one", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArcsinExactNegOne(_)) => self.compile_inverse_trig_exact(fact, "Arcsin", -1, Some((-1, 2)), "Real.arcsin_neg_one", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArccosExactOne(_)) => self.compile_inverse_trig_exact(fact, "Arccos", 1, None, "Real.arccos_one", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArccosExactZero(_)) => self.compile_inverse_trig_exact(fact, "Arccos", 0, Some((1, 2)), "Real.arccos_zero", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArccosExactNegOne(_)) => self.compile_inverse_trig_exact(fact, "Arccos", -1, Some((1, 1)), "Real.arccos_neg_one", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArctanExactZero(_)) => self.compile_inverse_trig_exact(fact, "Arctan", 0, None, "Real.arctan_zero", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ArccotExactZero(_)) => self.compile_inverse_trig_exact(fact, "Arccot", 0, Some((1, 2)), "Real.arctan_zero", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ReciprocalTrig(p)) => self.compile_reciprocal_trig(fact, p, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::CotQuotientDefinition(_)) => self.compile_reciprocal_trig_definition(fact, "Cot", position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::PythagoreanIdentity(_)) => self.compile_trig_identity(fact, false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::TanQuotientDefinition(_)) => self.compile_trig_identity(fact, true, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::TrigComplexIdentity(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof::ComplexReconstruction)) => self.compile_complex_reconstruction(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Conjugation(p)) => self.compile_conjugate_identity(fact, p, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::TrigComplexIdentity(crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_trig_complex_identities::TrigComplexIdentityProof::ComplexModulusProduct)) => self.compile_complex_modulus_product(fact,position)?,
            EqualFactSearchedProof::ByClosedCalculation(proof) => {
                self.compile_closed_equality(fact, proof, position)?
            }
            EqualFactSearchedProof::ByKnownSpecialProperty(proof) => {
                self.compile_equality_known_special_property(fact, proof, position)?
            }
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ScalarIdentity(p @ (ScalarIdentityBuiltinRuleProof::FiniteSetMaxSelection(_) | ScalarIdentityBuiltinRuleProof::FiniteSetMinSelection(_)))) => self.compile_finite_extremum_selection(fact, p, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::AbsNonnegEqualsSelf(proof),
            ) => self.compile_abs_nonnegative_identity(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::MinIdempotent(_),
            ) => self.compile_min_max_identity(fact, false, false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::FactorialSuccessor(p),
            ) => self.compile_factorial_step(
                fact,
                false,
                &p.proof_of_requirement_facts.iter().collect::<Vec<_>>(),
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::FactorialPredecessor(p),
            ) => self.compile_factorial_step(fact, true, &[&p.positive_natural], position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::GcdCommutative(_),
            ) => self.compile_gcd_lcm_commutative(fact, false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::LcmCommutative(_),
            ) => self.compile_gcd_lcm_commutative(fact, true, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::GcdIdempotentAbs(_),
            ) => self.compile_gcd_lcm_self_abs(fact, false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::LcmIdempotentAbs(_),
            ) => self.compile_gcd_lcm_self_abs(fact, true, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::GcdRightZeroAbs(p),
            ) => self.compile_gcd_zero_abs(fact, false, &p.proof_of_requirement_facts, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::GcdLeftZeroAbs(p),
            ) => self.compile_gcd_zero_abs(fact, true, &p.proof_of_requirement_facts, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::GcdEuclideanStep(_),
            ) => self.compile_gcd_euclidean_step(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::LcmGcdProductAbs(_),
            ) => self.compile_gcd_lcm_product(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::QuotEuclideanDecomposition(_),
            ) => self.compile_quot_decomposition(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::QuotByOne(
                _,
            )) => self.compile_quot_identity(fact, false, &[], position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::QuotSelfOne(p),
            ) => self.compile_quot_identity(fact, true, &p.proof_of_requirement_facts, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::FloorOfInteger(p),
            ) => self.compile_rounding_integer_identity(
                fact,
                false,
                false,
                &p.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::CeilOfInteger(p),
            ) => self.compile_rounding_integer_identity(
                fact,
                true,
                false,
                &p.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::FloorOfCeilOfInteger(p),
            ) => self.compile_rounding_integer_identity(
                fact,
                false,
                true,
                &p.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::CeilOfFloorOfInteger(p),
            ) => self.compile_rounding_integer_identity(
                fact,
                true,
                true,
                &p.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SignOfPositive(proof),
            ) => {
                self.compile_sign_identity(fact, true, &proof.proof_of_requirement_facts, position)?
            }
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SignOfNegative(proof),
            ) => self.compile_sign_identity(
                fact,
                false,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SignOfNegation(_),
            ) => self.compile_sign_negation(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SignOfProduct(_),
            ) => self.compile_sign_product(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SignTimesAbsEqualsArg(_),
            ) => self.compile_sign_abs_identity(fact, false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::AbsEqualsSignTimesArg(_),
            ) => self.compile_sign_abs_identity(fact, true, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::MaxIdempotent(_),
            ) => self.compile_min_max_identity(fact, true, false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::MinCommutative(_),
            ) => self.compile_min_max_identity(fact, false, true, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::MaxCommutative(_),
            ) => self.compile_min_max_identity(fact, true, true, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::MinLeftWhenLessEqual(proof),
            ) => self.compile_min_max_selection(
                fact,
                false,
                true,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::MinRightWhenLessEqual(proof),
            ) => self.compile_min_max_selection(
                fact,
                false,
                false,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::MaxLeftWhenLessEqual(proof),
            ) => self.compile_min_max_selection(
                fact,
                true,
                true,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::MaxRightWhenLessEqual(proof),
            ) => self.compile_min_max_selection(
                fact,
                true,
                false,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SqrtSquare(proof),
            ) => self.compile_sqrt_square(fact, &proof.proof_of_requirement_facts, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
                    ElementaryArithmeticProof::AbsEvenPower,
                ),
            ) => self.compile_abs_even_power_identity(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::PowerProductSameBase(proof),
            ) => self.compile_natural_power_product(
                fact,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::PowerOfPower(proof),
            ) => self.compile_natural_power_of_power(
                fact,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::AddZeroRightFromEqualities(proof),
            ) => self.compile_add_zero_from_equalities(
                fact,
                &proof.remaining_equal,
                &proof.zero_equal,
                proof.reversed,
                false,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::AddZeroLeftFromEqualities(proof),
            ) => self.compile_add_zero_from_equalities(
                fact,
                &proof.remaining_equal,
                &proof.zero_equal,
                proof.reversed,
                true,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Calculation(
                    EqualitySearchProofByCalculation::Complex {},
                ),
            ) => self.compile_complex_polynomial(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Calculation(
                    EqualitySearchProofByCalculation::Rational {},
                ),
            ) => self.compile_rational(fact, &[], &[], false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Calculation(
                    proof @ (EqualitySearchProofByCalculation::ClosedDecimal { .. }
                    | EqualitySearchProofByCalculation::ClosedRational { .. }),
                ),
            ) => self.compile_builtin_closed_equality(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(proof),
            ) => self.compile_scalar_division_relation(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::EqualFromKnownDifferenceZero(proof),
            ) => self.compile_equal_from_known_difference_zero(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::EqualityFromTwoSidedWeakOrder(proof),
            ) => self.compile_order_antisymmetry(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ElementaryArithmetic(
                    ElementaryArithmeticProof::PositivePowerZero {
                        premise,
                        requirements,
                    },
                ),
            ) => self.compile_positive_power_zero(fact, premise, requirements, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ZeroProductCancel(proof),
            ) => {
                self.compile_zero_product_cancel(fact, &proof.proof_of_requirement_facts, position)?
            }
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::DiffZeroFromEqualOperands(proof),
            ) => self.compile_difference_zero_from_equal(
                fact,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::SubtractionFromKnownAddition(proof),
            ) => self.compile_subtraction_from_addition(
                fact,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                rule @ (EqualitySearchProofByBuiltinRule::IntersectCommutative(_)
                | EqualitySearchProofByBuiltinRule::UnionCommutative(_)
                | EqualitySearchProofByBuiltinRule::IntersectIdempotent(_)
                | EqualitySearchProofByBuiltinRule::UnionIdempotent(_)
                | EqualitySearchProofByBuiltinRule::IntersectEmptyLeft(_)
                | EqualitySearchProofByBuiltinRule::UnionEmptyLeft(_)
                | EqualitySearchProofByBuiltinRule::IntersectEmptyRight(_)
                | EqualitySearchProofByBuiltinRule::UnionEmptyRight(_)
                | EqualitySearchProofByBuiltinRule::IntersectAssociative(_)
                | EqualitySearchProofByBuiltinRule::UnionAssociative(_)
                | EqualitySearchProofByBuiltinRule::IntersectUnionDistributive(_)),
            ) => self.compile_set_identity(fact, rule, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::IntersectFromSubset(proof),
            ) => self.compile_intersect_from_subset(
                fact,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::UnionOverIntersectDistributive(_),
            ) => self.compile_union_over_intersection(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                rule @ (EqualitySearchProofByBuiltinRule::SetMinusSelfEmpty(_)
                | EqualitySearchProofByBuiltinRule::SetMinusChainToUnion(_)
                | EqualitySearchProofByBuiltinRule::SetMinusEmptyRight(_)
                | EqualitySearchProofByBuiltinRule::SetMinusEmptyLeft(_)
                | EqualitySearchProofByBuiltinRule::SetMinusUnionDeMorgan(_)
                | EqualitySearchProofByBuiltinRule::SetMinusIntersectDeMorgan(_)
                | EqualitySearchProofByBuiltinRule::IntersectSetMinusSelfEmpty(_)),
            ) => self.compile_set_minus_identity(fact, rule, position)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Composition(p),
            ) => self.compile_composition_equality(fact, p, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::AggregateCalculation(proof)) => self.compile_aggregate_calculation(fact, proof, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::SeqEqualsFnOnNPos(_)) => self.compile_seq_equality(fact, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::LnOfExp(_)) => self.compile_exp_ln_inverse(fact, false, &[], position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::ExpOfLn(p)) => self.compile_exp_ln_inverse(fact, true, &p.proof_of_requirement_facts, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::EulerEqualsExpOne(_)) => self.compile_euler_identity(fact, false, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::LnOfEuler(_)) => self.compile_euler_identity(fact, true, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::LogOfOne(p)) => self.compile_log_basic_identity(fact, false, &p.proof_of_requirement_facts, position)?,
            EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::LogBaseSelf(p)) => self.compile_log_basic_identity(fact, true, &p.proof_of_requirement_facts, position)?,
            EqualFactSearchedProof::ByBuiltinRule(_) => {
                return Err(LeanCompileError::new(
                    "Equality/BuiltinRule",
                    &format!(
                        "Unsupported selected builtin for `{}`.",
                        AtomicFact::EqualFact(fact.clone()).readable_string()
                    ),
                ))
            }
            EqualFactSearchedProof::ByEquivalenceClass(proof) => {
                self.compile_equivalence_class(fact, proof, position)?
            }
            EqualFactSearchedProof::ByObjectDefinition(proof) => {
                self.compile_function_definition(fact, proof, parent_wd, position)?
            }
            EqualFactSearchedProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(proof),
            ) => self.compile_arithmetic_congruence_strategy(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ) => self.compile_rational(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                true,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::TupleComponentEquality(proof),
            ) => self.compile_tuple_component_strategy(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                position,
            )?,
            EqualFactSearchedProof::ByBuiltinStrategy(_) => {
                return Err(LeanCompileError::unsupported("Equality/BuiltinStrategy"))
            }
            EqualFactSearchedProof::ByMatchingOneArgByOne(proof) => self
                .compile_matching_one_arg_by_one(
                    fact,
                    &proof.corresponding_arg_equal_proofs,
                    position,
                )?,
            EqualFactSearchedProof::ByKnownForallFact(proof) => {
                self.compile_known_application(&fact.clone().into(), proof, position)?
                    .1
            }
            EqualFactSearchedProof::ByKnownForallFactViaSymmetry(proof) => {
                if proof.reversed_equal.left.ir() != fact.right.ir()
                    || proof.reversed_equal.right.ir() != fact.left.ir()
                {
                    return Err(LeanCompileError::new(
                        "Equality/KnownForallSymmetryEndpoints",
                        "The original symmetry capture must reverse both exact goal endpoints.",
                    ));
                }
                let reversed = self
                    .compile_known_application(
                        &proof.reversed_equal.clone().into(),
                        &proof.known_forall,
                        position,
                    )?
                    .1;
                format!("(Eq.symm {reversed})")
            }
            EqualFactSearchedProof::ByBuiltinRewrite(proof) => {
                self.compile_equality_builtin_rewrite(fact, proof, position)?
            }
        };
        Ok(proof)
    }
}
