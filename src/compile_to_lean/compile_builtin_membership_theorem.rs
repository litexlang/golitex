use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_builtin_membership_theorem(
        &self,
        call: &TheoremCall,
        builtin: Option<&BuiltinThmApplication>,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        let Some(builtin) = builtin else {
            return Err(LeanCompileError::unsupported(
                "BuiltinMembership/Application",
            ));
        };
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::SequenceLimitUnique
                | BuiltinTheoremId::SequenceLimitExists
                | BuiltinTheoremId::SequenceLimitSelected
                | BuiltinTheoremId::SequenceLimitFromEpsilon
                | BuiltinTheoremId::SequenceLimitTail
                | BuiltinTheoremId::SequenceCauchyFromEpsilon
                | BuiltinTheoremId::SequenceCauchyTail
                | BuiltinTheoremId::SequenceConvergentFromLimit
                | BuiltinTheoremId::SequenceLimitFromConvergent
                | BuiltinTheoremId::SequenceStrictIncreasingNondecreasing
                | BuiltinTheoremId::SequenceStrictDecreasingNonincreasing
                | BuiltinTheoremId::SequenceBoundedFromBounds
        ) {
            return self.compile_builtin_sequence_limit_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::FnLimitAtSqueeze
                | BuiltinTheoremId::FnLimitLeftSqueeze
                | BuiltinTheoremId::FnLimitRightSqueeze
                | BuiltinTheoremId::FnLimitPosInfSqueeze
                | BuiltinTheoremId::FnLimitNegInfSqueeze
        ) {
            return self.compile_builtin_function_limit_squeeze(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::FnLimitAtLocalEqual
                | BuiltinTheoremId::FnLimitLeftLocalEqual
                | BuiltinTheoremId::FnLimitRightLocalEqual
                | BuiltinTheoremId::FnLimitPosInfLocalEqual
                | BuiltinTheoremId::FnLimitNegInfLocalEqual
        ) {
            return self.compile_builtin_function_limit_local(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::FnLimitAtCompare
                | BuiltinTheoremId::FnLimitLeftCompare
                | BuiltinTheoremId::FnLimitRightCompare
                | BuiltinTheoremId::FnLimitPosInfCompare
                | BuiltinTheoremId::FnLimitNegInfCompare
        ) {
            return self.compile_builtin_function_limit_order(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::FnLimitAtEventuallyPositive
                | BuiltinTheoremId::FnLimitAtEventuallyNonzero
                | BuiltinTheoremId::FnLimitLeftEventuallyPositive
                | BuiltinTheoremId::FnLimitLeftEventuallyNonzero
                | BuiltinTheoremId::FnLimitRightEventuallyPositive
                | BuiltinTheoremId::FnLimitRightEventuallyNonzero
                | BuiltinTheoremId::FnLimitPosInfEventuallyPositive
                | BuiltinTheoremId::FnLimitPosInfEventuallyNonzero
                | BuiltinTheoremId::FnLimitNegInfEventuallyPositive
                | BuiltinTheoremId::FnLimitNegInfEventuallyNonzero
        ) {
            return self.compile_builtin_function_limit_eventual(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::FnLimitAtToLeft
                | BuiltinTheoremId::FnLimitAtToRight
                | BuiltinTheoremId::FnLimitFromSides
                | BuiltinTheoremId::FnLimitSidesMismatch
        ) {
            return self.compile_builtin_function_limit_sides(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::FnLimitAtAdd
                | BuiltinTheoremId::FnLimitAtSubtract
                | BuiltinTheoremId::FnLimitAtMultiply
                | BuiltinTheoremId::FnLimitLeftAdd
                | BuiltinTheoremId::FnLimitLeftSubtract
                | BuiltinTheoremId::FnLimitLeftMultiply
                | BuiltinTheoremId::FnLimitRightAdd
                | BuiltinTheoremId::FnLimitRightSubtract
                | BuiltinTheoremId::FnLimitRightMultiply
                | BuiltinTheoremId::FnLimitPosInfAdd
                | BuiltinTheoremId::FnLimitPosInfSubtract
                | BuiltinTheoremId::FnLimitPosInfMultiply
                | BuiltinTheoremId::FnLimitNegInfAdd
                | BuiltinTheoremId::FnLimitNegInfSubtract
                | BuiltinTheoremId::FnLimitNegInfMultiply
                | BuiltinTheoremId::FnLimitAtDivide
                | BuiltinTheoremId::FnLimitLeftDivide
                | BuiltinTheoremId::FnLimitRightDivide
                | BuiltinTheoremId::FnLimitPosInfDivide
                | BuiltinTheoremId::FnLimitNegInfDivide
        ) {
            return self.compile_builtin_function_limit_binary(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::FnLimitAtNeg
                | BuiltinTheoremId::FnLimitAtAbs
                | BuiltinTheoremId::FnLimitLeftNeg
                | BuiltinTheoremId::FnLimitLeftAbs
                | BuiltinTheoremId::FnLimitRightNeg
                | BuiltinTheoremId::FnLimitRightAbs
                | BuiltinTheoremId::FnLimitPosInfNeg
                | BuiltinTheoremId::FnLimitPosInfAbs
                | BuiltinTheoremId::FnLimitNegInfNeg
                | BuiltinTheoremId::FnLimitNegInfAbs
                | BuiltinTheoremId::FnLimitAtScale
                | BuiltinTheoremId::FnLimitAtPower
                | BuiltinTheoremId::FnLimitLeftScale
                | BuiltinTheoremId::FnLimitLeftPower
                | BuiltinTheoremId::FnLimitRightScale
                | BuiltinTheoremId::FnLimitRightPower
                | BuiltinTheoremId::FnLimitPosInfScale
                | BuiltinTheoremId::FnLimitPosInfPower
                | BuiltinTheoremId::FnLimitNegInfScale
                | BuiltinTheoremId::FnLimitNegInfPower
        ) {
            return self.compile_builtin_function_limit_unary(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::FnLimitAtRealAccumulation
                | BuiltinTheoremId::FnLimitLeftRealAccumulation
                | BuiltinTheoremId::FnLimitRightRealAccumulation
                | BuiltinTheoremId::FnLimitPosInfRealAccumulation
                | BuiltinTheoremId::FnLimitNegInfRealAccumulation
                | BuiltinTheoremId::FnLimitAtUnique
                | BuiltinTheoremId::FnLimitLeftUnique
                | BuiltinTheoremId::FnLimitRightUnique
                | BuiltinTheoremId::FnLimitPosInfUnique
                | BuiltinTheoremId::FnLimitNegInfUnique
                | BuiltinTheoremId::FnLimitAtExists
                | BuiltinTheoremId::FnLimitAtSelected
                | BuiltinTheoremId::FnLimitLeftExists
                | BuiltinTheoremId::FnLimitLeftSelected
                | BuiltinTheoremId::FnLimitRightExists
                | BuiltinTheoremId::FnLimitRightSelected
                | BuiltinTheoremId::FnLimitPosInfExists
                | BuiltinTheoremId::FnLimitPosInfSelected
                | BuiltinTheoremId::FnLimitNegInfExists
                | BuiltinTheoremId::FnLimitNegInfSelected
                | BuiltinTheoremId::FnLimitAtIdentity
                | BuiltinTheoremId::FnLimitLeftIdentity
                | BuiltinTheoremId::FnLimitRightIdentity
                | BuiltinTheoremId::FnLimitAtConstant
                | BuiltinTheoremId::FnLimitLeftConstant
                | BuiltinTheoremId::FnLimitRightConstant
                | BuiltinTheoremId::FnLimitPosInfConstant
                | BuiltinTheoremId::FnLimitNegInfConstant
                | BuiltinTheoremId::FnLimitAtFromEpsilon
                | BuiltinTheoremId::FnLimitLeftFromEpsilon
                | BuiltinTheoremId::FnLimitRightFromEpsilon
                | BuiltinTheoremId::FnLimitPosInfFromEpsilon
                | BuiltinTheoremId::FnLimitNegInfFromEpsilon
                | BuiltinTheoremId::FnLimitAtAccumulation
                | BuiltinTheoremId::FnLimitLeftAccumulation
                | BuiltinTheoremId::FnLimitRightAccumulation
                | BuiltinTheoremId::FnLimitPosInfAccumulation
                | BuiltinTheoremId::FnLimitNegInfAccumulation
                | BuiltinTheoremId::FnLimitAtControl
                | BuiltinTheoremId::FnLimitLeftControl
                | BuiltinTheoremId::FnLimitRightControl
                | BuiltinTheoremId::FnLimitPosInfControl
                | BuiltinTheoremId::FnLimitNegInfControl
        ) {
            return self.compile_builtin_function_limit_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::RealLeastUpperBoundFromDefinition
                | BuiltinTheoremId::RealGreatestLowerBoundFromDefinition
                | BuiltinTheoremId::RealLeastUpperBoundUpperBound
                | BuiltinTheoremId::RealGreatestLowerBoundLowerBound
                | BuiltinTheoremId::RealLeastUpperBoundUnique
                | BuiltinTheoremId::RealGreatestLowerBoundUnique
                | BuiltinTheoremId::RealLeastUpperBoundCrosses
                | BuiltinTheoremId::RealGreatestLowerBoundCrosses
                | BuiltinTheoremId::RealLeastUpperBoundExists
                | BuiltinTheoremId::RealGreatestLowerBoundExists
                | BuiltinTheoremId::RealMemberLeLeastUpperBound
                | BuiltinTheoremId::RealGreatestLowerBoundLeMember
                | BuiltinTheoremId::RealLeastUpperBoundLeUpperBound
                | BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound
        ) {
            return self.compile_builtin_extremum_certificate_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::RealSupremumExists
                | BuiltinTheoremId::RealInfimumExists
                | BuiltinTheoremId::RealSupremumSelected
                | BuiltinTheoremId::RealInfimumSelected
        ) {
            return self.compile_builtin_extremum_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::MatrixPowerZero | BuiltinTheoremId::MatrixPowerSuccessor
        ) {
            return self.compile_builtin_matrix_power_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::MatrixRankBounds
                | BuiltinTheoremId::MatrixRankZero
                | BuiltinTheoremId::MatrixRankIdentity
        ) {
            return self.compile_builtin_rank_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::MatrixDetIdentity
                | BuiltinTheoremId::MatrixDetTranspose
                | BuiltinTheoremId::MatrixDetAdjoint
        ) {
            return self.compile_builtin_determinant_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if matches!(
            builtin.theorem,
            BuiltinTheoremId::EuclideanNormSquare | BuiltinTheoremId::FrobeniusNormSquare
        ) {
            return self.compile_builtin_norm_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if builtin.theorem == BuiltinTheoremId::FiniteSetReduceSingleton {
            return self.compile_builtin_fold_theorem(
                call,
                builtin,
                derivation,
                type_proofs,
                type_stores,
                function_domain,
                dom_proofs,
                dom_stores,
                conclusions_wd,
                position,
            );
        }
        if !matches!(
            builtin.theorem,
            BuiltinTheoremId::SetBuilderMember
                | BuiltinTheoremId::FamilyIntersectionMember
                | BuiltinTheoremId::IndexedIntersectionMember
                | BuiltinTheoremId::IndexCartesianMember
                | BuiltinTheoremId::DefinedSetMember
                | BuiltinTheoremId::CartesianMemberFromCoordinates
                | BuiltinTheoremId::FunctionSetMember
        ) || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
        {
            return Err(LeanCompileError::unsupported("BuiltinMembership/Contract"));
        }
        let (AtomicName::Plain { name }, TheoremCallArguments::Parenthesized(arguments)) =
            (&call.name, &call.arguments)
        else {
            return Err(LeanCompileError::unsupported("BuiltinMembership/Arguments"));
        };
        if name != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != 2
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
            || dom_proofs.len() != builtin.requirements.len()
            || dom_stores.len() != dom_proofs.len()
        {
            return Err(LeanCompileError::unsupported("BuiltinMembership/Stages"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(member)) = &builtin.conclusions[0] else {
            return Err(LeanCompileError::unsupported(
                "BuiltinMembership/Conclusion",
            ));
        };
        if member.element.ir() != arguments[0].ir() || member.set.ir() != arguments[1].ir() {
            return Err(LeanCompileError::unsupported(
                "BuiltinMembership/Conclusion",
            ));
        }
        let mut definitions = Vec::new();
        let domain = match (builtin.theorem, function_domain) {
            (
                BuiltinTheoremId::CartesianMemberFromCoordinates
                | BuiltinTheoremId::FunctionSetMember,
                Some(BuiltinFunctionDomainProof::Membership(domain)),
            ) => Some(domain),
            (
                BuiltinTheoremId::SetBuilderMember
                | BuiltinTheoremId::FamilyIntersectionMember
                | BuiltinTheoremId::DefinedSetMember
                | BuiltinTheoremId::IndexedIntersectionMember
                | BuiltinTheoremId::IndexCartesianMember,
                None,
            ) => None,
            _ => {
                return Err(LeanCompileError::unsupported(
                    "BuiltinMembership/CompleteDomain",
                ))
            }
        };
        let mut domain_equality = "(by rfl)".to_string();
        let domain_complete = if let Some(domain) = domain {
            ensure_object(&arguments[0], &domain.function_wd)?;
            ensure_object(
                &Obj::FunctionSpace(FunctionSpace::FnSet(domain.target.clone())),
                &domain.target_wd,
            )?;
            let prior =
                SourcePosition::new(Some(position), SourceOwner::FunctionDomainWD(domain), 0);
            let function = self.compile_wd(&domain.function_wd, &prior)?;
            let formed = SourcePosition { before: 1, ..prior };
            let target = self.compile_wd(&domain.target_wd, &formed)?;
            definitions.push(format!("let _membership_function := {function}"));
            definitions.push(format!("let _membership_target := {target}"));
            let before = if builtin.theorem == BuiltinTheoremId::FunctionSetMember {
                // Domain comparisons precede every return obligation in the
                // native theorem invocation. Keep later stores out of ancestry.
                let (comparisons, equality) =
                    self.compile_function_domain_match(domain, position)?;
                definitions.extend(comparisons);
                domain_equality = equality;
                usize::MAX
            } else {
                2
            };
            Some(SourcePosition { before, ..prior })
        } else {
            None
        };
        let invocation = SourcePosition {
            parent: domain_complete.as_ref().or(position.parent),
            ..*position
        };
        let position = &invocation;
        let mut references = Vec::new();
        for (index, ((requirement, proof), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(proof)? != *requirement {
                return Err(LeanCompileError::unsupported("BuiltinMembership/Premise"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(proof, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            let published = SourcePosition {
                before: index + 1,
                ..*position
            };
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, reference.clone()),
                &published,
            )?);
            references.push(reference);
        }
        let formed = SourcePosition {
            before: dom_proofs.len(),
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let formation = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let application = match builtin.theorem {
            BuiltinTheoremId::FamilyIntersectionMember => self.compile_family_intersection_member(
                member,
                &builtin.requirements,
                &references,
                &formation,
            )?,
            BuiltinTheoremId::IndexedIntersectionMember
            | BuiltinTheoremId::IndexCartesianMember => self.compile_indexed_member_theorem(
                builtin.theorem,
                member,
                &builtin.requirements,
                &references,
                &formation,
            )?,
            BuiltinTheoremId::SetBuilderMember => self.compile_builder_membership_evidence(
                member,
                &builtin.requirements,
                references,
                &formation,
            )?,
            BuiltinTheoremId::DefinedSetMember => {
                if !matches!(
                    member.set,
                    Obj::Identifier(_) | Obj::InstantiatedTemplateObj(_)
                ) || builtin.requirements.len() != 1
                    || builtin.requirements[0].ir() != builtin.conclusions[0].ir()
                {
                    return Err(LeanCompileError::unsupported(
                        "BuiltinMembership/DefinedSet",
                    ));
                }
                references.remove(0)
            }
            BuiltinTheoremId::CartesianMemberFromCoordinates => self
                .compile_builtin_cart_membership(
                    member,
                    domain.unwrap(),
                    &builtin.requirements,
                    &references,
                    &formation,
                    domain_complete.as_ref().unwrap(),
                )?,
            BuiltinTheoremId::FunctionSetMember => self.compile_builtin_function_membership(
                member,
                domain.unwrap(),
                &domain_equality,
                &builtin.requirements,
                &references,
                &formation,
            )?,
            _ => unreachable!(),
        };
        Ok((definitions, application, builtin.conclusions.clone()))
    }
}
