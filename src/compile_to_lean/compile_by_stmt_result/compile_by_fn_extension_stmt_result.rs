use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult;
use crate::execute::execute_fact_stmt::function_domain::{
    function_application, function_domains_alpha_equal, CompleteFunctionDomainProof,
    CompleteFunctionDomainSourceProof, FunctionDomainComparisonProof,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_by_fn_extension_result(
        &self,
        result: &ExecByFnExtensionStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecByFnExtensionStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("FnExtension/Failed"));
        };
        let VerifyFactWellDefinedResult::Success(wd) = &proof.goal_wd else {
            return Err(LeanCompileError::unsupported("FnExtension/GoalWD"));
        };
        let goal = self.resolve_fact(
            proof.stored.primary_fact_id(),
            &SourcePosition {
                before: 4,
                ..*position
            },
        )?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = &goal else {
            return Err(LeanCompileError::unsupported("FnExtension/Goal"));
        };
        self.compile_fact_wd(wd, &goal, position)?;
        let domain = &proof.domain_match;
        if proof.carrier != domain.source.signature
            || domain.target != proof.right_domain.signature
            || !matches!(
                domain.comparison,
                FunctionDomainComparisonProof::AlphaEquivalent
            )
            || !function_domains_alpha_equal(&proof.carrier, &proof.right_domain.signature)
            || domain.function_wd.obj().ir() != equal.left.ir()
            || domain.target_wd.obj().ir()
                != Obj::FunctionSpace(FunctionSpace::FnSet(domain.target.clone())).ir()
        {
            return Err(LeanCompileError::unsupported("FnExtension/CompleteDomain"));
        }
        let parameters: Vec<_> = proof
            .carrier
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| {
                group
                    .params
                    .iter()
                    .map(move |p| (p, group.param_type.as_ref()))
            })
            .collect();
        let [(old, carrier)] = parameters.as_slice() else {
            return Err(LeanCompileError::unsupported("FnExtension/OneParameter"));
        };
        if **carrier == Obj::StandardSet(StandardSet::RPos) {
            return Err(LeanCompileError::unsupported(
                "FnExtension/PositiveParameter",
            ));
        }
        let pointwise = source_subject(&proof.pointwise_proof)?;
        let Fact::ForallFact(pointwise) = &pointwise else {
            return Err(LeanCompileError::unsupported("FnExtension/PointwiseForall"));
        };
        let [group] = pointwise.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "FnExtension/PointwiseParameters",
            ));
        };
        let [parameter] = group.params.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "FnExtension/PointwiseParameters",
            ));
        };
        let argument = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let substitution = HashMap::from([(old.id, argument.clone())]);
        if !matches!(&group.param_type, ParamType::Obj(set) if instantiated_object_matches(carrier, set, &substitution))
            || pointwise.dom_facts.len() != proof.carrier.dom_facts.len()
            || !pointwise
                .dom_facts
                .iter()
                .zip(&proof.carrier.dom_facts)
                .all(|(actual, source)| {
                    instantiated_fact_matches(
                        &crate::instantiate::quantifier_free_fact_to_fact(source.clone()),
                        actual,
                        &substitution,
                    )
                })
            || pointwise.then_facts.len() != 1
        {
            return Err(LeanCompileError::unsupported("FnExtension/PointwiseDomain"));
        }
        let left_call = function_application(&equal.left, vec![Box::new(argument.clone())])
            .map_err(|_| LeanCompileError::unsupported("FnExtension/LeftApplication"))?;
        let right_call = function_application(&equal.right, vec![Box::new(argument.clone())])
            .map_err(|_| LeanCompileError::unsupported("FnExtension/RightApplication"))?;
        if !matches!(&pointwise.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f))
            if f.left.ir() == left_call.ir() && f.right.ir() == right_call.ir())
        {
            return Err(LeanCompileError::unsupported(
                "FnExtension/PointwiseSubject",
            ));
        }
        let caller = SourcePosition {
            before: 1,
            ..*position
        };
        let domain_scope = SourcePosition::new(
            Some(&caller),
            SourceOwner::FunctionDomainWD(domain),
            usize::MAX,
        );
        self.compile_wd(&domain.function_wd, &domain_scope)?;
        self.compile_wd(&domain.target_wd, &domain_scope)?;
        let formed = SourcePosition::new(Some(position), SourceOwner::FactWD(wd), usize::MAX);
        let left = self.compile_object_reference(&equal.left, &formed)?;
        let right = self.compile_object_reference(&equal.right, &formed)?;
        let s = self.compile_fn_signature(&domain.source.signature, &domain_scope)?;
        let t = self.compile_fn_signature(&proof.right_domain.signature, &domain_scope)?;
        let hf = self.compile_complete_domain_member(&equal.left, &domain.source, &domain_scope)?;
        let hg =
            self.compile_complete_domain_member(&equal.right, &proof.right_domain, &domain_scope)?;
        let caller = SourcePosition {
            before: 2,
            ..*position
        };
        let scope = SourcePosition::new(Some(&caller), SourceOwner::FnExtension(proof), 0);
        let mut lines = Vec::new();
        for (j, statement) in proof.proof_steps.iter().enumerate() {
            lines.push(self.compile_statement_in_scope(
                statement,
                &SourcePosition { before: j, ..scope },
                j + 1,
                true,
            )?);
        }
        let checked = self.compile_verify(
            &proof.pointwise_proof,
            &SourcePosition {
                before: proof.proof_steps.len(),
                ..scope
            },
        )?;
        lines.push(format!("have _pointwise : {} := {}", checked.0, checked.1));
        let (base, _) = self.compile_function_base_domain(&proof.carrier, &domain_scope)?;
        let guard = self.compile_function_packed_guard_template(&proof.carrier, &domain_scope)?;
        let guards = (0..pointwise.dom_facts.len())
            .map(|i| conjunction_projection("_guard", i, pointwise.dom_facts.len()))
            .collect::<Vec<_>>()
            .join(" ");
        lines.push(format!(
            "apply Litex.functionExtOnDomain {left} {right} {s} {t} {hf} {hg} (by rfl)"
        ));
        lines.push("intro _input _domain".into());
        lines.push(format!("have _parts : M.mem _input {base} ∧ {guard} _input := (Litex.SetSemantics.sep_members {base} {guard} _input).mp _domain"));
        lines.push("have _guard := _parts.2".into());
        lines.push(format!("exact _pointwise (Litex.semanticObject _input (M.member_isSet _parts.1)) _parts.1 {guards}"));
        self.emit_by_completed_fact(
            &goal,
            (
                self.fact_proposition(&goal, &formed)?,
                format!("(by\n  {}\n)", lines.join("\n").replace('\n', "\n  ")),
            ),
            &proof.stored,
            position,
            4,
            index,
            local,
        )
    }

    pub(in crate::compile_to_lean) fn compile_complete_domain_member(
        &self,
        subject: &Obj,
        proof: &CompleteFunctionDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let signature = self.compile_fn_signature(&proof.signature, position)?;
        let target = self.compile_object_reference(subject, position)?;
        match &proof.source {
            CompleteFunctionDomainSourceProof::AnonymousFunction {
                function,
                subject_equal,
            } => {
                if function.body != proof.signature {
                    return Err(LeanCompileError::unsupported("FnExtension/SourceSignature"));
                }
                let literal = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()));
                let object = self.compile_object_reference(&literal, position)?;
                let same =
                    self.compile_equality_path(subject, &literal, subject_equal, position)?;
                Ok(format!("(Litex.inOfSame {object} {target} (Litex.fnSet {signature}) (Litex.fnSet {signature}) ({same}).symm (Litex.sameRefl _) (Litex.formulaFnInFnSet {object}))"))
            }
            CompleteFunctionDomainSourceProof::Membership {
                membership,
                subject_equal,
                carrier_equal,
            } => {
                let (fact, cited) = self.cited_fact_reference(membership.fact_id, position)?;
                if fact != &Fact::AtomicFact(AtomicFact::InFact(membership.clone())) {
                    return Err(LeanCompileError::unsupported("FnExtension/DomainCitation"));
                }
                let value = self.compile_object_reference(&membership.element, position)?;
                let carrier = self.compile_object_reference(&membership.set, position)?;
                let same = self.compile_equality_path(
                    subject,
                    &membership.element,
                    subject_equal,
                    position,
                )?;
                let target_carrier =
                    Obj::FunctionSpace(FunctionSpace::FnSet(proof.signature.clone()));
                let carrier_same = self.compile_equality_path(
                    &membership.set,
                    &target_carrier,
                    carrier_equal,
                    position,
                )?;
                Ok(format!("(Litex.inOfSame {value} {target} {carrier} (Litex.fnSet {signature}) ({same}).symm {carrier_same} {cited})"))
            }
            _ => Err(LeanCompileError::unsupported("FnExtension/DomainSource")),
        }
    }
}
