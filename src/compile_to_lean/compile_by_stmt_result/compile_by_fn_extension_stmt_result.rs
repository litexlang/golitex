use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::ExecByFnExtensionStmtResult;
use crate::execute::execute_fact_stmt::function_domain::{
    function_application, CompleteFunctionDomainProof, CompleteFunctionDomainSourceProof,
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
        if !(1..=2).contains(&parameters.len()) {
            return Err(LeanCompileError::unsupported("FnExtension/Arity"));
        }
        let pointwise = source_subject(&proof.pointwise_proof)?;
        let Fact::ForallFact(pointwise) = &pointwise else {
            return Err(LeanCompileError::unsupported("FnExtension/PointwiseForall"));
        };
        let actual = pointwise
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        if actual.len() != parameters.len() {
            return Err(LeanCompileError::unsupported(
                "FnExtension/PointwiseParameters",
            ));
        }
        let arguments = actual
            .iter()
            .map(|(p, _)| Box::new(Obj::Identifier(IdentifierObj::from_bound_name(p))))
            .collect::<Vec<_>>();
        let substitution = parameters
            .iter()
            .zip(&arguments)
            .map(|((p, _), a)| (p.id, a.as_ref().clone()))
            .collect::<HashMap<_, _>>();
        if substitution.len()!=parameters.len()
            || actual.iter().map(|(p,_)|p.id).collect::<std::collections::HashSet<_>>().len()!=actual.len()
            || !parameters.iter().zip(&actual).all(|((_,carrier),(_,ty))|
                matches!(ty, ParamType::Obj(set) if instantiated_object_matches(carrier,set,&substitution)))
            || pointwise.dom_facts.len() != proof.carrier.dom_facts.len()
            || !pointwise.dom_facts.iter().zip(&proof.carrier.dom_facts).all(|(actual, source)| {
                instantiated_fact_matches(
                    &crate::instantiate::quantifier_free_fact_to_fact(source.clone()), actual, &substitution,
                )
            })
            || pointwise.then_facts.len() != 1
        {
            return Err(LeanCompileError::unsupported("FnExtension/PointwiseDomain"));
        }
        let left_call = function_application(&equal.left, arguments.clone())
            .map_err(|_| LeanCompileError::unsupported("FnExtension/LeftApplication"))?;
        let right_call = function_application(&equal.right, arguments)
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
        let (mut lines, domain_equal) = self.compile_function_domain_match(domain, &caller)?;
        let caller = SourcePosition {
            before: 2,
            ..*position
        };
        let scope = SourcePosition::new(Some(&caller), SourceOwner::FnExtension(proof), 0);
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
        lines.push(format!(
            "apply Litex.functionExtOnDomain {left} {right} {s} {t} {hf} {hg} {domain_equal}"
        ));
        lines.push("intro _preimage_input _preimage_domain".into());
        let (parts, values, guards) =
            self.compile_preimage_domain_parts(&proof.carrier, "_preimage_input", &domain_scope)?;
        lines.extend(parts);
        let mut arguments = Vec::new();
        for (i, value) in values.iter().enumerate() {
            let member = if values.len() == 1 {
                "_preimage_base".to_string()
            } else {
                format!("(Litex.FiniteFunction.coordinate_mem_number _preimage_base ({i} : Fin {}) ({} : ℂ) (by norm_num))",values.len(),i+1)
            };
            arguments.push(format!(
                "(Litex.semanticObject {value} (M.member_isSet {member})) {member}"
            ));
        }
        arguments.extend(guards);
        let packed = if values.len() == 1 {
            values[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                values.join(", ")
            )
        };
        let predicate = format!("fun x => Litex.FunctionSemantics.callValue (M := M) (Litex.denote {left}) x = Litex.FunctionSemantics.callValue (M := M) (Litex.denote {right}) x");
        let repack = self.compile_preimage_repack(&values, "_preimage_base");
        lines.push(format!(
            "have _repack : _preimage_input = {packed} := {repack}"
        ));
        lines.push(format!(
            "exact Eq.mpr (congrArg ({predicate}) _repack) (_pointwise {})",
            arguments.join(" ")
        ));
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
        match &proof.source {
            CompleteFunctionDomainSourceProof::ApplicationReturn { .. } => {
                self.compile_application_return_member(subject, proof, position)
            }
            CompleteFunctionDomainSourceProof::Matrix(callable) => {
                if proof.signature != callable.function.body {
                    return Err(LeanCompileError::unsupported("Matrix/DomainSignature"));
                }
                self.compile_matrix_callable_member(subject, callable, position)
            }
            CompleteFunctionDomainSourceProof::Composition(callable) => {
                if proof.signature != callable.function.body {
                    return Err(LeanCompileError::unsupported("Composition/DomainSignature"));
                }
                self.compile_composition_member(subject, callable, position)
            }
            CompleteFunctionDomainSourceProof::AnonymousFunction {
                function,
                subject_equal,
            } => {
                let signature = self.compile_complete_domain_signature(proof, position)?;
                let target = self.compile_object_reference(subject, position)?;
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
                let signature = self.compile_complete_domain_signature(proof, position)?;
                let target = self.compile_object_reference(subject, position)?;
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
                let carrier_same = self.compile_function_carrier_path(
                    &membership.set,
                    &proof.signature,
                    carrier_equal,
                    position,
                )?;
                Ok(format!("(Litex.inOfSame {value} {target} {carrier} (Litex.fnSet {signature}) ({same}).symm {carrier_same} {cited})"))
            }
            _ => Err(LeanCompileError::unsupported("FnExtension/DomainSource")),
        }
    }
}
