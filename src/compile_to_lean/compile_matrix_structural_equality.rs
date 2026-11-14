//! Replay bounded matrix entry normalization and complete-domain extensionality.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::function_application;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::matrix_entry_normalization_proof::*;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_structural_equality(
        &self,
        equal: &EqualFact,
        proof: &MatrixStructuralEqualityProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let domain = &proof.domain_match;
        if domain.target != proof.right_domain.signature
            || domain.function_wd.obj().ir() != equal.left.ir()
            || domain.target_wd.obj().ir()
                != Obj::FunctionSpace(FunctionSpace::FnSet(domain.target.clone())).ir()
        {
            return Err(LeanCompileError::unsupported(
                "MatrixStructural/CompleteDomain",
            ));
        }
        let parameters: Vec<_> = domain
            .source
            .signature
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
            return Err(LeanCompileError::unsupported("MatrixStructural/Arity"));
        }
        let pointwise = source_subject(&proof.pointwise)?;
        let Fact::ForallFact(pointwise) = &pointwise else {
            return Err(LeanCompileError::unsupported(
                "MatrixStructural/PointwiseForall",
            ));
        };
        let actual = pointwise
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        if actual.len() != parameters.len() {
            return Err(LeanCompileError::unsupported(
                "MatrixStructural/PointwiseParameters",
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
            || pointwise.dom_facts.len() != domain.source.signature.dom_facts.len()
            || !pointwise.dom_facts.iter().zip(&domain.source.signature.dom_facts).all(|(actual, source)| {
                instantiated_fact_matches(
                    &crate::instantiate::quantifier_free_fact_to_fact(source.clone()), actual, &substitution,
                )
            })
            || pointwise.then_facts.len() != 1
        {
            return Err(LeanCompileError::unsupported("MatrixStructural/PointwiseDomain"));
        }
        let left_call = function_application(&equal.left, arguments.clone())
            .map_err(|_| LeanCompileError::unsupported("MatrixStructural/LeftApplication"))?;
        let right_call = function_application(&equal.right, arguments)
            .map_err(|_| LeanCompileError::unsupported("MatrixStructural/RightApplication"))?;
        if !matches!(&pointwise.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f))
            if f.left.ir() == left_call.ir() && f.right.ir() == right_call.ir())
        {
            return Err(LeanCompileError::unsupported(
                "MatrixStructural/PointwiseSubject",
            ));
        }
        // This strategy publishes no outer facts. Keep the caller's exact
        // visibility boundary while replaying its domain evidence.
        let caller = *position;
        let domain_scope = SourcePosition::new(
            Some(&caller),
            SourceOwner::FunctionDomainWD(domain),
            usize::MAX,
        );
        self.compile_wd(&domain.function_wd, &domain_scope)?;
        self.compile_wd(&domain.target_wd, &domain_scope)?;
        let formed = *position;
        let left = self.compile_object_reference(&equal.left, &formed)?;
        let right = self.compile_object_reference(&equal.right, &formed)?;
        let s = self.compile_fn_signature(&domain.source.signature, &domain_scope)?;
        let t = self.compile_fn_signature(&proof.right_domain.signature, &domain_scope)?;
        let hf = self.compile_complete_domain_member(&equal.left, &domain.source, &domain_scope)?;
        let hg =
            self.compile_complete_domain_member(&equal.right, &proof.right_domain, &domain_scope)?;
        let (mut lines, domain_equal) = self.compile_function_domain_match(domain, &caller)?;
        let checked = self.compile_verify(&proof.pointwise, position)?;
        lines.push(format!("have _pointwise : {} := {}", checked.0, checked.1));
        lines.push(format!(
            "apply Litex.functionExtOnDomain {left} {right} {s} {t} {hf} {hg} {domain_equal}"
        ));
        lines.push("intro _preimage_input _preimage_domain".into());
        let (parts, values, guards) = self.compile_preimage_domain_parts(
            &domain.source.signature,
            "_preimage_input",
            &domain_scope,
        )?;
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
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }
}
