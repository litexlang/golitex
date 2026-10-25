use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof;
use crate::prelude::*;
use std::collections::HashMap;

pub(super) fn preimage_parts(object: &Obj) -> Result<(&Obj, &Obj, bool), LeanCompileError> {
    match object {
        Obj::FunctionSpace(FunctionSpace::Preimage(p)) => Ok((&p.function, &p.value, false)),
        Obj::FunctionSpace(FunctionSpace::PreimageSet(p)) => Ok((&p.function, &p.target_set, true)),
        _ => Err(LeanCompileError::unsupported("Preimage/Constructor")),
    }
}

/// Validate the producer's bounded construction without discovering a new domain.
pub(super) fn validate_preimage_builder(
    object: &Obj,
    source: &CompleteFunctionDomainProof,
    builder: &SetBuilder,
) -> Result<(), LeanCompileError> {
    let (function, target, set_target) = preimage_parts(object)?;
    let parameters = source
        .signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
        .collect::<Vec<_>>();
    if parameters.is_empty() || builder.facts.len() != source.signature.dom_facts.len() + 1 {
        return Err(LeanCompileError::unsupported("Preimage/ConstructionArity"));
    }
    let carriers = if parameters.len() == 1 {
        vec![builder.param_set.as_ref()]
    } else if let Obj::ProductShape(ProductShape::Cart(cart)) = builder.param_set.as_ref() {
        cart.args.iter().map(Box::as_ref).collect()
    } else {
        return Err(LeanCompileError::unsupported("Preimage/InputCarrier"));
    };
    if carriers.len() != parameters.len()
        || carriers
            .iter()
            .zip(&parameters)
            .any(|(a, (_, b))| a.ir() != b.ir())
    {
        return Err(LeanCompileError::unsupported("Preimage/InputCarrier"));
    }
    let input = Obj::Identifier(IdentifierObj::from_bound_name(&builder.param_binding));
    let mut substitution = HashMap::new();
    let mut arguments = Vec::new();
    for (i, (parameter, _)) in parameters.iter().enumerate() {
        let argument = if parameters.len() == 1 {
            input.clone()
        } else {
            crate::execute::execute_fact_stmt::function_domain::function_application(
                &input,
                vec![Box::new(Obj::Literal(Literal::Number(Number {
                    normalized_value: (i + 1).to_string(),
                })))],
            )
            .map_err(|_| LeanCompileError::unsupported("Preimage/InputCoordinate"))?
        };
        substitution.insert(parameter.id, argument.clone());
        arguments.push(Box::new(argument));
    }
    for (guard, condition) in source.signature.dom_facts.iter().zip(&builder.facts) {
        let guard = crate::instantiate::quantifier_free_fact_to_fact(guard.clone());
        let condition = crate::instantiate::quantifier_free_fact_to_fact(condition.clone());
        if !instantiated_fact_matches(&guard, &condition, &substitution) {
            return Err(LeanCompileError::unsupported("Preimage/ConstructionGuard"));
        }
    }
    let call = crate::execute::execute_fact_stmt::function_domain::function_application(
        function, arguments,
    )
    .map_err(|_| LeanCompileError::unsupported("Preimage/OutputCall"))?;
    let matches = match (set_target, builder.facts.last()) {
        (false, Some(QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(p)))) => {
            p.left.ir() == call.ir() && p.right.ir() == target.ir()
        }
        (true, Some(QuantifierFreeFact::AtomicFact(AtomicFact::InFact(p)))) => {
            p.element.ir() == call.ir() && p.set.ir() == target.ir()
        }
        _ => false,
    };
    if !matches {
        return Err(LeanCompileError::unsupported("Preimage/OutputCondition"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_preimage_construction(
        &self,
        object: &Obj,
        construction: &FunctionPreimageConstructionProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        validate_preimage_builder(object, &construction.source, &construction.builder)?;
        let (function, _, _) = preimage_parts(object)?;
        let member =
            self.compile_complete_domain_member(function, &construction.source, position)?;
        let builder = Obj::SetFormer(SetFormer::SetBuilder(construction.builder.clone()));
        ensure_object(&builder, &construction.builder_well_defined)?;
        let checked = self.compile_wd(&construction.builder_well_defined, position)?;
        Ok((member, checked))
    }

    pub(super) fn compile_preimage_wd(
        &self,
        object: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        construction: &FunctionPreimageConstructionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (function, target, set_target) = preimage_parts(object)?;
        if children.len() != 2 || requirements.len() != usize::from(set_target) {
            return Err(LeanCompileError::unsupported("Preimage/FormationStages"));
        }
        let mut terms = Vec::new();
        for (index, (object, child)) in [function, target].into_iter().zip(children).enumerate() {
            ensure_object(object, child)?;
            terms.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let mut lines = Vec::new();
        if let Some(proof) = requirements.first() {
            if !matches!(source_subject(proof)?,Fact::AtomicFact(AtomicFact::IsSetFact(p)) if p.set.ir()==target.ir())
            {
                return Err(LeanCompileError::unsupported("Preimage/TargetSethood"));
            }
            let proved = self.compile_verify(
                proof,
                &SourcePosition {
                    before: 2,
                    ..*position
                },
            )?;
            lines.push(format!(
                "have _preimage_target : {} := {}",
                proved.0, proved.1
            ));
        }
        let formed = SourcePosition {
            before: 2 + requirements.len(),
            ..*position
        };
        let (member, builder) =
            self.compile_preimage_construction(object, construction, &formed)?;
        let signature = self.compile_fn_signature(&construction.source.signature, &formed)?;
        lines.push(format!("let _preimage_builder := {builder}"));
        let ctor = if set_target {
            "preimageSet"
        } else {
            "preimage"
        };
        lines.push(format!(
            "exact Litex.{ctor} {} {} {signature} {member}",
            terms[0], terms[1]
        ));
        Ok(format!("(by\n  {})", lines.join("\n  ")))
    }
}
