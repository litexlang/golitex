//! Render only the original Euclidean limit context, without domain discovery.
use super::compile_multivariable_scalar_limit::vector_carrier;
use super::compile_real_set_bounds::contains_parameter;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof;
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("EuclideanLimitContext/{stage}"))
}
fn same_object(a: &Obj, b: &Obj) -> bool {
    a.ir() == b.ir()
        || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(a, b)
}
fn carrier_requirement(fact: &Fact, source: &Obj, dimension: &Obj) -> bool {
    match fact {
        Fact::AtomicFact(AtomicFact::SubsetFact(f)) => {
            same_object(&f.left, source) && vector_carrier(&f.right, dimension)
        }
        Fact::AtomicFact(AtomicFact::EqualFact(f)) => {
            vector_carrier(source, dimension)
                && vector_carrier(&f.left, dimension)
                && vector_carrier(&f.right, dimension)
        }
        _ => false,
    }
}

pub(super) fn validate_limit_context(
    args: &[Obj],
    req: &[Fact],
    source: &CompleteFunctionDomainProof,
    output_dimension: Option<&Obj>,
) -> Result<(), LeanCompileError> {
    let [group] = source.signature.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("Signature"));
    };
    if args.len() < 3
        || group.params.len() != 1
        || req.len() != 4 + usize::from(output_dimension.is_some())
    {
        return Err(invalid("ContextArity"));
    }
    let binder = group.params[0].id;
    if contains_parameter(&group.param_type, binder)
        || contains_parameter(&source.signature.ret_set, binder)
        || args.iter().any(|arg| contains_parameter(arg, binder))
    {
        return Err(invalid("SignatureCapture"));
    }
    if !matches!(&req[0],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[2].ir()&&f.set==Obj::StandardSet(StandardSet::NPos))
    {
        return Err(invalid("PositiveInputDimension"));
    }
    if !carrier_requirement(&req[1], &group.param_type, &args[2]) {
        return Err(invalid("InputCarrier"));
    }
    let output_index = if let Some(dimension) = output_dimension {
        if !matches!(&req[2],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==dimension.ir()&&f.set==Obj::StandardSet(StandardSet::NPos))
        {
            return Err(invalid("PositiveOutputDimension"));
        }
        if !carrier_requirement(&req[3], &source.signature.ret_set, dimension) {
            return Err(invalid("OutputCarrier"));
        }
        3
    } else {
        if !matches!(&req[2],Fact::AtomicFact(AtomicFact::SubsetFact(f)) if same_object(&f.left,&source.signature.ret_set)&&f.right==Obj::StandardSet(StandardSet::R))
        {
            return Err(invalid("RealOutput"));
        }
        2
    };
    if !matches!(&req[output_index+1],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[1].ir()&&vector_carrier(&f.set,&args[2]))
    {
        return Err(invalid("PointVector"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_euclidean_limit_function_context(
        &self,
        args: &[Obj],
        req: &[Fact],
        source: &CompleteFunctionDomainProof,
        output_dimension: Option<&Obj>,
        scope: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_limit_context(args, req, source, output_dimension)?;
        let base = self.compile_object_reference(
            &source.signature.set_bound_parameters.groups[0].param_type,
            scope,
        )?;
        let output = self.compile_object_reference(&source.signature.ret_set, scope)?;
        let f = self.compile_object_reference(&args[0], scope)?;
        let n = self.compile_object_reference(&args[2], scope)?;
        let strip = if source.signature.dom_facts.is_empty() {
            "exact hsource"
        } else {
            "exact ((Litex.SetSemantics.sep_members _ _ _).mp hsource).1"
        };
        let transfer = |index: usize,
                        variable: &str,
                        hypothesis: &str|
         -> Result<String, LeanCompileError> {
            let name = format!("h_{}", req[index].fact_id().value());
            match &req[index] {
                Fact::AtomicFact(AtomicFact::SubsetFact(_)) => {
                    Ok(format!("exact {name} {variable} {hypothesis}"))
                }
                Fact::AtomicFact(AtomicFact::EqualFact(eq)) => {
                    let left = self.compile_object_reference(&eq.left, scope)?;
                    Ok(format!("have hleft : M.mem {variable} (Litex.denote {left}) := {hypothesis}\nexact (congrArg (fun D => M.mem {variable} D) {name}).mp hleft"))
                }
                _ => Err(invalid("CarrierProof")),
            }
        };
        let input_transfer = transfer(1, "input", "hbase")?;
        let output_index = if output_dimension.is_some() { 3 } else { 2 };
        let output_transfer = transfer(output_index, "value", "hvalue")?;
        let predicate = if let Some(m) = output_dimension {
            format!("Litex.VectorMultivariableFunctionValue M (Litex.denote {f}) (Litex.denote {n}) (Litex.denote {})", self.compile_object_reference(m, scope)?)
        } else {
            format!("Litex.RealMultivariableFunctionValue M (Litex.denote {f}) (Litex.denote {n})")
        };
        Ok(format!("  have _multivariable_real : {predicate} := by\n    refine ⟨_multivariable_signature,_multivariable_member,?_,?_⟩\n    · intro input hinput\n      have hsource : M.mem input _multivariable_source_domain := (congrArg (fun D => M.mem input D) _multivariable_domain_match).mpr hinput\n      have hbase : M.mem input (Litex.denote {base}) := by\n        {strip}\n      {}\n    · intro value hvalue\n      have hvalue : M.mem value (Litex.denote {output}) := hvalue\n      {}", input_transfer.replace('\n',"\n      "),output_transfer.replace('\n',"\n      ")))
    }
}
