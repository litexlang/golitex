//! Replay Jacobian/Hessian projections through their original candidate captures.
use super::compile_builtin_derivative_schema::validate_context;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::multivariable::helper as schema;
use crate::prelude::*;
use crate::rational_expression::helper::sub_objs;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("MatrixDifferential/{stage}"))
}
fn relation(fact: &Fact) -> Result<&MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = fact else {
        return Err(invalid("PositiveRelation"));
    };
    Ok(&p.relation)
}
fn candidate(fact: &Fact, name: &str, args: &[&Obj]) -> Result<(), LeanCompileError> {
    let r = relation(fact)?;
    let actual = r.argument_refs();
    if r.predicate_name() != name
        || actual.len() != args.len()
        || !actual.iter().zip(args).all(|(a, b)| a.ir() == b.ir())
    {
        return Err(invalid("OriginalCandidate"));
    }
    Ok(())
}
fn trace_target(value: &Obj, matrix: &Obj, n: &Obj) -> bool {
    matches!(value, Obj::MatrixOperator(MatrixOperator::Trace(p))
        if p.matrix.ir()==matrix.ir() && p.order.ir()==n.ir())
}
fn curl_target(value: &Obj, matrix: &Obj) -> bool {
    let Obj::ProductShape(ProductShape::Tuple(p)) = value else {
        return false;
    };
    let entry = |i, j| schema::apply(matrix, vec![schema::number(i), schema::number(j)]);
    let wanted = [
        sub_objs(entry(3, 2), entry(2, 3)),
        sub_objs(entry(1, 3), entry(3, 1)),
        sub_objs(entry(2, 1), entry(1, 2)),
    ];
    p.args.len() == 3 && p.args.iter().zip(wanted).all(|(a, b)| a.ir() == b.ir())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_matrix_differential(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        use BuiltinTheoremId::*;
        let (context, source_name, target_name, law) = match builtin.theorem {
            JacobianAtDivergence => (
                6,
                "has_jacobian_at",
                "has_divergence_at",
                "divergenceOfJacobianMatrix",
            ),
            HessianAtLaplacian => (
                5,
                "has_hessian_at",
                "has_laplacian_at",
                "laplacianOfHessianMatrix",
            ),
            JacobianAtCurl => (6, "has_jacobian_at", "has_curl_at", "curlOfJacobianMatrix"),
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = context + 1;
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let three = schema::number(3);
        let curl = builtin.theorem == JacobianAtCurl;
        let n = if curl { &three } else { &args[2] };
        let matrix = if curl { &args[2] } else { &args[3] };
        let mut expected = vec![&args[0], &args[1], n];
        if builtin.theorem != HessianAtLaplacian {
            expected.push(n);
        }
        expected.push(matrix);
        candidate(&builtin.requirements[context], source_name, &expected)?;
        let goal = relation(&builtin.conclusions[0])?;
        let out = goal.argument_refs();
        let valid = goal.predicate_name() == target_name
            && out.len() == if curl { 3 } else { 4 }
            && out[0].ir() == args[0].ir()
            && out[1].ir() == args[1].ir()
            && if curl {
                curl_target(out[2], matrix)
            } else {
                out[2].ir() == n.ir() && trace_target(out[3], matrix, n)
            };
        if !valid {
            return Err(invalid("OriginalOrderedProjection"));
        }
        let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
            &dom_stores[context].infer
        else {
            return Err(invalid("OriginalInference"));
        };
        let [InferMultivariableAnalysisFactResult::Definition(capture)] = rules.as_slice() else {
            return Err(invalid("OriginalInference"));
        };
        if capture.source_fact_id != builtin.requirements[context].fact_id()
            || capture.derived.len() != 2
        {
            return Err(invalid("OriginalInferenceIdentity"));
        }
        let source = capture
            .function_domain
            .as_ref()
            .ok_or_else(|| invalid("OriginalCompleteDomain"))?;
        validate_context(
            relation(&builtin.requirements[context])?,
            &builtin.requirements[..context],
            source,
        )?;
        let (definitions, refs) = self.compile_function_limit_requirements(
            &builtin.requirements,
            dom_proofs,
            dom_stores,
            position,
        )?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let raw = args
            .iter()
            .map(|a| {
                self.compile_object_reference(a, &scope)
                    .map(|v| format!("(Litex.denote {v})"))
            })
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let natural = if curl {
            String::new()
        } else {
            format!(
                " (Litex.inNPos_natural {} {})",
                self.compile_object_reference(n, &scope)?,
                refs[0]
            )
        };
        let proof = format!("(Litex.{law} {raw}{natural} {})", refs[context]);
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
