//! Replay the original partial-derivative algebra NativeSchemas.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::function_domain::{
    function_domains_alpha_equal, CompleteFunctionDomainProof,
};
use crate::execute::execute_fact_stmt::multivariable::helper as schema;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Operation {
    Add,
    Subtract,
    Multiply,
    Divide,
}
impl Operation {
    fn field(self) -> &'static str {
        match self {
            Self::Add => "addValue",
            Self::Subtract => "subValue",
            Self::Multiply => "mulValue",
            Self::Divide => "divValue",
        }
    }
    fn matches(self, obj: &Obj, a: &Obj, b: &Obj) -> bool {
        let (left, right) = match (self, obj) {
            (Self::Add, Obj::ArithmeticOperator(ArithmeticOperator::Add(x))) => (&x.left, &x.right),
            (Self::Subtract, Obj::ArithmeticOperator(ArithmeticOperator::Sub(x))) => {
                (&x.left, &x.right)
            }
            (Self::Multiply, Obj::ArithmeticOperator(ArithmeticOperator::Mul(x))) => {
                (&x.left, &x.right)
            }
            (Self::Divide, Obj::ArithmeticOperator(ArithmeticOperator::Div(x))) => {
                (&x.left, &x.right)
            }
            _ => return false,
        };
        left.ir() == a.ir() && right.ir() == b.ir()
    }
    fn coefficient(self, args: &[Obj]) -> Obj {
        let a = args[6].clone();
        let b = args[7].clone();
        let fp = schema::apply(&args[0], vec![args[3].clone()]);
        let gp = schema::apply(&args[1], vec![args[3].clone()]);
        match self {
            Self::Add => add_objs(a, b),
            Self::Subtract => sub_objs(a, b),
            Self::Multiply => add_objs(mul_objs(a, gp), mul_objs(fp, b)),
            Self::Divide => div_objs(
                div_objs(
                    sub_objs(mul_objs(a, gp.clone()), mul_objs(fp, b)),
                    gp.clone(),
                ),
                gp,
            ),
        }
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("PartialAlgebra/{stage}"))
}
fn candidate<'a>(
    fact: &'a Fact,
    args: &[&Obj],
) -> Result<&'a MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(p)) = fact else {
        return Err(invalid("PositiveCandidate"));
    };
    if !matches!(
        p.relation,
        MultivariableAnalysisRelation::PartialDerivativeAt(_)
    ) {
        return Err(invalid("CandidateFamily"));
    }
    let actual = p.relation.argument_refs();
    if actual.len() != args.len() || !actual.iter().zip(args).all(|(a, b)| a.ir() == b.ir()) {
        return Err(invalid("CandidateArguments"));
    }
    Ok(&p.relation)
}
fn inferred_source<'a>(
    store: &'a StoreFactAndInferResult,
    fact: &Fact,
) -> Result<&'a CompleteFunctionDomainProof, LeanCompileError> {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &store.infer
    else {
        return Err(invalid("OriginalInference"));
    };
    let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_slice() else {
        return Err(invalid("OriginalInferenceRule"));
    };
    if p.source_fact_id != fact.fact_id() || p.derived.len() != 3 {
        return Err(invalid("OriginalInferenceIdentity"));
    }
    p.function_domain
        .as_ref()
        .ok_or_else(|| invalid("OriginalCompleteDomain"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_partial_algebra(
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
        let (op, law) = match builtin.theorem {
            BuiltinTheoremId::PartialAtAdd => (Operation::Add, "partialDerivativeAddFunctions"),
            BuiltinTheoremId::PartialAtSubtract => {
                (Operation::Subtract, "partialDerivativeSubFunctions")
            }
            BuiltinTheoremId::PartialAtMultiply => {
                (Operation::Multiply, "partialDerivativeMulFunctions")
            }
            BuiltinTheoremId::PartialAtDivide => {
                (Operation::Divide, "partialDerivativeDivFunctions")
            }
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = 21 + usize::from(op == Operation::Divide);
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != 8
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        let first = candidate(
            &req[18],
            &[&args[0], &args[3], &args[4], &args[5], &args[6]],
        )?;
        let second = candidate(
            &req[19],
            &[&args[1], &args[3], &args[4], &args[5], &args[7]],
        )?;
        let coefficient = op.coefficient(args);
        let output = candidate(
            &builtin.conclusions[0],
            &[&args[2], &args[3], &args[4], &args[5], &coefficient],
        )?;
        let source_f = inferred_source(&dom_stores[18], &req[18])?;
        let source_g = inferred_source(&dom_stores[19], &req[19])?;
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &conclusions_wd[0] else {
            return Err(invalid("OriginalFormation"));
        };
        let PredicateDomainProof::MultivariableAnalysis(formation) = &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedFormation"))?
            .predicate_domain
        else {
            return Err(invalid("OriginalFormationDomain"));
        };
        if formation.requirements.len() != 7 {
            return Err(invalid("OriginalFormationStages"));
        }
        let source_h = &formation.function_domain;
        for source in [source_g, source_h] {
            if !function_domains_alpha_equal(&source_f.signature, &source.signature) {
                return Err(invalid("SameCompleteDomains"));
            }
        }
        for (i, (r, source)) in [(first, source_f), (second, source_g), (output, source_h)]
            .into_iter()
            .enumerate()
        {
            super::compile_builtin_derivative_schema::validate_context(
                r,
                &req[6 * i..6 * i + 6],
                source,
            )?;
        }
        let domain =
            schema::actual_domain(&source_f.signature).ok_or_else(|| invalid("OriginalDomain"))?;
        let Fact::ForallFact(formula) = &req[20] else {
            return Err(invalid("OriginalFormula"));
        };
        let x = parameter(&formula.typed_parameters, &domain)?;
        if !formula.dom_facts.is_empty()
            || args
                .iter()
                .chain([&domain])
                .any(|a| contains_parameter(a, x.id))
        {
            return Err(invalid("FormulaCapture"));
        }
        let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
        if !matches!(formula.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))]
            if call_matches(&eq.left,&args[2],&input) && op.matches(&eq.right,&schema::apply(&args[0],vec![input.clone()]),&schema::apply(&args[1],vec![input.clone()])))
        {
            return Err(invalid("OriginalPointwiseOperation"));
        }
        if op == Operation::Divide
            && !matches!(&req[21],Fact::AtomicFact(AtomicFact::NotEqualFact(p))
            if call_matches(&p.left,&args[1],&args[3]) && closed_integer(&p.right)==Some(0))
        {
            return Err(invalid("OriginalDenominatorNonzero"));
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
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
            .map(|o| self.compile_function_raw_expression_bound(o, &scope, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let dimension_object = self.compile_object_reference(&args[4], &scope)?;
        let source_domain =
            self.compile_function_raw_expression_bound(&domain, &scope, &HashMap::new())?;
        let mut lines = Vec::new();
        let nested = |s: &str| format!("  {}", s.replace('\n', "\n  "));
        for (i, source) in [source_f, source_g, source_h].into_iter().enumerate() {
            let (view, equal) = self.compile_multivariable_limit_view(&args[i], source, &scope)?;
            let real = self.compile_euclidean_limit_function_context(
                &[args[i].clone(), args[3].clone(), args[4].clone()],
                &req[6 * i..6 * i + 4],
                source,
                None,
                &scope,
            )?;
            lines.push(format!("  have _partial_real_{i} : Litex.RealMultivariableFunctionValue M {} {} := by\n{}\n{}\n    exact _multivariable_real",raw[i],raw[4],nested(&view),nested(&real)));
            lines.push(format!("  have _partial_domain_{i} : {source_domain} = Litex.FunctionSemantics.domainValue {} := by\n{}\n    exact {equal}",raw[i],nested(&view)));
        }
        let field = op.field();
        let f = &raw[0];
        let g = &raw[1];
        let h = &raw[2];
        lines.push(format!("  have _partial_formula : ∀ x, M.mem x (Litex.FunctionSemantics.domainValue {f}) → Litex.FunctionSemantics.callValue {h} x = M.{field} (Litex.FunctionSemantics.callValue {f} x) (Litex.FunctionSemantics.callValue {g} x) := by\n    intro x hx\n    have hx : M.mem x {source_domain} := _partial_domain_0.symm ▸ hx\n    exact {} (Litex.semanticObject x (M.member_isSet hx)) hx",refs[20]));
        let nonzero = if op == Operation::Divide {
            format!(" {}", refs[21])
        } else {
            String::new()
        };
        lines.push(format!("  exact Litex.{law} {} (Litex.inNPos_natural {} {}) {} {} _partial_real_0 _partial_real_1 _partial_real_2 (_partial_domain_1.symm.trans _partial_domain_0) (_partial_domain_2.symm.trans _partial_domain_0) (_partial_domain_0 ▸ {}) _partial_formula{nonzero} {} {}",raw.join(" "),dimension_object,refs[0],refs[3],refs[5],refs[4],refs[18],refs[19]));
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof = format!("(by\n{}\n)", lines.join("\n"));
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
