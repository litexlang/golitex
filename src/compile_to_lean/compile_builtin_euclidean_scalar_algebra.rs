//! Replay scalar Euclidean algebra from its unchanged ordered NativeSchema.
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
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferMultivariableAnalysisFactResult, InferResult,
};

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
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("EuclideanScalarAlgebra/{stage}"))
}
fn stage(mut e: LeanCompileError, stage: impl std::fmt::Display) -> LeanCompileError {
    e.message = format!("Euclidean scalar algebra {stage}: {}", e.message);
    e
}
fn candidate<'a>(
    fact: &'a Fact,
    name: &str,
    args: &[Obj],
) -> Result<&'a MultivariableAnalysisRelation, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::MultivariableAnalysisFact(f)) = fact else {
        return Err(invalid("PositiveCandidate"));
    };
    let r = &f.relation;
    if r.predicate_name() != name
        || r.argument_refs().len() != args.len()
        || !r
            .argument_refs()
            .iter()
            .zip(args)
            .all(|(a, b)| a.ir() == b.ir())
    {
        return Err(invalid("CandidateArguments"));
    }
    Ok(r)
}
fn source_domain<'a>(
    store: &'a StoreFactAndInferResult,
    fact: &Fact,
    derived: usize,
) -> Result<&'a CompleteFunctionDomainProof, LeanCompileError> {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::MultivariableAnalysisFact(rules))) =
        &store.infer
    else {
        return Err(invalid("OriginalInference"));
    };
    let [InferMultivariableAnalysisFactResult::Definition(p)] = rules.as_slice() else {
        return Err(invalid("OriginalInference"));
    };
    if p.source_fact_id != fact.fact_id() || p.derived.len() != derived {
        return Err(invalid("OriginalInferenceIdentity"));
    }
    p.function_domain
        .as_ref()
        .ok_or_else(|| invalid("OriginalCompleteDomain"))
}
impl LitexToLeanCompiler {
    fn scalar_algebra_domain_view(
        &self,
        f: &Obj,
        proof: &CompleteFunctionDomainProof,
        prefix: &str,
        scope: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let domain =
            schema::actual_domain(&proof.signature).ok_or_else(|| invalid("ActualDomain"))?;
        let signature = self.compile_complete_domain_signature(proof, scope)?;
        let member = self.compile_complete_domain_member(f, proof, scope)?;
        self.compile_named_limit_domain_view(
            f,
            &domain,
            &proof.signature,
            &signature,
            &member,
            prefix,
            scope,
        )
    }
    pub(super) fn compile_builtin_euclidean_scalar_algebra(
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
        let (continuous, op, law) = match builtin.theorem {
            MultiLimitAtAdd => (false, Operation::Add, "scalarMultivariableLimitAdd"),
            MultiLimitAtSubtract => (
                false,
                Operation::Subtract,
                "scalarMultivariableLimitSubtract",
            ),
            MultiLimitAtMultiply => (
                false,
                Operation::Multiply,
                "scalarMultivariableLimitMultiply",
            ),
            MultiLimitAtDivide => (false, Operation::Divide, "scalarMultivariableLimitDivide"),
            MultiContinuousAtAdd => (true, Operation::Add, "scalarMultivariableContinuousAdd"),
            MultiContinuousAtSubtract => (
                true,
                Operation::Subtract,
                "scalarMultivariableContinuousSubtract",
            ),
            MultiContinuousAtMultiply => (
                true,
                Operation::Multiply,
                "scalarMultivariableContinuousMultiply",
            ),
            MultiContinuousAtDivide => (
                true,
                Operation::Divide,
                "scalarMultivariableContinuousDivide",
            ),
            _ => return Err(invalid("Identity")),
        };
        let context = if continuous { 5 } else { 4 };
        let first_index = 3 * context;
        let second_index = first_index + 1;
        let formula_index = first_index + 2;
        let count = formula_index + 1 + usize::from(op == Operation::Divide);
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
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
        let name = if continuous {
            "is_multi_continuous_at"
        } else {
            "has_multi_limit_at"
        };
        let mut first = vec![args[0].clone(), args[3].clone(), args[4].clone()];
        let mut second = vec![args[1].clone(), args[3].clone(), args[4].clone()];
        if !continuous {
            first.push(args[5].clone());
            second.push(args[6].clone());
        }
        let first_r = candidate(&builtin.requirements[first_index], name, &first)?;
        let second_r = candidate(&builtin.requirements[second_index], name, &second)?;
        let first_source = source_domain(
            &dom_stores[first_index],
            &builtin.requirements[first_index],
            if continuous { 1 } else { 3 },
        )?;
        let second_source = source_domain(
            &dom_stores[second_index],
            &builtin.requirements[second_index],
            if continuous { 1 } else { 3 },
        )?;
        let Fact::AtomicFact(atomic @ AtomicFact::MultivariableAnalysisFact(out)) =
            &builtin.conclusions[0]
        else {
            return Err(invalid("PositiveConclusion"));
        };
        let output_r = &out.relation;
        let out_args = output_r.argument_refs();
        if output_r.predicate_name() != name
            || out_args.len() != if continuous { 3 } else { 4 }
            || out_args[0].ir() != args[2].ir()
            || out_args[1].ir() != args[3].ir()
            || out_args[2].ir() != args[4].ir()
            || (!continuous && !op.matches(out_args[3], &args[5], &args[6]))
        {
            return Err(invalid("OriginalConclusion"));
        }
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
        let req = &builtin.requirements;
        if formation.requirements.len()!=context+usize::from(!continuous)
            || !req[2*context..3*context].iter().zip(&formation.requirements[..context]).all(|(a,b)|crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::quantifier_free_source_facts_alpha_equal(a,&b.requirement)){return Err(invalid("OriginalOutputContext"));}
        let third_source = &formation.function_domain;
        for source in [second_source, third_source] {
            if !function_domains_alpha_equal(&first_source.signature, &source.signature) {
                return Err(invalid("OriginalCommonDomains"));
            }
        }
        let output: Vec<_> = out_args.iter().map(|o| (*o).clone()).collect();
        let all_args = [first, second, output];
        let relations = [first_r, second_r, output_r];
        let sources = [first_source, second_source, third_source];
        for i in 0..3 {
            let prefix = &req[i * context..(i + 1) * context];
            if continuous {
                super::compile_builtin_derivative_schema::validate_context(
                    relations[i],
                    prefix,
                    sources[i],
                )?;
            } else {
                super::compile_multivariable_limit_context::validate_limit_context(
                    &all_args[i],
                    prefix,
                    sources[i],
                    None,
                )?;
            }
        }
        let domain = schema::actual_domain(&first_source.signature)
            .ok_or_else(|| invalid("OriginalDomain"))?;
        let Fact::ForallFact(formula) = &req[formula_index] else {
            return Err(invalid("OriginalFormula"));
        };
        let x = parameter(&formula.typed_parameters, &domain)?;
        if !formula.dom_facts.is_empty()
            || args
                .iter()
                .chain([&domain])
                .any(|o| contains_parameter(o, x.id))
        {
            return Err(invalid("FormulaCapture"));
        }
        let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
        if !matches!(formula.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))]
            if call_matches(&eq.left,&args[2],&input) && op.matches(&eq.right,&schema::apply(&args[0],vec![input.clone()]),&schema::apply(&args[1],vec![input.clone()])))
        {
            return Err(invalid("OriginalPointwiseOperation"));
        }
        if op == Operation::Divide {
            let denominator = if continuous {
                schema::apply(&args[1], vec![args[3].clone()])
            } else {
                args[6].clone()
            };
            if !matches!(&req[formula_index+1],Fact::AtomicFact(AtomicFact::NotEqualFact(f)) if f.left.ir()==denominator.ir() && closed_integer(&f.right)==Some(0))
            {
                return Err(invalid("OriginalDenominatorNonzero"));
            }
        }
        let value_id = if continuous {
            None
        } else {
            let value = &formation.requirements[context];
            if !matches!(&value.requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==out_args[3].ir() && f.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("OriginalValueCarrier"));
            }
            let PredicateDomainRequirementProof::Verified(p) = &value.result else {
                return Err(invalid("OriginalValueProof"));
            };
            if source_subject(p)? != value.requirement {
                return Err(invalid("OriginalValueSubject"));
            }
            Some(value.requirement.fact_id())
        };
        let mut definitions = Vec::new();
        for (i, ((fact, proof), store)) in req.iter().zip(dom_proofs).zip(dom_stores).enumerate() {
            if source_subject(proof)? != *fact {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: i,
                ..*position
            };
            let compiled = self
                .compile_verify(proof, &prior)
                .map_err(|e| stage(e, format!("requirement {i}")))?;
            self.validate_store(&store.store, fact)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            definitions.extend(
                self.compile_stored_inferences(
                    store,
                    fact,
                    &(compiled.0, format!("h_{}", fact.fact_id().value())),
                    &SourcePosition {
                        before: i + 1,
                        ..*position
                    },
                )
                .map_err(|e| stage(e, format!("inference {i}")))?,
            );
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], &builtin.conclusions[0], &formed)?;
        let bindings = self.compile_atomic_wd_locals(wd, atomic, &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::AtomicWDLocals(wd, out_args.len()),
            usize::MAX,
        );
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let raw = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect::<Vec<_>>();
        let mut lines = Vec::new();
        let mut equals = Vec::new();
        for i in 0..3 {
            let (view, eq) = self.scalar_algebra_domain_view(
                &args[i],
                sources[i],
                &format!("scalar_algebra_{i}_"),
                &scope,
            )?;
            lines.push(view);
            equals.push(eq);
            let (view, _) = self.compile_multivariable_limit_view(&args[i], sources[i], &scope)?;
            let function = self.compile_euclidean_limit_function_context(
                &all_args[i],
                &req[i * context..i * context + 4],
                sources[i],
                None,
                &scope,
            )?;
            lines.push(format!("  have _scalar_algebra_real_{i} : Litex.RealMultivariableFunctionValue M {} {} := by\n  {}\n  {}\n    exact _multivariable_real",raw[i],raw[4],view.replace('\n',"\n  "),function.replace('\n',"\n  ")));
        }
        for i in 0..2 {
            lines.push(format!("  have _scalar_algebra_domain_{i} : Litex.FunctionSemantics.domainValue {} = Litex.FunctionSemantics.domainValue {} := ({}).symm.trans ((show _scalar_algebra_{i}_source_domain = _scalar_algebra_2_source_domain from by rfl).trans {})",raw[i],raw[2],equals[i],equals[2]));
        }
        let field = op.field();
        let formula_id = req[formula_index].fact_id().value();
        lines.push(format!("  have _scalar_algebra_formula : ∀ x, M.mem x (Litex.FunctionSemantics.domainValue {}) → Litex.FunctionSemantics.callValue {} x = M.{field} (Litex.FunctionSemantics.callValue {} x) (Litex.FunctionSemantics.callValue {} x) := by\n    intro x hx\n    have hs : M.mem x _scalar_algebra_0_source_domain := ({}).symm ▸ (_scalar_algebra_domain_0.symm ▸ hx)\n    exact h_{formula_id} (Litex.semanticObject x (M.member_isSet hs)) hs",raw[2],raw[2],raw[0],raw[1],equals[0]));
        let specific = if continuous {
            format!(
                " ({} ▸ h_{})",
                equals[2],
                req[3 * context - 1].fact_id().value()
            )
        } else {
            format!(" h_{}", value_id.unwrap().value())
        };
        let denominator = if op == Operation::Divide {
            format!(" h_{}", req[formula_index + 1].fact_id().value())
        } else {
            String::new()
        };
        lines.push(format!("  exact Litex.{law} {} _scalar_algebra_real_0 _scalar_algebra_real_1 _scalar_algebra_real_2 _scalar_algebra_domain_0 _scalar_algebra_domain_1{specific} _scalar_algebra_formula h_{} h_{}{denominator}",raw.join(" "),req[first_index].fact_id().value(),req[second_index].fact_id().value()));
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof = format!(
            "(by\n  {}\n  exact (by\n  {}\n  )\n)",
            bindings.join("\n").replace('\n', "\n  "),
            lines.join("\n").replace('\n', "\n  ")
        );
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
