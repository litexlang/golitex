//! Ordinary/one-sided bridges preserve the domain's explicit side accumulation.
use super::compile_function_limit::finite_side;
use super::compile_function_limit_definition::{
    signature_domain_matches, validate_accumulation_clause,
};
use super::compile_function_limit_unary::real_limit_signature;
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FunctionLimitSides/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_function_limit_sides(
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
        let mismatch = builtin.theorem == FnLimitSidesMismatch;
        let narrow = matches!(builtin.theorem, FnLimitAtToLeft | FnLimitAtToRight);
        if !matches!(
            builtin.theorem,
            FnLimitAtToLeft | FnLimitAtToRight | FnLimitFromSides | FnLimitSidesMismatch
        ) {
            return Err(invalid("Id"));
        }
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = 7 + usize::from(mismatch);
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain { name } if name == builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != 3 + usize::from(mismatch)
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let req = &builtin.requirements;
        let (signature, _) = real_limit_signature(&req[..3], &args[0])?;
        for index in 1..=2 {
            if !matches!(&req[index+2], Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == args[index].ir() && f.set == Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("RealPointOrValue"));
            }
        }
        let at = LimitApproach::AtPoint(args[1].clone().into());
        let left = LimitApproach::FromLeft(args[1].clone().into());
        let right = LimitApproach::FromRight(args[1].clone().into());
        let candidate = |fact: &Fact, approach: &LimitApproach, value: &Obj| {
            matches!(fact,
            Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(f))
                if f.function.ir() == args[0].ir() && f.approach == *approach && f.value.ir() == value.ir())
        };
        if !candidate(&req[5], if narrow { &at } else { &left }, &args[2])
            || (!narrow && !candidate(&req[6], &right, &args[if mismatch { 3 } else { 2 }]))
        {
            return Err(invalid("Candidates"));
        }
        let goal = &builtin.conclusions[0];
        let domain = if narrow {
            let side = if builtin.theorem == FnLimitAtToLeft {
                &left
            } else {
                &right
            };
            if !candidate(goal, side, &args[2]) {
                return Err(invalid("NarrowConclusion"));
            }
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(goal)) = goal else {
                unreachable!()
            };
            let domain = validate_accumulation_clause(goal, &req[6])?;
            if !signature_domain_matches(domain, signature) {
                return Err(invalid("AccumulationDomain"));
            }
            Some(domain)
        } else if mismatch {
            if !matches!(&req[7], Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                if f.left.ir() == args[2].ir() && f.right.ir() == args[3].ir())
            {
                return Err(invalid("DifferentValues"));
            }
            let Fact::ForallFact(all) = goal else {
                return Err(invalid("MismatchConclusion"));
            };
            let value = parameter(&all.typed_parameters, &Obj::StandardSet(StandardSet::R))?;
            let x = Obj::Identifier(IdentifierObj::from_bound_name(value));
            if !all.dom_facts.is_empty()
                || args.iter().any(|a| contains_parameter(a, value.id))
                || !matches!(all.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NotHasFunctionLimitFact(f))]
                    if f.function.ir() == args[0].ir() && f.approach == at && f.value.ir() == x.ir())
            {
                return Err(invalid("MismatchSubject"));
            }
            None
        } else {
            if !candidate(goal, &at, &args[2]) {
                return Err(invalid("CombinedConclusion"));
            }
            None
        };
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let object = |a: &Obj| {
            self.compile_object_reference(a, &scope)
                .map(|s| format!("(Litex.denote {s})"))
        };
        let mut steps = Vec::new();
        if let Some(domain) = domain {
            steps.extend(self.compile_function_limit_context(
                0,
                &args[0],
                domain,
                &req[..3],
                &refs[..3],
                &scope,
            )?);
            let side = if builtin.theorem == FnLimitAtToLeft {
                &left
            } else {
                &right
            };
            let (side, _) = finite_side(side)?;
            steps.push(format!("exact Litex.finiteFunctionLimitRestrictSide .{side} {} {} {} _law0_domain _law_real_0 _law_domain_0 {} {}", object(&args[0])?, object(&args[1])?, object(&args[2])?, refs[6], refs[5]));
        } else if mismatch {
            steps.push("intro _Host _rep _value _member".into());
            steps.push(format!("exact Litex.finiteFunctionLimitSidesDifferent {} {} {} {} {} {} {} (Litex.denote _value)", object(&args[0])?, object(&args[1])?, object(&args[2])?, object(&args[3])?, refs[5], refs[6], refs[7]));
        } else {
            steps.push(format!(
                "exact Litex.finiteFunctionLimitFromSides {} {} {} {} {}",
                object(&args[0])?,
                object(&args[1])?,
                object(&args[2])?,
                refs[5],
                refs[6]
            ));
        }
        Ok((
            definitions,
            format!(
                "(show {statement} from (by\n  {}\n))",
                steps.join("\n").replace('\n', "\n  ")
            ),
            builtin.conclusions.clone(),
        ))
    }
}
