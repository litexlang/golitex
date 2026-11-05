//! Replay the original definition and restriction NativeSchemas without search.
use super::compile_antiderivative::{context_count, invalid, parts, validate_context};
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_analysis::call_matches;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;
use std::collections::HashMap;

fn candidate(fact: &Fact, args: &[&Obj]) -> Result<(), LeanCompileError> {
    let Fact::AtomicFact(p) = fact else {
        return Err(invalid("PositivePredicate"));
    };
    let Some((actual, false)) = parts(p) else {
        return Err(invalid("PositivePredicate"));
    };
    if actual.len() != 3
        || args.len() != 3
        || !actual.iter().zip(args).all(|(a, b)| a.ir() == b.ir())
    {
        return Err(invalid("PredicateArguments"));
    }
    Ok(())
}
fn definition(fact: &Fact, args: &[Obj]) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(p) = fact else {
        return Err(invalid("DefiningUniversal"));
    };
    let point = parameter(&p.typed_parameters, &args[2])?;
    if !p.dom_facts.is_empty() || args.iter().any(|a| contains_parameter(a, point.id)) {
        return Err(invalid("DefiningScope"));
    }
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::HasDerivativeAtFact(d))] =
        p.then_facts.as_slice()
    else {
        return Err(invalid("DefiningDerivative"));
    };
    let input = Obj::Identifier(IdentifierObj::from_bound_name(point));
    if d.function.ir() != args[0].ir()
        || d.point.ir() != input.ir()
        || !call_matches(&d.value, &args[1], &input)
    {
        return Err(invalid("DefiningDerivativeSubject"));
    }
    Ok(())
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_antiderivative(
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
        let (fold, restrict) = match builtin.theorem {
            BuiltinTheoremId::AntiderivativeFromDefinition => (true, false),
            BuiltinTheoremId::AntiderivativeToDefinition => (false, false),
            BuiltinTheoremId::AntiderivativeRestrict => (false, true),
            _ => return Err(invalid("Identity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if args.len() != 3 + usize::from(restrict) {
            return Err(invalid("Arguments"));
        }
        let context = context_count(&args[2])?;
        let count = context + 1 + usize::from(restrict);
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        validate_context(&args[..3], &req[..context].iter().collect::<Vec<_>>())?;
        if fold {
            definition(&req[context], args)?;
            candidate(&builtin.conclusions[0], &[&args[0], &args[1], &args[2]])?;
        } else {
            candidate(&req[context], &[&args[0], &args[1], &args[2]])?;
            if restrict {
                if !matches!(&req[context+1],Fact::AtomicFact(AtomicFact::SubsetFact(p)) if p.left.ir()==args[3].ir() && p.right.ir()==args[2].ir())
                {
                    return Err(invalid("RestrictionSubset"));
                }
                candidate(&builtin.conclusions[0], &[&args[0], &args[1], &args[3]])?;
            } else {
                definition(&builtin.conclusions[0], args)?;
            }
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
        let head = raw[..3].join(" ");
        let original = &refs[context];
        let proof = if fold {
            format!("(by\n  apply Litex.antiderivativeFromDefiningClause {head}\n  intro x hx\n  exact {original} (Litex.semanticObject x (M.member_isSet hx)) hx\n)")
        } else if restrict {
            format!(
                "(Litex.antiderivativeRestrict {head} {} {} {original})",
                raw[3],
                refs[context + 1]
            )
        } else {
            format!("(by\n  intro _PointHost _PointRep x hx\n  exact Litex.antiderivativeDefiningClause {head} {original} (Litex.denote x) hx\n)")
        };
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
