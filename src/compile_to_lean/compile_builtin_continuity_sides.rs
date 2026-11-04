//! Three original side-continuity schemas; point membership remains conclusion WD.
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ContinuitySidesBuiltin/{stage}"))
}
fn at(fact: &Fact, function: &Obj, point: &Obj, side: RealApproachSide) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.function.ir()==function.ir() && f.point.ir()==point.ir() && f.side==side)
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_continuity_sides(
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
        let side = match builtin.theorem {
            FnContinuousAtToLeft => RealApproachSide::Left,
            FnContinuousAtToRight => RealApproachSide::Right,
            FnContinuousFromSides => RealApproachSide::Both,
            _ => return Err(invalid("Identity")),
        };
        let count = if side == RealApproachSide::Both { 5 } else { 4 };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != 2
            || args.len() != builtin.theorem.arity()
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        let (signature, _) = real_limit_signature(&req[..3], &args[0])?;
        if side == RealApproachSide::Both {
            if !at(&req[3], &args[0], &args[1], RealApproachSide::Left)
                || !at(&req[4], &args[0], &args[1], RealApproachSide::Right)
            {
                return Err(invalid("LeftAndRightPremises"));
            }
        } else if !at(&req[3], &args[0], &args[1], RealApproachSide::Both) {
            return Err(invalid("BothPremise"));
        }
        let goal = &builtin.conclusions[0];
        if !at(goal, &args[0], &args[1], side) {
            return Err(invalid("ExactConclusion"));
        }
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        self.compile_fact_wd(&conclusions_wd[0], goal, &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let statement = self.compile_formed_fact_proposition(&conclusions_wd[0], goal, &formed)?;
        let (Fact::AtomicFact(atom), FactWellDefinedProof::AtomicExceptEquality(wd)) =
            (goal, &conclusions_wd[0])
        else {
            return Err(invalid("ConclusionFormation"));
        };
        let point = self.compile_continuity_point_formation(atom, wd, &formed)?;
        if !signature_domain_matches(&point.domain, signature) {
            return Err(invalid("OriginalCompleteDomain"));
        }
        // Original argument constructors must be emitted before a native
        // context can refer to their lexical object names.
        let mut context = point.bindings;
        context.extend(self.compile_function_limit_context(
            0,
            &args[0],
            &point.domain,
            &req[..3],
            &refs[..3],
            &scope,
        )?);
        let f = point.function;
        let p = point.point;
        let hp = point.membership;
        context.push(if side==RealApproachSide::Both {
            format!("exact Litex.functionContinuousAtFromSides (Litex.denote {f}) (Litex.denote {p}) _law_real_0 {hp} {} {}",refs[3],refs[4])
        } else {
            let side=super::compile_function_continuity::continuity_side(side);
            format!("exact Litex.functionContinuousAtRestrictSide .{side} (Litex.denote {f}) (Litex.denote {p}) _law_real_0 {hp} {}",refs[3])
        });
        let proof = format!(
            "(by\n{}\n)",
            context
                .join("\n")
                .lines()
                .map(|line| format!("  {line}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
