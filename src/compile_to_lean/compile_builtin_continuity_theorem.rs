//! Replay explicit continuity introduction and epsilon-control certificates.
use super::compile_function_continuity::continuity_side;
use super::compile_function_continuity_definition::{
    validate_continuity_clause, validate_continuity_control,
};
use super::compile_function_limit_definition::signature_domain_matches;
use super::compile_function_limit_unary::real_limit_signature;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_continuity_theorem(
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
        use ContinuityLaw::*;
        let (side, law) = match builtin.theorem {
            FnContinuousAtFromEpsilon => (RealApproachSide::Both, FromEpsilon),
            FnContinuousLeftFromEpsilon => (RealApproachSide::Left, FromEpsilon),
            FnContinuousRightFromEpsilon => (RealApproachSide::Right, FromEpsilon),
            FnContinuousAtControl => (RealApproachSide::Both, Control),
            FnContinuousLeftControl => (RealApproachSide::Left, Control),
            FnContinuousRightControl => (RealApproachSide::Right, Control),
            FnContinuousAtConstant => (RealApproachSide::Both, Constant),
            FnContinuousLeftConstant => (RealApproachSide::Left, Constant),
            FnContinuousRightConstant => (RealApproachSide::Right, Constant),
            FnContinuousAtIdentity => (RealApproachSide::Both, Identity),
            FnContinuousLeftIdentity => (RealApproachSide::Left, Identity),
            FnContinuousRightIdentity => (RealApproachSide::Right, Identity),
            FnContinuousAtFromLimit => (RealApproachSide::Both, FromLimit),
            FnContinuousLeftFromLimit => (RealApproachSide::Left, FromLimit),
            FnContinuousRightFromLimit => (RealApproachSide::Right, FromLimit),
            FnContinuousAtToLimit => (RealApproachSide::Both, ToLimit),
            FnContinuousLeftToLimit => (RealApproachSide::Left, ToLimit),
            FnContinuousRightToLimit => (RealApproachSide::Right, ToLimit),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let control = matches!(law, Control);
        let constant = matches!(law, Constant);
        let to_limit = matches!(law, ToLimit);
        let count = if control || constant || to_limit {
            6
        } else {
            5
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != if control || constant { 3 } else { 2 }
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
        let Fact::AtomicFact(AtomicFact::InFact(point)) = &req[3] else {
            return Err(invalid("PointMember"));
        };
        if point.element.ir() != args[1].ir() || !signature_domain_matches(&point.set, signature) {
            return Err(invalid("PointDomain"));
        }
        let domain = &point.set;
        let (source, goal) = if control || to_limit {
            (&req[4], &builtin.conclusions[0])
        } else {
            (&builtin.conclusions[0], &req[4])
        };
        let Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(source)) = source else {
            return Err(invalid("ContinuityFact"));
        };
        if source.side != side
            || source.function.ir() != args[0].ir()
            || source.point.ir() != args[1].ir()
        {
            return Err(invalid("ContinuitySubject"));
        }
        if control {
            if !matches!(&req[5],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[2].ir()&&f.set==Obj::StandardSet(StandardSet::RPos))
            {
                return Err(invalid("EpsilonMember"));
            }
            let Fact::ExistFact(exists) = goal else {
                return Err(invalid("ControlExistence"));
            };
            validate_continuity_control(source, domain, &args[2], exists)?;
        } else if matches!(law, FromEpsilon) {
            validate_continuity_clause(source, domain, goal)?;
        } else if matches!(law, FromLimit | ToLimit) {
            let Fact::AtomicFact(AtomicFact::HasFunctionLimitFact(candidate)) = goal else {
                return Err(invalid("PointValueLimit"));
            };
            if candidate.function.ir() != args[0].ir()
                || candidate.approach != source.side.limit_approach(args[1].clone())
                || !super::compile_sequence_analysis::call_matches(
                    &candidate.value,
                    &args[0],
                    &args[1],
                )
            {
                return Err(invalid("PointValueLimitSubject"));
            }
            if to_limit
                && !matches!(&req[5],Fact::AtomicFact(AtomicFact::RealAccumulationFact(f))
                if f.side==source.side&&f.domain.ir()==domain.ir()&&f.point.ir()==args[1].ir())
            {
                return Err(invalid("AccumulationSubject"));
            }
        } else {
            if constant
                && !matches!(&req[4],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[2].ir()&&f.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("ConstantReal"));
            }
            let Fact::ForallFact(all) = &req[count - 1] else {
                return Err(invalid("Formula"));
            };
            let x = super::compile_real_set_bounds::parameter(&all.typed_parameters, domain)?;
            let input = Obj::Identifier(IdentifierObj::from_bound_name(x));
            let value = if constant { &args[2] } else { &input };
            if !all.dom_facts.is_empty()
                || args
                    .iter()
                    .any(|a| super::compile_real_set_bounds::contains_parameter(a, x.id))
                || !matches!(all.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] if super::compile_sequence_analysis::call_matches(&eq.left,&args[0],&input)&&eq.right.ir()==value.ir())
            {
                return Err(invalid("FormulaSubject"));
            }
        }
        let mut definitions = Vec::new();
        let mut references = Vec::new();
        for (index, ((fact, checked), stored)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(invalid("PremiseSubject"));
            }
            self.validate_store(&stored.store, fact)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            let reference = format!("h_{}", fact.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                stored,
                fact,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            references.push(reference);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let goal = &builtin.conclusions[0];
        self.compile_fact_wd(&conclusions_wd[0], goal, &formed)?;
        let statement = self.compile_formed_fact_proposition(&conclusions_wd[0], goal, &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let context = self.compile_function_limit_context(
            0,
            &args[0],
            domain,
            &req[..3],
            &references[..3],
            &scope,
        )?;
        let objects = args
            .iter()
            .map(|a| self.compile_object_reference(a, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let side = continuity_side(side);
        let point_member=format!("(show M.mem (Litex.denote {}) (Litex.FunctionSemantics.domainValue (Litex.denote {})) from _law_domain_0 ▸ {})",objects[1],objects[0],references[3]);
        let law = if control {
            format!("obtain ⟨_delta, _delta_member, _control⟩ := Litex.functionContinuousAtControl .{side} {} {} {} {} {}\nrw [← _law_domain_0] at _control\nexact ⟨_delta, _delta_member, _control⟩",objects[0],objects[1],objects[2],references[5],references[4])
        } else if matches!(law, FromEpsilon) {
            format!("exact Litex.functionContinuousAtOfForall .{side} {} {} _law0_domain _law_domain_0 {}",objects[0],objects[1],references[4])
        } else if matches!(law, FromLimit) {
            format!("exact Litex.functionContinuousAtOfLimit .{side} (Litex.denote {}) (Litex.denote {}) _law_real_0 {point_member} {}",objects[0],objects[1],references[4])
        } else if to_limit {
            let accumulation=format!("(show Litex.RealAccumulationValue M .{side} (Litex.FunctionSemantics.domainValue (Litex.denote {})) (Litex.denote {}) from _law_domain_0 ▸ {})",objects[0],objects[1],references[5]);
            format!("exact Litex.functionLimitOfContinuousAt .{side} (Litex.denote {}) (Litex.denote {}) _law_real_0 {point_member} {} {accumulation}",objects[0],objects[1],references[4])
        } else {
            let formula=format!("(by\n  intro x hx\n  exact {} (Litex.semanticObject x (M.member_isSet hx)) (show M.mem x (Litex.denote _law0_domain) from _law_domain_0.symm ▸ hx)\n)",references[count-1]);
            // The raw law shares the same certified graph and source formula.
            if constant {
                format!("exact Litex.functionContinuousAtOfConstant .{side} (Litex.denote {}) (Litex.denote {}) (Litex.denote {}) _law_real_0 {point_member} {} {formula}",objects[0],objects[1],objects[2],references[4])
            } else {
                format!("exact Litex.functionContinuousAtOfIdentity .{side} (Litex.denote {}) (Litex.denote {}) _law_real_0 {point_member} {formula}",objects[0],objects[1])
            }
        };
        let body = format!("{}\n{law}", context.join("\n"));
        let body = body
            .lines()
            .map(|s| format!("  {s}"))
            .collect::<Vec<_>>()
            .join("\n");
        Ok((
            definitions,
            format!("(show {statement} from by\n{body}\n)"),
            builtin.conclusions.clone(),
        ))
    }
}
enum ContinuityLaw {
    FromEpsilon,
    Control,
    Constant,
    Identity,
    FromLimit,
    ToLimit,
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ContinuityTheorem/{stage}"))
}
