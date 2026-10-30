//! Consume the original explicit finite sequence-extremum theorem applications.
use super::compile_real_set_bounds::{contains_parameter, parameter};
use super::compile_sequence_extremum::{extremum_parts, validate_extremum_existence};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("SequenceExtremumTheorem/{stage}"))
}
fn candidate(f: &Fact, sequence: &Obj, value: &Obj, upper: bool) -> bool {
    matches!(f,Fact::AtomicFact(f) if extremum_parts(f).is_some_and(|(a,v,u,n)|a.ir()==sequence.ir()&&v.ir()==value.ir()&&u==upper&&!n))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_sequence_extremum_theorem(
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
        let (upper, arity, count) = match builtin.theorem {
            SequenceLimsupConstant => (true, 2, 3),
            SequenceLiminfConstant => (false, 2, 3),
            SequenceLimsupFromLimit | SequenceLimsupExists => (true, 2, 2),
            SequenceLiminfFromLimit | SequenceLiminfExists => (false, 2, 2),
            SequenceLimsupUnique => (true, 3, 3),
            SequenceLiminfUnique => (false, 3, 3),
            SequenceLimsupSelected => (true, 1, 2),
            SequenceLiminfSelected => (false, 1, 2),
            _ => return Err(invalid("Id")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name,AtomicName::Plain{name} if name==builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let req = &builtin.requirements;
        let goal = &builtin.conclusions[0];
        let Fact::AtomicFact(AtomicFact::InFact(member)) = &req[0] else {
            return Err(invalid("SequenceDomain"));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
            return Err(invalid("SequenceSignature"));
        };
        if member.element.ir() != args[0].ir()
            || !matches!(signature.set_bound_parameters.groups.as_slice(),[g] if g.params.len()==1&&g.param_type.as_ref()==&Obj::StandardSet(StandardSet::NPos))
            || !signature.dom_facts.is_empty()
            || signature.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
        {
            return Err(invalid("SequenceSignature"));
        }
        let selected = match builtin.theorem {
            SequenceLimsupConstant | SequenceLiminfConstant => {
                if !matches!(&req[1],Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[1].ir()&&f.set==Obj::StandardSet(StandardSet::R))
                {
                    return Err(invalid("ConstantReal"));
                }
                let Fact::ForallFact(f) = &req[2] else {
                    return Err(invalid("ConstantFormula"));
                };
                let n = parameter(&f.typed_parameters, &Obj::StandardSet(StandardSet::NPos))?;
                if !f.dom_facts.is_empty()
                    || args.iter().any(|a| contains_parameter(a, n.id))
                    || !matches!(f.then_facts.as_slice(),[ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))]
                        if super::compile_sequence_analysis::call_matches(&eq.left,&args[0],&Obj::Identifier(IdentifierObj::from_bound_name(n)))&&eq.right.ir()==args[1].ir())
                    || !candidate(goal, &args[0], &args[1], upper)
                {
                    return Err(invalid("ConstantSubject"));
                }
                None
            }
            SequenceLimsupFromLimit | SequenceLiminfFromLimit => {
                if !matches!(&req[1],Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) if f.sequence.ir()==args[0].ir()&&f.value.ir()==args[1].ir())
                    || !candidate(goal, &args[0], &args[1], upper)
                {
                    return Err(invalid("LimitSubject"));
                }
                None
            }
            SequenceLimsupExists | SequenceLiminfExists => {
                if !candidate(&req[1], &args[0], &args[1], upper) {
                    return Err(invalid("ExistencePremise"));
                }
                validate_extremum_existence(&args[0], upper, goal)?;
                None
            }
            SequenceLimsupUnique | SequenceLiminfUnique => {
                if !candidate(&req[1], &args[0], &args[1], upper)
                    || !candidate(&req[2], &args[0], &args[2], upper)
                    || !matches!(goal,Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.left.ir()==args[1].ir()&&eq.right.ir()==args[2].ir())
                {
                    return Err(invalid("UniqueSubject"));
                }
                None
            }
            SequenceLimsupSelected | SequenceLiminfSelected => {
                validate_extremum_existence(&args[0], upper, &req[1])?;
                let Fact::AtomicFact(f) = goal else {
                    return Err(invalid("SelectedConclusion"));
                };
                let (_, value, _, _) = extremum_parts(f).ok_or_else(|| invalid("SelectedKind"))?;
                let source = match (value, upper) {
                    (Obj::LimitOperator(LimitOperator::SequenceLimsup(s)), true) => {
                        s.sequence.as_ref()
                    }
                    (Obj::LimitOperator(LimitOperator::SequenceLiminf(s)), false) => {
                        s.sequence.as_ref()
                    }
                    _ => return Err(invalid("SelectedKind")),
                };
                if !candidate(goal, &args[0], value, upper) || source.ir() != args[0].ir() {
                    return Err(invalid("SelectedSubject"));
                }
                Some(value)
            }
            _ => unreachable!(),
        };
        let (definitions, refs) =
            self.compile_function_limit_requirements(req, dom_proofs, dom_stores, position)?;
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let objects = args
            .iter()
            .map(|a| self.compile_object_reference(a, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let hf=format!("(Litex.unguardedFunctionDomain {} (Litex.denote (Litex.NPos (M := M))) (Litex.denote (Litex.R (M := M))) (Litex.isSet (Litex.NPos (M := M))) (Litex.isSet (Litex.R (M := M))) {})",objects[0],refs[0]);
        let law=match builtin.theorem{
            SequenceLimsupConstant|SequenceLiminfConstant=>format!("Litex.sequenceExtremumConstant {upper} {} {} {hf} {} (by intro n hn; exact {} (Litex.semanticObject n (M.member_isSet hn)) hn)",objects[0],objects[1],refs[1],refs[2]),
            SequenceLimsupFromLimit|SequenceLiminfFromLimit=>format!("Litex.sequenceExtremumOfLimit {upper} {} {} {hf} {} {}",objects[0],objects[1],self.compile_real_membership_certificate(&args[1],&scope)?,refs[1]),
            SequenceLimsupExists|SequenceLiminfExists=>format!("Litex.sequenceExtremumExistsOfCandidate {upper} {} {} {} {}",objects[0],objects[1],self.compile_real_membership_certificate(&args[1],&scope)?,refs[1]),
            SequenceLimsupUnique|SequenceLiminfUnique=>format!("Litex.sequenceExtremumCandidatesEqual {upper} {} {hf} {} {} {} {}",objects.join(" "),self.compile_real_membership_certificate(&args[1],&scope)?,self.compile_real_membership_certificate(&args[2],&scope)?,refs[1],refs[2]),
            SequenceLimsupSelected|SequenceLiminfSelected=>format!("Litex.sequenceExtremumSelected {upper} {}",self.compile_object_reference(selected.expect("validated selected value"),&scope)?),
            _=>unreachable!(),
        };
        Ok((
            definitions,
            format!("(show {statement} from {law})"),
            builtin.conclusions.clone(),
        ))
    }
}
