//! Replay explicit integral certificate/existence/selection/uniqueness NativeSchemas.
use super::compile_riemann_integral::{parts, validate_domain_requirement, validate_existence};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RiemannCertificate/{stage}"))
}
fn candidate(fact: &Fact, args: &[Obj], value: &Obj) -> bool {
    matches!(fact,Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(p))
        if p.function.ir()==args[0].ir() && p.lower.ir()==args[1].ir()
            && p.upper.ir()==args[2].ir() && p.value.ir()==value.ir())
}
impl LitexToLeanCompiler {
    // Read the original formation's complete domain through its original owner.
    // No Runtime domain lookup or reconstructed source WD evidence is used.
    fn riemann_certificate_domain(
        &self,
        fact: &AtomicFact,
        wd: &AtomicFactWellDefinedProof,
        prior: &SourcePosition<'_>,
    ) -> Result<(Obj, String), LeanCompileError> {
        let (f, a, b, value, negative) = parts(fact).ok_or_else(|| invalid("CandidateFamily"))?;
        let value = value.ok_or_else(|| invalid("PositiveCandidate"))?;
        if negative {
            return Err(invalid("PositiveCandidate"));
        }
        let formed =
            SourcePosition::new(Some(prior), SourceOwner::AtomicWDLocals(wd, 4), usize::MAX);
        match &wd
            .as_detailed()
            .map_err(|_| invalid("DetailedCandidateFormation"))?
            .predicate_domain
        {
            PredicateDomainProof::FunctionAnalysis(capture) => {
                if capture.requirements.len() != 4 {
                    return Err(invalid("OriginalCandidateDomainStages"));
                }
                for (index, requirement) in capture.requirements[..3].iter().enumerate() {
                    validate_domain_requirement(
                        &requirement.requirement,
                        index,
                        a,
                        b,
                        &capture.function_domain.domain,
                    )?;
                }
                if !matches!(&capture.requirements[3].requirement,Fact::AtomicFact(AtomicFact::InFact(m))
                    if m.element.ir()==value.ir() && m.set==Obj::StandardSet(StandardSet::R))
                {
                    return Err(invalid("OriginalCandidateValueReal"));
                }
                let bindings = self
                    .compile_atomic_wd_locals(wd, fact, prior)?
                    .join("\n")
                    .replace('\n', "\n  ");
                Ok((
                    capture.function_domain.domain.clone(),
                    format!("(by\n  {bindings}\n  exact _integral_real\n)"),
                ))
            }
            PredicateDomainProof::ByKnownFact(cite) => {
                self.compile_known_atomic(cite, fact, &formed)?;
                self.with_cited_atomic_formation(cite.cite_fact_id,&formed,&mut |old,old_wd,old_prior| {
                    let (old_f,_,_,old_v,old_negative)=parts(old).ok_or_else(||invalid("CitedCandidateFamily"))?;
                    old_v.ok_or_else(||invalid("CitedCandidateValue"))?;
                    let same=|x:&Obj,y:&Obj| x.ir()==y.ir() || crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(x,y);
                    // The ordinary citation consumer above replays all original
                    // argument equalities. A function's complete domain and real
                    // function proof do not depend on endpoint/value spelling.
                    if old_negative || !same(f,old_f) {
                        return Err(invalid("CitedCandidateArguments"));
                    }
                    self.riemann_certificate_domain(old,old_wd,old_prior)
                })
            }
            _ => Err(invalid("OriginalCandidateFormation")),
        }
    }
    pub(super) fn compile_builtin_riemann_certificate(
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
        let (arity, count) = match builtin.theorem {
            RiemannIntegralExists | RiemannIntegrableFromCandidate => (4, 4),
            RiemannIntegralSelected => (3, 4),
            RiemannIntegralUnique => (5, 5),
            _ => return Err(invalid("Identity")),
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
            return Err(invalid("OriginalStages"));
        }
        let req = &builtin.requirements;
        let goal = &builtin.conclusions[0];
        if builtin.theorem == RiemannIntegralSelected {
            validate_existence(&args[0], &args[1], &args[2], &req[3])?;
            let Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(p)) = goal else {
                return Err(invalid("SelectedCandidate"));
            };
            let Obj::IntegralOperator(IntegralOperator::Riemann(integral)) = &p.value else {
                return Err(invalid("SelectedOperator"));
            };
            if integral.function.ir() != args[0].ir()
                || integral.lower.ir() != args[1].ir()
                || integral.upper.ir() != args[2].ir()
                || !candidate(goal, args, &p.value)
            {
                return Err(invalid("SelectedArguments"));
            }
        } else {
            if !candidate(&req[3], args, &args[3]) {
                return Err(invalid("OriginalCandidate"));
            }
            match builtin.theorem {
                RiemannIntegralExists => validate_existence(&args[0], &args[1], &args[2], goal)?,
                RiemannIntegrableFromCandidate => {
                    if !matches!(goal,Fact::AtomicFact(AtomicFact::FunctionRiemannIntegrableFact(p))
                        if p.function.ir()==args[0].ir() && p.lower.ir()==args[1].ir() && p.upper.ir()==args[2].ir())
                    {
                        return Err(invalid("IntegrabilitySubject"));
                    }
                }
                RiemannIntegralUnique => {
                    if !candidate(&req[4], args, &args[4])
                        || !matches!(goal,Fact::AtomicFact(AtomicFact::EqualFact(p))
                        if p.left.ir()==args[3].ir() && p.right.ir()==args[4].ir())
                    {
                        return Err(invalid("UniquenessSubjects"));
                    }
                }
                _ => unreachable!(),
            }
        }
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
        let (domain, real_formation) = if builtin.theorem == RiemannIntegralSelected {
            let (Fact::AtomicFact(atom), FactWellDefinedProof::AtomicExceptEquality(wd)) =
                (goal, wd)
            else {
                return Err(invalid("SelectedFormation"));
            };
            self.riemann_certificate_domain(atom, wd, &formed)?
        } else {
            let VerifyFactResult::AtomicExceptEquality(p) = &dom_proofs[3] else {
                return Err(invalid("OriginalCandidateProof"));
            };
            let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_ref() else {
                return Err(invalid("OriginalCandidateSuccess"));
            };
            self.riemann_certificate_domain(
                &p.fact,
                &p.well_defined_proof,
                &SourcePosition {
                    before: 3,
                    ..*position
                },
            )?
        };
        for (index, r) in req[..3].iter().enumerate() {
            validate_domain_requirement(r, index, &args[1], &args[2], &domain)?;
        }
        let object = |o: &Obj| {
            self.compile_object_reference(o, &scope)
                .map(|s| format!("(Litex.denote {s})"))
        };
        let prefix = args[..3]
            .iter()
            .map(object)
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let proof = match builtin.theorem {
            RiemannIntegralExists | RiemannIntegrableFromCandidate => format!(
                "Litex.riemannIntegralExistsOfCandidate {prefix} {} {}",
                object(&args[3])?,
                refs[3]
            ),
            RiemannIntegralSelected => {
                format!("Litex.riemannIntegralValueSelected {prefix} {}", refs[3])
            }
            RiemannIntegralUnique => format!(
                "Litex.riemannIntegralCandidatesEqual {prefix} {} {} {} {}",
                object(&args[3])?,
                object(&args[4])?,
                refs[3],
                refs[4]
            ),
            _ => unreachable!(),
        };
        Ok((
            definitions,
            format!("(show {statement} from (by\n  have _riemann_original_real : Litex.RealFunctionValue M {} := {}\n  exact {proof}\n))",object(&args[0])?,real_formation.replace('\n',"\n  ")) ,
            builtin.conclusions.clone(),
        ))
    }
}
