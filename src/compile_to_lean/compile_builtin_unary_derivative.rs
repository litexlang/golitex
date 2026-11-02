//! Unary derivative actions replay their four original function/point prerequisites.
use super::compile_function_derivative::validate_derivative_existence;
use super::compile_function_derivative_definition::validate_derivative_interior;
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

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("UnaryDerivativeBuiltin/{stage}"))
}
fn candidate(
    fact: &Fact,
    function: &Obj,
    point: &Obj,
    value: &Obj,
) -> Result<(), LeanCompileError> {
    if matches!(fact,Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) if f.function.ir()==function.ir()&&f.point.ir()==point.ir()&&f.value.ir()==value.ir())
    {
        Ok(())
    } else {
        Err(invalid("OriginalCandidate"))
    }
}
impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_real_interior(
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
        let (set, law) = match builtin.theorem {
            FnDerivativeAtRealInterior => (StandardSet::R, "realDomainOpen"),
            FnDerivativeAtNonzeroInterior => (StandardSet::RStar, "nonzeroRealDomainOpen"),
            FnDerivativeAtPositiveInterior => (StandardSet::RPos, "positiveRealDomainOpen"),
            FnDerivativeAtNegativeInterior => (StandardSet::RNeg, "negativeRealDomainOpen"),
            _ => return Err(invalid("InteriorIdentity")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("InteriorArguments"));
        };
        let ([point], [requirement], [checked], [store], [conclusion], [wd]) = (
            args.as_slice(),
            builtin.requirements.as_slice(),
            dom_proofs,
            dom_stores,
            builtin.conclusions.as_slice(),
            conclusions_wd,
        ) else {
            return Err(invalid("InteriorStages"));
        };
        let domain = Obj::StandardSet(set);
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || !matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==point.ir()&&f.set==domain)
            || source_subject(checked)? != *requirement
        {
            return Err(invalid("InteriorOriginalContext"));
        }
        validate_derivative_interior(&domain, point, &domain, conclusion)?;
        let prior = SourcePosition {
            before: 0,
            ..*position
        };
        let compiled = self.compile_verify(checked, &prior)?;
        self.validate_store(&store.store, requirement)?;
        let mut definitions = vec![self.emit_internal_fact(requirement, &compiled, &prior)?];
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        definitions.extend(self.compile_stored_inferences(
            store,
            requirement,
            &(compiled.0, format!("h_{}", requirement.fact_id().value())),
            &formed,
        )?);
        self.compile_fact_wd(wd, conclusion, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let p = self.compile_object_reference(point, &scope)?;
        let d = self.compile_object_reference(&domain, &scope)?;
        let real = self.compile_real_membership_certificate(point, &scope)?;
        let proof = format!("(by\n  have _point_real : Litex.In {p} Litex.R := {real}\n  exact Litex.realInteriorOfOpenDomain (Litex.denote {d}) (Litex.denote {p}) (Litex.NativeBridge.asReal {p} _point_real) (Litex.NativeBridge.asReal_spec {p} _point_real) h_{} Litex.{law}\n)", requirement.fact_id().value());
        let statement = self.compile_formed_fact_proposition(wd, conclusion, &formed)?;
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }

    pub(super) fn compile_builtin_unary_derivative(
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
        let unique = builtin.theorem == FnDerivativeAtUnique;
        let selected = builtin.theorem == FnDerivativeAtSelected;
        let differentiable = builtin.theorem == FnDifferentiableAtFromDerivative;
        let continuous = matches!(
            builtin.theorem,
            FnDerivativeAtContinuous | FnDifferentiableAtContinuous
        );
        let from_differentiable = builtin.theorem == FnDifferentiableAtContinuous;
        if !matches!(
            builtin.theorem,
            FnDerivativeAtUnique
                | FnDerivativeAtExists
                | FnDerivativeAtSelected
                | FnDifferentiableAtFromDerivative
                | FnDerivativeAtContinuous
                | FnDifferentiableAtContinuous
        ) {
            return Err(invalid("Identity"));
        }
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let count = if unique { 6 } else { 5 };
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
        let (signature, _) = real_limit_signature(&builtin.requirements[..3], &args[0])?;
        let Fact::AtomicFact(AtomicFact::InFact(point)) = &builtin.requirements[3] else {
            return Err(invalid("PointMember"));
        };
        if point.element.ir() != args[1].ir() || !signature_domain_matches(&point.set, signature) {
            return Err(invalid("OriginalPointDomain"));
        }
        if differentiable || continuous {
            if from_differentiable {
                if !matches!(&builtin.requirements[4],Fact::AtomicFact(AtomicFact::FunctionDifferentiableAtFact(f)) if f.function.ir()==args[0].ir()&&f.point.ir()==args[1].ir())
                {
                    return Err(invalid("DifferentiablePremise"));
                }
            } else {
                candidate(&builtin.requirements[4], &args[0], &args[1], &args[2])?;
            }
            let valid = if differentiable {
                matches!(&builtin.conclusions[0],Fact::AtomicFact(AtomicFact::FunctionDifferentiableAtFact(f)) if f.function.ir()==args[0].ir()&&f.point.ir()==args[1].ir())
            } else {
                matches!(&builtin.conclusions[0],Fact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) if f.function.ir()==args[0].ir()&&f.point.ir()==args[1].ir()&&f.side==RealApproachSide::Both)
            };
            if !valid {
                return Err(invalid("DifferentiableContinuousConclusion"));
            }
        } else if selected {
            validate_derivative_existence(&args[0], &args[1], &builtin.requirements[4])?;
            let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(f)) = &builtin.conclusions[0]
            else {
                return Err(invalid("SelectedConclusion"));
            };
            let Obj::DerivativeOperator(DerivativeOperator::AtPoint(p)) = &f.value else {
                return Err(invalid("SelectedConstructor"));
            };
            if p.function.ir() != args[0].ir() || p.point.ir() != args[1].ir() {
                return Err(invalid("SelectedArguments"));
            }
            candidate(&builtin.conclusions[0], &args[0], &args[1], &f.value)?;
        } else {
            candidate(&builtin.requirements[4], &args[0], &args[1], &args[2])?;
            if unique {
                candidate(&builtin.requirements[5], &args[0], &args[1], &args[3])?;
                if !matches!(&builtin.conclusions[0],Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==args[2].ir()&&f.right.ir()==args[3].ir())
                {
                    return Err(invalid("UniqueConclusion"));
                }
            } else {
                validate_derivative_existence(&args[0], &args[1], &builtin.conclusions[0])?;
            }
        }
        let mut definitions = Vec::new();
        for (index, ((fact, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *fact {
                return Err(invalid("OriginalProofSubject"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, fact)?;
            definitions.push(self.emit_internal_fact(fact, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                fact,
                &(compiled.0, format!("h_{}", fact.fact_id().value())),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
        }
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
        let objects = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        let f = &objects[0];
        let p = &objects[1];
        let original = format!("h_{}", builtin.requirements[4].fact_id().value());
        let proof = if unique {
            let a = &objects[2];
            let b = &objects[3];
            let ha = self.compile_real_membership_certificate(&args[2], &scope)?;
            let hb = self.compile_real_membership_certificate(&args[3], &scope)?;
            let other = format!("h_{}", builtin.requirements[5].fact_id().value());
            format!("(by\n  have _left_real : Litex.In {a} Litex.R := {ha}\n  have _right_real : Litex.In {b} Litex.R := {hb}\n  have _left_eq := Litex.NativeBridge.asReal_spec {a} _left_real\n  have _right_eq := Litex.NativeBridge.asReal_spec {b} _right_real\n  have _left_candidate := (congrArg (Litex.HasDerivativeAtValue M (Litex.denote {f}) (Litex.denote {p})) _left_eq).mp {original}\n  have _right_candidate := (congrArg (Litex.HasDerivativeAtValue M (Litex.denote {f}) (Litex.denote {p})) _right_eq).mp {other}\n  have _unique := Litex.derivativeCandidatesUnique (Litex.denote {f}) (Litex.denote {p}) (Litex.NativeBridge.asReal {a} _left_real) (Litex.NativeBridge.asReal {b} _right_real) _left_candidate _right_candidate\n  exact _left_eq.trans ((congrArg (fun value : ℝ => M.number (value : ℂ)) _unique).trans _right_eq.symm)\n)")
        } else if continuous {
            let references = builtin.requirements[..3]
                .iter()
                .map(|fact| format!("h_{}", fact.fact_id().value()))
                .collect::<Vec<_>>();
            let context = self.compile_function_limit_context(
                0,
                &args[0],
                &point.set,
                &builtin.requirements[..3],
                &references,
                &scope,
            )?;
            let member = format!("(show M.mem (Litex.denote {p}) (Litex.FunctionSemantics.domainValue (Litex.denote {f})) from _law_domain_0 ▸ h_{})",builtin.requirements[3].fact_id().value());
            let law = if from_differentiable {
                format!("Litex.functionContinuousAtOfDifferentiable (Litex.denote {f}) (Litex.denote {p}) _law_real_0 {member} {original}")
            } else {
                format!("Litex.functionContinuousAtOfDerivative (Litex.denote {f}) (Litex.denote {p}) (Litex.denote {}) _law_real_0 {member} {original}",objects[2])
            };
            format!(
                "(by\n{}\n  exact {law}\n)",
                context
                    .join("\n")
                    .lines()
                    .map(|line| format!("  {line}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        } else if selected {
            let Fact::AtomicFact(AtomicFact::HasDerivativeAtFact(goal)) = &builtin.conclusions[0]
            else {
                unreachable!()
            };
            format!(
                "(Litex.derivativeSelectedCandidate {})",
                self.compile_object_reference(&goal.value, &scope)?
            )
        } else {
            format!("(by\n  obtain ⟨value,hv,hc⟩ := Litex.derivativeExistsValueOfCandidate (Litex.denote {f}) (Litex.denote {p}) (Litex.denote {}) {original}\n  exact ⟨value,hv,hc⟩\n)",objects[2])
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
