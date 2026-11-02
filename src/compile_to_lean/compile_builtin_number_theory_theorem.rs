//! Fixed prime theorem schemas, consuming their original ordered stages.
use super::compile_real_set_bounds::contains_parameter;
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
    pub(super) fn compile_builtin_number_theory_theorem(
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
        let (arity, count, law) = match builtin.theorem {
            GcdWithPrimeIsOneOrPrime => (2, 3, "gcdWithPrimeValue"),
            PrimeDividesProduct => (3, 5, "primeDividesProductValue"),
            PrimeDividesPower => (3, 5, "primeDividesPowerValue"),
            PrimeDivisor => (1, 2, "primeDivisorWitness"),
            _ => return Err(invalid("Theorem")),
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(invalid("Contract"));
        }
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if call.name.local_name() != builtin.theorem.as_str()
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
        for (index, argument) in args.iter().enumerate() {
            let carrier = match builtin.theorem {
                GcdWithPrimeIsOneOrPrime if index == 0 => StandardSet::Z,
                PrimeDividesProduct if index < 2 => StandardSet::Z,
                PrimeDividesPower if index == 0 => StandardSet::Z,
                _ => StandardSet::NPos,
            };
            if !matches!(&req[index],Fact::AtomicFact(AtomicFact::InFact(p))
                if p.element.ir()==argument.ir() && p.set==Obj::StandardSet(carrier))
            {
                return Err(invalid("IntegerDomains"));
            }
        }
        if builtin.theorem == PrimeDivisor {
            if !matches!(&req[1],Fact::AtomicFact(AtomicFact::LessEqualFact(p))
                if literal_number(&p.left,"2") && p.right.ir()==args[0].ir())
            {
                return Err(invalid("AtLeastTwo"));
            }
        } else {
            let prime = &args[arity - 1];
            if !matches!(&req[arity],Fact::AtomicFact(AtomicFact::PrimeFact(p)) if p.value.ir()==prime.ir())
            {
                return Err(invalid("PrimeSubject"));
            }
            if arity == 3 {
                let Fact::AtomicFact(AtomicFact::DvdFact(p)) = &req[4] else {
                    return Err(invalid("DivisibilityPremise"));
                };
                let valid = match (&p.left, builtin.theorem) {
                    (Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)), PrimeDividesProduct) => {
                        p.left.ir() == args[0].ir() && p.right.ir() == args[1].ir()
                    }
                    (Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)), PrimeDividesPower) => {
                        p.base.ir() == args[0].ir() && p.exponent.ir() == args[1].ir()
                    }
                    _ => false,
                };
                if !valid || p.right.ir() != prime.ir() {
                    return Err(invalid("DivisibilitySubject"));
                }
            }
        }
        validate_conclusion(builtin.theorem, args, &builtin.conclusions[0])?;
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalPremise"));
            }
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            self.validate_store(&store.store, requirement)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, format!("h_{}", requirement.fact_id().value())),
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
        let fact = &builtin.conclusions[0];
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, fact, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, fact, &formed)?;
        let args = args
            .iter()
            .map(|o| self.compile_object_reference(o, &scope))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let evidence = req
            .iter()
            .map(|p| format!("h_{}", p.fact_id().value()))
            .collect::<Vec<_>>()
            .join(" ");
        Ok((
            definitions,
            format!("(show {statement} from Litex.{law} {args} {evidence})"),
            builtin.conclusions.clone(),
        ))
    }
}

fn validate_conclusion(
    id: BuiltinTheoremId,
    args: &[Obj],
    conclusion: &Fact,
) -> Result<(), LeanCompileError> {
    use BuiltinTheoremId::*;
    let dvd = |fact: &AndChainAtomicFact, left: &Obj, right: &Obj| matches!(fact,AndChainAtomicFact::AtomicFact(AtomicFact::DvdFact(p)) if p.left.ir()==left.ir() && p.right.ir()==right.ir());
    let valid=match (id,conclusion) {
        (GcdWithPrimeIsOneOrPrime,Fact::OrFact(p)) if p.facts.len()==2=> {
            p.facts.iter().enumerate().all(|(index,fact)| {
                matches!(fact,AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(p))
                    if matches!(&p.left,Obj::IntegerOperator(IntegerOperator::Gcd(g)) if g.left.ir()==args[0].ir() && g.right.ir()==args[1].ir())
                    && if index==0 {literal_number(&p.right,"1")} else {p.right.ir()==args[1].ir()})
            })
        }
        (PrimeDividesProduct,Fact::OrFact(p)) if p.facts.len()==2=>dvd(&p.facts[0],&args[0],&args[2]) && dvd(&p.facts[1],&args[1],&args[2]),
        (PrimeDividesPower,Fact::AtomicFact(AtomicFact::DvdFact(p)))=>p.left.ir()==args[0].ir() && p.right.ir()==args[2].ir(),
        (PrimeDivisor,Fact::ExistFact(p))=> {
            let [group]=p.typed_parameters.groups.as_slice() else {return Err(invalid("WitnessGroup"));};
            let [bound]=group.params.as_slice() else {return Err(invalid("WitnessCount"));};
            let witness=Obj::Identifier(IdentifierObj::from_bound_name(bound));
            group.param_type==ParamType::Obj(Obj::StandardSet(StandardSet::NPos))
                && !contains_parameter(&args[0],bound.id) && p.facts.len()==2
                && matches!(&p.facts[0],QuantifierFreeFact::AtomicFact(AtomicFact::PrimeFact(q)) if q.value.ir()==witness.ir())
                && matches!(&p.facts[1],QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(q))
                    if is_exact_zero(&q.right) && matches!(&q.left,Obj::IntegerOperator(IntegerOperator::Mod(m)) if m.left.ir()==args[0].ir() && m.right.ir()==witness.ir()))
        }
        _=>false,
    };
    if valid {
        Ok(())
    } else {
        Err(invalid("ConclusionSchema"))
    }
}

fn literal_number(object: &Obj, value: &str) -> bool {
    matches!(object,Obj::Literal(Literal::Number(n)) if n.normalized_value==value)
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("NumberTheory/{stage}"))
}
