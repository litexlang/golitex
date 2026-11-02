use super::compile_real_set_bounds::contains_parameter;
use super::helper::source_subject;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_reduced_fraction_theorem(
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
        if builtin.theorem != BuiltinTheoremId::RationalHasUniqueReducedFraction
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
        {
            return Err(invalid("Contract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let ([argument], [requirement], [checked], [store], [conclusion], [wd]) = (
            arguments.as_slice(),
            builtin.requirements.as_slice(),
            dom_proofs,
            dom_stores,
            builtin.conclusions.as_slice(),
            conclusions_wd,
        ) else {
            return Err(invalid("Stages"));
        };
        if arguments != &builtin.arguments
            || !matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==argument.ir() && f.set==Obj::StandardSet(StandardSet::Q))
        {
            return Err(invalid("RationalSubject"));
        }
        validate_conclusion(argument, conclusion)?;
        if source_subject(checked)? != *requirement {
            return Err(invalid("OriginalRequirement"));
        }
        let prior = SourcePosition {
            before: 0,
            ..*position
        };
        let proof = self.compile_verify(checked, &prior)?;
        self.validate_store(&store.store, requirement)?;
        let mut definitions = vec![self.emit_internal_fact(requirement, &proof, &prior)?];
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let member = format!("h_{}", requirement.fact_id().value());
        definitions.extend(self.compile_stored_inferences(
            store,
            requirement,
            &(proof.0, member.clone()),
            &formed,
        )?);
        self.compile_fact_wd(wd, conclusion, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, conclusion, &formed)?;
        let argument = self.compile_object_reference(argument, &scope)?;
        let argument = argument.replace('\n', "\n  ");
        let proof = format!("(show {statement} from (by\n  let _rf_argument := {argument}\n  have _rf_member : Litex.In _rf_argument (Litex.Q (M := M)) := {member}\n  constructor\n  · rcases Litex.rationalReducedFractionWitness _rf_argument _rf_member with ⟨_rf_num, _rf_num_z, _rf_den, _rf_den_pos, _rf_ratio, _rf_reduced⟩\n    exact ⟨_rf_num, _rf_num_z, _rf_den, _rf_den_pos, _rf_ratio, _rf_reduced⟩\n  · exact Litex.rationalReducedFractionUniqueness _rf_argument _rf_member\n))");
        Ok((definitions, proof, builtin.conclusions.clone()))
    }
}

fn validate_conclusion(argument: &Obj, conclusion: &Fact) -> Result<(), LeanCompileError> {
    let Fact::ExistUniqueFact(fact) = conclusion else {
        return Err(invalid("UniqueConclusion"));
    };
    let [num, den] = fact.typed_parameters.groups.as_slice() else {
        return Err(invalid("BinderGroups"));
    };
    let ([p], [d]) = (num.params.as_slice(), den.params.as_slice()) else {
        return Err(invalid("BinderCount"));
    };
    if p.id == d.id
        || num.param_type != ParamType::Obj(Obj::StandardSet(StandardSet::Z))
        || den.param_type != ParamType::Obj(Obj::StandardSet(StandardSet::NPos))
        || contains_parameter(argument, p.id)
        || contains_parameter(argument, d.id)
    {
        return Err(invalid("BinderDomains"));
    }
    let p = Obj::Identifier(IdentifierObj::from_bound_name(p));
    let d = Obj::Identifier(IdentifierObj::from_bound_name(d));
    let [QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(ratio)), QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(reduced))] =
        fact.facts.as_slice()
    else {
        return Err(invalid("BodyClauses"));
    };
    if ratio.left.ir() != argument.ir()
        || !matches!(&ratio.right,Obj::ArithmeticOperator(ArithmeticOperator::Div(v)) if v.left.ir()==p.ir() && v.right.ir()==d.ir())
        || !matches!(&reduced.left,Obj::IntegerOperator(IntegerOperator::Gcd(v)) if v.left.ir()==p.ir() && v.right.ir()==d.ir())
        || !matches!(&reduced.right,Obj::Literal(Literal::Number(n)) if n.normalized_value=="1")
    {
        return Err(invalid("RatioAndReduction"));
    }
    Ok(())
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("ReducedFraction/{part}"))
}
