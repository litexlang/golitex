//! Replay the original Archimedean and rational-density theorem contracts.
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
    pub(super) fn compile_builtin_dense_order_theorem(
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
        let (arity, count, carrier, law) = match builtin.theorem {
            BuiltinTheoremId::RealArchimedeanNaturalUpperBound => {
                (1, 1, StandardSet::NPos, "positiveNaturalAboveReal")
            }
            BuiltinTheoremId::RationalBetweenReals => {
                (2, 3, StandardSet::Q, "rationalBetweenRealObjects")
            }
            _ => return Err(invalid("Theorem")),
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
        {
            return Err(invalid("Contract"));
        }
        let TheoremCallArguments::Parenthesized(arguments) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if call.name.local_name() != builtin.theorem.as_str()
            || arguments != &builtin.arguments
            || arguments.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        for (argument, requirement) in arguments.iter().zip(&builtin.requirements) {
            if !matches!(requirement, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir()==argument.ir() && f.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(invalid("RealPremise"));
            }
        }
        if arity == 2
            && !matches!(&builtin.requirements[2],
            Fact::AtomicFact(AtomicFact::LessFact(f))
            if f.left.ir()==arguments[0].ir() && f.right.ir()==arguments[1].ir())
        {
            return Err(invalid("StrictPremise"));
        }
        let Fact::ExistFact(exists) = &builtin.conclusions[0] else {
            return Err(invalid("Existence"));
        };
        let [group] = exists.typed_parameters.groups.as_slice() else {
            return Err(invalid("WitnessGroup"));
        };
        let [witness] = group.params.as_slice() else {
            return Err(invalid("WitnessCount"));
        };
        if group.param_type != ParamType::Obj(Obj::StandardSet(carrier))
            || arguments
                .iter()
                .any(|argument| contains_parameter(argument, witness.id))
        {
            return Err(invalid("WitnessCarrierOrCapture"));
        }
        // The native producer groups the two density bounds into one AndFact.
        let bounds: &[AtomicFact] = match exists.facts.as_slice() {
            [QuantifierFreeFact::AtomicFact(bound)] if arity == 1 => std::slice::from_ref(bound),
            [QuantifierFreeFact::AndFact(bounds)] if arity == 2 && bounds.facts.len() == 2 => {
                &bounds.facts
            }
            _ => return Err(invalid("WitnessBody")),
        };
        let witness = Obj::Identifier(IdentifierObj::from_bound_name(witness));
        if !matches!(&bounds[0], AtomicFact::LessFact(f)
            if f.left.ir()==arguments[0].ir() && f.right.ir()==witness.ir())
            || arity == 2
                && !matches!(&bounds[1],
                    AtomicFact::LessFact(f)
                if f.left.ir()==witness.ir() && f.right.ir()==arguments[1].ir())
        {
            return Err(invalid("WitnessBounds"));
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("PremiseCapture"));
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
        self.compile_fact_wd(&conclusions_wd[0], fact, &formed)?;
        let scope = SourcePosition::new(
            Some(&formed),
            SourceOwner::FactWD(&conclusions_wd[0]),
            usize::MAX,
        );
        let statement = self.compile_formed_fact_proposition(&conclusions_wd[0], fact, &formed)?;
        let args = arguments
            .iter()
            .map(|argument| self.compile_object_reference(argument, &scope))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let evidence = builtin
            .requirements
            .iter()
            .map(|fact| format!("h_{}", fact.fact_id().value()))
            .collect::<Vec<_>>()
            .join(" ");
        Ok((
            definitions,
            format!("(show {statement} from Litex.{law} {args} {evidence})"),
            builtin.conclusions.clone(),
        ))
    }
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("DenseOrder/{stage}"))
}
