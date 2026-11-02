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
    pub(super) fn compile_builtin_indexed_choice_theorem(
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
        let family = match builtin.theorem {
            BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromFamily => true,
            BuiltinTheoremId::IndexCartesianNonemptyByChoiceFromPointwise => false,
            _ => return Err(invalid("SelectedRule")),
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
        {
            return Err(invalid("Contract"));
        }
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let (
            [argument],
            [requirement],
            [checked],
            [store],
            [Fact::AtomicFact(goal @ AtomicFact::IsNonemptySetFact(conclusion))],
            [FactWellDefinedProof::AtomicExceptEquality(wd)],
        ) = (
            args.as_slice(),
            builtin.requirements.as_slice(),
            dom_proofs,
            dom_stores,
            builtin.conclusions.as_slice(),
            conclusions_wd,
        )
        else {
            return Err(invalid("Stages"));
        };
        if args != &builtin.arguments || conclusion.set.ir() != argument.ir() {
            return Err(invalid("OriginalArgument"));
        }
        let Obj::SetOperator(SetOperator::IndexCart(cart)) = argument else {
            return Err(invalid("IndexCartConstructor"));
        };
        validate_requirement(
            requirement,
            &cart.index_set,
            &cart.family_set,
            &cart.family_fn,
            family,
        )?;
        if source_subject(checked)? != *requirement {
            return Err(invalid("OriginalRequirement"));
        }
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
        let hypothesis = format!("h_{}", requirement.fact_id().value());
        definitions.extend(self.compile_stored_inferences(
            store,
            requirement,
            &(compiled.0, hypothesis.clone()),
            &formed,
        )?);
        let bindings = self.compile_atomic_wd_locals(wd, goal, &formed)?;
        let complete = SourcePosition::new(
            Some(&formed),
            SourceOwner::AtomicWDLocals(wd, 1),
            usize::MAX,
        );
        let object = self
            .compile_object_reference(argument, &complete)?
            .replace('\n', "\n  ");
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let domain = if family { "familySet" } else { "index" };
        let factor = if family {
            "_x"
        } else {
            "(Litex.FunctionSemantics.callValue (M := M) (Litex.denote _cart.val.family) _x)"
        };
        let law = if family {
            "indexCartNonemptyFamily"
        } else {
            "indexCartNonemptyPointwise"
        };
        let proof=format!("(by\n  let _cart := {object}\n  have _nonempty : ∀ (_x : M.Value), M.mem _x (Litex.denote _cart.val.{domain}) → ∃ (_y : M.Value), M.mem _y {factor} := by\n    intro _x _hx\n    exact {hypothesis} (Litex.semanticObject (M := M) _x (M.member_isSet _hx)) _hx\n  exact Litex.{law} _cart _nonempty\n)");
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
fn validate_requirement(
    fact: &Fact,
    index: &Obj,
    sets: &Obj,
    function: &Obj,
    family: bool,
) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(point) = fact else {
        return Err(invalid("UniversalFamily"));
    };
    let [group] = point.typed_parameters.groups.as_slice() else {
        return Err(invalid("BinderGroups"));
    };
    let [parameter] = group.params.as_slice() else {
        return Err(invalid("BinderCount"));
    };
    let ParamType::Obj(domain) = &group.param_type else {
        return Err(invalid("BinderCarrier"));
    };
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::IsNonemptySetFact(body))] =
        point.then_facts.as_slice()
    else {
        return Err(invalid("NonemptyBody"));
    };
    if domain.ir() != if family { sets.ir() } else { index.ir() }
        || !point.dom_facts.is_empty()
        || [index, sets, function]
            .iter()
            .any(|o| contains_parameter(o, parameter.id))
    {
        return Err(invalid("UniversalDomain"));
    }
    if family {
        if !matches!(&body.set,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter.id) {
            return Err(invalid("FamilyMember"));
        }
    } else {
        let Obj::FnObj(application) = &body.set else {
            return Err(invalid("FactorCall"));
        };
        let Some(arguments) = application.body.last() else {
            return Err(invalid("FactorCallArity"));
        };
        let [argument] = arguments.as_slice() else {
            return Err(invalid("FactorCallArity"));
        };
        if !matches!(argument.as_ref(),Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter.id)
            || fold_application(function, &[argument.as_ref().clone()])?.ir() != body.set.ir()
        {
            return Err(invalid("FactorSubject"));
        }
    }
    Ok(())
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("IndexedChoice/{part}"))
}
