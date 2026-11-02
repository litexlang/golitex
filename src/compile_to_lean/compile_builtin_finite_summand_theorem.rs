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
    pub(super) fn compile_builtin_finite_summand_theorem(
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
        if builtin.theorem != BuiltinTheoremId::FiniteSetSummandLessEqualSum
            || !matches!(derivation, TheoremDerivationProof::NativeSchema)
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
            [value, sum],
            [equal, member, pointwise],
            [_, _, _],
            [_, _, _],
            [Fact::AtomicFact(goal @ AtomicFact::LessEqualFact(conclusion))],
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
        if args != &builtin.arguments
            || conclusion.left.ir() != value.ir()
            || conclusion.right.ir() != sum.ir()
        {
            return Err(invalid("Endpoints"));
        }
        let (
            Obj::FnObj(application),
            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum_data)),
        ) = (value, sum)
        else {
            return Err(invalid("ConstructorProfile"));
        };
        if !matches!(
            sum_data.func.as_ref(),
            Obj::Identifier(IdentifierObj::Plain { .. })
        ) {
            return Err(invalid("NamedCallbackProfile"));
        }
        let [arguments] = application.body.as_slice() else {
            return Err(invalid("SummandArity"));
        };
        let [argument] = arguments.as_slice() else {
            return Err(invalid("SummandArity"));
        };
        let canonical = fold_application(&sum_data.func, &[argument.as_ref().clone()])?;
        if !matches!(equal,Fact::AtomicFact(AtomicFact::EqualFact(p)) if p.left.ir()==value.ir() && p.right.ir()==canonical.ir())
            || !matches!(member,Fact::AtomicFact(AtomicFact::InFact(p)) if p.element.ir()==argument.ir() && p.set.ir()==sum_data.set.ir())
        {
            return Err(invalid("OriginalSubjects"));
        }
        validate_nonnegative(pointwise, &sum_data.set, &sum_data.func, argument)?;
        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalRequirement"));
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
            before: 3,
            ..*position
        };
        let bindings = self.compile_atomic_wd_locals(wd, goal, &formed)?;
        let complete = SourcePosition::new(
            Some(&formed),
            SourceOwner::AtomicWDLocals(wd, 2),
            usize::MAX,
        );
        let sum = self
            .compile_object_reference(sum, &complete)?
            .replace('\n', "\n  ");
        let argument = self
            .compile_object_reference(argument, &complete)?
            .replace('\n', "\n  ");
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let equal = format!("h_{}", equal.fact_id().value());
        let member = format!("h_{}", member.fact_id().value());
        let pointwise = format!("h_{}", pointwise.fact_id().value());
        let proof = format!("(by\n  let _sum := {sum}\n  let _member := {argument}\n  have _nonnegative : ∀ (_x : M.Value), M.mem _x (Litex.denote _sum.val.set) → Litex.realBound true (M.number (0 : ℂ)) (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _sum.val.function) _x) := by\n    intro _x _hx\n    exact {pointwise} (Litex.semanticObject (M := M) _x (M.member_isSet _hx)) _hx\n  have _bound : Litex.realBound true (Litex.FunctionSemantics.callValue (M := M) (Litex.denote _sum.val.function) (Litex.denote _member)) (Litex.denote _sum) := Litex.finiteSummandLeSumValue (Litex.denote _sum.val.set) (Litex.denote _sum.val.function) (Litex.denote _member) _sum.wd.1 {member} _nonnegative\n  exact Eq.mp (congrArg (fun (_v : M.Value) => Litex.realBound true _v (Litex.denote _sum)) {equal}.symm) _bound\n)");
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}
fn validate_nonnegative(
    fact: &Fact,
    set: &Obj,
    function: &Obj,
    member: &Obj,
) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(point) = fact else {
        return Err(invalid("PointwiseFamily"));
    };
    let [group] = point.typed_parameters.groups.as_slice() else {
        return Err(invalid("PointwiseGroups"));
    };
    let [parameter] = group.params.as_slice() else {
        return Err(invalid("PointwiseBinder"));
    };
    let ParamType::Obj(carrier) = &group.param_type else {
        return Err(invalid("PointwiseCarrier"));
    };
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(body))] =
        point.then_facts.as_slice()
    else {
        return Err(invalid("PointwiseBody"));
    };
    if carrier.ir() != set.ir()
        || !point.dom_facts.is_empty()
        || !matches!(&body.left,Obj::Literal(Literal::Number(n)) if n.normalized_value=="0")
        || [set, function, member]
            .iter()
            .any(|o| contains_parameter(o, parameter.id))
    {
        return Err(invalid("PointwiseDomain"));
    }
    let Obj::FnObj(call) = &body.right else {
        return Err(invalid("PointwiseApplication"));
    };
    let [arguments] = call.body.as_slice() else {
        return Err(invalid("PointwiseArity"));
    };
    let [argument] = arguments.as_slice() else {
        return Err(invalid("PointwiseArity"));
    };
    if !matches!(argument.as_ref(),Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter.id)
        || fold_application(function, &[argument.as_ref().clone()])?.ir() != body.right.ir()
    {
        return Err(invalid("PointwiseEndpoints"));
    }
    Ok(())
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FiniteSummand/{part}"))
}
