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
    pub(super) fn compile_builtin_finite_sum_theorem(
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
        let ordered = builtin.theorem == BuiltinTheoremId::FiniteSetSumLessEqualFromPointwise;
        if !matches!(
            builtin.theorem,
            BuiltinTheoremId::FiniteSetSumSubstitution
                | BuiltinTheoremId::FiniteSetSumLessEqualFromPointwise
        ) || !matches!(derivation, TheoremDerivationProof::NativeSchema)
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
        let ([left, right], [sets, pointwise], [_, _], [_, _], [conclusion], [_]) = (
            args.as_slice(),
            builtin.requirements.as_slice(),
            dom_proofs,
            dom_stores,
            builtin.conclusions.as_slice(),
            conclusions_wd,
        ) else {
            return Err(invalid("Stages"));
        };
        if args != &builtin.arguments {
            return Err(invalid("CapturedArguments"));
        }
        let (
            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(left_sum)),
            Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(right_sum)),
        ) = (left, right)
        else {
            return Err(invalid("SumEndpoints"));
        };
        if !matches!(
            left_sum.func.as_ref(),
            Obj::Identifier(IdentifierObj::Plain { .. })
        ) || !matches!(
            right_sum.func.as_ref(),
            Obj::Identifier(IdentifierObj::Plain { .. })
        ) {
            return Err(invalid("NamedCallbackProfile"));
        }
        if !matches!(sets, Fact::AtomicFact(AtomicFact::EqualFact(p)) if p.left.ir()==left_sum.set.ir() && p.right.ir()==right_sum.set.ir())
        {
            return Err(invalid("CommonSetProfile"));
        }
        validate_pointwise(
            pointwise,
            &left_sum.set,
            &right_sum.set,
            &left_sum.func,
            &right_sum.func,
            ordered,
        )?;
        let Fact::AtomicFact(goal) = conclusion else {
            return Err(invalid("ConclusionFamily"));
        };
        let (goal_left, goal_right) = match (goal, ordered) {
            (AtomicFact::EqualFact(p), false) => (&p.left, &p.right),
            (AtomicFact::LessEqualFact(p), true) => (&p.left, &p.right),
            _ => return Err(invalid("ConclusionRelation")),
        };
        if goal_left.ir() != left.ir() || goal_right.ir() != right.ir() {
            return Err(invalid("ConclusionEndpoints"));
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
            before: 2,
            ..*position
        };
        let (bindings, owner, before) = match (&conclusions_wd[0], goal, ordered) {
            (FactWellDefinedProof::Equality(wd), AtomicFact::EqualFact(goal), false) => (
                self.compile_equal_wd_locals(goal, wd, &formed)?,
                SourceOwner::EqualWDLocals(wd, 2),
                2,
            ),
            (
                FactWellDefinedProof::AtomicExceptEquality(wd),
                AtomicFact::LessEqualFact(_),
                true,
            ) => (
                self.compile_atomic_wd_locals(wd, goal, &formed)?,
                SourceOwner::AtomicWDLocals(wd, 2),
                usize::MAX,
            ),
            _ => return Err(invalid("ConclusionFormation")),
        };
        let complete = SourcePosition::new(Some(&formed), owner, before);
        let left = self
            .compile_object_reference(left, &complete)?
            .replace('\n', "\n  ");
        let right = self
            .compile_object_reference(right, &complete)?
            .replace('\n', "\n  ");
        let statement =
            self.compile_formed_fact_proposition(&conclusions_wd[0], conclusion, &formed)?;
        let set_proof = format!("h_{}", sets.fact_id().value());
        let point_proof = format!("h_{}", pointwise.fact_id().value());
        let left_value =
            "Litex.FunctionSemantics.callValue (M := M) (Litex.denote _sum_left.val.function) _x";
        let right_value =
            "Litex.FunctionSemantics.callValue (M := M) (Litex.denote _sum_right.val.function) _x";
        let point_statement = if ordered {
            format!("Litex.realBound true ({left_value}) ({right_value})")
        } else {
            format!("({left_value}) = ({right_value})")
        };
        let values = "(Litex.denote _sum_left.val.set) (Litex.denote _sum_right.val.set) (Litex.denote _sum_left.val.function) (Litex.denote _sum_right.val.function)";
        let application = if ordered {
            format!("Litex.finiteSumPointwiseLeValue {values} _sum_left.wd.1 {set_proof} _point")
        } else {
            format!("congrArg M.number (Litex.finiteAggregatePointwiseValue false {values} _sum_left.wd.1 {set_proof} _point)")
        };
        let proof = format!("(by\n  let _sum_left := {left}\n  let _sum_right := {right}\n  have _point : ∀ (_x : M.Value), M.mem _x (Litex.denote _sum_left.val.set) → {point_statement} := by\n    intro _x _hx\n    exact {point_proof} (Litex.semanticObject (M := M) _x (M.member_isSet _hx)) _hx\n  exact {application}\n)");
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}

fn validate_pointwise(
    fact: &Fact,
    domain: &Obj,
    other_domain: &Obj,
    left: &Obj,
    right: &Obj,
    ordered: bool,
) -> Result<(), LeanCompileError> {
    let Fact::ForallFact(fact) = fact else {
        return Err(invalid("PointwiseFamily"));
    };
    let [group] = fact.typed_parameters.groups.as_slice() else {
        return Err(invalid("PointwiseGroups"));
    };
    let [parameter] = group.params.as_slice() else {
        return Err(invalid("PointwiseBinder"));
    };
    let ParamType::Obj(carrier) = &group.param_type else {
        return Err(invalid("PointwiseCarrier"));
    };
    let [ExistOrAndChainAtomicFact::AtomicFact(body)] = fact.then_facts.as_slice() else {
        return Err(invalid("PointwiseBody"));
    };
    let (body_left, body_right) = match (body, ordered) {
        (AtomicFact::EqualFact(p), false) => (&p.left, &p.right),
        (AtomicFact::LessEqualFact(p), true) => (&p.left, &p.right),
        _ => return Err(invalid("PointwiseRelation")),
    };
    if carrier.ir() != domain.ir()
        || !fact.dom_facts.is_empty()
        || [domain, other_domain, left, right]
            .iter()
            .any(|object| contains_parameter(object, parameter.id))
    {
        return Err(invalid("PointwiseDomain"));
    }
    let Obj::FnObj(application) = body_left else {
        return Err(invalid("PointwiseApplication"));
    };
    let [arguments] = application.body.as_slice() else {
        return Err(invalid("PointwiseArity"));
    };
    let [argument] = arguments.as_slice() else {
        return Err(invalid("PointwiseArity"));
    };
    if !matches!(argument.as_ref(), Obj::Identifier(IdentifierObj::Plain { id, .. }) if *id==parameter.id)
        || fold_application(left, &[argument.as_ref().clone()])?.ir() != body_left.ir()
        || fold_application(right, &[argument.as_ref().clone()])?.ir() != body_right.ir()
    {
        return Err(invalid("PointwiseEndpoints"));
    }
    Ok(())
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("FiniteSum/{part}"))
}
