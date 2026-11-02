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
    pub(super) fn compile_builtin_range_sum_theorem(
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
        if builtin.theorem != BuiltinTheoremId::SumLessEqualFromPointwise
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
            [left, right],
            [first, last, pointwise],
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
            || conclusion.left.ir() != left.ir()
            || conclusion.right.ir() != right.ir()
        {
            return Err(invalid("Endpoints"));
        }
        let (
            Obj::IteratedOperator(IteratedOperator::Sum(l)),
            Obj::IteratedOperator(IteratedOperator::Sum(r)),
        ) = (left, right)
        else {
            return Err(invalid("SumProfile"));
        };
        if ![&l.func, &r.func]
            .iter()
            .all(|f| matches!(f.as_ref(), Obj::Identifier(IdentifierObj::Plain { .. })))
        {
            return Err(invalid("NamedCallbackProfile"));
        }
        if !matches!(first, Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==l.start.ir() && f.right.ir()==r.start.ir())
            || !matches!(last, Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==l.end.ir() && f.right.ir()==r.end.ir())
        {
            return Err(invalid("OriginalEndpoints"));
        }
        validate_pointwise(
            pointwise, &l.start, &l.end, &r.start, &r.end, &l.func, &r.func,
        )?;
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
        let left = self
            .compile_object_reference(left, &complete)?
            .replace('\n', "\n  ");
        let right = self
            .compile_object_reference(right, &complete)?
            .replace('\n', "\n  ");
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let first = format!("h_{}", first.fact_id().value());
        let last = format!("h_{}", last.fact_id().value());
        let pointwise = format!("h_{}", pointwise.fact_id().value());
        let values = "(Litex.denote _left.val.first) (Litex.denote _left.val.last) (Litex.denote _right.val.first) (Litex.denote _right.val.last) (Litex.denote _left.val.function) (Litex.denote _right.val.function)";
        let proof = format!("(by\n  let _left := {left}\n  let _right := {right}\n  apply Litex.rangeSumPointwiseLeValue {values} {first} {last}\n  intro _k _lo _hi\n  have _bounds := Litex.integerRangeBoundsValue (Litex.denote _left.val.first) (Litex.denote _left.val.last) _left.wd.1 _left.wd.2.1 _k _lo _hi\n  exact {pointwise} (Litex.semanticObject (M := M) (M.number (_k : ℂ)) (M.member_isSet (Litex.NativeBridge.numberInZ (M := M) _k))) (Litex.NativeBridge.numberInZ (M := M) _k) _bounds.1 _bounds.2\n)");
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
    first: &Obj,
    last: &Obj,
    other_first: &Obj,
    other_last: &Obj,
    left: &Obj,
    right: &Obj,
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
    if !matches!(
        &group.param_type,
        ParamType::Obj(Obj::StandardSet(StandardSet::Z))
    ) || [first, last, other_first, other_last, left, right]
        .iter()
        .any(|o| contains_parameter(o, parameter.id))
    {
        return Err(invalid("PointwiseDomain"));
    }
    let [Fact::AtomicFact(AtomicFact::LessEqualFact(lo)), Fact::AtomicFact(AtomicFact::LessEqualFact(hi))] =
        point.dom_facts.as_slice()
    else {
        return Err(invalid("PointwiseGuards"));
    };
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(body))] =
        point.then_facts.as_slice()
    else {
        return Err(invalid("PointwiseBody"));
    };
    if lo.left.ir() != first.ir()
        || hi.right.ir() != last.ir()
        || !matches!(&lo.right,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter.id)
        || !matches!(&hi.left,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==parameter.id)
        || fold_application(left, &[lo.right.clone()])?.ir() != body.left.ir()
        || fold_application(right, &[lo.right.clone()])?.ir() != body.right.ir()
    {
        return Err(invalid("PointwiseEndpoints"));
    }
    Ok(())
}
fn invalid(part: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("RangeSum/{part}"))
}
