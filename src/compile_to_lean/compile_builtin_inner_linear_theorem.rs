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
    pub(super) fn compile_builtin_inner_linear_theorem(
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
        if builtin.theorem != BuiltinTheoremId::InnerProductLinearRight
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
            [u, v, w, a, b, n],
            [_, _, _, _, _, _, _, _],
            [_, _, _, _, _, _, _, _],
            [_, _, _, _, _, _, _, _],
            [Fact::AtomicFact(AtomicFact::EqualFact(goal))],
            [FactWellDefinedProof::Equality(wd)],
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
        if args != &builtin.arguments {
            return Err(invalid("OriginalArguments"));
        }
        for (index, requirement) in builtin.requirements.iter().enumerate() {
            let valid = if index < 6 && index % 2 == 0 {
                member(requirement, n, &Obj::StandardSet(StandardSet::N))
            } else if index < 6 {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = requirement else {
                    return Err(invalid("VectorMembership"));
                };
                f.element.ir() == args[index / 2].ir()
                    && matches!(&f.set, Obj::SetFormer(SetFormer::FiniteSeqSet(s))
                        if s.n.ir() == n.ir() && s.set.as_ref() == &Obj::StandardSet(StandardSet::C))
            } else {
                member(
                    requirement,
                    &args[index - 3],
                    &Obj::StandardSet(StandardSet::C),
                )
            };
            if !valid {
                return Err(invalid("OriginalRequirement"));
            }
        }
        let Obj::MatrixOperator(MatrixOperator::InnerProduct(inner)) = &goal.left else {
            return Err(invalid("InnerProduct"));
        };
        if inner.left.ir() != u.ir() || inner.dimension.ir() != n.ir() {
            return Err(invalid("InnerArguments"));
        }
        validate_combination(&inner.right, u, v, w, a, b, n)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &goal.right else {
            return Err(invalid("RightSum"));
        };
        validate_summand(&sum.left, a, u, v, n)?;
        validate_summand(&sum.right, b, u, w, n)?;

        let mut definitions = Vec::new();
        for (index, ((requirement, checked), store)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            if source_subject(checked)? != *requirement {
                return Err(invalid("OriginalProofSubject"));
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
            before: 8,
            ..*position
        };
        let bindings = self.compile_equal_wd_locals(goal, wd, &formed)?;
        let complete = SourcePosition::new(Some(&formed), SourceOwner::EqualWDLocals(wd, 2), 2);
        let left = self
            .compile_object_reference(&goal.left, &complete)?
            .replace('\n', "\n  ");
        let values = [v, w, a, b].map(|o| {
            self.compile_object_reference(o, &complete)
                .map(|s| format!("(Litex.denote {s})"))
        });
        let [v, w, a, b] = values;
        let (v, w, a, b) = (v?, w?, a?, b?);
        let refs = [3, 5, 6, 7].map(|i| format!("h_{}", builtin.requirements[i].fact_id().value()));
        let [hv, hw, ha, hb] = refs;
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof = format!("(by\n  let _linear_inner := {left}\n  exact Litex.finiteInnerProductLinearRight _linear_inner _linear_inner.val.right {v} {w} {a} {b} {hv} {hw} {ha} {hb} (by rfl) (by rfl) (by rfl)\n)");
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}

fn member(fact: &Fact, element: &Obj, set: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==element.ir() && f.set.ir()==set.ir())
}
fn validate_summand(
    term: &Obj,
    scalar: &Obj,
    u: &Obj,
    v: &Obj,
    n: &Obj,
) -> Result<(), LeanCompileError> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = term else {
        return Err(invalid("ScalarProduct"));
    };
    let Obj::MatrixOperator(MatrixOperator::InnerProduct(inner)) = product.right.as_ref() else {
        return Err(invalid("RightInnerProduct"));
    };
    if product.left.ir() != scalar.ir()
        || inner.left.ir() != u.ir()
        || inner.right.ir() != v.ir()
        || inner.dimension.ir() != n.ir()
    {
        return Err(invalid("RightInnerArguments"));
    }
    Ok(())
}
fn validate_combination(
    object: &Obj,
    u: &Obj,
    v: &Obj,
    w: &Obj,
    a: &Obj,
    b: &Obj,
    n: &Obj,
) -> Result<(), LeanCompileError> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = object else {
        return Err(invalid("CombinationFunction"));
    };
    let [group] = literal.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("CombinationBinders"));
    };
    let [binder] = group.params.as_slice() else {
        return Err(invalid("CombinationBinders"));
    };
    let Obj::SetFormer(SetFormer::ClosedRange(range)) = group.param_type.as_ref() else {
        return Err(invalid("CombinationDomain"));
    };
    if closed_integer(&range.start) != Some(1)
        || range.end.ir() != n.ir()
        || literal.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
        || !literal.body.dom_facts.is_empty()
        || [u, v, w, a, b, n]
            .iter()
            .any(|o| contains_parameter(o, binder.id))
    {
        return Err(invalid("CombinationDomain"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = literal.equal_to.as_ref() else {
        return Err(invalid("CombinationSum"));
    };
    for (term, scalar, vector) in [(&sum.left, a, v), (&sum.right, b, w)] {
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = term.as_ref() else {
            return Err(invalid("CombinationProduct"));
        };
        let Obj::FnObj(call) = product.right.as_ref() else {
            return Err(invalid("CombinationCall"));
        };
        let [args] = call.body.as_slice() else {
            return Err(invalid("CombinationCall"));
        };
        let [arg] = args.as_slice() else {
            return Err(invalid("CombinationCall"));
        };
        if product.left.ir() != scalar.ir()
            || *call.head != FnObjHead::from_obj(vector.clone())
            || !matches!(arg.as_ref(), Obj::Identifier(IdentifierObj::Plain { id, .. }) if *id==binder.id)
        {
            return Err(invalid("CombinationCall"));
        }
    }
    Ok(())
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("InnerLinear/{stage}"),
        "Inner-product linearity requires the original ordered vector/scalar evidence, exact linear combination and constructor formation.")
}
