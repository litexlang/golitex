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
    pub(super) fn compile_builtin_norm_scale_theorem(
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
        if builtin.theorem != BuiltinTheoremId::EuclideanNormScale
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
            [a, v, n],
            [scalar, natural, vector],
            [_, _, _],
            [_, _, _],
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
        if args != &builtin.arguments
            || !matches!(scalar,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==a.ir() && f.set==Obj::StandardSet(StandardSet::C))
            || !matches!(natural,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==n.ir() && f.set==Obj::StandardSet(StandardSet::N))
            || !matches!(vector,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==v.ir() && matches!(&f.set,Obj::SetFormer(SetFormer::FiniteSeqSet(s)) if s.n.ir()==n.ir() && s.set.as_ref()==&Obj::StandardSet(StandardSet::C)))
        {
            return Err(invalid("OriginalRequirements"));
        }
        let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(norm)) = &goal.left else {
            return Err(invalid("LeftNorm"));
        };
        if norm.dimension.ir() != n.ir() {
            return Err(invalid("Dimension"));
        }
        validate_scale(&norm.vector, a, v, n)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = &goal.right else {
            return Err(invalid("RightProduct"));
        };
        let Obj::ComplexOperator(ComplexOperator::ComplexAbs(modulus)) = product.left.as_ref()
        else {
            return Err(invalid("ScalarModulus"));
        };
        let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(original)) = product.right.as_ref()
        else {
            return Err(invalid("OriginalNorm"));
        };
        if modulus.arg.ir() != a.ir()
            || original.vector.ir() != v.ir()
            || original.dimension.ir() != n.ir()
        {
            return Err(invalid("RightArguments"));
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
            before: 3,
            ..*position
        };
        let bindings = self.compile_equal_wd_locals(goal, wd, &formed)?;
        let complete = SourcePosition::new(Some(&formed), SourceOwner::EqualWDLocals(wd, 2), 2);
        let left = self
            .compile_object_reference(&goal.left, &complete)?
            .replace('\n', "\n  ");
        let a = self.compile_object_reference(a, &complete)?;
        let v = self.compile_object_reference(v, &complete)?;
        let ha = format!("h_{}", scalar.fact_id().value());
        let hv = format!("h_{}", vector.fact_id().value());
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof=format!("(by\n  let _scaled_norm := {left}\n  exact Litex.euclideanNormScale _scaled_norm _scaled_norm.val.vector (Litex.denote {a}) (Litex.denote {v}) {ha} {hv} (by rfl) (by rfl) (by rfl)\n)");
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }
}

fn validate_scale(object: &Obj, a: &Obj, v: &Obj, n: &Obj) -> Result<(), LeanCompileError> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = object else {
        return Err(invalid("ScaleFunction"));
    };
    let [group] = literal.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("ScaleBinder"));
    };
    let [binder] = group.params.as_slice() else {
        return Err(invalid("ScaleBinder"));
    };
    let Obj::SetFormer(SetFormer::ClosedRange(range)) = group.param_type.as_ref() else {
        return Err(invalid("ScaleDomain"));
    };
    if closed_integer(&range.start) != Some(1)
        || range.end.ir() != n.ir()
        || literal.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
        || !literal.body.dom_facts.is_empty()
        || [a, v, n].iter().any(|o| contains_parameter(o, binder.id))
    {
        return Err(invalid("ScaleDomain"));
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = literal.equal_to.as_ref()
    else {
        return Err(invalid("ScaleBody"));
    };
    let Obj::FnObj(call) = product.right.as_ref() else {
        return Err(invalid("ScaleCall"));
    };
    let [args] = call.body.as_slice() else {
        return Err(invalid("ScaleCall"));
    };
    let [arg] = args.as_slice() else {
        return Err(invalid("ScaleCall"));
    };
    if product.left.ir() != a.ir()
        || *call.head != FnObjHead::from_obj(v.clone())
        || !matches!(arg.as_ref(),Obj::Identifier(IdentifierObj::Plain { id,.. }) if *id==binder.id)
    {
        return Err(invalid("ScaleCall"));
    }
    Ok(())
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("NormScale/{stage}"),
        "Norm scaling requires the original complex scalar/vector domains, exact coordinate function and formation stages.")
}
