//! Replay both original zero-norm implications, including their local WD owners.
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

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("NormZero/{stage}"))
}

fn equality(fact: &Fact) -> Result<&EqualFact, LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::EqualFact(f)) => Ok(f),
        _ => Err(invalid("OriginalEquality")),
    }
}

fn implication(fact: &Fact) -> Result<(&ForallFact, &EqualFact, &EqualFact), LeanCompileError> {
    let Fact::ForallFact(f) = fact else {
        return Err(invalid("OriginalConditional"));
    };
    if !f.typed_parameters.groups.is_empty() || f.dom_facts.len() != 1 || f.then_facts.len() != 1 {
        return Err(invalid("ConditionalStages"));
    }
    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(then)) = &f.then_facts[0]
    else {
        return Err(invalid("ConditionalThen"));
    };
    Ok((f, equality(&f.dom_facts[0])?, then))
}

fn same_equality(a: &EqualFact, b: &EqualFact) -> bool {
    a.left.ir() == b.left.ir() && a.right.ir() == b.right.ir()
}

fn validate_zero_function(obj: &Obj, n: &Obj, args: &[Obj]) -> Result<(), LeanCompileError> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(zero)) = obj else {
        return Err(invalid("ZeroFunction"));
    };
    let [group] = zero.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("ZeroFunctionBinder"));
    };
    let [binder] = group.params.as_slice() else {
        return Err(invalid("ZeroFunctionBinder"));
    };
    let Obj::SetFormer(SetFormer::ClosedRange(range)) = group.param_type.as_ref() else {
        return Err(invalid("ZeroFunctionDomain"));
    };
    if closed_integer(&range.start) != Some(1)
        || range.end.ir() != n.ir()
        || zero.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
        || !zero.body.dom_facts.is_empty()
        || closed_integer(&zero.equal_to) != Some(0)
        || args.iter().any(|a| contains_parameter(a, binder.id))
    {
        return Err(invalid("ExactZeroFunction"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_norm_zero(
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
        let vector = match builtin.theorem {
            BuiltinTheoremId::EuclideanNormZero => true,
            BuiltinTheoremId::FrobeniusNormZero => false,
            _ => return Err(invalid("Theorem")),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        let arity = if vector { 2 } else { 3 };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || call.name.local_name() != builtin.theorem.as_str()
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != arity
            || dom_proofs.len() != arity
            || dom_stores.len() != arity
            || builtin.conclusions.len() != 2
            || conclusions_wd.len() != 2
        {
            return Err(invalid("OriginalStages"));
        }
        let (_, norm_zero, object_zero) = implication(&builtin.conclusions[0])?;
        let (_, object_zero_back, norm_zero_back) = implication(&builtin.conclusions[1])?;
        if !same_equality(norm_zero, norm_zero_back)
            || !same_equality(object_zero, object_zero_back)
            || closed_integer(&norm_zero.right) != Some(0)
            || object_zero.left.ir() != args[0].ir()
        {
            return Err(invalid("OrderedImplications"));
        }
        match &norm_zero.left {
            Obj::MatrixOperator(MatrixOperator::EuclideanNorm(p))
                if vector && p.vector.ir() == args[0].ir() && p.dimension.ir() == args[1].ir() =>
            {
                validate_zero_function(&object_zero.right, &args[1], args)?;
            }
            Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(p))
                if !vector
                    && p.matrix.ir() == args[0].ir()
                    && p.rows.ir() == args[1].ir()
                    && p.cols.ir() == args[2].ir() =>
            {
                if !matches!(&object_zero.right, Obj::MatrixOperator(MatrixOperator::ZeroMatrix(z))
                    if z.rows.ir()==args[1].ir() && z.cols.ir()==args[2].ir())
                {
                    return Err(invalid("ZeroMatrixDimensions"));
                }
            }
            _ => return Err(invalid("OriginalNorm")),
        }
        let mut definitions = Vec::new();
        let mut refs = Vec::new();
        for (index, ((requirement, checked), stored)) in builtin
            .requirements
            .iter()
            .zip(dom_proofs)
            .zip(dom_stores)
            .enumerate()
        {
            let valid = if index + 1 < arity {
                matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f))
                    if f.element.ir()==args[index+1].ir() && f.set==Obj::StandardSet(StandardSet::N))
            } else {
                matches!(requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==args[0].ir()
                && match &f.set {
                    Obj::SetFormer(SetFormer::FiniteSeqSet(s)) => vector && s.n.ir()==args[1].ir() && s.set.as_ref()==&Obj::StandardSet(StandardSet::C),
                    Obj::SetFormer(SetFormer::MatrixSet(s)) => !vector && s.rows.ir()==args[1].ir() && s.cols.ir()==args[2].ir() && s.set.as_ref()==&Obj::StandardSet(StandardSet::C),
                    _ => false,
                })
            };
            if !valid || source_subject(checked)? != *requirement {
                return Err(invalid("OriginalPremise"));
            }
            self.validate_store(&stored.store, requirement)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                stored,
                requirement,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            refs.push(reference);
        }
        let formed = SourcePosition {
            before: arity,
            ..*position
        };
        let mut proofs = Vec::new();
        for (index, (fact, wd)) in builtin.conclusions.iter().zip(conclusions_wd).enumerate() {
            let (clause, _, then) = implication(fact)?;
            let FactWellDefinedProof::ForallFact(wd) = wd else {
                return Err(invalid("ConditionalWD"));
            };
            self.compile_forall_wd(clause, wd, &formed)?;
            let statement = self.compile_forall_formation(clause, wd, &formed)?;
            let head = SourcePosition::new(Some(&formed), SourceOwner::ForallWD(clause, wd), 0);
            let (binders, _, locals) = self.compile_forall_head(
                clause,
                &wd.detailed_ref().introduced_params,
                &wd.detailed_ref().assumed_dom_facts,
                &head,
            )?;
            let then_position = SourcePosition { before: 1, ..head };
            let [FactWellDefinedProof::Equality(equal_wd)] = wd.detailed_ref().then.as_slice()
            else {
                return Err(invalid("ThenWD"));
            };
            let bindings = self.compile_equal_wd_locals(then, equal_wd, &then_position)?;
            let complete = SourcePosition::new(
                Some(&then_position),
                SourceOwner::EqualWDLocals(equal_wd, 2),
                2,
            );
            let objects = args
                .iter()
                .map(|o| self.compile_object_reference(o, &complete))
                .collect::<Result<Vec<_>, _>>()?;
            let law = if vector {
                let zero = self.compile_object_reference(&object_zero.right, &complete)?;
                format!("Litex.euclideanNormZeroFormula {} {} {zero} {} {} (by rfl) (by rfl) (by intro k; rfl)", objects[0],objects[1],refs[0],refs[1])
            } else {
                format!(
                    "Litex.frobeniusNormZeroCharacterization {} {} {} {} {} {}",
                    objects[0], objects[1], objects[2], refs[0], refs[1], refs[2]
                )
            };
            let hypothesis = format!("h_{}", clause.dom_facts[0].fact_id().value());
            let body = format!("({law}).{} {hypothesis}", index + 1);
            let then_statement = self.compile_formed_fact_proposition(
                &wd.detailed_ref().then[0],
                &then.clone().into(),
                &then_position,
            )?;
            let body = Self::scope_equal_wd_proof(then_statement, body, &bindings);
            let body = self.scope_proposition(body, &locals);
            proofs.push(format!(
                "(show {statement} from (fun {} => {body}))",
                binders.join(" ")
            ));
        }
        Ok((
            definitions,
            format!("(And.intro {} {})", proofs[0], proofs[1]),
            builtin.conclusions.clone(),
        ))
    }
}
