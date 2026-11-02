use super::compile_real_set_bounds::contains_parameter;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    PredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_enumeration_sum_theorem(
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
        if builtin.theorem != BuiltinTheoremId::SumOverBijectiveFiniteSetEnumerations
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
            [left_callback, right_callback, first, last, outer, targets, finite, left_bij, right_bij],
            [_, _, _, _, _, _, _, _, _],
            [_, _, _, _, _, _, _, _, _],
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
            || goal.left.ir() != left.ir()
            || goal.right.ir() != right.ir()
        {
            return Err(invalid("Conclusion"));
        }
        let (
            Obj::IteratedOperator(IteratedOperator::Sum(l)),
            Obj::IteratedOperator(IteratedOperator::Sum(r)),
        ) = (left, right)
        else {
            return Err(invalid("SumProfile"));
        };
        // This slice retains named callbacks and syntactically common bounds.
        // Distinct equal endpoint expressions and anonymous BT arguments remain
        // explicit unsupported profiles, rather than re-verifying a new schema.
        if !matches!(l.func.as_ref(), Obj::Identifier(_))
            || !matches!(r.func.as_ref(), Obj::Identifier(_))
            || l.start.ir() != r.start.ir()
            || l.end.ir() != r.end.ir()
            || !same_equality(first, &l.start, &r.start)
            || !same_equality(last, &l.end, &r.end)
        {
            return Err(invalid("NamedCommonBoundsProfile"));
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(outer)) = outer else {
            return Err(invalid("OuterFunctions"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(targets)) = targets else {
            return Err(invalid("Targets"));
        };
        let (
            Fact::AtomicFact(AtomicFact::BijectiveFact(lb)),
            Fact::AtomicFact(AtomicFact::BijectiveFact(rb)),
        ) = (left_bij, right_bij)
        else {
            return Err(invalid("Bijections"));
        };
        let Obj::SetFormer(SetFormer::ClosedRange(range)) = &lb.domain else {
            return Err(invalid("EnumerationDomain"));
        };
        if range.start.ir() != l.start.ir()
            || range.end.ir() != l.end.ir()
            || rb.domain.ir() != lb.domain.ir()
            || lb.codomain.ir() != targets.left.ir()
            || rb.codomain.ir() != targets.left.ir()
            || !matches!(finite, Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir() == targets.left.ir())
        {
            return Err(invalid("EnumerationCarriers"));
        }
        let literal_left = validate_callback(
            left_callback,
            &l.func,
            &lb.domain,
            &outer.left,
            &lb.function,
        )?;
        let literal_right = validate_callback(
            right_callback,
            &r.func,
            &lb.domain,
            &outer.right,
            &rb.function,
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
            before: 9,
            ..*position
        };
        let bindings = self.compile_equal_wd_locals(goal, wd, &formed)?;
        let complete = SourcePosition::new(Some(&formed), SourceOwner::EqualWDLocals(wd, 2), 2);
        let left = self
            .compile_object_reference(left, &complete)?
            .replace('\n', "\n  ");
        let right = self
            .compile_object_reference(right, &complete)?
            .replace('\n', "\n  ");
        let callback_left = self
            .compile_original_enumeration_callback(
                &dom_proofs[0],
                literal_left,
                &SourcePosition {
                    before: 0,
                    ..*position
                },
            )?
            .replace('\n', "\n  ");
        let callback_right = self
            .compile_original_enumeration_callback(
                &dom_proofs[1],
                literal_right,
                &SourcePosition {
                    before: 1,
                    ..*position
                },
            )?
            .replace('\n', "\n  ");
        let callable_left = self
            .compile_original_enumerator_callable(
                &dom_proofs[7],
                &SourcePosition {
                    before: 7,
                    ..*position
                },
            )?
            .replace('\n', "\n  ");
        let callable_right = self
            .compile_original_enumerator_callable(
                &dom_proofs[8],
                &SourcePosition {
                    before: 8,
                    ..*position
                },
            )?
            .replace('\n', "\n  ");
        let target = self.compile_object_reference(&targets.left, &formed)?;
        let outer_left = self.compile_object_reference(&outer.left, &formed)?;
        let outer_right = self.compile_object_reference(&outer.right, &formed)?;
        let enum_left = self.compile_object_reference(&lb.function, &formed)?;
        let enum_right = self.compile_object_reference(&rb.function, &formed)?;
        let maps = |side: &str, function: &str, callable: &str| {
            format!(
            "have _enum_maps_{side} : ∀ _x, M.mem _x (Litex.denote (Litex.closedRange _enum_sum_{side}.val.first _enum_sum_{side}.val.last _enum_sum_{side}.wd.1 _enum_sum_{side}.wd.2.1)) → M.mem (Litex.FunctionSemantics.callValue (Litex.denote {function}) _x) (Litex.denote {target}) := by\n    intro _x _hx\n    have _enum_callable := {callable}\n    exact Litex.FunctionSemantics.call_mem _ _ _ _ _enum_callable ((Litex.SetSemantics.sep_members _ _ _).mpr ⟨_hx, True.intro⟩)")
        };
        let map_left = maps("left", &enum_left, &callable_left);
        let map_right = maps("right", &enum_right, &callable_right);
        let finite_ref = format!("h_{}", finite.fact_id().value());
        let left_eq = format!("h_{}", left_callback.fact_id().value());
        let right_eq = format!("h_{}", right_callback.fact_id().value());
        let left_bij = format!("h_{}", left_bij.fact_id().value());
        let right_bij = format!("h_{}", right_bij.fact_id().value());
        let outer_eq = format!("h_{}", outer.fact_id.value());
        let proof = format!("(by\n  let _enum_sum_left := {left}\n  let _enum_sum_right := {right}\n  let _enum_callback_left := {callback_left}\n  let _enum_callback_right := {callback_right}\n  {map_left}\n  {map_right}\n  have _enum_left := Litex.rangeSumNamedEnumerationValue _enum_sum_left _enum_callback_left (Litex.denote {target}) (Litex.denote {outer_left}) (Litex.denote {enum_left}) {finite_ref} {left_eq} (fun _ => rfl) rfl _enum_maps_left {left_bij}\n  have _enum_right := Litex.rangeSumNamedEnumerationValue _enum_sum_right _enum_callback_right (Litex.denote {target}) (Litex.denote {outer_right}) (Litex.denote {enum_right}) {finite_ref} {right_eq} (fun _ => rfl) rfl _enum_maps_right {right_bij}\n  exact _enum_left.trans ((congrArg (fun _f => M.number (Litex.finiteAggregateValue false (Litex.denote {target}) (fun _x => Litex.NativeBridge.complexValue (Litex.FunctionSemantics.callValue _f _x)))) {outer_eq}).trans _enum_right.symm)\n)");
        let statement = self.compile_formed_fact_proposition(
            &conclusions_wd[0],
            &builtin.conclusions[0],
            &formed,
        )?;
        let proof = Self::scope_equal_wd_proof(statement.clone(), proof, &bindings);
        Ok((
            definitions,
            format!("(show {statement} from {proof})"),
            builtin.conclusions.clone(),
        ))
    }

    fn compile_original_enumeration_callback(
        &self,
        proof: &VerifyFactResult,
        literal: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let VerifyFactResult::Equality(proof) = proof else {
            return Err(invalid("CallbackProof"));
        };
        let VerifyEqualityResult::Success(proof) = proof.as_ref() else {
            return Err(invalid("CallbackProof"));
        };
        let wd = &proof.well_defined_proof.detailed_ref().right;
        ensure_object(literal, wd)?;
        self.compile_wd(
            wd,
            &SourcePosition::new(
                Some(position),
                SourceOwner::EqualWDLocals(&proof.well_defined_proof, 1),
                1,
            ),
        )
    }

    fn compile_original_enumerator_callable(
        &self,
        proof: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let VerifyFactResult::AtomicExceptEquality(proof) = proof else {
            return Err(invalid("BijectionProof"));
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
            return Err(invalid("BijectionProof"));
        };
        let wd = &proof.well_defined_proof;
        if matches!(
            wd.detailed_ref().predicate_domain,
            PredicateDomainProof::ByKnownFact(_)
        ) {
            // A repeated bijection can inherit formation from its original
            // prior citation. Borrow this enumerator's checked parameter
            // signature; the bijection proposition alone does not imply
            // that every output belongs to the stated target.
            self.compile_atomic_wd_locals(wd, &proof.fact, position)?;
            let AtomicFact::BijectiveFact(bijection) = &proof.fact else {
                return Err(invalid("BijectionProof"));
            };
            let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &bijection.function else {
                return Err(invalid("EnumeratorParameterProfile"));
            };
            let (_, Some(carrier), fact_id, _) = position.visible_parameter(*id, &self.runtime)?
            else {
                return Err(invalid("EnumeratorParameterProfile"));
            };
            let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = carrier else {
                return Err(invalid("EnumeratorSignature"));
            };
            let [group] = signature.set_bound_parameters.groups.as_slice() else {
                return Err(invalid("EnumeratorSignature"));
            };
            if group.params.len() != 1
                || group.param_type.ir() != bijection.domain.ir()
                || signature.ret_set.ir() != bijection.codomain.ir()
                || !signature.dom_facts.is_empty()
            {
                return Err(invalid("EnumeratorSignature"));
            }
            let (source, member) = self.cited_fact_reference(fact_id, position)?;
            if !matches!(source, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == bijection.function.ir() && f.set.ir() == carrier.ir())
            {
                return Err(invalid("EnumeratorParameterMembership"));
            }
            return Ok(member);
        }
        let PredicateDomainProof::ByRequirements(requirements) =
            &wd.detailed_ref().predicate_domain
        else {
            return Err(invalid("BijectionFormation"));
        };
        let [_, _, callable] = requirements.as_slice() else {
            return Err(invalid("BijectionFormation"));
        };
        let PredicateDomainRequirementProof::Verified(callable) = &callable.result else {
            return Err(invalid("CallableProof"));
        };
        let bindings = self.compile_atomic_wd_locals(wd, &proof.fact, position)?;
        let prior = SourcePosition::new(Some(position), SourceOwner::AtomicWDLocals(wd, 3), 5);
        let checked = self.compile_verify(callable, &prior)?;
        Ok(Self::scope_equal_wd_proof(checked.0, checked.1, &bindings))
    }
}

fn same_equality(fact: &Fact, left: &Obj, right: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==left.ir() && f.right.ir()==right.ir())
}

fn validate_callback<'a>(
    fact: &'a Fact,
    function: &Obj,
    domain: &Obj,
    outer: &Obj,
    enumerator: &Obj,
) -> Result<&'a Obj, LeanCompileError> {
    let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = fact else {
        return Err(invalid("CallbackEquality"));
    };
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = &eq.right else {
        return Err(invalid("CallbackLiteral"));
    };
    let [group] = literal.body.set_bound_parameters.groups.as_slice() else {
        return Err(invalid("CallbackBinders"));
    };
    let [binder] = group.params.as_slice() else {
        return Err(invalid("CallbackBinders"));
    };
    if eq.left.ir() != function.ir()
        || group.param_type.ir() != domain.ir()
        || !literal.body.dom_facts.is_empty()
        || [function, domain, outer, enumerator]
            .iter()
            .any(|o| contains_parameter(o, binder.id))
    {
        return Err(invalid("CallbackDomain"));
    }
    let Obj::FnObj(call) = literal.equal_to.as_ref() else {
        return Err(invalid("CallbackComposition"));
    };
    let [args] = call.body.as_slice() else {
        return Err(invalid("CallbackComposition"));
    };
    let [inner] = args.as_slice() else {
        return Err(invalid("CallbackComposition"));
    };
    let Obj::FnObj(inner) = inner.as_ref() else {
        return Err(invalid("CallbackComposition"));
    };
    let [args] = inner.body.as_slice() else {
        return Err(invalid("CallbackComposition"));
    };
    let [arg] = args.as_slice() else {
        return Err(invalid("CallbackComposition"));
    };
    if *call.head != FnObjHead::from_obj(outer.clone())
        || *inner.head != FnObjHead::from_obj(enumerator.clone())
        || !matches!(arg.as_ref(), Obj::Identifier(IdentifierObj::Plain { id, .. }) if *id == binder.id)
    {
        return Err(invalid("CallbackComposition"));
    }
    Ok(&eq.right)
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("EnumerationSum/{stage}"),
        "Enumeration sum evidence has another original callback, range, target, bijection or formation stage.")
}
