use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::FnApplicationInFnRangeKnownSpecialPropertyProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{FnRangeObjWellDefinedProof, FnObjDomainFnSetEvidence};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_function_range_empty(
        &self,
        goal: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_function_domain_image::FnRangeOfEmptyDomainBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::function_domain::FunctionDomainEmptyProof as E;
        let (range, reverse) = match (&goal.left, &goal.right) {
            (
                Obj::FunctionSpace(FunctionSpace::FnRange(range)),
                Obj::SetFormer(SetFormer::ListSet(empty)),
            ) if empty.list.is_empty() => (range, false),
            (
                Obj::SetFormer(SetFormer::ListSet(empty)),
                Obj::FunctionSpace(FunctionSpace::FnRange(range)),
            ) if empty.list.is_empty() => (range, true),
            _ => return Err(LeanCompileError::unsupported("FnRangeEmpty/Endpoints")),
        };
        let signature = match &proof.domain_empty {
            E::ParameterCarrier(p) => &p.signature,
            E::GuardExclusion(p) => &p.signature,
        };
        if signature != &proof.source.signature {
            return Err(LeanCompileError::unsupported(
                "FnRangeEmpty/OriginalSignature",
            ));
        }
        let member =
            self.compile_complete_domain_member(&range.function, &proof.source, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::CompleteDomainSource(&proof.source),
            usize::MAX,
        );
        let compiled = self.compile_complete_domain_signature(&proof.source, &formed)?;
        let function = self.compile_object_reference(&range.function, &formed)?;
        let excluded = self.compile_complete_function_empty_domain(
            &proof.source,
            &proof.domain_empty,
            &compiled,
            position,
            &formed,
        )?;
        let term =
            format!("(Litex.fnRangeEmptyOfDomainEmpty {function} {compiled} {member} {excluded})");
        Ok(if reverse {
            format!("({term}).symm")
        } else {
            term
        })
    }

    pub(in crate::compile_to_lean) fn compile_complete_function_empty_domain(
        &self,
        source: &crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainProof,
        absence: &crate::execute::execute_fact_stmt::function_domain::FunctionDomainEmptyProof,
        compiled: &str,
        position: &SourcePosition<'_>,
        formed: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof as S;
        let signature = &source.signature;
        let carrier = match &source.source {
            S::Membership {
                membership,
                carrier_equal,
                ..
            } => Some(
                carrier_equal
                    .path
                    .last()
                    .map(|(_, to, _)| to)
                    .unwrap_or(&membership.set),
            ),
            S::ApplicationReturn {
                return_space,
                carrier_equal,
                ..
            } => Some(
                carrier_equal
                    .path
                    .last()
                    .map(|(_, to, _)| to)
                    .unwrap_or(return_space),
            ),
            _ => None,
        };
        let (base, guard) = if let Some(carrier) = carrier {
            self.checked_space_signature(carrier, signature, formed)?;
            let (base, _, guard) = self.space_domain_components(carrier, signature, formed)?;
            (base, guard)
        } else if matches!(&source.source, S::FiniteFunction(_) | S::Matrix(_)) {
            // These validated complete signatures own their one-based integer
            // inputs. Compile the original endpoints, not a synthetic range WD.
            if !signature.dom_facts.is_empty() {
                return Err(LeanCompileError::unsupported("FnRangeEmpty/IntervalGuards"));
            }
            let mut inputs = Vec::new();
            for group in &signature.set_bound_parameters.groups {
                let Obj::SetFormer(SetFormer::ClosedRange(interval)) = group.param_type.as_ref()
                else {
                    return Err(LeanCompileError::unsupported(
                        "FnRangeEmpty/IntervalSubject",
                    ));
                };
                // Literal bounds are part of the certified implicit signature;
                // they have no separate source WD registration to cite.
                let endpoint = |value: &Obj| match value {
                    Obj::Literal(Literal::Number(n)) => {
                        Ok(format!("(Litex.number {})", number_literal(n, "ℂ")?))
                    }
                    value => self.compile_object_reference(value, formed),
                };
                let start = endpoint(&interval.start)?;
                let end = endpoint(&interval.end)?;
                let input = format!("(Litex.SetSemantics.sepValue (M.standard .integer) (Litex.ClosedRangeObj.condition ⟨{start}, {end}⟩))");
                inputs.extend(group.params.iter().map(|_| input.clone()));
            }
            let base = if inputs.len() == 1 {
                inputs.remove(0)
            } else {
                format!(
                    "(Litex.FiniteFunction.cartValue (M := M) ![{}])",
                    inputs.join(", ")
                )
            };
            (base, "(fun _ => True)".into())
        } else {
            (
                self.compile_function_semantic_base_domain(signature, formed)?
                    .0,
                self.compile_function_packed_guard_template(signature, formed)?,
            )
        };
        // Only the complete finite signature embeds its arity as a Nat cast.
        // Other sources retain their original reducible domain membership.
        let input_membership = if matches!(&source.source, S::FiniteFunction(_)) {
            "(by simpa only [Litex.cartCompleteSignature, Litex.FunctionSignature.ofDomain, Litex.finiteSeqDomain, Nat.cast_zero] using _space_domain)"
        } else {
            "_space_domain"
        };
        let excluded = self.compile_empty_signature_domain(
            absence,
            compiled,
            &base,
            &guard,
            input_membership,
            position,
        )?;
        Ok(excluded)
    }

    pub(super) fn compile_function_range_subset(
        &self,
        goal: &SubsetFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::FunctionRangeInCodomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::FunctionRangeCodomainContainment;
        let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = &goal.left else {
            return Err(LeanCompileError::unsupported("FnRange/SubsetSubject"));
        };
        let member =
            self.compile_complete_domain_member(&range.function, &proof.source, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::CompleteDomainSource(&proof.source),
            usize::MAX,
        );
        let signature = self.compile_complete_domain_signature(&proof.source, &formed)?;
        let function = self.compile_object_reference(&range.function, &formed)?;
        let output = self.compile_object_reference(&proof.source.signature.ret_set, &formed)?;
        let target = self.compile_object_reference(&goal.right, &formed)?;
        let range = self.compile_object_reference(&goal.left, &formed)?;
        let step = match &proof.containment {
            FunctionRangeCodomainContainment::Exact(equal) => {
                let obligation = EqualFact {
                    fact_id: goal.fact_id,
                    left: *proof.source.signature.ret_set.clone(),
                    right: goal.right.clone(),
                    line_file: None,
                };
                let same = self.compile_equality_search(&obligation, equal, &formed)?;
                format!("Litex.subsetOfSame {range} {output} {range} {target} (Litex.sameRefl {range}) {same} _range_subset")
            }
            FunctionRangeCodomainContainment::Subset(child) => {
                if !matches!(source_subject(child)?, Fact::AtomicFact(AtomicFact::SubsetFact(f))
                    if f.left.ir() == proof.source.signature.ret_set.ir()
                        && f.right.ir() == goal.right.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "FnRange/CodomainSubsetSubject",
                    ));
                }
                let child_position = position.atomic_search_verify_prior(child)?;
                let subset = self.compile_verify(child, &child_position)?.1;
                format!("(by\n  have _codomain_subset : Litex.Subset {output} {target} := {subset}\n  exact fun _x _hx => _codomain_subset _ (_range_subset _ _hx))")
            }
        };
        Ok(format!("(by\n  have _range_function : Litex.In {function} (Litex.fnSet {signature}) := {member}\n  have _range_subset : Litex.Subset {range} {output} := fun _x _hx => Litex.FunctionSemantics.range_subset ({signature}).output_isSet _range_function _hx\n  exact {step})"))
    }

    /// A named inference may introduce the range before a separate range WD
    /// result exists. Reuse an original parameter's membership or a preceding
    /// checked literal constructor; never manufacture a new function WD record.
    pub(super) fn compile_inferred_parameter_range(
        &self,
        range: &FnRange,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if matches!(
            range.function.as_ref(),
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(_))
        ) {
            use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
            let function = position
                .with_visible_wd(&range.function, &mut |wd, producer| {
                    if !matches!(
                        wd.detailed_ref(),
                        DetailedObjWellDefinedProof::ByDef {
                            proof: ObjWellDefinedProofByDef::FunctionSpace(
                                FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(_)
                            ),
                            ..
                        }
                    ) {
                        return Err(LeanCompileError::unsupported(
                            "FnRange/InferenceLiteralConstructor",
                        ));
                    }
                    self.compile_wd(wd, producer)
                })?
                .ok_or_else(|| {
                    LeanCompileError::unsupported("FnRange/InferenceLiteralFormation")
                })?;
            return Ok(format!(
                "(by\n  let _range_original_function := {}\n  exact Litex.fnRange _range_original_function _range_original_function.val.signature (Litex.formulaFnInFnSet _range_original_function)\n)",
                function.replace('\n', "\n  ")
            ));
        }
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = range.function.as_ref() else {
            return Err(LeanCompileError::unsupported("FnRange/InferenceParameter"));
        };
        let (_, Some(carrier), fact_id, _) = position.visible_parameter(*id, &self.runtime)? else {
            return Err(LeanCompileError::unsupported("FnRange/InferenceCarrier"));
        };
        let (source, member) = self.cited_fact_reference(fact_id, position)?;
        if !matches!(source, Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir() == range.function.ir() && f.set.ir() == carrier.ir())
        {
            return Err(LeanCompileError::unsupported("FnRange/InferenceMembership"));
        }
        let carrier_term = self.compile_object_reference(carrier, position)?;
        let (signature, equality) = match carrier {
            Obj::FunctionSpace(FunctionSpace::FnSet(_)) => (
                format!("({carrier_term}).val"),
                format!("(Litex.sameRefl {carrier_term})"),
            ),
            Obj::SetFormer(SetFormer::SeqSet(_)) => (
                format!("(Litex.seqSignature ({carrier_term}).val.carrier)"),
                format!("(Litex.seqSet_eq_fnSet {carrier_term})"),
            ),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FnRange/InferenceFunctionCarrier",
                ))
            }
        };
        let function = self.compile_object_reference(&range.function, position)?;
        Ok(format!("(Litex.fnRange {function} {signature} (Litex.inOfSame {function} {function} {carrier_term} (Litex.fnSet {signature}) (Litex.sameRefl {function}) {equality} {member}))"))
    }

    pub(super) fn compile_anonymous_call_in_range(
        &self,
        goal: &InFact,
        equality: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = &goal.set else {
            return Err(LeanCompileError::unsupported("FnRange/Goal"));
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(literal)) = range.function.as_ref()
        else {
            return Err(LeanCompileError::unsupported("FnRange/LiteralRange"));
        };
        position
            .with_visible_wd(&goal.element, &mut |wd, producer| {
                let DetailedObjWellDefinedProof::ByDef {
                    obj: Obj::FnObj(call),
                    proof: ObjWellDefinedProofByDef::FnObj(evidence),
                } = (wd).detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("FnRange/CallFormation"));
                };
                let arity = literal
                    .body
                    .set_bound_parameters
                    .groups
                    .iter()
                    .map(|g| g.params.len())
                    .sum::<usize>();
                if call.body.len() != 1 || call.body[0].len() != arity {
                    return Err(LeanCompileError::unsupported("FnRange/CallArity"));
                }
                let head = match call.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(f) => {
                        Obj::FunctionSpace(FunctionSpace::AnonymousFn(f.as_ref().clone()))
                    }
                    FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
                    _ => return Err(LeanCompileError::unsupported("FnRange/CallHead")),
                };
                let same = match equality {
                    EqualFactSearchedProof::ByTheyAreTheSame(p) => {
                        self.compile_identity(&head, &range.function, p, position)?
                    }
                    EqualFactSearchedProof::ByEquivalenceClass(
                        EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
                    ) => self.compile_equality_path(&head, &range.function, p, position)?,
                    _ => return Err(LeanCompileError::unsupported("FnRange/FunctionEquality")),
                };
                let signature = match &evidence.domain_fn_set {
                    Some(
                        FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set }
                        | FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. },
                    ) => fn_set,
                    _ => return Err(LeanCompileError::unsupported("FnRange/CallSignature")),
                };
                let ctor = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                let object = match position
                    .bound_wd_child(wd)
                    .or_else(|| producer.bound_wd_child(wd))
                {
                    Some(t) => t,
                    None => self.compile_fn_obj_wd(call, evidence, &ctor)?,
                };
                let law = if !Self::function_uses_numeric_interface(signature) {
                    "callOnInFnRange"
                } else if arity == 1 {
                    "callInFnRange"
                } else {
                    "call2InFnRange"
                };
                Ok(format!(
                    "(Litex.{law} {object} {} {same})",
                    self.compile_object_reference(&goal.set, position)?
                ))
            })?
            .ok_or_else(|| LeanCompileError::unsupported("FnRange/CallProducer"))
    }

    pub(super) fn compile_function_range_wd(
        &self,
        range: &FnRange,
        p: &FnRangeObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if p.child_obj_well_defined.len() != 1
            || !p.requirement_fact_verified.is_empty()
            || p.function_domains.is_empty()
        {
            return Err(LeanCompileError::unsupported("FnRange/FormationStages"));
        }
        ensure_object(&range.function, &p.child_obj_well_defined[0])?;
        let function = self.compile_wd(&p.child_obj_well_defined[0], position)?;
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let mut checks = Vec::new();
        for (i, domain) in p.function_domains.iter().enumerate() {
            let member = self.compile_complete_domain_member(&range.function, domain, &formed)?;
            let signature = self.compile_complete_domain_signature(domain, &formed)?;
            checks.push(format!("have _range_signature_{i} : Litex.In {function} (Litex.fnSet {signature}) := {member}"));
        }
        let signature = self.compile_complete_domain_signature(&p.function_domains[0], &formed)?;
        Ok(format!(
            "(by\n  {}\n  exact Litex.fnRange {function} {signature} _range_signature_0)",
            checks.join("\n  ")
        ))
    }

    pub(super) fn compile_selected_signature(
        &self,
        function: &Obj,
        selected: &FunctionSignatureSelection,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let term = self.compile_object_reference(function, position)?;
        match selected {
            FunctionSignatureSelection::AnonymousLiteral { signature } => {
                if !matches!(function,Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) if f.body==*signature)
                {
                    return Err(LeanCompileError::unsupported("FnRange/SelectedLiteral"));
                }
                Ok(format!("(Litex.formulaFnInFnSet {term})"))
            }
            FunctionSignatureSelection::Property { signature, fact_id } => {
                let (original, member) =
                    self.compile_fn_return_citation(*fact_id, function, &term, None, position)?;
                if original != signature {
                    return Err(LeanCompileError::unsupported("FnRange/SelectedSignature"));
                }
                Ok(member)
            }
            FunctionSignatureSelection::DeclaredField { .. } => Err(LeanCompileError::unsupported(
                "Function/SelectedFieldSignature",
            )),
        }
    }

    pub(super) fn compile_call_in_range(
        &self,
        goal: &InFact,
        p: &FnApplicationInFnRangeKnownSpecialPropertyProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = &goal.set else {
            return Err(LeanCompileError::unsupported("FnRange/Goal"));
        };
        let function = self.compile_object_reference(&range.function, position)?;
        let (property_signature, _) = self.compile_fn_return_citation(
            p.cite_property_fact_id,
            &range.function,
            &function,
            Some(&p.function_equal),
            position,
        )?;
        let mut ids = Vec::new();
        for matched in &p.signature_matches {
            if ids.contains(&matched.cite_signature_fact_id) {
                return Err(LeanCompileError::unsupported("FnRange/DuplicateSignature"));
            }
            ids.push(matched.cite_signature_fact_id);
            let (candidate, _) = self.compile_fn_return_citation(
                matched.cite_signature_fact_id,
                &range.function,
                &function,
                None,
                position,
            )?;
            self.compile_fn_return_set_match(
                &Obj::FunctionSpace(FunctionSpace::FnSet(candidate.clone())),
                &Obj::FunctionSpace(FunctionSpace::FnSet(property_signature.clone())),
                &matched.signature_match,
                position,
            )?;
        }
        position
            .with_visible_wd(&goal.element, &mut |wd, producer| {
                let DetailedObjWellDefinedProof::ByDef {
                    obj: Obj::FnObj(call),
                    proof: ObjWellDefinedProofByDef::FnObj(evidence),
                } = (wd).detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported("FnRange/CallFormation"));
                };
                if call.body.len() != 1
                    || *call.head != FnObjHead::from_obj(range.function.as_ref().clone())
                {
                    return Err(LeanCompileError::unsupported("FnRange/CallHead"));
                }
                let Some(FnObjDomainFnSetEvidence::InFunctionSet {
                    fn_set, fact_id, ..
                }) = &evidence.domain_fn_set
                else {
                    return Err(LeanCompileError::unsupported("FnRange/CallSignature"));
                };
                if !ids.contains(fact_id) {
                    return Err(LeanCompileError::unsupported(
                        "FnRange/UnmatchedCallSignature",
                    ));
                }
                let ctor = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                let object = match position
                    .bound_wd_child(wd)
                    .or_else(|| producer.bound_wd_child(wd))
                {
                    Some(t) => t,
                    None => self.compile_fn_obj_wd(call, evidence, &ctor)?,
                };
                let law = if !Self::function_uses_numeric_interface(fn_set) {
                    "callOnInFnRange"
                } else if call.body[0].len() == 1 {
                    "callInFnRange"
                } else {
                    "call2InFnRange"
                };
                Ok(format!(
                    "(Litex.{law} {object} {} (Litex.sameRefl {function}))",
                    self.compile_object_reference(&goal.set, position)?
                ))
            })?
            .ok_or_else(|| LeanCompileError::unsupported("FnRange/CallProducer"))
    }
}
