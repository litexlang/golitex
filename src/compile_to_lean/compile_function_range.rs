use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::FnApplicationInFnRangeKnownSpecialPropertyProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{FnRangeObjWellDefinedProof, FnObjDomainFnSetEvidence};
use crate::prelude::*;

impl LitexToLeanCompiler {
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
                let ObjWellDefinedProof::ByDef {
                    obj: Obj::FnObj(call),
                    proof: ObjWellDefinedProofByDef::FnObj(evidence),
                } = wd
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
            let signature = self.compile_fn_signature(&domain.signature, &formed)?;
            checks.push(format!("have _range_signature_{i} : Litex.In {function} (Litex.fnSet {signature}) := {member}"));
        }
        let signature = self.compile_fn_signature(&p.function_domains[0].signature, &formed)?;
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
                let ObjWellDefinedProof::ByDef {
                    obj: Obj::FnObj(call),
                    proof: ObjWellDefinedProofByDef::FnObj(evidence),
                } = wd
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
