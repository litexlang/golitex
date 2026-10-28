use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_composition::*;
use crate::execute::execute_fact_stmt::function_domain::function_application;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_composition_range_subset(
        &self,
        goal: &SubsetFact,
        p: &CompositionCallableProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            Obj::FunctionSpace(FunctionSpace::FnRange(left)),
            Obj::FunctionSpace(FunctionSpace::FnRange(right)),
        ) = (&goal.left, &goal.right)
        else {
            return Err(LeanCompileError::unsupported("CompositionRange/Endpoints"));
        };
        if right.function.ir() != p.composition.outer.ir() {
            return Err(LeanCompileError::unsupported("CompositionRange/Outer"));
        }
        let member = self.compile_composition_member(&left.function, p, position)?;
        let root = Obj::FunctionSpace(FunctionSpace::Composition(p.composition.clone()));
        let same =
            self.compile_equality_path(&left.function, &root, &p.function_equal, position)?;
        let c = self.compile_object_reference(&root, position)?;
        let l = self.compile_object_reference(&goal.left, position)?;
        let r = self.compile_object_reference(&goal.right, position)?;
        Ok(format!("(by\n  have _composition_interface := {member}\n  exact Litex.composeRangeSubset {c} {l} {r} {same} (by rfl))"))
    }

    pub(super) fn compile_composition_output(
        &self,
        goal: &InFact,
        proof: &CompositionApplicationInCodomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(call) = &goal.element else {
            return Err(LeanCompileError::unsupported("Composition/OutputSubject"));
        };
        if call.body.len() != 1
            || proof.return_set.ir() != proof.callable.function.body.ret_set.ir()
        {
            return Err(LeanCompileError::unsupported("Composition/OutputSignature"));
        }
        let head = match call.head.as_ref() {
            FnObjHead::Identifier(i) => Obj::Identifier(i.clone()),
            FnObjHead::Object(o) => o.as_ref().clone(),
            _ => return Err(LeanCompileError::unsupported("Composition/OutputHead")),
        };
        let hf = self.compile_composition_member(&head, &proof.callable, position)?;
        let sig = self.compile_fn_signature(&proof.callable.function.body, position)?;
        let f = self.compile_object_reference(&head, position)?;
        let member=position.with_visible_wd(&goal.element,&mut |wd,producer| {
            let DetailedObjWellDefinedProof::ByDef {proof:ObjWellDefinedProofByDef::FnObj(p),..} = (wd).detailed_ref() else {
                return Err(LeanCompileError::unsupported("Composition/OutputCallWD"));
            };
            let scope=SourcePosition::new(Some(producer),SourceOwner::WD(wd),0);
            let (input,domain)=self.compile_fn_return_domain(call,p,&proof.callable.function.body,&scope)?;
            Ok(format!("(Litex.FunctionSemantics.call_mem ({sig}).domain ({sig}).output (Litex.denote {f}) {input} {hf} {domain})"))
        })?.ok_or_else(||LeanCompileError::unsupported("Composition/OutputCallProducer"))?;
        if goal.set.ir() == proof.return_set.ir() {
            return Ok(member);
        }
        let (Obj::StandardSet(source), Obj::StandardSet(target)) = (&proof.return_set, &goal.set)
        else {
            return Err(LeanCompileError::unsupported("Composition/OutputInclusion"));
        };
        standard_inclusion_term(
            source,
            target,
            &self.compile_object_reference(&goal.element, position)?,
            &member,
        )
    }

    pub(super) fn compile_composition_beta(
        &self,
        application: &Obj,
        wd: &ObjWellDefinedProof,
        composition: &Composition,
        path: &KnownEqualityPathProof,
        expanded: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        ensure_object(application, wd)?;
        if let DetailedObjWellDefinedProof::ByKnown { wd_id, .. } = (wd).detailed_ref() {
            if self.resolve_wd(*wd_id, position)?.ir() != application.ir() {
                return Err(LeanCompileError::unsupported("Composition/BetaWDId"));
            }
            return position
                .with_visible_wd(application, &mut |original, producer| {
                    self.compile_composition_beta(
                        application,
                        original,
                        composition,
                        path,
                        expanded,
                        producer,
                    )
                })?
                .ok_or_else(|| LeanCompileError::unsupported("Composition/BetaWDProducer"));
        }
        let (
            Obj::FnObj(call),
            DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call_wd),
                ..
            },
        ) = (application, wd.detailed_ref())
        else {
            return Err(LeanCompileError::unsupported("Composition/BetaCallWD"));
        };
        let Some(FnObjDomainFnSetEvidence::Composition(p)) = &call_wd.domain_fn_set else {
            return Err(LeanCompileError::unsupported("Composition/BetaSignature"));
        };
        if p.composition != *composition
            || call.body.len() != 1
            || call_wd.child_obj_well_defined.len() != call.body[0].len()
        {
            return Err(LeanCompileError::unsupported("Composition/BetaSubject"));
        }
        let inner = function_application(&composition.inner, call.body[0].clone())
            .map_err(|_| LeanCompileError::unsupported("Composition/BetaInner"))?;
        let body = function_application(&composition.outer, vec![Box::new(inner)])
            .map_err(|_| LeanCompileError::unsupported("Composition/BetaOuter"))?;
        if body.ir() != expanded.ir() {
            return Err(LeanCompileError::unsupported("Composition/BetaEndpoint"));
        }
        let CompositionWellDefinedPremise::Checked(root_wd) = &p.well_defined else {
            return Err(LeanCompileError::unsupported("Composition/BetaFormation"));
        };
        let root = Obj::FunctionSpace(FunctionSpace::Composition(composition.clone()));
        ensure_object(&root, root_wd)?;
        let term = self.compile_wd(root_wd, position)?;
        let scope = SourcePosition::new(Some(position), SourceOwner::WD(root_wd), usize::MAX);
        let (outer, inner) = match &p.signature {
            CompositionSignatureProof::Interfaces {
                outer_domain,
                inner_domain,
            } => (outer_domain.as_ref(), inner_domain.as_ref()),
            CompositionSignatureProof::Construction => match (root_wd.as_ref()).detailed_ref() {
                DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::FunctionSpace(
                            FunctionSpaceObjWellDefinedProofByDef::Composition(c),
                        ),
                    ..
                } if c.function == p.function => (c.outer_domain.as_ref(), c.inner_domain.as_ref()),
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "Composition/BetaConstruction",
                    ))
                }
            },
        };
        validate_composition_function(
            composition,
            &outer.signature,
            &inner.signature,
            &p.function,
        )?;
        let head = match call.head.as_ref() {
            FnObjHead::Identifier(i) => Obj::Identifier(i.clone()),
            FnObjHead::Object(o) => o.as_ref().clone(),
            _ => return Err(LeanCompileError::unsupported("Composition/BetaHead")),
        };
        let same = self.compile_equality_path(&head, &root, path, &scope)?;
        let head_value = self.compile_normalization_value(&head, &scope)?;
        let same = format!("(show {head_value} = Litex.denote {term} from {same})");
        let s = self.compile_fn_signature(&outer.signature, &scope)?;
        let t = self.compile_fn_signature(&inner.signature, &scope)?;
        let hf = self.compile_complete_domain_member(&composition.outer, outer, &scope)?;
        let hg = self.compile_complete_domain_member(&composition.inner, inner, &scope)?;
        let call_scope = SourcePosition::new(Some(&scope), SourceOwner::WD(wd), 0);
        // Validate all call stages as well as the selected beta endpoint.
        self.compile_fn_obj_wd(call, call_wd, &call_scope)?;
        let (input, domain) =
            self.compile_fn_return_domain(call, call_wd, &p.function.body, &call_scope)?;
        let lhs = self.compile_normalization_value(application, &scope)?;
        let rhs = self.compile_normalization_value(expanded, &scope)?;
        Ok(format!("(show {lhs} = {rhs} from by\n  have _composition_head := congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f {input}) {same}\n  exact _composition_head.trans (Litex.composeCall {term} {s} {t} {hf} {hg} {input} {domain}))"))
    }

    pub(super) fn compile_composition_member(
        &self,
        subject: &Obj,
        proof: &CompositionCallableProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let root = Obj::FunctionSpace(FunctionSpace::Composition(proof.composition.clone()));
        match &proof.well_defined {
            CompositionWellDefinedPremise::Checked(wd) => {
                ensure_object(&root, wd)?;
                let term = self.compile_wd(wd, position)?;
                let scope = SourcePosition::new(Some(position), SourceOwner::WD(wd), usize::MAX);
                self.compile_composition_member_at(subject, proof, &term, Some(wd), &scope)
            }
            CompositionWellDefinedPremise::ParentAtomic => {
                let term = self.compile_object_reference(&root, position)?;
                if matches!(proof.signature, CompositionSignatureProof::Construction) {
                    position
                        .with_visible_wd(&root, &mut |wd, producer| {
                            let scope = SourcePosition::new(
                                Some(producer),
                                SourceOwner::WD(wd),
                                usize::MAX,
                            );
                            self.compile_composition_member_at(
                                subject,
                                proof,
                                &term,
                                Some(wd),
                                &scope,
                            )
                        })?
                        .ok_or_else(|| {
                            LeanCompileError::unsupported("Composition/ParentConstructor")
                        })
                } else {
                    self.compile_composition_member_at(subject, proof, &term, None, position)
                }
            }
        }
    }

    fn compile_composition_member_at(
        &self,
        subject: &Obj,
        proof: &CompositionCallableProof,
        term: &str,
        wd: Option<&ObjWellDefinedProof>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (outer, inner) = match &proof.signature {
            CompositionSignatureProof::Interfaces {
                outer_domain,
                inner_domain,
            } => (outer_domain.as_ref(), inner_domain.as_ref()),
            CompositionSignatureProof::Construction => {
                let Some(DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::FunctionSpace(
                            FunctionSpaceObjWellDefinedProofByDef::Composition(p),
                        ),
                    ..
                }) = wd.map(ObjWellDefinedProof::detailed_ref)
                else {
                    return Err(LeanCompileError::unsupported(
                        "Composition/ConstructionSignature",
                    ));
                };
                if p.function != proof.function {
                    return Err(LeanCompileError::unsupported(
                        "Composition/ConstructionFunction",
                    ));
                }
                (p.outer_domain.as_ref(), p.inner_domain.as_ref())
            }
        };
        validate_composition_function(
            &proof.composition,
            &outer.signature,
            &inner.signature,
            &proof.function,
        )?;
        let root = Obj::FunctionSpace(FunctionSpace::Composition(proof.composition.clone()));
        let same = self.compile_equality_path(subject, &root, &proof.function_equal, position)?;
        let s = self.compile_fn_signature(&outer.signature, position)?;
        let t = self.compile_fn_signature(&inner.signature, position)?;
        let hf = self.compile_complete_domain_member(&proof.composition.outer, outer, position)?;
        let hg = self.compile_complete_domain_member(&proof.composition.inner, inner, position)?;
        let member = format!("(Litex.composeInFnSet {term} {s} {t} {hf} {hg})");
        if proof.function_equal.path.is_empty() {
            return Ok(member);
        }
        let target = self.compile_object_reference(subject, position)?;
        let sig = self.compile_fn_signature(&proof.function.body, position)?;
        Ok(format!("(Litex.inOfSame {term} {target} (Litex.fnSet {sig}) (Litex.fnSet {sig}) ({same}).symm (Litex.sameRefl _) {member})"))
    }

    pub(super) fn compile_composition_wd(
        &self,
        value: &Composition,
        proof: &CompositionObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        validate_composition_function(
            value,
            &proof.outer_domain.signature,
            &proof.inner_domain.signature,
            &proof.function,
        )?;
        ensure_object(&value.outer, &proof.outer_well_defined)?;
        ensure_object(&value.inner, &proof.inner_well_defined)?;
        let outer = self.compile_wd(
            &proof.outer_well_defined,
            &SourcePosition {
                before: 0,
                ..*position
            },
        )?;
        let inner = self.compile_wd(
            &proof.inner_well_defined,
            &SourcePosition {
                before: 1,
                ..*position
            },
        )?;
        let operands = SourcePosition {
            before: 2,
            ..*position
        };
        let hf =
            self.compile_complete_domain_member(&value.outer, &proof.outer_domain, &operands)?;
        let hg =
            self.compile_complete_domain_member(&value.inner, &proof.inner_domain, &operands)?;
        let s = self.compile_fn_signature(&proof.outer_domain.signature, &operands)?;
        let t = self.compile_fn_signature(&proof.inner_domain.signature, &operands)?;
        ensure_object(
            &Obj::FunctionSpace(FunctionSpace::AnonymousFn(proof.function.clone())),
            &proof.function_well_defined,
        )?;
        let checked = self.compile_wd(&proof.function_well_defined, &operands)?;
        let compatibility = self.compile_composition_compatibility(proof, &s, &hf, &operands)?;
        Ok(format!("(let _composition_lambda := {checked};\nLitex.compose {outer} {inner} {s} {t} {hf} {hg} {compatibility})"))
    }

    fn compile_composition_compatibility(
        &self,
        proof: &CompositionObjWellDefinedProof,
        outer_signature: &str,
        outer_member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(wd),
                ),
            ..
        } = (proof.function_well_defined.as_ref()).detailed_ref()
        else {
            return Err(LeanCompileError::unsupported(
                "Composition/ExpandedLambdaWD",
            ));
        };
        let function = &proof.function;
        let scope = SourcePosition::new(
            Some(position),
            SourceOwner::WD(&proof.function_well_defined),
            0,
        );
        let head = self.compile_function_binder_head(
            &function.body,
            &wd.param_type_well_defined,
            &wd.defined_params,
            &wd.assumed_dom_facts,
            &scope,
        )?;
        let body_position = SourcePosition {
            before: self.function_header_stages(&function.body) + 1,
            ..scope
        };
        let body_call = self.compile_wd(&wd.body_well_defined, &body_position)?;
        let law = self.composition_body_domain_law(&wd.body_well_defined, &body_position)?;
        let inputs = self.compile_function_input_sets(&function.body, position)?;
        let raw = function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .map(|p| format!("_raw_i{}", p.id.value()))
            .collect::<Vec<_>>();
        let binders = raw
            .iter()
            .map(|v| format!("({v} : M.Value)"))
            .collect::<Vec<_>>()
            .join(" ");
        let input_values = if Self::function_uses_numeric_interface(&function.body) {
            let mut domains = self.compile_function_domains(&function.body, position)?;
            domains.pop();
            domains
                .into_iter()
                .map(|s| format!("(M.standard {s})"))
                .collect::<Vec<_>>()
        } else {
            inputs
                .iter()
                .map(|s| format!("(Litex.denote {s})"))
                .collect::<Vec<_>>()
        };
        let members = raw
            .iter()
            .zip(&input_values)
            .map(|(v, s)| format!("M.mem {v} {s}"))
            .collect::<Vec<_>>()
            .join(" → ");
        let guard = self.compile_function_guard_template(&function.body, position)?;
        let Obj::FnObj(call) = function.equal_to.as_ref() else {
            return Err(LeanCompileError::unsupported("Composition/ExpandedCall"));
        };
        let inner_call = &call.body[0][0];
        let raw_inner =
            self.compile_function_raw_expression(inner_call, &function.body, position)?;
        let checked_type = format!(
            "∀ {binders}, {members} → ({guard} {}) → M.mem {raw_inner} ({outer_signature}).domain",
            raw.join(" ")
        );
        let checked = format!("(by\n  {}\n  let _composition_call := {body_call}\n  exact Litex.{law} _composition_call {outer_signature} {outer_member})",head.replace('\n',"\n  "));
        let inner_signature = &proof.inner_domain.signature;
        let (parts, values, guards) =
            self.compile_preimage_domain_parts(inner_signature, "_composition_input", position)?;
        // The complete-domain eliminator restores source carriers (including R+).
        let member_proofs = values.iter().enumerate().map(|(i,_)|if values.len()==1 {"_preimage_members".into()} else {
            format!("(by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using Litex.FiniteFunction.coordinate_mem_number _preimage_members ({i} : Fin {}) ({} : ℂ) (by norm_num))",values.len(),i+1)
        }).collect::<Vec<String>>();
        let positive = self.compile_function_positive_inputs(inner_signature, position)?;
        let mut guard_proofs = positive
            .iter()
            .map(|id| format!("_preimage_positive_i{}", id.value()))
            .collect::<Vec<_>>();
        guard_proofs.extend(guards);
        let guard_proof = guard_proofs
            .iter()
            .rev()
            .cloned()
            .reduce(|tail, p| format!("(And.intro {p} {tail})"))
            .unwrap_or_else(|| "True.intro".into());
        let repack = if values.len() == 1 {
            String::new()
        } else {
            format!("\n  have _composition_repack : _composition_input = Litex.FiniteFunction.tupleValue (M := M) ![{}] := {}",values.join(", "),self.compile_preimage_repack(&values,"_preimage_base"))
        };
        let result = format!(
            "_composition_checked {} {} {guard_proof}",
            values.join(" "),
            member_proofs.join(" ")
        );
        let finish = if values.len() == 1 {
            format!("exact {result}")
        } else {
            format!("simpa only [← _composition_repack] using ({result})")
        };
        Ok(format!("(by\n  have _composition_checked : {checked_type} := {checked}\n  intro _composition_input _preimage_domain\n  {}{repack}\n  {finish})",parts.join("\n  ")))
    }

    fn composition_body_domain_law(
        &self,
        wd: &ObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<&'static str, LeanCompileError> {
        match (wd).detailed_ref() {
            DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(p),
                ..
            } => match &p.domain_fn_set {
                Some(
                    FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
                    | FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set },
                ) => Ok(if Self::function_uses_numeric_interface(fn_set) {
                    "callInputInDomain"
                } else {
                    "callOnInputInDomain"
                }),
                Some(FnObjDomainFnSetEvidence::Composition(p)) => {
                    Ok(if Self::function_uses_numeric_interface(&p.function.body) {
                        "callInputInDomain"
                    } else {
                        "callOnInputInDomain"
                    })
                }
                _ => Err(LeanCompileError::unsupported("Composition/BodyCallDomain")),
            },
            DetailedObjWellDefinedProof::ByKnown { obj, wd_id } => {
                if self.resolve_wd(*wd_id, position)?.ir() != obj.ir() {
                    return Err(LeanCompileError::unsupported("Composition/BodyWDId"));
                }
                position
                    .with_visible_wd(obj, &mut |original, producer| {
                        self.composition_body_domain_law(original, producer)
                    })?
                    .ok_or_else(|| LeanCompileError::unsupported("Composition/BodyWDProducer"))
            }
            _ => Err(LeanCompileError::unsupported(
                "Composition/BodyCallConstructor",
            )),
        }
    }
}

pub(super) fn validate_composition_function(
    value: &Composition,
    outer: &FnSet,
    inner: &FnSet,
    function: &AnonymousFn,
) -> Result<(), LeanCompileError> {
    // A different output can select another packed-domain representation.
    // That case needs an explicit domain-transport law before replay supports it.
    if LitexToLeanCompiler::function_uses_numeric_interface(inner)
        != LitexToLeanCompiler::function_uses_numeric_interface(&function.body)
    {
        return Err(LeanCompileError::unsupported(
            "Composition/DomainRepresentationChange",
        ));
    }
    let outer_parameters = outer
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .count();
    let source = inner
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
        .collect::<Vec<_>>();
    let parameters = function
        .body
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|g| g.params.iter().map(move |p| (p, g.param_type.as_ref())))
        .collect::<Vec<_>>();
    if outer_parameters != 1
        || source.is_empty()
        || source.len() != parameters.len()
        || inner.dom_facts.len() != function.body.dom_facts.len()
        || outer.ret_set.ir() != function.body.ret_set.ir()
        || source
            .iter()
            .zip(&parameters)
            .any(|((_, a), (_, b))| a.ir() != b.ir())
    {
        return Err(LeanCompileError::unsupported(
            "Composition/CompleteSignature",
        ));
    }
    let substitutions = source
        .iter()
        .zip(&parameters)
        .map(|((a, _), (b, _))| (a.id, Obj::Identifier(IdentifierObj::from_bound_name(b))))
        .collect::<HashMap<_, _>>();
    if substitutions.len() != source.len()
        || parameters
            .iter()
            .map(|(p, _)| p.id)
            .collect::<std::collections::HashSet<_>>()
            .len()
            != parameters.len()
    {
        return Err(LeanCompileError::unsupported(
            "Composition/ParameterIdentity",
        ));
    }
    for (a, b) in inner.dom_facts.iter().zip(&function.body.dom_facts) {
        if !instantiated_fact_matches(
            &crate::instantiate::quantifier_free_fact_to_fact(a.clone()),
            &crate::instantiate::quantifier_free_fact_to_fact(b.clone()),
            &substitutions,
        ) {
            return Err(LeanCompileError::unsupported("Composition/CompleteGuards"));
        }
    }
    let arguments = parameters
        .iter()
        .map(|(p, _)| Box::new(Obj::Identifier(IdentifierObj::from_bound_name(p))))
        .collect();
    let inner_call = function_application(&value.inner, arguments)
        .map_err(|_| LeanCompileError::unsupported("Composition/InnerCall"))?;
    let body = function_application(&value.outer, vec![Box::new(inner_call)])
        .map_err(|_| LeanCompileError::unsupported("Composition/OuterCall"))?;
    if body.ir() != function.equal_to.ir() {
        return Err(LeanCompileError::unsupported("Composition/ExpandedBody"));
    }
    Ok(())
}
