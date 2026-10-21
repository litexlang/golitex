use crate::compile_to_lean::helper::{finite_vector_proof, instantiated_object_matches};
use crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::finite_call_parts;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_domain::function_domains_alpha_equal;
use crate::execute::execute_fact_stmt::known_tuple::{
    literal_positive_usize, KnownFunctionTupleApplicability, KnownFunctionTupleValueProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::SameFreeParamShapeProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::search_equal_fact_proof_by_known_special_property::{
    EqualFactSearchProofByKnownSpecialProperty, FnTupleProjectionKnownProof, FnTupleValueKnownProof,
    TupleReconstructionKnownProof, TupleProjectionKnownProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_equality_known_special_property(
        &self,
        fact: &EqualFact,
        proof: &EqualFactSearchProofByKnownSpecialProperty,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            EqualFactSearchProofByKnownSpecialProperty::FnTupleValue(proof) => {
                self.compile_known_function_tuple_value(fact, proof, position)
            }
            EqualFactSearchProofByKnownSpecialProperty::FnTupleProjection(proof) => {
                self.compile_known_function_tuple_projection(fact, proof, position)
            }
            EqualFactSearchProofByKnownSpecialProperty::TupleProjection(proof) => {
                self.compile_known_tuple_projection(fact, proof, position)
            }
            EqualFactSearchProofByKnownSpecialProperty::TupleReconstruction(proof) => {
                self.compile_known_tuple_reconstruction(fact, proof, position)
            }
        }
    }

    fn compile_known_tuple_projection(
        &self,
        fact: &EqualFact,
        proof: &TupleProjectionKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (subject, target) = if proof.reversed {
            (&fact.right, &fact.left)
        } else {
            (&fact.left, &fact.right)
        };
        let Obj::FnObj(application) = subject else {
            return Err(LeanCompileError::unsupported("TupleProjection/Application"));
        };
        let (receiver, argument) = finite_call_parts(application)?;
        let n = proof.tuple.value.args.len();
        if proof.index == 0
            || proof.index > n
            || literal_positive_usize(argument) != Some(proof.index)
        {
            return Err(LeanCompileError::unsupported("TupleProjection/Index"));
        }
        let value = Obj::ProductShape(ProductShape::Tuple(proof.tuple.value.clone()));
        let component = &proof.tuple.value.args[proof.index - 1];
        let receiver_equal =
            self.compile_equality_path(&receiver, &value, &proof.tuple.tuple_equal, position)?;
        let component_equal =
            self.compile_known_tuple_match(component, target, &proof.component_equal, position)?;
        let tuple = self.compile_object_reference(&value, position)?;
        let receiver = self.compile_object_reference(&receiver, position)?;
        let target = self.compile_object_reference(target, position)?;
        let index = proof.index;
        let fin_index = index - 1;
        let equality = format!("(by\n  let _tuple := {tuple}\n  have _receiver_eq : Litex.Same {receiver} _tuple := {receiver_equal}\n  have _coordinate_eq := congrArg (fun value => Litex.FunctionSemantics.callValue (M := M) value (M.number ({index} : ℂ))) _receiver_eq\n  have _tuple_coordinate : Litex.FunctionSemantics.callValue (M := M) (Litex.denote _tuple) (M.number ({index} : ℂ)) = _tuple.val.values ({fin_index} : Fin {n}) := by\n    simpa [Litex.FiniteFunction.index] using (Litex.tuple_coordinate _tuple ({fin_index} : Fin {n}))\n  have _target_eq : _tuple.val.values ({fin_index} : Fin {n}) = Litex.denote {target} := {component_equal}\n  exact _coordinate_eq.trans (_tuple_coordinate.trans _target_eq)\n)");
        Ok(if proof.reversed {
            format!("({equality}).symm")
        } else {
            equality
        })
    }

    fn compile_known_tuple_reconstruction(
        &self,
        fact: &EqualFact,
        proof: &TupleReconstructionKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (subject, target) = if proof.reversed {
            (&fact.right, &fact.left)
        } else {
            (&fact.left, &fact.right)
        };
        let Obj::ProductShape(ProductShape::Tuple(tuple)) = target else {
            return Err(LeanCompileError::new(
                "TupleReconstruction/Target",
                "The recorded target is not a tuple.",
            ));
        };
        let n = proof.shape.dimension();
        if tuple.args.len() != n || proof.subjects.len() != n {
            return Err(LeanCompileError::new(
                "TupleReconstruction/Arity",
                "Reconstruction needs every original coordinate and receiver proof.",
            ));
        }
        let (cart, member) = self.compile_cart_shape_member(subject, &proof.shape, position)?;
        let point = self.compile_object_reference(subject, position)?;
        self.compile_object_reference(target, position)?;
        let mut coordinates = Vec::new();
        let mut values = Vec::new();
        for (i, (item, equality)) in tuple.args.iter().zip(&proof.subjects).enumerate() {
            let Obj::FnObj(call) = item.as_ref() else {
                return Err(LeanCompileError::new(
                    "TupleReconstruction/Coordinate",
                    "Each tuple item must be an original coordinate call.",
                ));
            };
            let (receiver, index) = finite_call_parts(call)?;
            if literal_positive_usize(index) != Some(i + 1) {
                return Err(LeanCompileError::new(
                    "TupleReconstruction/Index",
                    "The original coordinate indices must cover 1 through n in order.",
                ));
            }
            let source = self.compile_normalization_value(&receiver, position)?;
            let matched = self.compile_known_tuple_match(&receiver, subject, equality, position)?;
            let value = self.compile_normalization_value(item, position)?;
            let number = i + 1;
            coordinates.push(format!("(show Litex.FunctionSemantics.callValue (M := M) (Litex.denote _litex_point) (Litex.FiniteFunction.index ({i} : Fin {n})) = {value} from by\n  have _receiver_equal : {source} = Litex.denote _litex_point := {matched}\n  have _index : Litex.FiniteFunction.index (M := M) ({i} : Fin {n}) = M.number ({number} : ℂ) := by norm_num [Litex.FiniteFunction.index]\n  simpa only [_index] using (congrArg (fun receiver => Litex.FunctionSemantics.callValue (M := M) receiver (M.number ({number} : ℂ))) _receiver_equal).symm\n)"));
            values.push(value);
        }
        let components = finite_vector_proof(&coordinates);
        let vector = format!("![{}]", values.join(", "));
        let conclude = if proof.reversed {
            "_reconstructed.symm"
        } else {
            "_reconstructed"
        };
        Ok(format!("(by\n  let _litex_point := {point}\n  have _litex_member : Litex.In _litex_point {cart} := {member}\n  have _coordinates : (fun i : Fin {n} => Litex.FunctionSemantics.callValue (M := M) (Litex.denote _litex_point) (Litex.FiniteFunction.index i)) = {vector} := funext {components}\n  have _reconstructed := (Litex.FiniteFunction.reconstruct _litex_member).trans (congrArg (Litex.FiniteFunction.tupleValue (M := M)) _coordinates)\n  exact {conclude}\n)"))
    }

    fn compile_known_function_tuple_projection(
        &self,
        fact: &EqualFact,
        proof: &FnTupleProjectionKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (subject, target) = if proof.reversed {
            (&fact.right, &fact.left)
        } else {
            (&fact.left, &fact.right)
        };
        let Obj::FnObj(coordinate) = subject else {
            return Err(LeanCompileError::new(
                "Equality/FnTupleProjectionApplication",
                "The selected projection endpoint is not a coordinate application.",
            ));
        };
        let (receiver, index) = finite_call_parts(coordinate)?;
        let n = proof.function.value.args.len();
        if proof.index == 0 || proof.index > n || literal_positive_usize(index) != Some(proof.index)
        {
            return Err(LeanCompileError::new(
                "Equality/FnTupleProjectionIndex",
                "The captured coordinate differs from the source index or tuple domain.",
            ));
        }
        let application = proof
            .subject_equal
            .path
            .last()
            .map_or(&receiver, |(_, to, _)| to);
        let subject_equal = if proof.subject_equal.path.is_empty() {
            // The receiver is the original full call's first stage. It need
            // not have a second, independently cached Obj WD constructor.
            format!(
                "(Eq.refl {})",
                self.compile_normalization_value(&receiver, position)?
            )
        } else {
            self.compile_equality_path(&receiver, application, &proof.subject_equal, position)?
        };
        let value = Obj::ProductShape(ProductShape::Tuple(proof.function.value.clone()));
        let checked_application = if proof.subject_equal.path.is_empty() {
            subject
        } else {
            application
        };
        let beta = self.compile_known_tuple_beta(
            application,
            checked_application,
            &proof.function,
            &value,
            position,
        )?;
        let component = &proof.function.value.args[proof.index - 1];
        let component_equal =
            self.compile_known_tuple_match(component, target, &proof.component_equal, position)?;
        let receiver_value = self.compile_normalization_value(&receiver, position)?;
        let tuple_value = self.compile_normalization_value(&value, position)?;
        let component_value = self.compile_normalization_value(component, position)?;
        let subject_value = self.compile_normalization_value(subject, position)?;
        let target_value = self.compile_normalization_value(target, position)?;
        let values = proof
            .function
            .value
            .args
            .iter()
            .map(|value| self.compile_normalization_value(value, position))
            .collect::<Result<Vec<_>, _>>()?;
        let index = proof.index;
        let fin_index = index - 1;
        let vector = format!("![{}]", values.join(", "));
        let equality = format!("(show {subject_value} = {target_value} from by\n  have _litex_receiver_eq : {receiver_value} = {tuple_value} := ({subject_equal}).trans {beta}\n  have _litex_coordinate_eq := congrArg (fun _receiver => Litex.FunctionSemantics.callValue (M := M) _receiver (M.number ({index} : ℂ))) _litex_receiver_eq\n  have _litex_component_eq : Litex.FunctionSemantics.callValue (M := M) {tuple_value} (M.number ({index} : ℂ)) = {component_value} := by\n    simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.call_tuple {vector} ({fin_index} : Fin {n}))\n  have _litex_target_eq : {component_value} = {target_value} := {component_equal}\n  exact _litex_coordinate_eq.trans (_litex_component_eq.trans _litex_target_eq)\n)");
        Ok(if proof.reversed {
            format!("({equality}).symm")
        } else {
            equality
        })
    }

    fn compile_known_function_tuple_value(
        &self,
        fact: &EqualFact,
        proof: &FnTupleValueKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (subject, target) = if proof.reversed {
            (&fact.right, &fact.left)
        } else {
            (&fact.left, &fact.right)
        };
        let application = proof
            .subject_equal
            .path
            .last()
            .map_or(subject, |(_, to, _)| to);
        let subject_equal =
            self.compile_equality_path(subject, application, &proof.subject_equal, position)?;
        let value = Obj::ProductShape(ProductShape::Tuple(proof.function.value.clone()));
        let beta = self.compile_known_tuple_beta(
            application,
            application,
            &proof.function,
            &value,
            position,
        )?;
        let value_equal =
            self.compile_known_tuple_match(&value, target, &proof.value_equal, position)?;
        let equality = format!("(({subject_equal}).trans (({beta}).trans {value_equal}))");
        Ok(if proof.reversed {
            format!("({equality}).symm")
        } else {
            equality
        })
    }

    fn compile_known_tuple_beta(
        &self,
        application: &Obj,
        checked_application: &Obj,
        proof: &KnownFunctionTupleValueProof,
        value: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FnObj(call) = application else {
            return Err(LeanCompileError::new(
                "Equality/FnTupleApplication",
                "The recorded subject path does not end at a function application.",
            ));
        };
        let continued = checked_application.ir() != application.ir();
        if continued {
            let Obj::FnObj(full_call) = checked_application else {
                return Err(LeanCompileError::new(
                    "Equality/FnTupleContinuation",
                    "The original continued WD subject is not a function application.",
                ));
            };
            let (prefix, _) = finite_call_parts(full_call)?;
            if prefix.ir() != application.ir() {
                return Err(LeanCompileError::new(
                    "Equality/FnTupleContinuation",
                    "The original call's first stage differs from the captured tuple application.",
                ));
            }
        }
        let head = match call.head.as_ref() {
            FnObjHead::Identifier(identifier) => Obj::Identifier(identifier.clone()),
            FnObjHead::AnonymousFnLiteral(function) => {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone()))
            }
            _ => return Err(LeanCompileError::unsupported("Equality/FnTupleHead")),
        };
        let literal = proof
            .function_equal
            .path
            .last()
            .map_or(&head, |(_, to, _)| to);
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) = literal else {
            return Err(LeanCompileError::unsupported("Equality/FnTupleBody"));
        };
        let head_equal =
            self.compile_equality_path(&head, literal, &proof.function_equal, position)?;
        let parameters = function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        if call.body.len() != 1
            || !(1..=3).contains(&parameters.len())
            || call.body[0].len() != parameters.len()
        {
            return Err(LeanCompileError::new(
                "Equality/FnTupleArguments",
                "The recorded tuple body needs one complete ordered argument group.",
            ));
        }
        let mut substitution = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(&call.body[0]) {
            if substitution
                .insert(parameter.id, argument.as_ref().clone())
                .is_some()
            {
                return Err(LeanCompileError::new(
                    "Equality/FnTupleParameterIdentity",
                    "The selected tuple body repeats a binder identity.",
                ));
            }
        }
        if !instantiated_object_matches(&function.equal_to, value, &substitution) {
            return Err(LeanCompileError::new(
                "Equality/FnTupleSubstitution",
                "The captured tuple is not the selected body's exact binder-ID substitution.",
            ));
        }

        // Read the constructor that actually established this call's WD. Its
        // producer position controls its own citations; the known-property
        // evidence below is consumed at the later equality-search position.
        position
            .with_visible_wd(checked_application, &mut |wd, producer| {
                let ObjWellDefinedProof::ByDef {
                    obj: Obj::FnObj(original_call),
                    proof: ObjWellDefinedProofByDef::FnObj(call_wd),
                } = wd
                else {
                    return Err(LeanCompileError::new(
                        "Equality/FnTupleWD",
                        "The selected WD producer is not a function application.",
                    ));
                };
                if Obj::FnObj(original_call.clone()).ir() != checked_application.ir() {
                    return Err(LeanCompileError::new(
                        "Equality/FnTupleWD",
                        "The original WD constructor certifies another application.",
                    ));
                }
                let selected = call_wd.domain_fn_set.as_ref().ok_or_else(|| {
                    LeanCompileError::new(
                        "Equality/FnTupleSignature",
                        "The original call has no selected signature evidence.",
                    )
                })?;
                let selected_signature = match selected {
                    FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }
                    | FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set } => fn_set,
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "Equality/FnTupleSelectedSignature",
                        ))
                    }
                };
                if !function_domains_alpha_equal(selected_signature, &function.body)
                    || Self::function_uses_numeric_interface(selected_signature)
                    || Self::function_uses_numeric_interface(&function.body)
                {
                    return Err(LeanCompileError::unsupported("Equality/FnTupleDomain"));
                }
                let signatures = self.compile_known_tuple_applicability(
                    &head,
                    function,
                    selected,
                    &proof.applicability,
                    position,
                )?;
                let actual = if continued {
                    let constructor = SourcePosition {
                        parent: Some(producer),
                        owner: SourceOwner::WD(wd),
                        before: 0,
                    };
                    self.compile_fn_first_call_with_member(original_call, call_wd, &constructor)?
                        .0
                } else {
                    self.compile_wd(wd, producer)?
                };
                let formula = self.compile_object_reference(literal, position)?;
                let application_value = self.compile_normalization_value(application, position)?;
                let value = self.compile_normalization_value(value, position)?;
                let packed_body =
                    self.compile_function_packed_body_template(function, position)?;
                let body = self.compile_function_body_template(function, position)?;
                let arguments = call.body[0]
                    .iter()
                    .map(|argument| self.compile_normalization_value(argument, position))
                    .collect::<Result<Vec<_>, _>>()?;
                let body_equal =
                    self.compile_function_packed_application_equality(&body, &arguments)?;
                Ok(format!("(show {application_value} = {value} from by\n  let _litex_original := {actual}\n  let _litex_formula := {formula}\n{signatures}  have _litex_head_eq : Litex.Same _litex_original.val.function _litex_formula := {head_equal}\n  have _litex_call_eq := congrArg (fun _f => Litex.FunctionSemantics.callValue (M := M) _f (Litex.denote _litex_original.val.argument)) _litex_head_eq\n  have _litex_beta := Litex.FunctionSemantics.call_graphValue _ _ _ _litex_formula.wd (Litex.denote _litex_original.val.argument) _litex_original.wd.2\n  have _litex_body_eq : _litex_formula.val.bodyValue (Litex.denote _litex_original.val.argument) = {value} := by\n    change {packed_body} (Litex.denote _litex_original.val.argument) = {value}\n    exact {body_equal}\n  exact _litex_call_eq.trans (_litex_beta.trans _litex_body_eq)\n)"))
            })?
            .ok_or_else(|| {
                LeanCompileError::new(
                    "Equality/FnTupleWDProducer",
                    "The recorded application has no preceding original WD constructor.",
                )
            })
    }

    fn compile_known_tuple_applicability(
        &self,
        head: &Obj,
        function: &AnonymousFn,
        selected: &FnObjDomainFnSetEvidence,
        proof: &KnownFunctionTupleApplicability,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (proof, selected) {
            (
                KnownFunctionTupleApplicability::AnonymousLiteral,
                FnObjDomainFnSetEvidence::AnonymousLiteral { fn_set },
            ) if *head == Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.clone()))
                && *fn_set == function.body =>
            {
                Ok(String::new())
            }
            (
                KnownFunctionTupleApplicability::AllSignaturesMatch {
                    signatures,
                    template_signatures,
                },
                FnObjDomainFnSetEvidence::InFunctionSet {
                    fn_set, fact_id, ..
                },
            ) => {
                if !template_signatures.is_empty() {
                    return Err(LeanCompileError::unsupported(
                        "Equality/FnTupleTemplateSignature",
                    ));
                }
                let mut ids = Vec::new();
                let mut selected_found = false;
                let mut compiled = String::new();
                for entry in signatures {
                    let id = entry.cite_signature_fact_id;
                    if ids.contains(&id) {
                        return Err(LeanCompileError::new(
                            "Equality/FnTupleDuplicateSignature",
                            "The applicability evidence repeats a source signature citation.",
                        ));
                    }
                    ids.push(id);
                    let (source, _) = self.cited_fact_reference(id, position)?;
                    if source.fact_id() != id || *source != self.resolve_fact(id, position)? {
                        return Err(LeanCompileError::new(
                            "Equality/FnTupleSignatureCitation",
                            "The signature citation differs from its original producer.",
                        ));
                    }
                    let (subject, signature) = match source {
                        Fact::AtomicFact(AtomicFact::InFact(member)) => {
                            let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set
                            else {
                                return Err(LeanCompileError::unsupported(
                                    "Equality/FnTupleSignatureCarrier",
                                ));
                            };
                            (&member.element, signature)
                        }
                        Fact::AtomicFact(AtomicFact::EqualFact(equal)) => {
                            match (&equal.left, &equal.right) {
                                (Obj::FunctionSpace(FunctionSpace::AnonymousFn(body)), subject)
                                | (subject, Obj::FunctionSpace(FunctionSpace::AnonymousFn(body))) => {
                                    (subject, &body.body)
                                }
                                _ => {
                                    return Err(LeanCompileError::unsupported(
                                        "Equality/FnTupleSignatureEquality",
                                    ))
                                }
                            }
                        }
                        _ => {
                            return Err(LeanCompileError::unsupported(
                                "Equality/FnTupleSignatureCitation",
                            ))
                        }
                    };
                    if subject.ir() != head.ir() {
                        return Err(LeanCompileError::new(
                            "Equality/FnTupleSignatureSubject",
                            "The signature row belongs to another function head.",
                        ));
                    }
                    if id == *fact_id {
                        if signature != fn_set {
                            return Err(LeanCompileError::new(
                                "Equality/FnTupleSelectedSignature",
                                "The recorded signature differs from the WD-selected source.",
                            ));
                        }
                        selected_found = true;
                    }
                    let source = Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone()));
                    let target = Obj::FunctionSpace(FunctionSpace::FnSet(function.body.clone()));
                    let equality = self.compile_known_tuple_match(
                        &source,
                        &target,
                        &entry.signature_match,
                        position,
                    )?;
                    let source = self.compile_fn_signature(signature, position)?;
                    let target = self.compile_fn_signature(&function.body, position)?;
                    compiled.push_str(&format!("  have _litex_signature_{} : Litex.Same (Litex.fnSet {source}) (Litex.fnSet {target}) := {equality}\n", id.value()));
                }
                if !selected_found {
                    return Err(LeanCompileError::new(
                        "Equality/FnTupleSelectedSignature",
                        "The captured applicability does not cover the original WD-selected signature.",
                    ));
                }
                Ok(compiled)
            }
            (KnownFunctionTupleApplicability::TemplateDefinition { .. }, _) => Err(
                LeanCompileError::unsupported("Equality/FnTupleTemplateDefinition"),
            ),
            _ => Err(LeanCompileError::new(
                "Equality/FnTupleApplicability",
                "The applicability branch differs from the original call constructor.",
            )),
        }
    }

    // These payloads record only identity/alpha comparison or an ordered known
    // equality path. Consume that exact leaf without constructing a new result.
    fn compile_known_tuple_match(
        &self,
        source: &Obj,
        target: &Obj,
        proof: &EqualFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_)) => {
                if source.ir() != target.ir() {
                    return Err(LeanCompileError::new(
                        "Equality/FnTupleIdentitySubject",
                        "The captured identity compares different endpoints.",
                    ));
                }
                Ok("rfl".into())
            }
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameFreeParamShape(
                SameFreeParamShapeProof::FnSet(_),
            )) => {
                let (
                    Obj::FunctionSpace(FunctionSpace::FnSet(source)),
                    Obj::FunctionSpace(FunctionSpace::FnSet(target)),
                ) = (source, target)
                else {
                    return Err(LeanCompileError::new(
                        "Equality/FnTupleSignatureAlpha",
                        "Function-signature alpha evidence has other endpoint families.",
                    ));
                };
                if !crate::execute::execute_fact_stmt::fn_sets_alpha_equal(source, target) {
                    return Err(LeanCompileError::new(
                        "Equality/FnTupleSignatureAlpha",
                        "The recorded signature endpoints are not alpha equivalent.",
                    ));
                }
                Ok("rfl".into())
            }
            EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) => self.compile_equality_path(source, target, path, position),
            _ => Err(LeanCompileError::unsupported(
                "Equality/FnTupleEndpointMatch",
            )),
        }
    }
}
