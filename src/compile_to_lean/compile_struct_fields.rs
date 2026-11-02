use super::compile_def_struct_stmt_result::validate_struct;
use super::compile_struct_conditions::{coordinate_bindings, field_substitution};
use super::compile_struct_header::header_substitution;
use super::helper::{
    conjunction_projection, ensure_object, instantiated_fact_matches, instantiated_object_matches,
};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FieldAccessObjWellDefinedProof;
use crate::execute::ReleaseOneStructLayerProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_struct_function_membership(
        &self,
        access: &FieldAccess,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if access.fields.len() != 1 || !has_direct_record_receiver(access) {
            return self.with_struct_field_evidence(access, position, |proof, scope| {
                let (_, member) = self.compile_struct_projection(access, proof, scope)?;
                let step = proof
                    .projection_steps
                    .last()
                    .ok_or_else(|| LeanCompileError::unsupported("StructField/ProjectionStages"))?;
                let (declaration, _, _) = scope.visible_struct(&step.carrier.name)?;
                let mut substitution = header_substitution(&declaration.statement, &step.carrier)?;
                let receiver = super::compile_struct_projection::field_receiver(
                    access,
                    access.fields.len() - 1,
                );
                substitution.extend(field_substitution(&declaration.statement, &receiver));
                if !instantiated_object_matches(
                    &declaration.statement.fields[step.field_index].field_type,
                    &Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
                    &substitution,
                ) {
                    return Err(LeanCompileError::unsupported(
                        "StructField/FunctionSignature",
                    ));
                }
                Ok(member)
            });
        }
        let [field] = access.fields.as_slice() else {
            return Err(LeanCompileError::unsupported("StructField/NestedPath"));
        };
        let (carrier, member) = self.compile_struct_receiver(&access.obj, position)?;
        let (declaration, _, _) = position.visible_struct(&carrier.name)?;
        let fields = &declaration.statement.fields;
        let index = fields
            .iter()
            .position(|f| &f.binding.name == field)
            .ok_or_else(|| LeanCompileError::unsupported("StructField/Name"))?;
        let mut substitution = header_substitution(&declaration.statement, &carrier)?;
        substitution.extend(field_substitution(&declaration.statement, &access.obj));
        if !instantiated_object_matches(
            &fields[index].field_type,
            &Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
            &substitution,
        ) {
            return Err(LeanCompileError::unsupported(
                "StructField/FunctionSignature",
            ));
        }
        let receiver = self.compile_object_reference(&access.obj, position)?;
        let member = self.compile_struct_cart_membership(&carrier, &receiver, &member, position)?;
        let n = fields.len();
        Ok(format!("(Litex.FiniteFunction.coordinate_mem_number (M := M) {member} ({index} : Fin {n}) ({} : ℂ) (by norm_num))", index + 1))
    }

    pub(super) fn compile_struct_receiver(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<(StructObj, String), LeanCompileError> {
        if let Obj::FnObj(application) = object {
            return position
                .with_visible_wd(object, &mut |wd, producer| {
                    ensure_object(object, wd)?;
                    let DetailedObjWellDefinedProof::ByDef {
                        proof: ObjWellDefinedProofByDef::FnObj(evidence),
                        ..
                    } = wd.detailed_ref()
                    else {
                        return Err(LeanCompileError::unsupported("StructField/ReceiverCallWD"));
                    };
                    let scope = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                    let (_, output, member) =
                        self.compile_fn_call(application, evidence, &scope)?;
                    let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier)) =
                        output
                    else {
                        return Err(LeanCompileError::unsupported("StructField/ReceiverReturn"));
                    };
                    Ok((carrier, member))
                })?
                .ok_or_else(|| LeanCompileError::unsupported("StructField/ReceiverCallWD"));
        }
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object else {
            return Err(LeanCompileError::unsupported("StructField/Receiver"));
        };
        let (carrier, member) = match position.visible_parameter(*id, &self.runtime) {
            Ok((_, Some(Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier))), _, member)) => (carrier.clone(), member),
            Ok(_) => return Err(LeanCompileError::unsupported("StructField/DeclaredCarrier")),
            Err(error) => position.with_visible_alias(object, &self.runtime, &mut |parameter, _, _, producer| {
                let SourceOwner::Statement(ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                    ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p))))) = producer.owner else {
                    return Err(LeanCompileError::unsupported("StructField/TypedAlias"));
                };
                let (index, (_, carrier)) = p.statement.param_def.groups.iter()
                    .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
                    .enumerate().find(|(_, (p, _))| p.id==parameter.id)
                    .ok_or_else(|| LeanCompileError::unsupported("StructField/AliasParameter"))?;
                let ParamType::Obj(Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier))) = carrier else {
                    return Err(LeanCompileError::unsupported("StructField/DeclaredCarrier"));
                };
                let store = &p.store_and_infer_result.store_and_infer_results[index];
                let (fact, member) = position.visible_fact(store.primary_fact_id(), &self.runtime)?;
                if !matches!(fact, Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==object.ir()
                    && matches!(&m.set, Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(s)) if s==carrier)) {
                    return Err(LeanCompileError::unsupported("StructField/AliasMembership"));
                }
                Ok((carrier.clone(), member))
            })?.ok_or(error)?,
        };
        Ok((carrier, member))
    }

    pub(super) fn compile_struct_field_reference(
        &self,
        access: &FieldAccess,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if access.fields.len() != 1 || !has_direct_record_receiver(access) {
            return self.with_struct_field_evidence(access, position, |proof, scope| {
                self.compile_struct_projection(access, proof, scope)
                    .map(|(value, _)| value)
            });
        }
        let [field] = access.fields.as_slice() else {
            return Err(LeanCompileError::unsupported("StructField/NestedPath"));
        };
        let (carrier, member) = self.compile_struct_receiver(&access.obj, position)?;
        let (declaration, _, _) = position.visible_struct(&carrier.name)?;
        validate_struct(declaration)?;
        let Some(index) = declaration
            .statement
            .fields
            .iter()
            .position(|f| &f.binding.name == field)
        else {
            return Err(LeanCompileError::unsupported("StructField/Name"));
        };
        let n = declaration.statement.fields.len();
        let receiver = self.compile_object_reference(&access.obj, position)?;
        let structure =
            self.compile_struct_cart_reference(&carrier, &receiver, &member, position)?;
        let member = self.compile_struct_cart_membership(&carrier, &receiver, &member, position)?;
        Ok(format!("(Litex.cartCall {receiver} {structure} (Litex.number (M := M) ({} : ℂ)) {member} (by change M.mem (M.number ({} : ℂ)) (Litex.FiniteFunction.indexSet {n}); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) ({index} : Fin {n}))))", index + 1, index + 1))
    }

    pub(super) fn compile_struct_field_wd(
        &self,
        access: &FieldAccess,
        proof: &FieldAccessObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Some(child) = proof.child_obj_well_defined.first() else {
            return Err(LeanCompileError::unsupported("StructField/ChildWD"));
        };
        ensure_object(&access.obj, child)?;
        self.compile_wd(child, position)?;
        let mut declared_input = None;
        if let Obj::FnObj(application) = access.obj.as_ref() {
            declared_input = Some(match application.head.as_ref() {
                FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) => {
                    if let Ok((_, carrier, _, _)) = position.visible_parameter(*id, &self.runtime) {
                        let Some(Obj::FunctionSpace(FunctionSpace::FnSet(signature))) = carrier
                        else {
                            return Err(LeanCompileError::unsupported(
                                "StructField/DeclaredParameterSignature",
                            ));
                        };
                        let signature_term = self.compile_fn_signature(signature, position)?;
                        self.compile_struct_declared_input(
                            application,
                            proof,
                            signature,
                            &signature_term,
                            position,
                        )?
                    } else {
                        let (declaration, _, _) = position.visible_function(id)?;
                        let head = self.compile_object_reference(
                            &Obj::Identifier(IdentifierObj::from_bound_name(
                                &declaration.statement.name,
                            )),
                            position,
                        )?;
                        self.compile_struct_declared_input(
                            application,
                            proof,
                            &declaration.statement.equal_to_anonymous_fn.body,
                            &format!("({head}).val.signature"),
                            position,
                        )?
                    }
                }
                FnObjHead::InstantiatedTemplateObj(instance) => {
                    self.compile_template_record_call_input(application, instance, proof, position)?
                }
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "StructField/DeclaredCallHead",
                    ))
                }
            });
        } else if proof.child_obj_well_defined.len() != 1
            || proof.argument_scope.is_some()
            || !proof.requirement_fact_verified.is_empty()
        {
            return Err(LeanCompileError::unsupported("StructField/CallStages"));
        }
        let formed = SourcePosition {
            before: proof.child_obj_well_defined.len() + proof.requirement_fact_verified.len(),
            ..*position
        };
        let (value, _) = self.compile_struct_projection(access, proof, &formed)?;
        Ok(match declared_input {
            Some(check) => format!("({check}{value})"),
            None => value,
        })
    }

    pub(super) fn compile_struct_declared_input(
        &self,
        application: &FnObj,
        proof: &FieldAccessObjWellDefinedProof,
        signature: &FnSet,
        signature_term: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let first = proof
            .projection_steps
            .first()
            .ok_or_else(|| LeanCompileError::unsupported("StructField/ProjectionStages"))?;
        if signature.ret_set.as_ref()
            != &Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(
                first.carrier.clone(),
            ))
            || proof.argument_scope.is_none()
        {
            return Err(LeanCompileError::unsupported(
                "StructField/DeclaredCallSignature",
            ));
        }
        let (input, domain) = self.compile_captured_call_domain(
            application,
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
            1,
            signature,
            position,
        )?;
        Ok(format!(
            "let _field_declared_input : M.mem {input} ({signature_term}).domain := {domain};\n"
        ))
    }

    pub(super) fn compile_auto_struct_layers(
        &self,
        groups: &[TypedParameterGroup],
        stores: &[std::rc::Rc<StoreFactAndInferResult>],
        layers: Option<&[ReleaseOneStructLayerProof]>,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let layers = layers.unwrap_or(&[]);
        let expected = groups
            .iter()
            .flat_map(|g| g.params.iter().map(move |p| (p, &g.param_type)))
            .enumerate()
            .filter_map(|(index, (p, carrier))| match carrier {
                ParamType::Obj(Obj::StructAndFieldAccessObj(
                    StructAndFieldAccessObj::StructObj(s),
                )) => Some((index, p, s)),
                _ => None,
            })
            .collect::<Vec<_>>();
        if expected.len() != layers.len() {
            return Err(LeanCompileError::unsupported(
                "StructRelease/ParameterLayers",
            ));
        }
        let mut output = Vec::new();
        for (index, ((parameter_index, parameter, carrier), layer)) in
            expected.iter().zip(layers).enumerate()
        {
            let obj = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
            if layer.obj.ir() != obj.ir() || &layer.struct_obj != *carrier {
                return Err(LeanCompileError::unsupported(
                    "StructRelease/ParameterSubject",
                ));
            }
            let store = stores
                .get(*parameter_index)
                .ok_or_else(|| LeanCompileError::unsupported("StructRelease/ParameterStore"))?;
            let (fact, member) = position.visible_fact(store.primary_fact_id(), &self.runtime)?;
            if !matches!(fact, Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==obj.ir()
                && matches!(&m.set, Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(s)) if s==*carrier))
            {
                return Err(LeanCompileError::unsupported(
                    "StructRelease/ParameterMembership",
                ));
            }
            let prefix =
                SourcePosition::new(Some(position), SourceOwner::StructLayers(layers), index + 1);
            output.extend(self.compile_struct_layer(layer, &member, &prefix)?);
        }
        Ok(output)
    }

    pub(super) fn compile_struct_layer(
        &self,
        layer: &ReleaseOneStructLayerProof,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (declaration, _, _) = position.visible_struct(&layer.struct_obj.name)?;
        validate_struct(declaration)?;
        let mut header = header_substitution(&declaration.statement, &layer.struct_obj)?;
        header.extend(field_substitution(&declaration.statement, &layer.obj));
        let fields = &declaration.statement.fields;
        let n = fields.len();
        if layer.store_and_infer.len() != 1 + n * 2 + declaration.statement.equivalent_facts.len() {
            return Err(LeanCompileError::unsupported("StructRelease/Stages"));
        }
        let receiver = self.compile_object_reference(&layer.obj, position)?;
        let cart_member =
            self.compile_struct_cart_membership(&layer.struct_obj, &receiver, member, position)?;
        self.compile_struct_reference(&layer.struct_obj, position)?;
        let mut output = Vec::new();
        for (index, stored) in layer.store_and_infer.iter().enumerate() {
            let prior = SourcePosition::new(Some(position), SourceOwner::StructLayer(layer), index);
            let fact = self.resolve_fact(stored.primary_fact_id(), &prior)?;
            self.validate_store(&stored.store, &fact)?;
            let field_obj = |i: usize| {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(FieldAccess {
                    obj: Box::new(layer.obj.clone()),
                    fields: vec![fields[i].binding.name.clone()],
                }))
            };
            let proof = if index == 0 {
                let Fact::AtomicFact(AtomicFact::InFact(membership)) = &fact else {
                    return Err(LeanCompileError::unsupported("StructRelease/CartesianFact"));
                };
                let Obj::ProductShape(ProductShape::Cart(cart)) = &membership.set else {
                    return Err(LeanCompileError::unsupported("StructRelease/CartesianFact"));
                };
                if membership.element.ir() != layer.obj.ir()
                    || cart.args.len() != n
                    || cart
                        .args
                        .iter()
                        .zip(fields)
                        .any(|(a, b)| !instantiated_object_matches(&b.field_type, a, &header))
                {
                    return Err(LeanCompileError::unsupported(
                        "StructRelease/CartesianSubject",
                    ));
                }
                cart_member.clone()
            } else if index <= n {
                let i = index - 1;
                let coordinate =
                    crate::execute::execute_fact_stmt::finite_function::finite_function_coordinate(
                        &layer.obj, i,
                    )
                    .map_err(|e| LeanCompileError::new("StructRelease/Coordinate", &e))?;
                if !matches!(&fact, Fact::AtomicFact(AtomicFact::EqualFact(e)) if e.left.ir()==field_obj(i).ir() && e.right.ir()==coordinate.ir())
                {
                    return Err(LeanCompileError::unsupported("StructRelease/BridgeSubject"));
                }
                "(by rfl)".into()
            } else if index <= n * 2 {
                let i = index - n - 1;
                if !matches!(&fact, Fact::AtomicFact(AtomicFact::InFact(m)) if m.element.ir()==field_obj(i).ir() && instantiated_object_matches(&fields[i].field_type, &m.set, &header))
                {
                    return Err(LeanCompileError::unsupported("StructRelease/FieldSubject"));
                }
                format!("(Litex.FiniteFunction.coordinate_mem_number (M := M) {cart_member} ({i} : Fin {n}) ({} : ℂ) (by norm_num))", i + 1)
            } else {
                let law_index = index - 1 - n * 2;
                let source = &declaration.statement.equivalent_facts[law_index];
                let mut substitution = header.clone();
                substitution.extend(field_substitution(&declaration.statement, &layer.obj));
                if !instantiated_fact_matches(source, &fact, &substitution) {
                    return Err(LeanCompileError::unsupported(
                        "StructRelease/ConditionSubject",
                    ));
                }
                let bridge =
                    self.compile_struct_members_reference(&layer.struct_obj, &receiver, position)?;
                conjunction_projection(
                    &format!("({bridge}.mp {member}).2"),
                    law_index,
                    declaration.statement.equivalent_facts.len(),
                )
            };
            // These subjects were constructed by this exact release stage.
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::InferredStore(&stored.store),
                usize::MAX,
            );
            let proposition = if index > 2 * n {
                let mut bindings = self.struct_header_raw_bindings(
                    &declaration.statement,
                    &layer.struct_obj,
                    &formed,
                )?;
                bindings.extend(coordinate_bindings(
                    &declaration.statement,
                    &format!("(Litex.denote {receiver})"),
                ));
                self.compile_function_raw_predicate(
                    &declaration.statement.equivalent_facts[index - 1 - 2 * n],
                    &formed,
                    &bindings,
                )?
            } else {
                self.fact_proposition(&fact, &formed)?
            };
            output.push(self.emit_internal_fact(&fact, &(proposition.clone(), proof), &formed)?);
            let completed = SourcePosition {
                before: index + 1,
                ..prior
            };
            output.extend(self.compile_stored_inferences(
                stored,
                &fact,
                &(
                    proposition,
                    if completed.is_local() {
                        format!("h_{}", fact.fact_id().value())
                    } else {
                        completed.context_application(&format!("h_{}", fact.fact_id().value()))
                    },
                ),
                &completed,
            )?);
        }
        Ok(output)
    }
}

// Named functions and parameters expose their declaration-owned return carrier.
// Template instances use their captured instantiation/projection path instead.
pub(super) fn has_direct_record_receiver(access: &FieldAccess) -> bool {
    match access.obj.as_ref() {
        Obj::Identifier(_) => true,
        Obj::FnObj(call) => matches!(call.head.as_ref(), FnObjHead::Identifier(_)),
        _ => false,
    }
}
