use super::compile_def_struct_stmt_result::{has_dependent_fields, validate_struct};
use super::compile_struct_conditions::field_substitution;
use super::compile_struct_header::header_substitution;
use super::helper::{ensure_object, instantiated_object_matches};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FieldAccessObjWellDefinedProof, StructishObjWellDefinedProofByDef,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_struct_declared_member(
        &self,
        goal: &InFact,
        evidence: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::FieldInDeclaredSetProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access)) =
            &goal.element
        else {
            return Err(LeanCompileError::unsupported(
                "StructField/DeclaredMemberSubject",
            ));
        };
        self.with_struct_field_evidence(access, position, |proof, scope| {
            let (value, member) = self.compile_struct_projection(access, proof, scope)?;
            let step = proof
                .projection_steps
                .last()
                .ok_or_else(|| LeanCompileError::unsupported("StructField/ProjectionStages"))?;
            let (declaration, _, _) = scope.visible_struct(&step.carrier.name)?;
            let mut substitution = header_substitution(&declaration.statement, &step.carrier)?;
            substitution.extend(field_substitution(
                &declaration.statement,
                &field_receiver(access, access.fields.len() - 1),
            ));
            if !instantiated_object_matches(
                &declaration.statement.fields[step.field_index].field_type,
                &evidence.declared_set,
                &substitution,
            ) {
                return Err(LeanCompileError::unsupported(
                    "StructField/DeclaredMemberCarrier",
                ));
            }
            let equality = EqualFact {
                fact_id: goal.fact_id,
                left: evidence.declared_set.clone(),
                right: goal.set.clone(),
                line_file: goal.line_file.clone(),
            };
            let same = self.compile_equality_search(&equality, &evidence.set_match, scope)?;
            Ok(format!(
                "((congrArg (fun A => M.mem (Litex.denote {value}) A) {same}).mp {member})"
            ))
        })
    }

    /// Project each field in the original WD order. Intermediate objects and
    /// memberships are local Lean bindings, not new source producers.
    pub(super) fn compile_struct_projection(
        &self,
        access: &FieldAccess,
        proof: &FieldAccessObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let member = self.validate_struct_projection(access, proof, position)?;
        let receiver = self.compile_object_reference(&access.obj, position)?;
        let mut lines = vec![
            format!("let _field_value_0 := {receiver}"),
            format!("let _field_member_0 := {member}"),
        ];
        let carrier = &proof.projection_steps[0].carrier;
        let instance = match access.obj.as_ref() {
            Obj::InstantiatedTemplateObj(instance) => Some(instance),
            Obj::FnObj(call) => match call.head.as_ref() {
                FnObjHead::InstantiatedTemplateObj(instance) => Some(instance),
                _ => None,
            },
            _ => None,
        };
        let mut arguments = if let Some(instance) = instance.filter(|_| !carrier.params.is_empty())
        {
            self.compile_template_record_arguments(instance, carrier, position)?
        } else {
            self.compile_struct_reference_arguments(carrier, position)?
        };
        bind_projection_arguments(&mut lines, &mut arguments, 0);
        for (depth, step) in proof.projection_steps.iter().enumerate() {
            let (declaration, producer, declaration_index) =
                position.visible_struct(&step.carrier.name)?;
            let n = declaration.statement.fields.len();
            let index = step.field_index;
            let coordinate = index + 1;
            let receiver = format!("_field_value_{depth}");
            let member = format!("_field_member_{depth}");
            let structure =
                self.context_application(&format!("struct_{}", declaration_index + 1), &producer);
            let structure = apply_arguments(&structure, &arguments);
            lines.push(format!("let _field_carrier_{depth} := {structure}"));
            let mut base = format!("_field_carrier_{depth}");
            let mut base_member = member;
            if !declaration.statement.equivalent_facts.is_empty() {
                base_member = format!("(Litex.setBuilderSubset {base}.val.bound {base}.val.predicate (Litex.denote {receiver}) {base_member})");
                base = format!("{base}.val.bound");
            }
            let (cart, cart_member) = if has_dependent_fields(&declaration.statement) {
                let indices = self.compile_struct_coordinate_indices(&step.carrier, position)?;
                (
                    format!("(Litex.dependentCartAt {receiver} {base} {indices} {base_member})"),
                    format!("(Litex.inDependentCartAt {receiver} {base} {indices} {base_member})"),
                )
            } else {
                (base, base_member)
            };
            let next = depth + 1;
            lines.push(format!("let _field_cart_{depth} := {cart}"));
            lines.push(format!("let _field_cart_member_{depth} := {cart_member}"));
            lines.push(format!("let _field_value_{next} := Litex.cartCall {receiver} _field_cart_{depth} (Litex.number (M := M) ({coordinate} : ℂ)) _field_cart_member_{depth} (by change M.mem (M.number ({coordinate} : ℂ)) (Litex.FiniteFunction.indexSet {n}); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) ({index} : Fin {n})))"));
            lines.push(format!("let _field_member_{next} := Litex.FiniteFunction.coordinate_mem_number (M := M) _field_cart_member_{depth} ({index} : Fin {n}) ({coordinate} : ℂ) (by norm_num)"));
            if next < proof.projection_steps.len() {
                arguments = self.compile_projected_struct_arguments(
                    declaration,
                    &producer,
                    index,
                    &arguments,
                    depth,
                )?;
                bind_projection_arguments(&mut lines, &mut arguments, next);
            }
        }
        let n = proof.projection_steps.len();
        let prefix = lines.join(";\n");
        Ok((
            format!("({prefix};\n_field_value_{n})"),
            // Check the projection proof after elaborating its dependent
            // carrier arguments, rather than inferring them from the goal set.
            format!("({prefix};\n(by exact _field_member_{n}))"),
        ))
    }

    /// Instantiate the constructor already checked at the original field stage.
    /// Only its original header/earlier-field parameters are abstracted. The
    /// resulting terms are bound once by the projection, including WD proofs.
    fn compile_projected_struct_arguments(
        &self,
        declaration: &crate::execute::ExecDefStructStmtSuccessResult,
        producer: &SourcePosition<'_>,
        index: usize,
        arguments: &[String],
        depth: usize,
    ) -> Result<Vec<String>, LeanCompileError> {
        let field = &declaration.statement.fields[index];
        let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier)) =
            &field.field_type
        else {
            return Err(LeanCompileError::unsupported(
                "StructField/IntermediateConstructor",
            ));
        };
        let header = SourcePosition::new(
            Some(producer),
            SourceOwner::StructHeader(declaration),
            usize::MAX,
        );
        let (mut binders, _, mut definitions) = self.compile_struct_header(declaration, &header)?;
        let mut applied = arguments.to_vec();
        let mut ids = declaration
            .statement
            .param_def_with_dom
            .as_ref()
            .map(|(p, _)| p.ordered_param_ids())
            .unwrap_or_default();
        let n = declaration.statement.fields.len();
        for (i, (prior_field, stage)) in declaration.statement.fields[..index]
            .iter()
            .zip(&declaration.field_scope.fields[..index])
            .enumerate()
        {
            let position =
                SourcePosition::new(Some(&header), SourceOwner::StructFields(declaration), i + 1);
            self.validate_parameter_store_capture(&stage.defined)?;
            let [store] = stage.defined.store_and_infer_results.as_slice() else {
                return Err(LeanCompileError::unsupported("Struct/FieldStore"));
            };
            let (field_binders, _) = self.introduce_member_parameter(
                &prior_field.binding,
                &prior_field.field_type,
                store,
                &position,
            )?;
            binders.extend(field_binders);
            ids.push(prior_field.binding.id);
            let fact = self.resolve_fact(store.primary_fact_id(), &position)?;
            let member = (
                self.fact_proposition(&fact, &position)?,
                format!("h_{}", store.primary_fact_id().value()),
            );
            definitions
                .extend(self.compile_parameter_inferences(store, &fact, &member, &position)?);
            let coordinate = i + 1;
            applied.push(format!("(Litex.cartCall _field_value_{depth} _field_cart_{depth} (Litex.number (M := M) ({coordinate} : ℂ)) _field_cart_member_{depth} (by change M.mem (M.number ({coordinate} : ℂ)) (Litex.FiniteFunction.indexSet {n}); simpa [Litex.FiniteFunction.index] using (Litex.FiniteFunction.index_mem (M := M) ({i} : Fin {n}))))"));
            applied.push(format!("(Litex.FiniteFunction.coordinate_mem_number (M := M) _field_cart_member_{depth} ({i} : Fin {n}) ({coordinate} : ℂ) (by norm_num))"));
        }
        for id in ids {
            let level = format!("Type v{}}}", id.value());
            for binder in &mut binders {
                *binder = binder.replace(&level, "Type _}");
            }
        }
        let prior =
            SourcePosition::new(Some(&header), SourceOwner::StructFields(declaration), index);
        let wd = &declaration.field_scope.fields[index].well_defined;
        ensure_object(&field.field_type, wd)?;
        let formed = SourcePosition::new(Some(&prior), SourceOwner::WD(wd), usize::MAX);
        let constructors = match wd.detailed_ref() {
            DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::Structish(StructishObjWellDefinedProofByDef::StructObj(
                        proof,
                    )),
                ..
            } => self.compile_struct_arguments(carrier, proof, &formed)?,
            _ => self.compile_struct_reference_arguments(carrier, &formed)?,
        };
        Ok(constructors
            .into_iter()
            .map(|term| {
                let body = self.scope_proposition(term, &definitions);
                if binders.is_empty() {
                    body
                } else {
                    apply_arguments(&format!("(fun {} => {body})", binders.join(" ")), &applied)
                }
            })
            .collect())
    }

    pub(super) fn validate_struct_projection(
        &self,
        access: &FieldAccess,
        proof: &FieldAccessObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if access.fields.is_empty() || proof.projection_steps.len() != access.fields.len() {
            return Err(LeanCompileError::unsupported(
                "StructField/ProjectionStages",
            ));
        }
        let member = if let Obj::InstantiatedTemplateObj(instance) = access.obj.as_ref() {
            self.compile_template_record_member(
                instance,
                &proof.projection_steps[0].carrier,
                position,
            )?
        } else {
            let (carrier, member) = self.compile_struct_receiver(&access.obj, position)?;
            if proof.projection_steps[0].carrier != carrier {
                return Err(LeanCompileError::unsupported("StructField/ReceiverCarrier"));
            }
            member
        };
        for (depth, (step, name)) in proof
            .projection_steps
            .iter()
            .zip(&access.fields)
            .enumerate()
        {
            let (declaration, _, _) = position.visible_struct(&step.carrier.name)?;
            validate_struct(declaration)?;
            let field = declaration
                .statement
                .fields
                .get(step.field_index)
                .filter(|f| &f.binding.name == name)
                .ok_or_else(|| LeanCompileError::unsupported("StructField/ProjectionIndex"))?;
            let mut substitution = header_substitution(&declaration.statement, &step.carrier)?;
            substitution.extend(field_substitution(
                &declaration.statement,
                &field_receiver(access, depth),
            ));
            if let Some(next) = proof.projection_steps.get(depth + 1) {
                let expected = Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(
                    next.carrier.clone(),
                ));
                if !instantiated_object_matches(&field.field_type, &expected, &substitution) {
                    return Err(LeanCompileError::unsupported(
                        "StructField/IntermediateCarrier",
                    ));
                }
            }
        }
        Ok(member)
    }

    pub(super) fn with_struct_field_evidence<T>(
        &self,
        access: &FieldAccess,
        position: &SourcePosition<'_>,
        consume: impl FnMut(
            &FieldAccessObjWellDefinedProof,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<T, LeanCompileError> {
        self.find_struct_field_evidence(access, position, consume)?
            .ok_or_else(|| LeanCompileError::unsupported("StructField/ProjectionProducer"))
    }

    fn find_struct_field_evidence<T>(
        &self,
        access: &FieldAccess,
        position: &SourcePosition<'_>,
        mut consume: impl FnMut(
            &FieldAccessObjWellDefinedProof,
            &SourcePosition<'_>,
        ) -> Result<T, LeanCompileError>,
    ) -> Result<Option<T>, LeanCompileError> {
        let object =
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()));
        position
            .with_visible_wd(&object, &mut |wd, producer| {
                ensure_object(&object, wd)?;
                let DetailedObjWellDefinedProof::ByDef {
                    proof:
                        ObjWellDefinedProofByDef::Structish(
                            StructishObjWellDefinedProofByDef::FieldAccess(proof),
                        ),
                    ..
                } = wd.detailed_ref()
                else {
                    return Err(LeanCompileError::unsupported(
                        "StructField/ProjectionProducer",
                    ));
                };
                let scope = SourcePosition::new(Some(producer), SourceOwner::WD(wd), usize::MAX);
                consume(proof, &scope)
            })
    }

    pub(super) fn compile_struct_field_raw_value(
        &self,
        access: &FieldAccess,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let object =
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access.clone()));
        let mut free = std::collections::HashSet::new();
        crate::instantiate::collect_free_plain_ids(
            &object,
            &std::collections::HashSet::new(),
            &mut free,
        );
        if !free.iter().any(|id| bindings.contains_key(id)) {
            // Rebinding unrelated quantified candidates does not change this
            // field. Keep its checked object/WD citation instead of requiring
            // a second fresh projection trace.
            return Ok(format!(
                "(Litex.denote {})",
                self.compile_object_reference(&object, position)?
            ));
        }
        let coordinates = self.struct_field_coordinates(access, position)?;
        let mut value =
            self.compile_function_raw_expression_bound(&access.obj, position, bindings)?;
        for coordinate in coordinates {
            value = format!("(Litex.FunctionSemantics.callValue (M := M) {value} (M.number ({coordinate} : ℂ)))");
        }
        Ok(value)
    }

    /// The same declaration-owned coordinates used by the checked field
    /// constructor. A direct receiver retains its declared carrier even when
    /// the field WD is already a citation rather than a fresh projection.
    pub(super) fn struct_field_coordinates(
        &self,
        access: &FieldAccess,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<usize>, LeanCompileError> {
        // A substituted function body retains the original receiver in its
        // captured WD scope, not in the caller's parameter scope.
        if let Some(coordinates) =
            self.find_struct_field_evidence(access, position, |proof, scope| {
                self.validate_struct_projection(access, proof, scope)?;
                Ok(proof
                    .projection_steps
                    .iter()
                    .map(|step| step.field_index + 1)
                    .collect())
            })?
        {
            return Ok(coordinates);
        }
        if access.fields.len() == 1
            && super::compile_struct_fields::has_direct_record_receiver(access)
        {
            let (carrier, _) = self.compile_struct_receiver(&access.obj, position)?;
            let (declaration, _, _) = position.visible_struct(&carrier.name)?;
            validate_struct(declaration)?;
            let index = declaration
                .statement
                .fields
                .iter()
                .position(|field| field.binding.name == access.fields[0])
                .ok_or_else(|| LeanCompileError::unsupported("StructField/Name"))?;
            return Ok(vec![index + 1]);
        }
        Err(LeanCompileError::unsupported(
            "StructField/ProjectionProducer",
        ))
    }
}

fn apply_arguments(function: &str, arguments: &[String]) -> String {
    if arguments.is_empty() {
        function.to_owned()
    } else {
        format!("({function} {})", arguments.join(" "))
    }
}

fn bind_projection_arguments(lines: &mut Vec<String>, arguments: &mut [String], depth: usize) {
    for (i, argument) in arguments.iter_mut().enumerate() {
        let name = format!("_field_arg_{depth}_{i}");
        lines.push(format!("let {name} := {argument}"));
        *argument = name;
    }
}

pub(super) fn field_receiver(access: &FieldAccess, depth: usize) -> Obj {
    if depth == 0 {
        access.obj.as_ref().clone()
    } else {
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(FieldAccess {
            obj: access.obj.clone(),
            fields: access.fields[..depth].to_vec(),
        }))
    }
}
