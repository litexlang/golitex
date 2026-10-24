use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FnSetObjWellDefinedProof, FunctionSpaceObjWellDefinedProofByDef,
};
use crate::execute::{
    ExecHaveFnByForallExistUniqueStmtResult, ExecHaveFnByForallExistUniqueStmtSuccessResult,
};
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_have_fn_by_exist_statement(
        &self,
        result: &ExecHaveFnByForallExistUniqueStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported(
                "SelectedFunction/LocalDeclaration",
            ));
        }
        let ExecHaveFnByForallExistUniqueStmtResult::Success(p) = result else {
            return Err(LeanCompileError::unsupported("SelectedFunction/Failed"));
        };
        let (signature, existential) = selected_shape(p)?;
        let expected = Fact::ForallFact(p.statement.forall.clone());
        if source_subject(&p.source_forall)? != expected {
            return Err(LeanCompileError::unsupported(
                "SelectedFunction/SourceSubject",
            ));
        }
        let mut source = self.compile_verify(&p.source_forall, position)?;
        // This local application uses canonical semantic objects. The source
        // theorem remains polymorphic; only its local copy is specialized.
        for parameter in p.statement.forall.typed_parameters.ordered_param_ids() {
            let level = format!("Type v{}}}", parameter.value());
            source.0 = source.0.replace(&level, "Type u}");
            source.1 = source.1.replace(&level, "Type u}");
        }
        let checked = success_object_wd(
            &p.fn_set_well_defined,
            &Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
        )?;
        let prior = SourcePosition {
            before: 1,
            ..*position
        };
        let compiled_set = format!(
            "(show Litex.Obj (M := M) (Litex.FunctionSignature M) from {})",
            self.compile_wd(checked, &prior)?
        );
        let ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::FnSet(
                    wd,
                )),
            ..
        } = checked
        else {
            return Err(LeanCompileError::unsupported(
                "SelectedFunction/SignatureEvidence",
            ));
        };
        let header = SourcePosition::new(Some(&prior), SourceOwner::WD(checked), 0);
        let formed = SourcePosition {
            before: self.function_header_stages(signature) + 1,
            ..header
        };
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        let values = self.compile_function_packed_values(signature, "_selected_input")?;
        let mut bindings: HashMap<_, _> = parameters
            .iter()
            .zip(&values)
            .map(|(p, v)| (p.id, v.clone()))
            .collect();
        let witness = &existential.typed_parameters.groups[0].params[0];
        bindings.insert(witness.id, "_selected_output".into());
        let relation = format!(
            "(fun (_selected_input _selected_output : M.Value) => {})",
            self.selected_body(existential, &bindings, &formed)?
        );
        let raw_unique = self.selected_pointwise_unique(
            p,
            signature,
            existential,
            wd,
            &source,
            &header,
            &formed,
        )?;
        let (base, base_set) = self.compile_function_semantic_base_domain(signature, &formed)?;
        let target = self.compile_object_reference(&signature.ret_set, &formed)?;
        let guard = self.compile_function_packed_guard_template(signature, &formed)?;
        let members = if parameters.len() == 1 {
            "_selected_members".into()
        } else {
            (0..parameters.len()).map(|i| format!("(by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _selected_members ({i} : Fin {}))",parameters.len())).collect::<Vec<_>>().join(" ")
        };
        let value = format!("(show Litex.Obj (M := M) (Litex.SelectedFn M) from by\n  let _selected_signature := ({compiled_set}).val\n  have _selected_pointwise : {} := {}\n  exact Litex.selectedFn _selected_signature {relation} (by\n    intro _selected_input _selected_domain\n    obtain ⟨_selected_members, _selected_guard⟩ := (Litex.FunctionSignature.withGuard_domain {base} (Litex.denote {target}) {base_set} (Litex.isSet {target}) {guard} _selected_input).mp _selected_domain\n    exact _selected_pointwise {} {members} _selected_guard))",
            raw_unique.0, raw_unique.1.replace('\n', "\n  "), values.join(" "));
        let object = Obj::Identifier(IdentifierObj::from_bound_name(&p.statement.name));
        let mut declarations =
            vec![self.bind_alias(&p.statement.name, &object, &object, &value, false, position)?];
        let name = self.context_application(
            &format!("_object_i{}", p.statement.name.id.value()),
            position,
        );
        let member_position = SourcePosition {
            before: 3,
            ..*position
        };
        let membership = self.resolve_fact(p.membership_fact_id, &member_position)?;
        self.validate_store(&p.membership.store, &membership)?;
        let member = (
            format!("Litex.In {name} (Litex.fnSet ({name}).val.signature)"),
            format!("(Litex.selectedFnInFnSet {name})"),
        );
        declarations.push(self.emit_internal_fact(&membership, &member, &member_position)?);
        declarations.extend(self.compile_stored_inferences(
            &p.membership,
            &membership,
            &(
                member.0,
                self.context_application(&format!("h_{}", p.membership_fact_id.value()), position),
            ),
            &member_position,
        )?);
        let property = self.resolve_fact(
            p.property_forall_fact_id,
            &SourcePosition {
                before: 5,
                ..*position
            },
        )?;
        self.compile_fact_wd(&p.property_well_defined, &property, &member_position)?;
        for (unique, store, stage) in [(false, &p.property, 5), (true, &p.uniqueness, 6)] {
            let cursor = SourcePosition {
                before: stage,
                ..*position
            };
            let fact = self.resolve_fact(store.primary_fact_id(), &cursor)?;
            self.validate_store(&store.store, &fact)?;
            let Fact::ForallFact(fact) = &fact else {
                return Err(LeanCompileError::unsupported(
                    "SelectedFunction/StoredFamily",
                ));
            };
            let compiled = self.selected_export(
                p,
                signature,
                existential,
                fact,
                unique,
                &name,
                &cursor,
                &formed,
            )?;
            declarations.push(self.emit_internal_fact(
                &Fact::ForallFact(fact.clone()),
                &compiled,
                &cursor,
            )?);
            declarations.extend(self.compile_stored_inferences(
                store,
                &Fact::ForallFact(fact.clone()),
                &(
                    compiled.0,
                    self.context_application(&format!("h_{}", fact.fact_id.value()), position),
                ),
                &cursor,
            )?);
        }
        Ok(declarations.join("\n\n"))
    }

    fn selected_pointwise_unique(
        &self,
        p: &ExecHaveFnByForallExistUniqueStmtSuccessResult,
        signature: &FnSet,
        existential: &PlainExistFact,
        wd: &FnSetObjWellDefinedProof,
        source: &(String, String),
        header: &SourcePosition<'_>,
        formed: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let head = self.compile_function_binder_head(
            signature,
            &wd.param_type_well_defined,
            &wd.defined_params,
            &wd.assumed_dom_facts,
            header,
        )?;
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        let mut bindings: HashMap<_, _> = parameters
            .iter()
            .map(|p| (p.id, format!("_raw_i{}", p.id.value())))
            .collect();
        bindings.insert(
            existential.typed_parameters.groups[0].params[0].id,
            "_selected_output".into(),
        );
        let body = self.selected_body(existential, &bindings, formed)?;
        let target = self.compile_object_reference(&signature.ret_set, formed)?;
        let conclusion = format!("∃! _selected_output : M.Value, M.mem _selected_output (Litex.denote {target}) ∧ ({body})");
        let proposition = self.compile_function_raw_quantified(signature, &conclusion, formed)?;
        let mut arguments = Vec::new();
        for (parameter, store) in parameters
            .iter()
            .zip(&wd.defined_params.store_and_infer_results)
        {
            arguments.extend([
                format!("_value_i{}", parameter.id.value()),
                format!("h_{}", store.primary_fact_id().value()),
            ]);
        }
        arguments.extend(
            wd.assumed_dom_facts
                .iter()
                .map(|s| format!("h_{}", s.store_and_infer.primary_fact_id().value())),
        );
        let clauses: Vec<_> = (0..existential.facts.len())
            .map(|i| format!("_selected_clause_{i}"))
            .collect();
        let tail = if clauses.is_empty() {
            ", _".into()
        } else {
            format!(", {}", clauses.join(", "))
        };
        let mut unique_arguments = vec![
            "_selected_left".to_string(),
            "_selected_left_member".into(),
            "_selected_right".into(),
            "_selected_right_member".into(),
        ];
        for i in 0..clauses.len() {
            unique_arguments.push(conjunction_projection(
                "_selected_left_body",
                i,
                clauses.len(),
            ));
            unique_arguments.push(conjunction_projection(
                "_selected_right_body",
                i,
                clauses.len(),
            ));
        }
        let proof = format!("(by\n  {}\n  have h_{} : {} := {}\n  obtain ⟨_selected_exists, _selected_unique⟩ := h_{} {}\n  apply Litex.existsUniqueValueOfObjects (Litex.denote {target}) (fun _selected_output => {body})\n  · obtain ⟨_selected_witness, _selected_member{tail}⟩ := _selected_exists\n    exact ⟨_selected_witness, _selected_member, {}⟩\n  · intro _selected_left _selected_right _selected_left_member _selected_right_member _selected_left_body _selected_right_body\n    exact _selected_unique {})",
            head.replace('\n',"\n  "),p.statement.forall.fact_id.value(),source.0,source.1.replace('\n',"\n  "),
            p.statement.forall.fact_id.value(),arguments.join(" "),conjunction_evidence(&clauses),unique_arguments.join(" "));
        Ok((proposition, proof))
    }

    fn selected_body(
        &self,
        fact: &PlainExistFact,
        bindings: &HashMap<IdentifierId, String>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        conjunction_proposition(
            fact.facts
                .iter()
                .map(|f| {
                    self.compile_function_raw_predicate(
                        &crate::instantiate::quantifier_free_fact_to_fact(f.clone()),
                        position,
                        bindings,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn selected_export(
        &self,
        p: &ExecHaveFnByForallExistUniqueStmtSuccessResult,
        signature: &FnSet,
        existential: &PlainExistFact,
        fact: &ForallFact,
        unique: bool,
        object: &str,
        position: &SourcePosition<'_>,
        formed: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let FactWellDefinedProof::ForallFact(property_wd) = &p.property_well_defined else {
            return Err(LeanCompileError::unsupported("SelectedFunction/PropertyWD"));
        };
        let inputs = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .count();
        let mut bindings =
            HashMap::from([(p.statement.name.id, format!("(Litex.denote {object})"))]);
        let mut binders = Vec::new();
        let mut introductions = Vec::new();
        let mut objects = Vec::new();
        let mut requirements = Vec::new();
        for (index, (parameter, carrier)) in fact
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
            .enumerate()
        {
            let ParamType::Obj(carrier) = carrier else {
                return Err(LeanCompileError::unsupported(
                    "SelectedFunction/ExportParameterKind",
                ));
            };
            let id = parameter.id.value();
            let name = format!("_value_i{id}");
            let member = if index < inputs {
                format!(
                    "h_{}",
                    property_wd
                        .introduced_params
                        .defined_params
                        .store_and_infer_results[index]
                        .primary_fact_id()
                        .value()
                )
            } else {
                format!("_membership_i{id}")
            };
            let raw = format!("(Litex.denote {name})");
            let carrier =
                self.compile_function_raw_expression_bound(carrier, position, &bindings)?;
            binders.push(format!("{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({name} : Litex.Obj (M := M) _Host_i{id}) ({member} : M.mem {raw} {carrier})"));
            introductions.extend([
                format!("_Host_i{id}"),
                format!("_rep_i{id}"),
                name.clone(),
                member.clone(),
            ]);
            bindings.insert(parameter.id, raw);
            objects.push(name);
            requirements.push(member);
        }
        for dom in &fact.dom_facts {
            let name = format!("h_{}", dom.fact_id().value());
            binders.push(format!(
                "({name} : {})",
                self.compile_function_raw_predicate(dom, position, &bindings)?
            ));
            introductions.push(name);
        }
        let original_dom = p
            .statement
            .forall
            .dom_facts
            .iter()
            .map(|f| format!("h_{}", f.fact_id().value()))
            .collect::<Vec<_>>();
        let mut input_requirements = requirements[..inputs].to_vec();
        input_requirements.extend(original_dom);
        let (members, guard) = self.compile_function_domain_certificates(
            signature,
            &objects[..inputs],
            &input_requirements,
            formed,
        )?;
        let values = objects[..inputs]
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect::<Vec<_>>();
        let packed = if inputs == 1 {
            values[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                values.join(", ")
            )
        };
        let (base, base_set) = self.compile_function_semantic_base_domain(signature, formed)?;
        let target = self.compile_object_reference(&signature.ret_set, formed)?;
        let packed_guard = self.compile_function_packed_guard_template(signature, formed)?;
        let member = if inputs == 1 {
            members[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.tuple_inCart ![{}] ![{}] {})",
                values.join(", "),
                if Self::function_uses_numeric_interface(signature) {
                    let mut d = self.compile_function_domains(signature, formed)?;
                    d.pop();
                    d.into_iter()
                        .map(|v| format!("M.standard {v}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                } else {
                    self.compile_function_input_sets(signature, formed)?
                        .iter()
                        .map(|v| format!("Litex.denote {v}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                },
                finite_vector_proof(&members)
            )
        };
        let mut lines = vec![format!("intro {}", introductions.join(" "))];
        let guard_template = self.compile_function_guard_template(signature, formed)?;
        let guard_eq =
            self.compile_function_packed_application_equality(&guard_template, &values)?;
        let guard_proof = format!(
            "(Eq.mpr {guard_eq} ({guard} : {guard_template} {}))",
            values.join(" ")
        );
        lines.push(format!("have _selected_domain : M.mem {packed} ({object}).val.signature.domain := (Litex.FunctionSignature.withGuard_domain {base} (Litex.denote {target}) {base_set} (Litex.isSet {target}) {packed_guard} {packed}).mpr ⟨{member}, {guard_proof}⟩"));
        let conclusion = conjunction_proposition(
            fact.then_facts
                .iter()
                .map(|f| {
                    self.compile_function_raw_predicate(&f.clone().into(), position, &bindings)
                })
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let output = if unique {
            format!("(Litex.denote {})", objects.last().unwrap())
        } else {
            format!("(Litex.FunctionSemantics.callValue (Litex.denote {object}) {packed})")
        };
        let mut raw_bindings = HashMap::new();
        let mut raw_binders = Vec::new();
        for parameter in signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
        {
            let raw = format!("_raw_i{}", parameter.id.value());
            raw_binders.push(format!("({raw} : M.Value)"));
            raw_bindings.insert(parameter.id, raw);
        }
        raw_bindings.insert(existential.typed_parameters.groups[0].params[0].id, output);
        let property_template = format!(
            "(fun {} => {})",
            raw_binders.join(" "),
            self.selected_body(existential, &raw_bindings, formed)?
        );
        let property_eq =
            self.compile_function_packed_application_equality(&property_template, &values)?;
        if unique {
            let output = objects.last().unwrap();
            let body_facts = &fact.dom_facts[p.statement.forall.dom_facts.len()..];
            let body_proposition = conjunction_proposition(
                body_facts
                    .iter()
                    .map(|f| self.compile_function_raw_predicate(f, position, &bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            )?;
            let body_proof = conjunction_evidence(
                &body_facts
                    .iter()
                    .map(|f| format!("h_{}", f.fact_id().value()))
                    .collect::<Vec<_>>(),
            );
            lines.push(format!("apply Litex.selectedFn_unique {object} {packed} (Litex.denote {output}) _selected_domain"));
            lines.push(format!("refine ⟨{}, ?_⟩", requirements.last().unwrap()));
            lines.push(format!(
                "exact Eq.mpr {property_eq} ({body_proof} : {body_proposition})"
            ));
        } else {
            // All published clauses are the selected witness's actual property.
            lines.push(format!("exact Eq.mp {property_eq} (Litex.selectedFn_call_spec {object} {packed} _selected_domain).2"));
        }
        Ok((
            format!("∀ {}, {conclusion}", binders.join(" ")),
            format!("(by\n  {})", lines.join("\n").replace('\n', "\n  ")),
        ))
    }
}

fn conjunction_evidence(terms: &[String]) -> String {
    terms
        .iter()
        .rev()
        .cloned()
        .reduce(|tail, head| format!("⟨{head}, {tail}⟩"))
        .unwrap_or_else(|| "True.intro".into())
}

fn selected_shape(
    p: &ExecHaveFnByForallExistUniqueStmtSuccessResult,
) -> Result<(&FnSet, &PlainExistFact), LeanCompileError> {
    let fail = || LeanCompileError::unsupported("SelectedFunction/StoredShape");
    let stores = [&p.membership, &p.property, &p.uniqueness];
    let ids = stores
        .iter()
        .map(|s| s.primary_fact_id())
        .collect::<Vec<_>>();
    if ids
        != [
            p.membership_fact_id,
            p.property_forall_fact_id,
            p.uniqueness_forall_fact_id,
        ]
        || ids.iter().collect::<HashSet<_>>().len() != 3
        || stores
            .iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect::<Vec<_>>()
            != p.stored_fact_ids
    {
        return Err(fail());
    }
    let StoreFactResult::AtomicFact(member) = &p.membership.store else {
        return Err(fail());
    };
    let AtomicFact::InFact(member) = &member.fact else {
        return Err(fail());
    };
    if !matches!(&member.element,Obj::Identifier(IdentifierObj::Plain{id,name}) if *id==p.statement.name.id && *name==p.statement.name.name)
    {
        return Err(fail());
    }
    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
        return Err(fail());
    };
    let source = &p.statement.forall;
    let [ExistOrAndChainAtomicFact::ExistUniqueFact(existential)] = source.then_facts.as_slice()
    else {
        return Err(fail());
    };
    let [group] = existential.typed_parameters.groups.as_slice() else {
        return Err(fail());
    };
    let [witness] = group.params.as_slice() else {
        return Err(fail());
    };
    let ParamType::Obj(output) = &group.param_type else {
        return Err(fail());
    };
    if &*signature.ret_set != output
        || signature.set_bound_parameters.groups.len() != source.typed_parameters.groups.len()
        || signature.dom_facts.len() != source.dom_facts.len()
    {
        return Err(fail());
    }
    for (s, t) in signature
        .set_bound_parameters
        .groups
        .iter()
        .zip(&source.typed_parameters.groups)
    {
        if s.params != t.params || !matches!(&t.param_type,ParamType::Obj(o) if o==&*s.param_type) {
            return Err(fail());
        }
    }
    for (s, t) in signature.dom_facts.iter().zip(&source.dom_facts) {
        if function_guard_fact(s)? != *t {
            return Err(fail());
        }
    }
    let StoreFactResult::ForallFact(property) = &p.property.store else {
        return Err(fail());
    };
    let StoreFactResult::ForallFact(unique) = &p.uniqueness.store else {
        return Err(fail());
    };
    let property = &property.fact;
    let unique = &unique.fact;
    let input_groups = source.typed_parameters.groups.len();
    if property.typed_parameters != source.typed_parameters
        || property.dom_facts != source.dom_facts
        || property.then_facts.len() != existential.facts.len()
        || unique.typed_parameters.groups.len() != input_groups + 1
        || unique.typed_parameters.groups[..input_groups] != source.typed_parameters.groups
        || unique.dom_facts.len() != source.dom_facts.len() + existential.facts.len()
        || unique.dom_facts[..source.dom_facts.len()] != source.dom_facts
    {
        return Err(fail());
    }
    let candidate = &unique.typed_parameters.groups[input_groups];
    let [candidate_name] = candidate.params.as_slice() else {
        return Err(fail());
    };
    if candidate.param_type != group.param_type
        || candidate_name.id == witness.id
        || source
            .typed_parameters
            .ordered_param_ids()
            .contains(&candidate_name.id)
    {
        return Err(fail());
    }
    let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] =
        unique.then_facts.as_slice()
    else {
        return Err(fail());
    };
    if !matches!(&eq.left,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==candidate_name.id) {
        return Err(fail());
    }
    let Obj::FnObj(call) = &eq.right else {
        return Err(fail());
    };
    if !matches!(call.head.as_ref(),FnObjHead::Identifier(IdentifierObj::Plain{id,name}) if *id==p.statement.name.id && *name==p.statement.name.name)
    {
        return Err(fail());
    }
    let [args] = call.body.as_slice() else {
        return Err(fail());
    };
    let params = source.typed_parameters.ordered_param_ids();
    if args.len()!=params.len() || args.iter().zip(&params).any(|(arg,id)|!matches!(arg.as_ref(),Obj::Identifier(IdentifierObj::Plain{id:actual,..}) if actual==id)) {return Err(fail());}
    let substitution = HashMap::from([(witness.id, eq.right.clone())]);
    let candidate_substitution = HashMap::from([(witness.id, eq.left.clone())]);
    for (i, clause) in existential.facts.iter().enumerate() {
        let source = crate::instantiate::quantifier_free_fact_to_fact(clause.clone());
        if !instantiated_fact_matches(
            &source,
            &property.then_facts[i].clone().into(),
            &substitution,
        ) || !instantiated_fact_matches(
            &source,
            &unique.dom_facts[p.statement.forall.dom_facts.len() + i],
            &candidate_substitution,
        ) {
            return Err(fail());
        }
    }
    Ok((signature, existential))
}
