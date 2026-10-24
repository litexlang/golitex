use super::compile_function_template::function_guard_fact;
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection;
use crate::execute::ExecHaveByFnPreimageStmtResult;
use crate::prelude::*;
use crate::store_fact_and_infer::InferInFactFnRangeResult;
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    /// The preimage statement itself constructs this call from the selected
    /// signature and its ordered witness/domain stores. There is no separate
    /// VerifyObj result to reconstruct or search for.
    pub(super) fn compile_preimage_call_reference(
        &self,
        object: &Obj,
        p: &crate::execute::ExecHaveByFnPreimageStmtSuccessResult,
        position: &SourcePosition<'_>,
        observe_numeric: bool,
    ) -> Result<Option<String>, LeanCompileError> {
        let stores = &p.store_and_infer_result.store_and_infer_results;
        if position.before < stores.len() + 1 {
            return Ok(None);
        }
        let function = range_function(&p.statement.range_membership)?;
        let args = p
            .statement
            .preimage_names
            .iter()
            .map(|p| Box::new(Obj::Identifier(IdentifierObj::from_bound_name(p))))
            .collect();
        let call = crate::execute::execute_fact_stmt::function_domain::function_application(
            function, args,
        )
        .map_err(|_| error("Application"))?;
        if call.ir() != object.ir() {
            return Ok(None);
        }
        let signature = p.signature_selection.signature();
        let before = SourcePosition {
            before: 0,
            ..*position
        };
        let hf = self.compile_selected_signature(function, &p.signature_selection, &before)?;
        let f = self.compile_object_reference(function, &before)?;
        let terms = p
            .statement
            .preimage_names
            .iter()
            .map(|p| self.compile_parameter_reference(p.id, position))
            .collect::<Result<Vec<_>, _>>()?;
        let proofs = stores
            .iter()
            .take(stores.len() - 1)
            .map(|s| {
                self.cited_fact_reference(s.primary_fact_id(), position)
                    .map(|(_, t)| t)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let (members, hg) =
            self.compile_function_domain_certificates(signature, &terms, &proofs, position)?;
        let (term, law) = if Self::function_uses_numeric_interface(signature) {
            let (params, target) =
                self.compile_function_constructor_arguments(signature, position)?;
            let guard = self.compile_function_guard_template(signature, position)?;
            let ctor = match (terms.len() == 1, target) {
                (true, false) => "call",
                (false, false) => "call2",
                (true, true) => "callTarget",
                (false, true) => "call2Target",
            };
            (
                format!(
                    "(Litex.{ctor} {params} {guard} {f} {} {hf} {} {hg})",
                    terms.join(" "),
                    members.join(" ")
                ),
                if terms.len() == 1 {
                    "callInOutput"
                } else {
                    "call2InOutput"
                },
            )
        } else {
            let (domain, packed, hm, hg) =
                self.compile_packed_call_arguments(signature, &terms, &members, &hg, position)?;
            let output = self.compile_object_reference(&signature.ret_set, position)?;
            let guard = self.compile_function_packed_guard_template(signature, position)?;
            (
                format!(
                    "(Litex.callOnDomain {domain} {output} {guard} {f} {packed} {hf} {hm} {hg})"
                ),
                "callOnInOutput",
            )
        };
        if !observe_numeric {
            return Ok(Some(term));
        }
        let Ok(output) = self.compile_numeric_carrier(&signature.ret_set, position) else {
            return Ok(None);
        };
        let member = standard_inclusion_term(
            &output,
            &StandardSet::C,
            "_preimage_call",
            &format!("(Litex.{law} _preimage_call)"),
        )?;
        Ok(Some(format!("(let _preimage_call := {term}; show {{ _z : ℂ // Litex.denote _preimage_call = M.number _z ∧ Litex.In _preimage_call Litex.C }} from ⟨Litex.NativeBridge.asComplex _preimage_call {member}, Litex.NativeBridge.asComplex_spec _preimage_call {member}, {member}⟩)")))
    }

    pub(super) fn compile_have_fn_preimage_statement(
        &self,
        result: &ExecHaveByFnPreimageStmtResult,
        position: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecHaveByFnPreimageStmtResult::Success(p) = result else {
            return Err(error("Failed"));
        };
        let source = Fact::AtomicFact(AtomicFact::InFact(p.statement.range_membership.clone()));
        if source_subject(&p.source_membership)? != source {
            return Err(error("SourceSubject"));
        }
        let signature_member = self.compile_selected_signature(
            range_function(&p.statement.range_membership)?,
            &p.signature_selection,
            position,
        )?;
        let compiled = self.compile_verify(&p.source_membership, position)?;
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let count = p.statement.preimage_names.len();
        let params: Vec<_> = p
            .preimage_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect();
        if params.len() != count
            || params
                .iter()
                .zip(&p.statement.preimage_names)
                .any(|(a, b)| *a != b)
        {
            return Err(error("Names"));
        }
        self.validate_parameter_store_capture(&p.store_and_infer_result)?;
        let stores = &p.store_and_infer_result.store_and_infer_results;
        if stores.len() != count + p.signature_selection.signature().dom_facts.len() + 1 {
            return Err(error("StoreArity"));
        }
        let mut facts = Vec::new();
        for (index, store) in stores.iter().enumerate() {
            let stage = SourcePosition {
                before: 2 + index,
                ..*position
            };
            let fact = self.resolve_fact(store.primary_fact_id(), &stage)?;
            self.validate_store(&store.store, &fact)?;
            if index < count {
                let group = p
                    .preimage_parameters
                    .groups
                    .iter()
                    .find(|g| g.params.iter().any(|p| p.id == params[index].id))
                    .ok_or_else(|| error("Parameter"))?;
                if !matches!((&group.param_type,&fact),(ParamType::Obj(carrier),Fact::AtomicFact(AtomicFact::InFact(f))) if f.set.ir()==carrier.ir() && matches!(&f.element,Obj::Identifier(IdentifierObj::Plain{id,..}) if *id==params[index].id))
                {
                    return Err(error("ParameterStore"));
                }
            } else {
                facts.push(fact);
            }
        }
        let (prop, term) = self.compile_range_preimage(
            &p.statement.range_membership,
            &p.signature_selection,
            &signature_member,
            &p.preimage_parameters,
            &facts,
            &compiled.1,
            &formed,
        )?;
        let name = format!(
            "_preimage_h_{}",
            stores.last().unwrap().primary_fact_id().value()
        );
        let mut lines = vec![if local {
            format!("have {name} : {prop} := {term}")
        } else {
            format!(
                "theorem {name}{} : {prop} := {term}",
                self.context_header(position)?
            )
        }];
        let mut tail = if local {
            name
        } else {
            self.context_application(&name, position)
        };
        if local {
            let mut names = Vec::new();
            for (name, store) in p.statement.preimage_names.iter().zip(stores) {
                names.extend([
                    format!("_value_i{}", name.id.value()),
                    format!("h_{}", store.primary_fact_id().value()),
                ]);
            }
            names.extend(
                stores
                    .iter()
                    .skip(count)
                    .map(|s| format!("h_{}", s.primary_fact_id().value())),
            );
            lines.push(format!("rcases {tail} with ⟨{}⟩", names.join(", ")));
        }
        for (index, store) in stores.iter().enumerate() {
            let completed = SourcePosition {
                before: 2 + index,
                ..*position
            };
            if !local && index < count {
                let name = format!("_value_i{}", params[index].id.value());
                lines.push(format!("noncomputable def {name}{} : Litex.Obj (M := M) M.Value :=\n  Classical.choose ({tail})",self.context_header(position)?));
                tail = format!("(Classical.choose_spec ({tail}))");
            }
            let fact = self.resolve_fact(store.primary_fact_id(), &completed)?;
            let proposition =
                self.compile_function_raw_predicate(&fact, &completed, &HashMap::new())?;
            let name = format!("h_{}", fact.fact_id().value());
            if !local {
                let last = index + 1 == stores.len();
                let evidence = if last {
                    tail.clone()
                } else {
                    format!("(Classical.choose ({tail}))")
                };
                lines.push(self.emit_internal_fact(
                    &fact,
                    &(proposition.clone(), evidence),
                    &completed,
                )?);
                if !last {
                    tail = format!("(Classical.choose_spec ({tail}))");
                }
            }
            let reference = if local {
                name
            } else {
                self.context_application(&name, position)
            };
            let compiled = (proposition, reference);
            lines.extend(if index < count {
                self.compile_parameter_inferences(store, &fact, &compiled, &completed)?
            } else {
                self.compile_stored_inferences(store, &fact, &compiled, &completed)?
            });
        }
        Ok(lines.join("\n\n"))
    }

    pub(super) fn compile_range_inference(
        &self,
        p: &InferInFactFnRangeResult,
        source: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(member)) = source else {
            return Err(error("InferenceSource"));
        };
        let function = range_function(member)?;
        let signature = p.signature_selection.signature();
        let hf = self.compile_selected_signature(function, &p.signature_selection, position)?;
        let range = self.compile_object_reference(&member.set, position)?;
        let value = self.compile_object_reference(&member.element, position)?;
        let sig = self.compile_fn_signature(signature, position)?;
        let fact = self.resolve_fact(p.codomain_membership.primary_fact_id(), position)?;
        if !matches!(&fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==member.element.ir() && f.set.ir()==signature.ret_set.ir())
        {
            return Err(error("InferredOutput"));
        }
        self.validate_store(&p.codomain_membership.store, &fact)?;
        let term = format!(
            "(Litex.fnRangeInOutput {range} {value} {sig} {hf} {})",
            compiled.1
        );
        let mut lines = vec![self.emit_internal_fact(
            &fact,
            &(self.fact_proposition(&fact, position)?, term),
            position,
        )?];
        if let Some(store) = &p.preimage_witness {
            let prior = SourcePosition {
                before: position.before + 1,
                ..*position
            };
            let fact = self.resolve_fact(store.primary_fact_id(), &prior)?;
            let Fact::ExistFact(ex) = &fact else {
                return Err(error("InferredExistence"));
            };
            self.validate_store(&store.store, &fact)?;
            let clauses = ex
                .facts
                .iter()
                .cloned()
                .map(crate::instantiate::quantifier_free_fact_to_fact)
                .collect::<Vec<_>>();
            let evidence = self.compile_range_preimage(
                member,
                &p.signature_selection,
                &hf,
                &ex.typed_parameters,
                &clauses,
                &compiled.1,
                &prior,
            )?;
            lines.push(self.emit_internal_fact(&fact, &evidence, &prior)?);
        }
        Ok(lines)
    }

    fn compile_range_preimage(
        &self,
        member: &InFact,
        selection: &FunctionSignatureSelection,
        hf: &str,
        parameters: &TypedParameterList,
        clauses: &[Fact],
        membership: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let signature = selection.signature();
        let function = range_function(member)?;
        let positive_inputs = self.compile_function_positive_inputs(signature, position)?;
        let original = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
            .collect::<Vec<_>>();
        let actual = parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        if original.len() != actual.len()
            || actual.is_empty()
            || clauses.len() != signature.dom_facts.len() + 1
        {
            return Err(error("ExistentialShape"));
        }
        let mut free = HashSet::new();
        for obj in [function, &member.element] {
            crate::instantiate::collect_free_plain_ids(obj, &HashSet::new(), &mut free);
        }
        if actual.iter().any(|(p, _)| free.contains(&p.id)) {
            return Err(error("CapturedWitness"));
        }
        let mut substitution = HashMap::new();
        let mut ids = HashSet::new();
        let mut objects = Vec::new();
        for ((old, domain), (p, carrier)) in original.iter().zip(&actual) {
            let ParamType::Obj(carrier) = carrier else {
                return Err(error("ParameterKind"));
            };
            if !ids.insert(p.id) || !instantiated_object_matches(domain, carrier, &substitution) {
                return Err(error("ParameterCarrier"));
            }
            let object = Obj::Identifier(IdentifierObj::from_bound_name(p));
            substitution.insert(old.id, object.clone());
            objects.push(Box::new(object));
        }
        for (original, actual) in signature.dom_facts.iter().zip(clauses) {
            if !instantiated_fact_matches(&function_guard_fact(original)?, actual, &substitution) {
                return Err(error("GuardClause"));
            }
        }
        let call = crate::execute::execute_fact_stmt::function_domain::function_application(
            function, objects,
        )
        .map_err(|_| error("Application"))?;
        if !matches!(clauses.last(),Some(Fact::AtomicFact(AtomicFact::EqualFact(f))) if f.left.ir()==member.element.ir() && f.right.ir()==call.ir())
        {
            return Err(error("PreimageEquation"));
        }
        let mut bindings = HashMap::new();
        let mut binders = Vec::new();
        for (p, carrier) in &actual {
            let ParamType::Obj(carrier) = carrier else {
                unreachable!()
            };
            let name = format!("_value_i{}", p.id.value());
            let domain =
                self.compile_function_raw_expression_bound(carrier, position, &bindings)?;
            binders.push(format!("({name} : Litex.Obj (M := M) M.Value), ∃ (_member_i{} : M.mem (Litex.denote {name}) {domain}),",p.id.value()));
            bindings.insert(p.id, format!("(Litex.denote {name})"));
        }
        let mut proposition =
            self.compile_function_raw_predicate(clauses.last().unwrap(), position, &bindings)?;
        for clause in clauses[..clauses.len() - 1].iter().rev() {
            proposition = format!(
                "∃ (h_{} : {}), {proposition}",
                clause.fact_id().value(),
                self.compile_function_raw_predicate(clause, position, &bindings)?
            );
        }
        for binder in binders.iter().rev() {
            proposition = format!("∃ {binder} {proposition}");
        }
        let range = self.compile_object_reference(&member.set, position)?;
        let value = self.compile_object_reference(&member.element, position)?;
        let sig = self.compile_fn_signature(signature, position)?;
        let (base, base_set) = self.compile_function_semantic_base_domain(signature, position)?;
        let output = self.compile_object_reference(&signature.ret_set, position)?;
        let guard = self.compile_function_packed_guard_template(signature, position)?;
        let values =
            self.compile_function_packed_values(signature, "(Litex.denote _range_input)")?;
        let mut lines=vec![format!("obtain ⟨_range_input, _range_domain, _range_eq⟩ := (Litex.inFnRange_iff {range} {value} {sig} {hf}).mp {membership}"),
            format!("obtain ⟨_range_members, _range_guard⟩ := (Litex.FunctionSignature.withGuard_domain {base} (Litex.denote {output}) {base_set} (Litex.isSet {output}) {guard} _).mp _range_domain")];
        // Numeric R+ signatures store positivity before their explicit guards.
        // Restore source memberships from these exact ordered components.
        let guards = &clauses[..clauses.len() - 1];
        let mut guard_names = positive_inputs
            .iter()
            .map(|id| format!("_range_positive_i{}", id.value()))
            .collect::<Vec<_>>();
        let explicit_names = guards
            .iter()
            .map(|g| format!("h_{}", g.fact_id().value()))
            .collect::<Vec<_>>();
        guard_names.extend(explicit_names.iter().cloned());
        if guard_names.len() == 1 {
            lines.push(format!("have {} := _range_guard", guard_names[0]));
        } else if guard_names.len() > 1 {
            lines.push(format!(
                "rcases _range_guard with ⟨{}⟩",
                guard_names.join(", ")
            ));
        }
        let mut witnesses = Vec::new();
        for (i, val) in values.iter().enumerate() {
            let mem = if values.len() == 1 {
                "_range_members".into()
            } else {
                format!("(by simpa [Litex.FiniteFunction.index] using Litex.FiniteFunction.coordinate_mem _range_members ({i} : Fin {}))",values.len())
            };
            lines.push(format!("have _range_base_member_{i} := {mem}"));
            let member = if positive_inputs.contains(&original[i].0.id) {
                format!("(Litex.positiveReal_members (M := M) {val}).mpr ⟨_range_base_member_{i}, _range_positive_i{}⟩",original[i].0.id.value())
            } else {
                format!("_range_base_member_{i}")
            };
            lines.push(format!("have _range_member_{i} := {member}"));
            witnesses.extend([
                format!("(Litex.semanticObject {val} (M.member_isSet _range_member_{i}))"),
                format!("_range_member_{i}"),
            ]);
        }
        witnesses.extend(explicit_names);
        let equation = if values.len() == 1 {
            "_range_eq".into()
        } else {
            lines.push(format!("have _range_repack : Litex.denote _range_input = Litex.FiniteFunction.tupleValue (M := M) ![{}] := by\n    apply (Litex.FiniteFunction.reconstruct _range_members).trans\n    apply congrArg (Litex.FiniteFunction.tupleValue (M := M))\n    funext i\n    fin_cases i <;> norm_num [Litex.FiniteFunction.index]",values.join(", ")));
            format!("(_range_eq.trans (congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote {})) _range_repack))",self.compile_object_reference(function,position)?)
        };
        witnesses.push(equation);
        lines.push(format!("exact ⟨{}⟩", witnesses.join(", ")));
        Ok((proposition, format!("(by\n  {})", lines.join("\n  "))))
    }
}

fn error(stage: &str) -> LeanCompileError {
    LeanCompileError::new(
        &format!("FnPreimage/{stage}"),
        "The original range, signature, witness names or ordered output clauses do not match.",
    )
}
fn range_function(member: &InFact) -> Result<&Obj, LeanCompileError> {
    let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = &member.set else {
        return Err(error("SourceRange"));
    };
    Ok(&range.function)
}
