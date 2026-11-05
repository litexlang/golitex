use super::compile_function_template::function_guard_fact;
use super::compile_have_fn_by_induc_result::recursive_signature;
use super::compile_real_set_bounds::contains_parameter;
use super::compile_recursive_case_tree::{
    recursive_guard_atoms, recursive_leaf_paths, recursive_path_guards,
    validate_recursive_case_tree,
};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::HaveFnByInducCaseBody;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::ExecHaveFnByInducStmtSuccessResult;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_general_recursive_statement(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        parent: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let signature = recursive_signature(p);
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        if parameters.is_empty() {
            return Err(general_error("Shape"));
        }
        validate_recursive_case_tree(&p.statement.cases, &p.case_checks, p.statement.name.id)?;
        let leaf_paths = recursive_leaf_paths(&p.statement.cases);
        for parameter in &parameters {
            if contains_parameter(&signature.ret_set, parameter.id)
                || signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .any(|g| contains_parameter(&g.param_type, parameter.id))
            {
                return Err(LeanCompileError::unsupported(
                    "RecursiveGeneral/DependentCarrier",
                ));
            }
        }
        let set = Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone()));
        let checked_set =
            self.compile_wd(success_object_wd(&p.fn_set_well_defined, &set)?, parent)?;
        let scope = SourcePosition::new(Some(parent), SourceOwner::RecursiveFunction(p), 7);
        let restricted = self.recursive_restricted_signature(p, &scope)?;
        let (measure, lower, recursive_domain, body) =
            self.compile_general_recursive_value_parts(p, &scope, &HashMap::new())?;
        let bindings = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .zip(self.compile_function_packed_values(&signature, "_input")?)
            .map(|(p, v)| (p.id, v))
            .collect();
        let formation = self.compile_general_recursive_formation(p, &scope)?;
        let domain_sound = self.compile_general_recursive_domain(p, &restricted, &scope)?;
        let (returned, congruent) = self.compile_general_recursive_branches(p, &scope)?;
        let value = format!("(show Litex.Obj (M := M) (Litex.RecursiveFn M) from by\n  classical\n  let _signature := ({checked_set}).val\n  let _recursive_domain := {recursive_domain}\n  let _body := fun (_input _prefix : M.Value) => {body}\n  let _rank := fun (_input : M.Value) => (Litex.NativeBridge.integerValue (M := M) {measure} - Litex.NativeBridge.integerValue (M := M) {lower}).toNat\n  let _data : Litex.RecursiveFn M := ⟨_signature, _rank, _recursive_domain, _body⟩\n  have _formation : ∀ _input : M.Value, M.mem _input _signature.domain → M.mem {} (M.standard .integer) ∧ M.mem {} (M.standard .integer) ∧ {} := {formation}\n  exact Litex.recursiveFn _data ⟨{domain_sound}, {returned}, {congruent}⟩)", measure, lower,
            self.compile_function_raw_predicate(&source_subject(&p.measure_ge_lower)?, &scope, &bindings)?);
        let object = Obj::Identifier(parent.defining_identifier(&p.statement.name, &self.runtime)?);
        let mut declarations =
            vec![self.bind_alias(&p.statement.name, &object, &object, &value, local, parent)?];
        let name = format!("_object_i{}", p.statement.name.id.value());
        let name = if local {
            name
        } else {
            self.context_application(&name, parent)
        };
        let stores = &p.store_and_infer_result;
        if stores.membership_fact_id != stores.membership.primary_fact_id()
            || stores.case_defining.len() != leaf_paths.len()
            || stores.case_defining_fact_ids
                != stores
                    .case_defining
                    .iter()
                    .map(|s| s.primary_fact_id())
                    .collect::<Vec<_>>()
            || stores.stored_fact_ids
                != std::iter::once(&stores.membership)
                    .chain(&stores.case_defining)
                    .flat_map(|s| s.stored_fact_ids())
                    .collect::<Vec<_>>()
        {
            return Err(general_error("StoreCapture"));
        }
        let stored = SourcePosition {
            before: 8,
            ..*parent
        };
        let membership = self.resolve_fact(stores.membership_fact_id, &stored)?;
        if !matches!(&membership, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==object.ir() && f.set==set)
        {
            return Err(general_error("MembershipSubject"));
        }
        self.validate_store(&stores.membership.store, &membership)?;
        let keyword = if local { "have" } else { "theorem" };
        let context = if local {
            String::new()
        } else {
            self.context_header(parent)?
        };
        declarations.push(format!(
            "{keyword} h_{}{context} : {} := Litex.recursiveFnInFnSet {name}",
            stores.membership_fact_id.value(),
            self.fact_proposition(&membership, &stored)?
        ));
        for (index, store) in stores.case_defining.iter().enumerate() {
            declarations.push(self.compile_general_recursive_equation(
                p,
                &leaf_paths[index],
                store,
                &name,
                &stored,
                parent,
                local,
            )?);
        }
        Ok(declarations.join("\n\n"))
    }

    fn compile_general_recursive_value_parts(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        site: &SourcePosition<'_>,
        outer: &HashMap<IdentifierId, String>,
    ) -> Result<(String, String, String, String), LeanCompileError> {
        let signature = recursive_signature(p);
        let mut bindings = outer.clone();
        for (parameter, value) in signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .zip(self.compile_function_packed_values(&signature, "_input")?)
        {
            if bindings.insert(parameter.id, value).is_some() {
                return Err(general_error("CaptureIdentity"));
            }
        }
        let restricted = self.recursive_restricted_signature(p, site)?;
        let (domain, _, _) =
            self.compile_function_signature_value_parts(&restricted, site, &bindings)?;
        let measure =
            self.compile_function_raw_expression_bound(&p.statement.measure, site, &bindings)?;
        let lower =
            self.compile_function_raw_expression_bound(&p.statement.lower_bound, site, &bindings)?;
        if bindings
            .insert(p.statement.name.id, "_prefix".into())
            .is_some()
        {
            return Err(general_error("CaptureIdentity"));
        }
        let body = self.compile_general_recursive_body(
            &p.statement.cases,
            &p.case_checks,
            site,
            &bindings,
        )?;
        Ok((
            measure,
            lower,
            format!("(fun (_input : M.Value) => {domain})"),
            body,
        ))
    }

    pub(super) fn compile_general_recursive_raw_value(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        parent: &SourcePosition<'_>,
        outer: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        let scope = SourcePosition::new(Some(parent), SourceOwner::RecursiveFunction(p), 7);
        let (domain, output, _) =
            self.compile_function_signature_value_parts(&recursive_signature(p), &scope, outer)?;
        let (measure, lower, recursive_domain, body) =
            self.compile_general_recursive_value_parts(p, &scope, outer)?;
        let rank = format!("(fun (_input : M.Value) => (Litex.NativeBridge.integerValue (M := M) {measure} - Litex.NativeBridge.integerValue (M := M) {lower}).toNat)");
        Ok(format!("(show M.Value from by classical exact Litex.FunctionSemantics.graphValue (M := M) {domain} {output} (Litex.RecursiveFn.valueOf {output} {rank} {recursive_domain} (fun (_input _prefix : M.Value) => {body})))"))
    }

    fn compile_general_recursive_head(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        input: &str,
        member: &str,
        scope: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let signature = recursive_signature(p);
        let introduction = &p.binder_introduction;
        self.validate_parameter_store_capture(&introduction.defined_params)?;
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
            .collect::<Vec<_>>();
        if parameters.len() != introduction.defined_params.store_and_infer_results.len()
            || signature.dom_facts.len() != introduction.assumed_dom_facts.len()
        {
            return Err(general_error("BinderCapture"));
        }
        let values = self.compile_function_packed_values(&signature, input)?;
        let formed = SourcePosition {
            before: 1,
            ..*scope
        };
        let mut lines = vec![format!("obtain ⟨_input_members, _input_guards⟩ := (Litex.SetSemantics.sep_members (M := M) _ _ _).mp {member}")];
        let positive = self.compile_function_positive_inputs(&signature, &formed)?;
        let guards = positive.len() + signature.dom_facts.len();
        for (i, ((param, carrier), store)) in parameters
            .iter()
            .zip(&introduction.defined_params.store_and_infer_results)
            .enumerate()
        {
            let fact = self.resolve_fact(store.primary_fact_id(), &formed)?;
            if !matches!(&fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element==Obj::Identifier(IdentifierObj::from_bound_name(param)) && f.set==**carrier)
            {
                return Err(general_error("ParameterSubject"));
            }
            self.validate_store(&store.store, &fact)?;
            let raw = format!("_raw_i{}", param.id.value());
            let h = format!("h_{}", store.primary_fact_id().value());
            let member = if values.len() == 1 {
                "_input_members".into()
            } else {
                format!("(by have _coordinate := Litex.FiniteFunction.coordinate_mem _input_members ({i} : Fin {}); norm_num [Litex.FiniteFunction.index] at _coordinate; exact _coordinate)",values.len())
            };
            let member = if let Some(index) = positive.iter().position(|id| id == &param.id) {
                format!(
                    "((Litex.positiveReal_members (M := M) {raw}).mpr ⟨{member}, {}⟩)",
                    conjunction_projection("_input_guards", index, guards)
                )
            } else {
                member
            };
            lines.push(format!("let {raw} : M.Value := {}", values[i]));
            lines.push(format!(
                "have {h} : M.mem {raw} {} := {member}",
                self.compile_function_raw_expression_bound(carrier, &formed, &HashMap::new())?
            ));
            lines.push(format!(
                "let _value_i{} := Litex.semanticObject (M := M) {raw} (M.member_isSet {h})",
                param.id.value()
            ));
            let prop = self.fact_proposition(&fact, &formed)?;
            lines.push(format!("have {h} : {prop} := {h}"));
            lines.extend(self.compile_parameter_inferences(store, &fact, &(prop, h), &formed)?);
        }
        for (index, (source, store)) in signature
            .dom_facts
            .iter()
            .zip(&introduction.assumed_dom_facts)
            .enumerate()
        {
            let fact = function_guard_fact(source)?;
            self.validate_store(&store.store, &fact)?;
            let h = format!("h_{}", store.primary_fact_id().value());
            let prop = self.fact_proposition(&fact, &formed)?;
            lines.push(format!(
                "have {h} : {prop} := {}",
                conjunction_projection("_input_guards", positive.len() + index, guards)
            ));
            lines.extend(self.compile_stored_inferences(store, &fact, &(prop, h), &formed)?);
        }
        Ok(lines)
    }

    fn compile_general_recursive_formation(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        scope: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut lines = vec!["intro _input _input_member".into()];
        lines.extend(self.compile_general_recursive_head(p, "_input", "_input_member", scope)?);
        for (i, (object, checked)) in [
            (&p.statement.measure, &p.measure_well_defined),
            (&p.statement.lower_bound, &p.lower_bound_well_defined),
        ]
        .into_iter()
        .enumerate()
        {
            self.compile_wd(
                success_object_wd(checked, object)?,
                &SourcePosition {
                    before: i + 1,
                    ..*scope
                },
            )?;
        }
        let mut proofs = Vec::new();
        for (i, checked) in [&p.measure_in_z, &p.lower_in_z, &p.measure_ge_lower]
            .into_iter()
            .enumerate()
        {
            let fact = source_subject(checked)?;
            let valid = if i < 2 {
                matches!(&fact,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element==*if i==0 {&p.statement.measure}else{&p.statement.lower_bound} && f.set==Obj::StandardSet(StandardSet::Z))
            } else {
                matches!(&fact,Fact::AtomicFact(AtomicFact::GreaterEqualFact(f)) if f.left==p.statement.measure && f.right==p.statement.lower_bound)
            };
            if !valid {
                return Err(general_error("FormationSubject"));
            }
            let site = SourcePosition {
                before: i + 3,
                ..*scope
            };
            let term = self.compile_verify(checked, &site)?;
            lines.push(self.emit_internal_fact(&fact, &term, &site)?);
            proofs.push(format!("h_{}", fact.fact_id().value()));
        }
        lines.push(format!("exact ⟨{}⟩", proofs.join(", ")));
        Ok(lean_by(lines))
    }

    fn compile_general_recursive_domain(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        restricted: &FnSet,
        scope: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let signature = recursive_signature(p);
        let positive = self
            .compile_function_positive_inputs(&signature, scope)?
            .len();
        let original = positive + signature.dom_facts.len();
        let count = positive + restricted.dom_facts.len();
        let original_guard = and_intro(
            (0..original)
                .map(|i| conjunction_projection("_next_guards", i, count))
                .collect(),
        );
        let lower_guard = if count == original + 3 {
            conjunction_projection("_next_guards", original + 2, count)
        } else {
            let lower = self.compile_function_raw_expression_bound(
                &p.statement.lower_bound,
                scope,
                &HashMap::new(),
            )?;
            format!("(by refine ⟨(Litex.NativeBridge.integerValue (M := M) {lower} : ℝ), (Litex.NativeBridge.integerValue (M := M) {lower} : ℝ), ?_, ?_, le_rfl⟩ <;> simpa only [Complex.ofReal_intCast] using Litex.NativeBridge.integerValue_spec (M := M) {lower} _current.2.1)")
        };
        Ok(lean_by(vec![
            "intro _input _next _input_member _next_member".into(),
            "have _current := _formation _input _input_member".into(),
            "obtain ⟨_next_members, _next_guards⟩ := (Litex.SetSemantics.sep_members (M := M) _ _ _).mp _next_member".into(),
            format!("have _next_domain : M.mem _next _signature.domain := (Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨_next_members, {original_guard}⟩"),
            "have _next_formation := _formation _next _next_domain".into(),
            format!("exact ⟨_next_domain, Litex.NativeBridge.integerRank_decreases _ _ _ _ _current.1 _current.2.1 _next_formation.1 _next_formation.2.1 {} _next_formation.2.2 {lower_guard}⟩",conjunction_projection("_next_guards",original,count)),
        ]))
    }

    fn compile_general_recursive_branches(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        scope: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let mut common =
            self.compile_general_recursive_head(p, "_input", "_input_member", scope)?;
        let self_fact = self.resolve_fact(p.restricted_self_membership.primary_fact_id(), scope)?;
        common.push(format!("let _object_i{} := Litex.semanticObject (M := M) _prefix (M.member_isSet _prefix_member)",p.statement.name.id.value()));
        common.push(format!(
            "have h_{} : {} := _prefix_member",
            self_fact.fact_id().value(),
            self.fact_proposition(&self_fact, scope)?
        ));
        common.extend(self.compile_recursive_formation_checks(p, scope)?);
        let mut returned = vec!["intro _input _prefix _input_member _prefix_member".into()];
        let mut congruent =
            vec!["intro _input _prefix _other_prefix _input_member _prefix_member _agree".into()];
        returned.extend(common.clone());
        congruent.extend(common);
        let mut bindings: HashMap<_, _> = p
            .statement
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .map(|p| (p.id, format!("_raw_i{}", p.id.value())))
            .collect();
        bindings.insert(p.statement.name.id, "_prefix".into());
        let mut other = bindings.clone();
        other.insert(p.statement.name.id, "_other_prefix".into());
        let body = self.compile_general_recursive_body(
            &p.statement.cases,
            &p.case_checks,
            scope,
            &bindings,
        )?;
        let other_body =
            self.compile_general_recursive_body(&p.statement.cases, &p.case_checks, scope, &other)?;
        returned.push(format!("change M.mem {body} _signature.output"));
        congruent.push(format!("change {body} = {other_body}"));
        let completed = SourcePosition {
            before: 8,
            ..*scope
        };
        let (case_returns, case_congruence) = self.compile_recursive_case_tree(
            p,
            &p.statement.cases,
            &p.case_checks,
            &completed,
            &bindings,
        )?;
        returned.extend(case_returns);
        congruent.extend(case_congruence);
        Ok((lean_by(returned), lean_by(congruent)))
    }

    pub(super) fn compile_general_recursive_congruence(
        &self,
        object: &Obj,
        p: &ExecHaveFnByInducStmtSuccessResult,
        site: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        if !self.recursive_body_uses_self(object, p, site)? {
            let value = self.compile_function_raw_expression_bound(object, site, bindings)?;
            return Ok(format!("(show {value} = {value} from rfl)"));
        }
        // This is the same proof-independent constructor catalog used by
        // ordinary equality compilation. It fixes both denotation and child
        // order; recursive leaves still consume their original restricted WD.
        if let Some((operation, children)) = arithmetic_constructor_pairs(object, object) {
            let operation = arithmetic_operation_term(operation);
            let equalities = children
                .iter()
                .map(|(child, _)| {
                    self.compile_general_recursive_congruence(child, p, site, bindings)
                })
                .collect::<Result<Vec<_>, _>>()?;
            return curried_value_congruence(&operation, &equalities);
        }
        match object {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(function)) => {
                self.compile_recursive_literal_congruence(object, function, p, site, bindings)
            }
            Obj::FnObj(call) => {
                self.compile_recursive_application_congruence(object, call, p, site, bindings)
            }
            _ => Err(LeanCompileError::unsupported(
                "RecursiveGeneral/CongruenceObject",
            )),
        }
    }

    /// Replay the exact restricted-self call. Consumers may use its original
    /// domain premises for the full graph, but must still check both decrease premises.
    pub(super) fn compile_recursive_call_arguments(
        &self,
        object: &Obj,
        p: &ExecHaveFnByInducStmtSuccessResult,
        wd: &ObjWellDefinedProof,
        owner: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        if !matches!(object, Obj::FnObj(call) if call.body.len() == 1) {
            return Err(general_error("CallSelfEvidence"));
        }
        self.compile_recursive_call_prefix_arguments(object, p, wd, owner)
    }

    /// The first application owns the recursive decrease; later applications
    /// retain their own recorded return-interface and argument obligations.
    pub(super) fn compile_recursive_call_prefix_arguments(
        &self,
        object: &Obj,
        p: &ExecHaveFnByInducStmtSuccessResult,
        wd: &ObjWellDefinedProof,
        owner: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        ensure_object(object, wd)?;
        let Obj::FnObj(call) = object else {
            return Err(general_error("CallWD"));
        };
        if !matches!(call.head.as_ref(), FnObjHead::Identifier(identifier) if self.recursive_identifier_is_self(identifier, p, owner)?)
            || call.body.is_empty()
        {
            return Err(general_error("CallSelfEvidence"));
        }
        let arguments = &call.body[0];
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(evidence),
            ..
        } = wd.detailed_ref()
        else {
            return Err(general_error("CallWD"));
        };
        let Some(FnObjDomainFnSetEvidence::InFunctionSet {
            fact_id,
            fn_set,
            function_equal,
        }) = &evidence.domain_fn_set
        else {
            return Err(general_error("CallSelfEvidence"));
        };
        let restricted = self.recursive_restricted_signature(p, owner)?;
        let total_args = call.body.iter().map(Vec::len).sum::<usize>();
        let first_requirements = arguments.len() + restricted.dom_facts.len();
        if *fact_id != p.restricted_self_membership.primary_fact_id()
            || !function_equal.path.is_empty()
            || fn_set != &restricted
            || evidence.child_obj_well_defined.len() != total_args
            || evidence.requirement_fact_verified.len() < first_requirements
            || (call.body.len() == 1
                && evidence.requirement_fact_verified.len() != first_requirements)
        {
            return Err(general_error("CallSelfEvidence"));
        }
        if call.body.len() > 1 {
            // This checks the entire original flat WD record, including each
            // returned callable interface, before exposing its first prefix.
            self.compile_wd(wd, owner)?;
        }
        let parameters = restricted
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
            .collect::<Vec<_>>();
        if parameters.len() != arguments.len() {
            return Err(general_error("CallParameterArity"));
        }
        let substitution = parameters
            .iter()
            .zip(arguments)
            .map(|((p, _), a)| (p.id, a.as_ref().clone()))
            .collect::<HashMap<_, _>>();
        let cursor = SourcePosition::new(Some(owner), SourceOwner::WD(wd), 0);
        let mut terms = Vec::new();
        let mut proofs = Vec::new();
        for (i, (arg, child)) in arguments
            .iter()
            .zip(&evidence.child_obj_well_defined)
            .enumerate()
        {
            ensure_object(arg, child)?;
            terms.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: i,
                    ..cursor
                },
            )?);
        }
        for (i, checked) in evidence
            .requirement_fact_verified
            .iter()
            .take(first_requirements)
            .enumerate()
        {
            let actual = source_subject(checked)?;
            let valid = if i < arguments.len() {
                matches!(&actual, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == arguments[i].ir()
                    && instantiated_object_matches(parameters[i].1, &f.set, &substitution))
            } else {
                instantiated_fact_matches(
                    &function_guard_fact(&restricted.dom_facts[i - arguments.len()])?,
                    &actual,
                    &substitution,
                )
            };
            if !valid {
                return Err(general_error("CallRequirementSubject"));
            }
            proofs.push(
                self.compile_verify(
                    checked,
                    &SourcePosition {
                        before: total_args + i,
                        ..cursor
                    },
                )?
                .1,
            );
        }
        Ok((terms, proofs))
    }

    pub(super) fn compile_general_recursive_domain_member(
        &self,
        signature: &FnSet,
        objects: &[String],
        requirements: &[String],
        site: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (members, guard) =
            self.compile_function_domain_certificates(signature, objects, requirements, site)?;
        let values = objects
            .iter()
            .map(|o| format!("(Litex.denote {o})"))
            .collect::<Vec<_>>();
        let packed = if values.len() == 1 {
            values[0].clone()
        } else {
            format!(
                "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
                values.join(", ")
            )
        };
        let base_member = if values.len() == 1 {
            members[0].clone()
        } else {
            let sets = if Self::function_uses_numeric_interface(signature) {
                let mut d = self.compile_function_domains(signature, site)?;
                d.pop();
                d.into_iter()
                    .map(|v| format!("M.standard {v}"))
                    .collect::<Vec<_>>()
            } else {
                self.compile_function_input_sets(signature, site)?
                    .iter()
                    .map(|s| format!("Litex.denote {s}"))
                    .collect()
            };
            format!(
                "(Litex.FiniteFunction.tuple_inCart ![{}] ![{}] {})",
                values.join(", "),
                sets.join(", "),
                finite_vector_proof(&members)
            )
        };
        let template = self.compile_function_guard_template(signature, site)?;
        let equality = self.compile_function_packed_application_equality(&template, &values)?;
        let proof=format!("(Litex.SetSemantics.sep_members (M := M) _ _ _).mpr ⟨{base_member}, Eq.mpr {equality} ({guard} : {template} {})⟩",values.join(" "));
        Ok((packed, format!("({proof})")))
    }

    pub(super) fn compile_recursive_published_conclusion(
        &self,
        declaration: &ExecHaveFnByInducStmtSuccessResult,
        source: &ForallFact,
        site: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some(index) = declaration
            .store_and_infer_result
            .case_defining_fact_ids
            .iter()
            .position(|id| *id == source.fact_id)
        else {
            return Ok(None);
        };
        self.validate_store(
            &declaration.store_and_infer_result.case_defining[index].store,
            &Fact::ForallFact(source.clone()),
        )?;
        let [ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))] =
            source.then_facts.as_slice()
        else {
            return Err(general_error("EquationConclusion"));
        };
        let paths = recursive_leaf_paths(&declaration.statement.cases);
        let path = paths
            .get(index)
            .ok_or_else(|| general_error("EquationPath"))?;
        let scope = SourcePosition::new(Some(site), SourceOwner::RecursiveFunction(declaration), 8);
        let left = self.compile_function_raw_expression_bound(&eq.left, &scope, bindings)?;
        let right = self.compile_recursive_leaf_value(
            &declaration.statement.cases,
            &declaration.case_checks,
            path,
            &scope,
            bindings,
        )?;
        Ok(Some(format!("{left} = {right}")))
    }

    fn compile_general_recursive_equation(
        &self,
        p: &ExecHaveFnByInducStmtSuccessResult,
        path: &[usize],
        store: &StoreFactAndInferResult,
        object: &str,
        site: &SourcePosition<'_>,
        parent: &SourcePosition<'_>,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let source = self.resolve_fact(store.primary_fact_id(), site)?;
        self.validate_store(&store.store, &source)?;
        let Fact::ForallFact(fact) = &source else {
            return Err(general_error("EquationFamily"));
        };
        let signature = recursive_signature(p);
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
            .collect::<Vec<_>>();
        let actual = fact
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        if parameters.len() != actual.len()
            || parameters
                .iter()
                .zip(actual)
                .any(|((p, c), (q, t))| p.id != q.id || !matches!(t,ParamType::Obj(d) if *c==d))
        {
            return Err(general_error("EquationParameters"));
        }
        let expected = signature
            .dom_facts
            .iter()
            .map(function_guard_fact)
            .collect::<Result<Vec<_>, _>>()?;
        let guards = recursive_path_guards(&p.statement.cases, path)?;
        let (merged_guard, original_domains) = fact
            .dom_facts
            .split_last()
            .ok_or_else(|| general_error("EquationPremises"))?;
        if original_domains != expected || fact.then_facts.len() != 1 {
            return Err(general_error("EquationPremises"));
        }
        if guards.len() == 1 {
            if *merged_guard != and_chain_as_fact(guards[0]) {
                return Err(general_error("EquationPremises"));
            }
        } else {
            let source_atoms = guards
                .iter()
                .map(|g| recursive_guard_atoms(&and_chain_as_fact(g)))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            let actual_atoms = recursive_guard_atoms(merged_guard)?;
            if source_atoms.len() != actual_atoms.len()
                || source_atoms
                    .iter()
                    .zip(&actual_atoms)
                    .any(|(a, b)| a.ir() != b.ir())
            {
                return Err(general_error("EquationPathGuard"));
            }
        }
        let conclusion: Fact = fact.then_facts[0].clone().into();
        let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = &conclusion else {
            return Err(general_error("EquationConclusion"));
        };
        let mut cases = p.statement.cases.as_slice();
        let mut leaf = None;
        for index in path {
            let case = &cases[*index];
            match &case.body {
                HaveFnByInducCaseBody::EqualTo(body) => leaf = Some(body),
                HaveFnByInducCaseBody::NestedCases(children) => cases = children,
            }
        }
        let body = leaf.ok_or_else(|| general_error("EquationBody"))?;
        let expected = parent.defining_identifier(&p.statement.name, &self.runtime)?;
        let self_binding =
            HashMap::from([(p.statement.name.id, Obj::Identifier(expected.clone()))]);
        if !instantiated_object_matches(body, &eq.right, &self_binding)
            || !matches!(&eq.left,Obj::FnObj(call) if matches!(call.head.as_ref(),FnObjHead::Identifier(identifier) if identifier == &expected) && call.body.len()==1 && call.body[0].len()==parameters.len() && call.body[0].iter().zip(&parameters).all(|(a,(p,_))|a.as_ref()==&Obj::Identifier(IdentifierObj::from_bound_name(p))))
        {
            return Err(general_error("EquationBody"));
        }
        let mut bindings =
            HashMap::from([(p.statement.name.id, format!("(Litex.denote {object})"))]);
        let mut binders = Vec::new();
        let mut intros = Vec::new();
        let mut objects = Vec::new();
        let mut requirements = Vec::new();
        for ((param, carrier), store) in parameters
            .iter()
            .zip(&p.binder_introduction.defined_params.store_and_infer_results)
        {
            let id = param.id.value();
            let name = format!("_value_i{id}");
            let h = format!("h_{}", store.primary_fact_id().value());
            let raw = format!("(Litex.denote {name})");
            if local {
                binders.push(format!("({name} : Litex.Obj (M := M) M.Value)"));
            } else {
                binders.push(format!("{{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({name} : Litex.Obj (M := M) _Host_i{id})"));
                intros.extend([format!("_Host_i{id}"), format!("_rep_i{id}")]);
            }
            binders.push(format!(
                "({h} : M.mem {raw} {})",
                self.compile_function_raw_expression_bound(carrier, site, &bindings)?
            ));
            intros.extend([name.clone(), h.clone()]);
            objects.push(name);
            requirements.push(h);
            bindings.insert(param.id, raw);
        }
        for dom in &fact.dom_facts {
            let h = format!("h_{}", dom.fact_id().value());
            binders.push(format!(
                "({h} : {})",
                self.compile_function_raw_predicate(dom, site, &bindings)?
            ));
            intros.push(h.clone());
            requirements.push(h);
        }
        let case_guard = requirements.pop().unwrap();
        let (packed, domain) = self.compile_general_recursive_domain_member(
            &signature,
            &objects,
            &requirements,
            site,
        )?;
        let mut lines = vec![
            "classical".into(),
            format!("intro {}", intros.join(" ")),
            format!(
                "have _case_domain : M.mem {packed} ({object}).val.signature.domain := {domain}"
            ),
            format!("refine (Litex.recursiveFn_equation {object} {packed} _case_domain).trans ?_"),
        ];
        // The equation already binds the original objects. Replay their stored
        // inferences without rebinding them to unpacked coordinates.
        let introduced = SourcePosition::new(Some(parent), SourceOwner::RecursiveFunction(p), 1);
        let mut inferences = Vec::new();
        for store in &p.binder_introduction.defined_params.store_and_infer_results {
            let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
            let member = (
                self.fact_proposition(&fact, &introduced)?,
                format!("h_{}", store.primary_fact_id().value()),
            );
            inferences.extend(self.compile_parameter_inferences(
                store,
                &fact,
                &member,
                &introduced,
            )?);
        }
        for (dom, store) in signature
            .dom_facts
            .iter()
            .zip(&p.binder_introduction.assumed_dom_facts)
        {
            let fact = function_guard_fact(dom)?;
            let member = (
                self.fact_proposition(&fact, &introduced)?,
                format!("h_{}", store.primary_fact_id().value()),
            );
            inferences.extend(self.compile_stored_inferences(
                store,
                &fact,
                &member,
                &introduced,
            )?);
        }
        lines.splice(lines.len() - 1..lines.len() - 1, inferences);
        let packed_values = self.compile_function_packed_values(&signature, &packed)?;
        let mut packed_bindings = bindings.clone();
        for ((param, _), value) in parameters.iter().zip(&packed_values) {
            packed_bindings.insert(param.id, value.clone());
        }
        let scope = SourcePosition::new(Some(parent), SourceOwner::RecursiveFunction(p), 8);
        let raw_body = self.compile_general_recursive_body(
            &p.statement.cases,
            &p.case_checks,
            &scope,
            &packed_bindings,
        )?;
        let leaf = self.compile_recursive_leaf_value(
            &p.statement.cases,
            &p.case_checks,
            path,
            &scope,
            &bindings,
        )?;
        lines.push(format!("change {raw_body} = {leaf}"));
        // Decode the packed argument once, before selecting the recorded case.
        for law in self.compile_function_packed_reduction_laws(
            &objects
                .iter()
                .map(|o| format!("(Litex.denote {o})"))
                .collect::<Vec<_>>(),
        )? {
            lines.push(format!("rw [{law}]"));
        }
        // Select the exact original root-to-leaf path using its disjointness proofs.
        lines.extend(self.compile_recursive_equation_path(
            &p.statement.cases,
            &p.case_checks,
            path,
            &case_guard,
            recursive_guard_atoms(merged_guard)?.len(),
            0,
            &bindings,
            &scope,
        )?);
        let keyword = if local { "have" } else { "theorem" };
        let context = if local {
            String::new()
        } else {
            self.context_header(parent)?
        };
        Ok(format!(
            "{keyword} h_{}{context} : ∀ {}, {} := {}",
            fact.fact_id.value(),
            binders.join(" "),
            format!(
                "{} = {leaf}",
                self.compile_function_raw_expression_bound(&eq.left, site, &bindings)?
            ),
            lean_by(lines)
        ))
    }
}

pub(super) fn general_error(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("RecursiveGeneral/{stage}"),"The original recursive declaration, ordered guards, call WD or branch stores differ from the captured result.")
}

pub(super) fn lean_by(lines: Vec<String>) -> String {
    format!("(by\n  {})", lines.join("\n").replace('\n', "\n  "))
}

pub(super) fn and_intro(terms: Vec<String>) -> String {
    terms
        .into_iter()
        .rev()
        .reduce(|tail, head| format!("⟨{head}, {tail}⟩"))
        .unwrap_or_else(|| "True.intro".into())
}
