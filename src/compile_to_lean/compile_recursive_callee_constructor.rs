use super::compile_function_template::function_guard_fact;
use super::compile_have_fn_by_induc_result::recursive_signature;
use super::compile_real_set_bounds::contains_parameter;
use super::compile_recursive_case_tree::{
    recursive_guard_atoms, recursive_leaf_paths, recursive_path_guards,
};
use super::helper::*;
use super::source_position::{visit_complete_wd, SourceConstructor, SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::execute::ExecHaveFnByInducStmtSuccessResult;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// Instantiate a constructor in the exact cited recursive equation. Its
    /// original case WD belongs to the restricted self, not the completed graph.
    pub(super) fn compile_recursive_callee_constructor(
        &self,
        source: &ForallFact,
        then_index: usize,
        pattern: &Obj,
        application: &SearchProofByKnownForallFact,
        caller: &SourcePosition<'_>,
        observe_numeric: bool,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some(ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))) =
            source.then_facts.get(then_index)
        else {
            return Ok(None);
        };
        let Obj::FnObj(call) = &eq.left else {
            return Ok(None);
        };
        let FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) = call.head.as_ref() else {
            return Ok(None);
        };
        let Ok((body, producer, _)) = caller.visible_recursive_function(id) else {
            return Ok(None);
        };
        let Some(index) = body
            .store_and_infer_result
            .case_defining_fact_ids
            .iter()
            .position(|f| *f == source.fact_id)
        else {
            return Ok(None);
        };
        let store = &body.store_and_infer_result.case_defining[index];
        self.validate_store(&store.store, &Fact::ForallFact(source.clone()))?;
        let signature = recursive_signature(body);
        let expected = signature
            .dom_facts
            .iter()
            .map(function_guard_fact)
            .collect::<Result<Vec<_>, _>>()?;
        let (merged_guard, domains) = source
            .dom_facts
            .split_last()
            .ok_or_else(|| recursive_callee_error("Header"))?;
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, g.param_type.as_ref())))
            .collect::<Vec<_>>();
        let declared = source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
            .collect::<Vec<_>>();
        if then_index != 0
            || source.then_facts.len() != 1
            || domains != expected
            || parameters.len() != declared.len()
            || parameters
                .iter()
                .zip(&declared)
                .any(|((p, c), (q, t))| p.id != q.id || !matches!(t, ParamType::Obj(d) if *c == d))
        {
            return Err(recursive_callee_error("Header"));
        }
        let paths = recursive_leaf_paths(&body.statement.cases);
        let path = paths
            .get(index)
            .ok_or_else(|| recursive_callee_error("Path"))?;
        let guards = recursive_path_guards(&body.statement.cases, path)?;
        let atoms = guards
            .iter()
            .map(|g| recursive_guard_atoms(&and_chain_as_fact(g)))
            .collect::<Result<Vec<_>, _>>()?;
        let actual = recursive_guard_atoms(merged_guard)?;
        if !atoms
            .iter()
            .flatten()
            .map(|a| a.ir())
            .eq(actual.iter().map(|a| a.ir()))
        {
            return Err(recursive_callee_error("Guard"));
        }
        let recursion =
            SourcePosition::new(Some(&producer), SourceOwner::RecursiveFunction(body), 1);
        self.validate_parameter_store_capture(&body.binder_introduction.defined_params)?;
        if parameters.len()
            != body
                .binder_introduction
                .defined_params
                .store_and_infer_results
                .len()
            || domains.len() != body.binder_introduction.assumed_dom_facts.len()
        {
            return Err(recursive_callee_error("Binders"));
        }
        let mut binders = Vec::new();
        let mut definitions = Vec::new();
        let mut objects = Vec::new();
        let mut requirements = Vec::new();
        for ((parameter, carrier), store) in parameters.iter().zip(
            &body
                .binder_introduction
                .defined_params
                .store_and_infer_results,
        ) {
            binders.extend(
                self.introduce_member_parameter(parameter, carrier, store, &recursion)?
                    .0,
            );
            let fact = self.resolve_fact(store.primary_fact_id(), &recursion)?;
            let member = (
                self.fact_proposition(&fact, &recursion)?,
                format!("h_{}", fact.fact_id().value()),
            );
            definitions
                .extend(self.compile_parameter_inferences(store, &fact, &member, &recursion)?);
            objects.push(format!("_value_i{}", parameter.id.value()));
            requirements.push(member.1);
        }
        for (fact, store) in domains
            .iter()
            .zip(&body.binder_introduction.assumed_dom_facts)
        {
            self.validate_store(&store.store, fact)?;
            let member = (
                self.fact_proposition(fact, &recursion)?,
                format!("h_{}", fact.fact_id().value()),
            );
            binders.push(format!("({} : {})", member.1, member.0));
            definitions.extend(self.compile_stored_inferences(store, fact, &member, &recursion)?);
            requirements.push(member.1);
        }
        definitions.extend(self.compile_recursive_formation_checks(body, &recursion)?);
        let formed = SourcePosition {
            before: 8,
            ..recursion
        };
        let guard_name = format!("h_{}", merged_guard.fact_id().value());
        binders.push(format!(
            "({guard_name} : {})",
            self.compile_function_raw_predicate(merged_guard, &formed, &HashMap::new())?
        ));
        let mut offset = 0;
        let guard_proofs = atoms
            .iter()
            .map(|atoms| {
                let proof = super::compile_general_recursive_result::and_intro(
                    (offset..offset + atoms.len())
                        .map(|i| conjunction_projection(&guard_name, i, actual.len()))
                        .collect(),
                );
                offset += atoms.len();
                proof
            })
            .collect::<Vec<_>>();
        self.visit_recursive_case_wd(&body.statement.cases, &body.case_checks, path, &guard_proofs, &formed, definitions,
            &mut |root, _, branch, definitions| {
                visit_complete_wd(root, branch, &mut |constructor, site| {
                    let SourceConstructor::Checked(wd) = constructor else { return Ok(None) };
                    if wd.obj().ir() != pattern.ir() { return Ok(None) }
                    if !contains_parameter(pattern, body.statement.name.id) {
                        return self.apply_callee_constructor(source, wd, site, application, caller, observe_numeric, binders.clone(), definitions.clone()).map(Some);
                    }
                    let function = self.compile_object_reference(&Obj::Identifier(IdentifierObj::from_bound_name(&body.statement.name)), caller)?;
                    let mut bindings = parameters.iter().zip(&objects).map(|((p, _), o)| (p.id, format!("(Litex.denote {o})"))).collect::<HashMap<_, _>>();
                    let mut locals = definitions.clone();
                    if self.recursive_uses_nat_representation(body, &producer)? {
                        locals.extend(self.compile_recursive_nat_callee_prefix(body, site, &function, &objects[0], &requirements[0])?);
                    } else {
                        let (input, input_member) = self.compile_general_recursive_domain_member(&signature, &objects, &requirements, site)?;
                        let restricted = self.recursive_restricted_signature(body, site)?;
                        let mut packed = bindings.clone();
                        for ((p, _), raw) in parameters.iter().zip(self.compile_function_packed_values(&signature, "_callee_input")?) { packed.insert(p.id, raw); }
                        let (packed_domain, output, _) = self.compile_function_signature_value_parts(&restricted, site, &packed)?;
                        let laws = self.compile_function_packed_reduction_laws(&objects.iter().map(|o| format!("(Litex.denote {o})")).collect::<Vec<_>>())?;
                        let reductions = laws.iter().map(|law| format!("rw [{law}]")).collect::<Vec<_>>().join("\n");
                        let self_fact = self.resolve_fact(body.restricted_self_membership.primary_fact_id(), site)?;
                        let self_prop = self.fact_proposition(&self_fact, site)?;
                        // The restriction is taken only after the recursive graph
                        // has been certified. Original call WD still proves that
                        // each accessed argument belongs to this restricted domain.
                        locals.extend([
                            format!("let _complete_fn := {function}"),
                            format!("let _callee_input := {input}"),
                            format!("have _callee_domain : M.mem _callee_input _complete_fn.val.signature.domain := {input_member}"),
                            "let _prefix := _complete_fn.val.prefixGraph _callee_input _complete_fn.val.value".into(),
                            "have _prefix_returns : ∀ y, M.mem y (_complete_fn.val.recursiveDomain _callee_input) → M.mem (_complete_fn.val.value y) _complete_fn.val.signature.output := fun y hy => _complete_fn.val.value_mem _complete_fn.wd y (_complete_fn.wd.domainSound _callee_input y _callee_domain hy).1".into(),
                            "have _prefix_member := Litex.FunctionSemantics.graph_inFnSet _ _ _ _prefix_returns".into(),
                            format!("let _object_i{} := Litex.semanticObject (M := M) _prefix (M.member_isSet _prefix_member)", body.statement.name.id.value()),
                            format!("have h_{} : {self_prop} := by\n  have _h : M.mem _prefix (Litex.FunctionSemantics.fnSetValue (M := M) {packed_domain} {output}) := _prefix_member\n  {}\n  exact _h", self_fact.fact_id().value(), laws.iter().map(|law| format!("rw [{law}] at _h")).collect::<Vec<_>>().join("\n  ")),
                            "let _other_prefix := Litex.denote _complete_fn".into(),
                        ]);
                        let (domain, _, _) = self.compile_function_signature_value_parts(&restricted, site, &bindings)?;
                        locals.push(format!("have _agree : ∀ y, M.mem y {domain} → Litex.FunctionSemantics.callValue (M := M) _prefix y = Litex.FunctionSemantics.callValue (M := M) _other_prefix y := by\n  intro y hy\n  have _hy : M.mem y (_complete_fn.val.recursiveDomain _callee_input) := by\n    change M.mem y {packed_domain}\n    {}\n    exact hy\n  exact (Litex.FunctionSemantics.call_graphValue _ _ _ _prefix_returns y _hy).trans (_complete_fn.val.call_graph _complete_fn.wd y (_complete_fn.wd.domainSound _callee_input y _callee_domain _hy).1).symm", reductions.replace('\n', "\n    ")));
                    }
                    let constructor = self.compile_wd(wd, site)?;
                    // Congruence follows the original branch's completed WD.
                    // The visitor itself points before the selected constructor.
                    let completed = SourcePosition { before: 2, ..*branch };
                    bindings.insert(body.statement.name.id, "_prefix".into());
                    let equality = self.compile_general_recursive_congruence(pattern, body, &completed, &bindings)?;
                    bindings.insert(body.statement.name.id, "_other_prefix".into());
                    let value = self.compile_function_raw_expression_bound(pattern, site, &bindings)?;
                    locals.push(format!("let _original_constructor := {constructor}"));
                    locals.push(format!("have _constructor_equal : Litex.denote _original_constructor = {value} := {equality}"));
                    let term = format!("(Litex.semanticObject (M := M) {value} (Eq.mp (congrArg M.isSet _constructor_equal) (Litex.isSet _original_constructor)))");
                    let term = if observe_numeric {
                        let (numeric, denotation, member, _) = self.numeric_wd(wd, site)?;
                        format!("(show {{ z : ℂ // {value} = M.number z ∧ M.mem {value} (M.standard .complex) }} from ⟨{numeric}, _constructor_equal.symm.trans {denotation}, Eq.mp (congrArg (fun z => M.mem z (M.standard .complex)) _constructor_equal) {member}⟩)")
                    } else { term };
                    let scoped = self.scope_proposition(term, &locals);
                    let scoped = if observe_numeric {
                        // State the dependent observation type outside the
                        // local prefix proofs, so its result cannot capture them.
                        bindings.insert(body.statement.name.id, format!("(Litex.denote {function})"));
                        let public_value = self.compile_function_raw_expression_bound(pattern, site, &bindings)?;
                        format!("(show {{ z : ℂ // {public_value} = M.number z ∧ M.mem {public_value} (M.standard .complex) }} from {scoped})")
                    } else { scoped };
                    self.apply_callee_body(source, application, caller, binders.clone(), scoped).map(Some)
                }, &mut |_, _| Ok(None))
            })
    }

    /// Restrict the already certified natural graph, retaining the source
    /// parameter and the original restricted membership FactId.
    fn compile_recursive_nat_callee_prefix(
        &self,
        body: &ExecHaveFnByInducStmtSuccessResult,
        site: &SourcePosition<'_>,
        function: &str,
        object: &str,
        member: &str,
    ) -> Result<Vec<String>, LeanCompileError> {
        let restricted = self.recursive_restricted_signature(body, site)?;
        let parameter = &body.statement.fn_set_clause.set_bound_parameters.groups[0].params[0];
        let mut bindings = HashMap::from([(parameter.id, format!("(Litex.denote {object})"))]);
        let (domain, output, _) =
            self.compile_function_signature_value_parts(&restricted, site, &bindings)?;
        bindings.insert(parameter.id, "(M.number (_callee_index : ℂ))".into());
        let (indexed_domain, _, _) =
            self.compile_function_signature_value_parts(&restricted, site, &bindings)?;
        let self_fact =
            self.resolve_fact(body.restricted_self_membership.primary_fact_id(), site)?;
        let self_prop = self.fact_proposition(&self_fact, site)?;
        Ok(vec![
            format!("let _complete_fn := {function}"),
            format!("let _callee_index := Litex.NativeBridge.asNat {object} {member}"),
            format!("have _index_spec : Litex.denote {object} = M.number (_callee_index : ℂ) := Litex.NativeBridge.asNat_spec {object} {member}"),
            "let _prefix := _complete_fn.val.prefixGraph _callee_index _complete_fn.val.value".into(),
            "have _prefix_returns : ∀ k, M.mem (_complete_fn.val.value k) _complete_fn.val.output := fun k => _complete_fn.val.history_mem _complete_fn.wd k k".into(),
            "have _prefix_member := _complete_fn.val.prefixGraph_mem _callee_index _complete_fn.val.value _prefix_returns".into(),
            format!("let _object_i{} := Litex.semanticObject (M := M) _prefix (M.member_isSet _prefix_member)", body.statement.name.id.value()),
            format!("have h_{} : {self_prop} := by\n  change M.mem _prefix (Litex.FunctionSemantics.fnSetValue (M := M) {domain} {output})\n  rw [_index_spec]\n  exact _prefix_member", self_fact.fact_id().value()),
            "let _other_prefix := Litex.denote _complete_fn".into(),
            format!("have _agree : ∀ y, M.mem y {domain} → Litex.FunctionSemantics.callValue (M := M) _prefix y = Litex.FunctionSemantics.callValue (M := M) _other_prefix y := by\n  intro y hy\n  have _hy : M.mem y (_complete_fn.val.prefixSignature _callee_index).domain := by\n    change M.mem y {indexed_domain}\n    rw [← _index_spec]\n    exact hy\n  have _hyN := ((Litex.FunctionSignature.oneTarget_domain .natural _complete_fn.val.output _complete_fn.val.output_isSet (_complete_fn.val.restrictedGuard _callee_index) y).mp _hy).1\n  exact (Litex.FunctionSemantics.call_graphValue _ _ _ (fun y _ => _prefix_returns (Litex.NativeBridge.naturalValue y)) y _hy).trans (_complete_fn.val.call_graph _complete_fn.wd y _hyN).symm"),
        ])
    }
}

fn recursive_callee_error(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("WD/RecursiveCallee/{stage}"))
}
