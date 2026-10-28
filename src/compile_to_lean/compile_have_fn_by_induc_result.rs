use crate::ast::stmt::HaveFnByInducCaseBody;
use crate::compile_to_lean::compile_function_template::function_guard_fact;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::{
    ExecHaveFnByInducStmtResult, ExecHaveFnByInducStmtSuccessResult, InducCaseBodySuccess,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_have_fn_by_induc_statement(
        &self,
        result: &ExecHaveFnByInducStmtResult,
        position: &SourcePosition<'_>,
        _index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/LocalDeclaration",
            ));
        }
        let ExecHaveFnByInducStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::new(
                "RecursiveFunction/Failed",
                "Failed formation is not compiler evidence.",
            ));
        };
        let signature = recursive_signature(proof);
        let parameter = self.validate_recursive_nat_shape(proof, &signature, position)?;
        let fn_set = Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone()));
        self.compile_wd(
            success_object_wd(&proof.fn_set_well_defined, &fn_set)?,
            position,
        )?;
        let scope = SourcePosition::new(Some(position), SourceOwner::RecursiveFunction(proof), 0);
        let completed = SourcePosition { before: 7, ..scope };
        let restricted = self.recursive_restricted_signature(proof, &completed)?;
        let restricted_parameter = &restricted.set_bound_parameters.groups[0].params[0];
        let mut bindings = HashMap::from([
            (parameter.id, "(M.number (_index : ℂ))".to_string()),
            (restricted_parameter.id, "_argument".to_string()),
        ]);
        let mut clauses = Vec::new();
        for clause in &restricted.dom_facts {
            clauses.push(self.compile_function_raw_predicate(
                &function_guard_fact(clause)?,
                &completed,
                &bindings,
            )?);
        }
        let guard = format!(
            "(fun (_index : ℕ) (_argument : M.Value) => {})",
            conjunction_proposition(clauses)?
        );
        let base_body = recursive_case_body(proof, 0)?;
        let step_body = recursive_case_body(proof, 1)?;
        bindings.remove(&restricted_parameter.id);
        bindings.insert(proof.statement.name.id, "_prefix".into());
        let step = format!(
            "(fun (_index : ℕ) (_prefix : M.Value) => {})",
            self.compile_function_raw_expression_bound(step_body, &completed, &bindings)?
        );
        bindings.insert(parameter.id, "(M.number 0)".into());
        let base = self.compile_function_raw_expression_bound(base_body, &completed, &bindings)?;
        let target = self.compile_object_reference(&signature.ret_set, &completed)?;
        let guard_sound = "(by\n  intro _index _argument _member _guard\n  exact Litex.NativeBridge.naturalValue_lt_number _index _argument _member _guard.1)";
        let base_proof = self.compile_recursive_case_return(proof, 0, &scope)?;
        let step_proof = self.compile_recursive_case_return(proof, 1, &scope)?;
        let congruence = self.compile_recursive_step_congruence(proof, &scope)?;
        let value = format!("(Litex.recursiveNatFnTarget (M := M) (Litex.denote {target}) (Litex.isSet {target}) {guard} {base} {step} {guard_sound} {base_proof} {step_proof} {congruence})");
        let object = Obj::Identifier(IdentifierObj::from_bound_name(&proof.statement.name));
        let declaration = self.bind_alias(
            &proof.statement.name,
            &object,
            &object,
            &value,
            false,
            position,
        )?;
        let name = self.context_application(
            &format!("_object_i{}", proof.statement.name.id.value()),
            position,
        );
        let stored = &proof.store_and_infer_result;
        if stored.membership_fact_id != stored.membership.primary_fact_id()
            || stored.case_defining_fact_ids
                != stored
                    .case_defining
                    .iter()
                    .map(|r| r.primary_fact_id())
                    .collect::<Vec<_>>()
            || stored.case_defining.len() != 2
        {
            return Err(LeanCompileError::new(
                "RecursiveFunction/StoreCapture",
                "The actual ordered stores differ from the declaration ID view.",
            ));
        }
        let mut actual_ids = stored.membership.stored_fact_ids();
        actual_ids.extend(
            stored
                .case_defining
                .iter()
                .flat_map(|r| r.stored_fact_ids()),
        );
        if actual_ids != stored.stored_fact_ids {
            return Err(LeanCompileError::new(
                "RecursiveFunction/StoreCapture",
                "The declaration has another flattened stored-ID view.",
            ));
        }
        let after_stores = SourcePosition {
            before: 8,
            ..*position
        };
        let membership = self.resolve_fact(stored.membership_fact_id, &after_stores)?;
        if !matches!(&membership, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == object.ir() && f.set == fn_set)
        {
            return Err(LeanCompileError::new(
                "RecursiveFunction/MembershipSubject",
                "The declaration's final membership has another function or signature.",
            ));
        }
        self.validate_store(&stored.membership.store, &membership)?;
        let member = (
            self.fact_proposition(&membership, &after_stores)?,
            format!("(Litex.recursiveNatFnInFnSet {name})"),
        );
        let mut declarations = vec![
            declaration,
            format!(
                "theorem h_{}{} : {} :=\n  {}",
                stored.membership_fact_id.value(),
                self.context_header(position)?,
                member.0,
                member.1
            ),
        ];
        for (index, store) in stored.case_defining.iter().enumerate() {
            declarations.push(self.compile_recursive_case_equation(
                proof,
                index,
                store,
                &name,
                &after_stores,
                position,
            )?);
        }
        Ok(declarations.join("\n"))
    }

    pub(in crate::compile_to_lean) fn compile_recursive_signature_reference(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        let Some((signature, store, producer)) = position.generated_recursive_signature(object)
        else {
            return Ok(None);
        };
        let fact = self.resolve_fact(store.primary_fact_id(), &producer)?;
        self.validate_store(&store.store, &fact)?;
        let SourceOwner::RecursiveFunction(declaration) = producer.owner else {
            unreachable!();
        };
        if self.recursive_restricted_signature(declaration, &producer)? != *signature {
            return Err(LeanCompileError::new(
                "RecursiveFunction/GeneratedSignature",
                "The generated object differs from the exact captured restricted self signature.",
            ));
        }
        Ok(Some(format!(
            "(Litex.fnSet {})",
            self.compile_fn_signature(signature, &producer)?
        )))
    }

    fn validate_recursive_nat_shape<'a>(
        &self,
        proof: &'a ExecHaveFnByInducStmtSuccessResult,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<&'a BoundName, LeanCompileError> {
        let groups = &proof.statement.fn_set_clause.set_bound_parameters.groups;
        if groups.len() != 1
            || groups[0].params.len() != 1
            || *groups[0].param_type != Obj::StandardSet(StandardSet::N)
            || !signature.dom_facts.is_empty()
            || proof.statement.cases.len() != 2
            || proof.case_checks.cases.len() != 2
        {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/UnaryNaturalCases",
            ));
        }
        let parameter = &groups[0].params[0];
        let parameter_obj = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        if proof.statement.measure != parameter_obj
            || !is_zero(&proof.statement.lower_bound)
            || !matches!(&proof.statement.cases[0].case_fact, AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f)) if f.left == parameter_obj && is_zero(&f.right))
            || !matches!(&proof.statement.cases[1].case_fact, AndChainAtomicFact::AtomicFact(AtomicFact::GreaterFact(f)) if f.left == parameter_obj && is_zero(&f.right))
        {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/ZeroSuccessorShape",
            ));
        }
        self.compile_numeric_carrier(&signature.ret_set, position)?;
        self.validate_parameter_store_capture(&proof.binder_introduction.defined_params)?;
        if proof
            .binder_introduction
            .defined_params
            .store_and_infer_results
            .len()
            != 1
            || !proof.binder_introduction.assumed_dom_facts.is_empty()
        {
            return Err(LeanCompileError::new(
                "RecursiveFunction/BinderCapture",
                "The captured introductions differ from the unary empty-domain header.",
            ));
        }
        if contains_identifier(recursive_case_body(proof, 0)?, proof.statement.name.id) {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/RecursiveBase",
            ));
        }
        Ok(parameter)
    }

    fn recursive_restricted_signature(
        &self,
        proof: &ExecHaveFnByInducStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<FnSet, LeanCompileError> {
        let store = &proof.restricted_self_membership;
        let fact = self.resolve_fact(store.primary_fact_id(), position)?;
        self.validate_store(&store.store, &fact)?;
        let Fact::AtomicFact(AtomicFact::InFact(member)) = fact else {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/SelfMembershipFamily",
            ));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = member.set else {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/SelfSignature",
            ));
        };
        let groups = &signature.set_bound_parameters.groups;
        if member.element.ir()
            != Obj::Identifier(IdentifierObj::from_bound_name(&proof.statement.name)).ir()
            || groups.len() != 1
            || groups[0].params.len() != 1
            || *groups[0].param_type != Obj::StandardSet(StandardSet::N)
            || signature.ret_set.as_ref() != &proof.statement.fn_set_clause.ret_set
            || signature.dom_facts.len() != 2
        {
            return Err(LeanCompileError::new(
                "RecursiveFunction/SelfSignature",
                "The original self membership has another declaration, domain, or target.",
            ));
        }
        let parameter = Obj::Identifier(IdentifierObj::from_bound_name(&groups[0].params[0]));
        if !matches!(&signature.dom_facts[0], QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(f)) if f.left == parameter && f.right == proof.statement.measure)
            || !matches!(&signature.dom_facts[1], QuantifierFreeFact::AtomicFact(AtomicFact::GreaterEqualFact(f)) if f.left == parameter && f.right == proof.statement.lower_bound)
        {
            return Err(LeanCompileError::new(
                "RecursiveFunction/SelfGuard",
                "The self signature must retain the exact smaller-measure and lower-bound guards.",
            ));
        }
        Ok(signature)
    }

    fn compile_recursive_parameter(
        &self,
        proof: &ExecHaveFnByInducStmtSuccessResult,
        raw: &str,
        member: &str,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let parameter = &proof.statement.fn_set_clause.set_bound_parameters.groups[0].params[0];
        let store = &proof
            .binder_introduction
            .defined_params
            .store_and_infer_results[0];
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let fact = self.resolve_fact(store.primary_fact_id(), &formed)?;
        if !matches!(&fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element == Obj::Identifier(IdentifierObj::from_bound_name(parameter)) && f.set == Obj::StandardSet(StandardSet::N))
        {
            return Err(LeanCompileError::new(
                "RecursiveFunction/ParameterSubject",
                "The retained binder membership has another source subject.",
            ));
        }
        self.validate_store(&store.store, &fact)?;
        let id = parameter.id.value();
        let h = format!("h_{}", fact.fact_id().value());
        let mut definitions = vec![
            format!("let _raw_i{id} : M.Value := {raw}"),
            format!("have {h} : M.mem _raw_i{id} (M.standard .natural) := {member}"),
            format!(
                "let _value_i{id} := Litex.semanticObject (M := M) _raw_i{id} (M.member_isSet {h})"
            ),
            format!(
                "have {h} : {} := {h}",
                self.fact_proposition(&fact, &formed)?
            ),
        ];
        definitions.extend(self.compile_parameter_inferences(
            store,
            &fact,
            &(self.fact_proposition(&fact, &formed)?, h),
            &formed,
        )?);
        Ok(definitions)
    }

    fn compile_recursive_formation_checks(
        &self,
        proof: &ExecHaveFnByInducStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let mut definitions = Vec::new();
        for (index, (obj, result)) in [
            (&proof.statement.measure, &proof.measure_well_defined),
            (
                &proof.statement.lower_bound,
                &proof.lower_bound_well_defined,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            self.compile_wd(
                success_object_wd(result, obj)?,
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?;
        }
        for (index, result) in [
            &proof.measure_in_z,
            &proof.lower_in_z,
            &proof.measure_ge_lower,
        ]
        .into_iter()
        .enumerate()
        {
            let site = SourcePosition {
                before: index + 3,
                ..*position
            };
            let compiled = self.compile_verify(result, &site)?;
            definitions.push(self.emit_internal_fact(
                &source_subject(result)?,
                &compiled,
                &site,
            )?);
        }
        let formed = SourcePosition {
            before: 7,
            ..*position
        };
        let coverage = self.compile_verify(&proof.case_checks.coverage, &formed)?;
        definitions.push(self.emit_internal_fact(
            &source_subject(&proof.case_checks.coverage)?,
            &coverage,
            &formed,
        )?);
        for disjoint in &proof.case_checks.disjoint {
            let scope =
                SourcePosition::new(Some(&formed), SourceOwner::RecursiveDisjoint(disjoint), 1);
            let assumption =
                self.resolve_fact(disjoint.assumption_stored.primary_fact_id(), &scope)?;
            self.validate_store(&disjoint.assumption_stored.store, &assumption)?;
            let proposition = self.fact_proposition(&assumption, &scope)?;
            let name = format!("h_{}", assumption.fact_id().value());
            let mut lines = vec![format!("intro {name}")];
            lines.extend(self.compile_stored_inferences(
                &disjoint.assumption_stored,
                &assumption,
                &(proposition.clone(), name),
                &scope,
            )?);
            let negated = self.compile_verify(&disjoint.negated_component, &scope)?;
            lines.push(format!("exact {}", negated.1));
            definitions.push(format!(
                "have _disjoint_{}_{} : {proposition} → {} := by\n  {}",
                disjoint.i,
                disjoint.j,
                self.scope_proposition(negated.0, &lines[1..lines.len() - 1]),
                lines.join("\n").replace('\n', "\n  ")
            ));
        }
        Ok(definitions)
    }

    fn compile_recursive_case_assumption(
        &self,
        proof: &ExecHaveFnByInducStmtSuccessResult,
        index: usize,
        hypothesis: &str,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let store = &proof.case_checks.cases[index].assumption_stored;
        let formed = SourcePosition {
            before: 1,
            ..*position
        };
        let fact = self.resolve_fact(store.primary_fact_id(), &formed)?;
        if fact != and_chain_as_fact(&proof.statement.cases[index].case_fact) {
            return Err(LeanCompileError::new(
                "RecursiveFunction/CaseAssumption",
                "The branch's captured store has another original guard.",
            ));
        }
        self.validate_store(&store.store, &fact)?;
        let proposition = self.fact_proposition(&fact, &formed)?;
        let name = format!("h_{}", fact.fact_id().value());
        let mut definitions = vec![format!("have {name} : {proposition} := {hypothesis}")];
        definitions.extend(self.compile_stored_inferences(
            store,
            &fact,
            &(proposition, name),
            &formed,
        )?);
        Ok(definitions)
    }

    fn compile_recursive_case_return(
        &self,
        proof: &ExecHaveFnByInducStmtSuccessResult,
        index: usize,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let current = if index == 0 {
            "(M.number 0)"
        } else {
            "(M.number ((_index + 1 : ℕ) : ℂ))"
        };
        let member = if index == 0 {
            "(show M.mem (M.number 0) (M.standard .natural) from (M.natural_members _).mpr ⟨0, by simp only [Nat.cast_zero]⟩)"
        } else {
            "(Litex.NativeBridge.numberInN (M := M) (_index + 1))"
        };
        let mut definitions = if index == 0 {
            Vec::new()
        } else {
            vec!["intro _index _prefix _prefix_member".into()]
        };
        definitions.extend(self.compile_recursive_parameter(proof, current, member, position)?);
        definitions.extend(self.compile_recursive_formation_checks(proof, position)?);
        let formed = SourcePosition {
            before: 7,
            ..*position
        };
        if index == 1 {
            let self_fact =
                self.resolve_fact(proof.restricted_self_membership.primary_fact_id(), &formed)?;
            let id = proof.statement.name.id.value();
            definitions.push(format!("let _object_i{id} := Litex.semanticObject (M := M) _prefix (M.member_isSet _prefix_member)"));
            definitions.push(format!(
                "have h_{} : {} := _prefix_member",
                self_fact.fact_id().value(),
                self.fact_proposition(&self_fact, &formed)?
            ));
        }
        let case = &proof.case_checks.cases[index];
        let case_position = SourcePosition::new(Some(&formed), SourceOwner::RecursiveCase(case), 0);
        let hypothesis = if index == 0 {
            "rfl"
        } else {
            "(by\n  refine ⟨0, ((_index + 1 : ℕ) : ℝ), rfl, ?_, ?_⟩\n  · change M.number ((_index + 1 : ℕ) : ℂ) = M.number (((_index + 1 : ℕ) : ℝ) : ℂ)\n    simp only [Complex.ofReal_natCast]\n  · exact_mod_cast Nat.zero_lt_succ _index)"
        };
        definitions.extend(self.compile_recursive_case_assumption(
            proof,
            index,
            hypothesis,
            &case_position,
        )?);
        let InducCaseBodySuccess::EqualTo {
            well_defined,
            in_ret_set,
        } = &case.body
        else {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/NestedCases",
            ));
        };
        let body_position = SourcePosition {
            before: 1,
            ..case_position
        };
        let body = recursive_case_body(proof, index)?;
        let object = self.compile_wd(success_object_wd(well_defined, body)?, &body_position)?;
        let returned = SourcePosition {
            before: 2,
            ..case_position
        };
        let membership = self.compile_verify(in_ret_set, &returned)?;
        if !matches!(source_subject(in_ret_set)?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == body.ir() && f.set == proof.statement.fn_set_clause.ret_set)
        {
            return Err(LeanCompileError::new(
                "RecursiveFunction/ReturnSubject",
                "The checked branch return has another body or target.",
            ));
        }
        definitions.push(format!("have _checked_body := {object}"));
        definitions.push(format!("exact {}", membership.1));
        Ok(format!(
            "(by\n  {})",
            definitions.join("\n").replace('\n', "\n  ")
        ))
    }

    fn compile_recursive_step_congruence(
        &self,
        proof: &ExecHaveFnByInducStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut definitions = vec!["intro _index _left_prefix _right_prefix _agree".into()];
        definitions.extend(self.compile_recursive_parameter(
            proof,
            "(M.number ((_index + 1 : ℕ) : ℂ))",
            "(Litex.NativeBridge.numberInN (M := M) (_index + 1))",
            position,
        )?);
        let formed = SourcePosition {
            before: 7,
            ..*position
        };
        let case = &proof.case_checks.cases[1];
        let case_position = SourcePosition::new(Some(&formed), SourceOwner::RecursiveCase(case), 0);
        definitions.extend(self.compile_recursive_case_assumption(proof, 1, "(by\n  refine ⟨0, ((_index + 1 : ℕ) : ℝ), rfl, ?_, ?_⟩\n  · change M.number ((_index + 1 : ℕ) : ℂ) = M.number (((_index + 1 : ℕ) : ℝ) : ℂ)\n    simp only [Complex.ofReal_natCast]\n  · exact_mod_cast Nat.zero_lt_succ _index)", &case_position)?);
        let completed = SourcePosition {
            before: 2,
            ..case_position
        };
        let parameter = &proof.statement.fn_set_clause.set_bound_parameters.groups[0].params[0];
        let bindings = HashMap::from([(parameter.id, "(M.number ((_index + 1 : ℕ) : ℂ))".into())]);
        let equality = self.compile_recursive_body_congruence(
            recursive_case_body(proof, 1)?,
            proof,
            &completed,
            &bindings,
        )?;
        definitions.push(format!("exact {equality}"));
        Ok(format!(
            "(by\n  {})",
            definitions.join("\n").replace('\n', "\n  ")
        ))
    }

    fn compile_recursive_body_congruence(
        &self,
        object: &Obj,
        declaration: &ExecHaveFnByInducStmtSuccessResult,
        position: &SourcePosition<'_>,
        bindings: &HashMap<IdentifierId, String>,
    ) -> Result<String, LeanCompileError> {
        if !contains_identifier(object, declaration.statement.name.id) {
            return Ok("rfl".into());
        }
        match object {
            Obj::FnObj(application) => {
                if application.body.len() != 1 || application.body[0].len() != 1 {
                    return Err(LeanCompileError::unsupported(
                        "RecursiveFunction/CongruenceCallArity",
                    ));
                }
                let FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) =
                    application.head.as_ref()
                else {
                    return Err(LeanCompileError::unsupported(
                        "RecursiveFunction/CongruenceCallHead",
                    ));
                };
                let argument = &application.body[0][0];
                if *id == declaration.statement.name.id {
                    let parameter = &declaration
                        .statement
                        .fn_set_clause
                        .set_bound_parameters
                        .groups[0]
                        .params[0];
                    if !matches!(argument.as_ref(), Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) if s.left.as_ref() == &Obj::Identifier(IdentifierObj::from_bound_name(parameter)) && is_one(&s.right))
                    {
                        return Err(LeanCompileError::unsupported(
                            "RecursiveFunction/PredecessorCall",
                        ));
                    }
                    let guard = position.with_visible_wd(object, &mut |wd, producer| {
                        let DetailedObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::FnObj(call), .. } = (wd).detailed_ref() else {
                            return Err(LeanCompileError::unsupported("RecursiveFunction/CallFormation"));
                        };
                        let Some(FnObjDomainFnSetEvidence::InFunctionSet { fact_id, fn_set, function_equal }) = &call.domain_fn_set else {
                            return Err(LeanCompileError::unsupported("RecursiveFunction/CallSelfEvidence"));
                        };
                        if *fact_id != declaration.restricted_self_membership.primary_fact_id() || !function_equal.path.is_empty()
                            || call.child_obj_well_defined.len() != 1 || call.requirement_fact_verified.len() != 3
                        {
                            return Err(LeanCompileError::new("RecursiveFunction/CallSelfEvidence", "The recursive call lost its exact self-signature and ordered smaller-index evidence."));
                        }
                        let selected = self.recursive_restricted_signature(declaration, position)?;
                        if *fn_set != selected {
                            return Err(LeanCompileError::new("RecursiveFunction/CallSelfSignature", "The call selected another restricted signature."));
                        }
                        ensure_object(argument, &call.child_obj_well_defined[0])?;
                        let call_parameter = &fn_set.set_bound_parameters.groups[0].params[0];
                        let substitution = HashMap::from([(call_parameter.id, argument.as_ref().clone())]);
                        if !matches!(source_subject(&call.requirement_fact_verified[0])?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == argument.ir() && f.set == Obj::StandardSet(StandardSet::N)) {
                            return Err(LeanCompileError::new("RecursiveFunction/CallParameterSubject", "The selected call's first requirement is not this exact argument in N."));
                        }
                        for (guard, verified) in fn_set.dom_facts.iter().zip(&call.requirement_fact_verified[1..]) {
                            if !instantiated_fact_matches(&function_guard_fact(guard)?, &source_subject(verified)?, &substitution) {
                                return Err(LeanCompileError::new("RecursiveFunction/CallGuardSubject", "The selected smaller-index guard proof has another subject or stage order."));
                            }
                        }
                        let cursor = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
                        let mut requirements = Vec::new();
                        for (index, verified) in call.requirement_fact_verified.iter().enumerate() {
                            requirements.push(self.compile_verify(verified, &SourcePosition { before: 1 + index, ..cursor })?.1);
                        }
                        Ok(requirements)
                    })?.ok_or_else(|| LeanCompileError::new("RecursiveFunction/CallProducer", "The source body owns no preceding WD for this recursive call."))?;
                    let raw =
                        self.compile_function_raw_expression_bound(argument, position, bindings)?;
                    Ok(format!(
                        "(_agree {raw} {} (And.intro {} {}))",
                        guard[0], guard[1], guard[2]
                    ))
                } else {
                    let head = self.compile_object_reference(
                        &Obj::Identifier(match application.head.as_ref() {
                            FnObjHead::Identifier(id) => id.clone(),
                            _ => unreachable!(),
                        }),
                        position,
                    )?;
                    let child = self.compile_recursive_body_congruence(
                        argument,
                        declaration,
                        position,
                        bindings,
                    )?;
                    Ok(format!("(congrArg (Litex.FunctionSemantics.callValue (M := M) (Litex.denote {head})) {child})"))
                }
            }
            Obj::ArithmeticOperator(operator) => {
                let (name, left, right) = match operator {
                    ArithmeticOperator::Add(v) => ("M.addValue", &v.left, Some(&v.right)),
                    ArithmeticOperator::Sub(v) => ("M.subValue", &v.left, Some(&v.right)),
                    ArithmeticOperator::Mul(v) => ("M.mulValue", &v.left, Some(&v.right)),
                    ArithmeticOperator::Div(v) => ("M.divValue", &v.left, Some(&v.right)),
                    ArithmeticOperator::Pow(v) => ("M.powValue", &v.base, Some(&v.exponent)),
                    ArithmeticOperator::Neg(v) => ("M.negValue", &v.arg, None),
                    ArithmeticOperator::Abs(v) => ("(Litex.absValue (M := M))", &v.arg, None),
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "RecursiveFunction/CongruenceOperator",
                        ))
                    }
                };
                let left =
                    self.compile_recursive_body_congruence(left, declaration, position, bindings)?;
                Ok(if let Some(right) = right {
                    format!(
                        "(congrArg₂ {name} {left} {})",
                        self.compile_recursive_body_congruence(
                            right,
                            declaration,
                            position,
                            bindings
                        )?
                    )
                } else {
                    format!("(congrArg {name} {left})")
                })
            }
            _ => Err(LeanCompileError::unsupported(
                "RecursiveFunction/CongruenceObject",
            )),
        }
    }

    fn compile_recursive_case_equation(
        &self,
        proof: &ExecHaveFnByInducStmtSuccessResult,
        index: usize,
        store: &StoreFactAndInferResult,
        object: &str,
        position: &SourcePosition<'_>,
        outer: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let source = self.resolve_fact(store.primary_fact_id(), position)?;
        self.validate_store(&store.store, &source)?;
        let Fact::ForallFact(forall) = source else {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/CaseEquationFamily",
            ));
        };
        if forall.typed_parameters.groups.len() != 1
            || forall.dom_facts.len() != 1
            || forall.then_facts.len() != 1
            || forall.typed_parameters.groups[0].params
                != proof.statement.fn_set_clause.set_bound_parameters.groups[0].params
            || forall.typed_parameters.groups[0].param_type
                != ParamType::Obj(Obj::StandardSet(StandardSet::N))
            || forall.dom_facts[0] != and_chain_as_fact(&proof.statement.cases[index].case_fact)
        {
            return Err(LeanCompileError::new(
                "RecursiveFunction/CaseEquationSubject",
                "The stored case equation differs from the original leaf case.",
            ));
        }
        let parameter = &proof.statement.fn_set_clause.set_bound_parameters.groups[0].params[0];
        let id = parameter.id.value();
        let member_id = proof
            .binder_introduction
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id()
            .value();
        let guard_id = proof.case_checks.cases[index]
            .assumption_stored
            .primary_fact_id()
            .value();
        let bindings = HashMap::from([
            (parameter.id, format!("(Litex.denote _value_i{id})")),
            (proof.statement.name.id, format!("(Litex.denote {object})")),
        ]);
        let guard =
            self.compile_function_raw_predicate(&forall.dom_facts[0], position, &bindings)?;
        let then: Fact = forall.then_facts[0].clone().into();
        let Fact::AtomicFact(AtomicFact::EqualFact(equation)) = &then else {
            return Err(LeanCompileError::unsupported(
                "RecursiveFunction/CaseEquationConclusion",
            ));
        };
        if equation.right != *recursive_case_body(proof, index)?
            || !matches!(&equation.left, Obj::FnObj(f) if matches!(f.head.as_ref(), FnObjHead::Identifier(IdentifierObj::Plain { id: function_id, .. }) if *function_id == proof.statement.name.id)
                && f.body.len() == 1 && f.body[0].len() == 1 && f.body[0][0].as_ref() == &Obj::Identifier(IdentifierObj::from_bound_name(parameter)))
        {
            return Err(LeanCompileError::new("RecursiveFunction/CaseEquationConclusion", "The stored conclusion differs from this exact source function and selected branch body."));
        }
        let proposition = self.compile_function_raw_predicate(&then, position, &bindings)?;
        let body = if index == 0 {
            format!("rw [h_{guard_id}]\n  exact Litex.recursiveNatFn_zero {object}")
        } else {
            format!("let _index := Litex.NativeBridge.asNat _value_i{id} h_{member_id}\n  have _index_spec : Litex.denote _value_i{id} = M.number (_index : ℂ) := Litex.NativeBridge.asNat_spec _value_i{id} h_{member_id}\n  have _index_positive : 0 < _index := Litex.NativeBridge.naturalValue_pos (Litex.denote _value_i{id}) h_{member_id} h_{guard_id}\n  obtain ⟨_previous, _index_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt _index_positive)\n  rw [_index_spec, _index_eq]\n  exact Litex.recursiveNatFn_succ {object} _previous")
        };
        Ok(format!("theorem h_{}{} : ∀ {{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id}) (h_{member_id} : Litex.In _value_i{id} Litex.N) (h_{guard_id} : {guard}), {proposition} := by\n  intro _Host_i{id} _rep_i{id} _value_i{id} h_{member_id} h_{guard_id}\n  {body}", forall.fact_id.value(), self.context_header(outer)?))
    }
}

fn recursive_signature(proof: &ExecHaveFnByInducStmtSuccessResult) -> FnSet {
    FnSet {
        set_bound_parameters: proof.statement.fn_set_clause.set_bound_parameters.clone(),
        dom_facts: proof.statement.fn_set_clause.dom_facts.clone(),
        ret_set: Box::new(proof.statement.fn_set_clause.ret_set.clone()),
    }
}

fn recursive_case_body(
    proof: &ExecHaveFnByInducStmtSuccessResult,
    index: usize,
) -> Result<&Obj, LeanCompileError> {
    match &proof.statement.cases[index].body {
        HaveFnByInducCaseBody::EqualTo(body) => Ok(body),
        HaveFnByInducCaseBody::NestedCases(_) => Err(LeanCompileError::unsupported(
            "RecursiveFunction/NestedCases",
        )),
    }
}

fn is_zero(object: &Obj) -> bool {
    matches!(object, Obj::Literal(Literal::Number(n)) if n.normalized_value == "0")
}

fn is_one(object: &Obj) -> bool {
    matches!(object, Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
}

fn contains_identifier(object: &Obj, target: IdentifierId) -> bool {
    match object {
        Obj::Identifier(IdentifierObj::Plain { id, .. }) => *id == target,
        Obj::FnObj(f) => {
            matches!(f.head.as_ref(), FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) if *id == target)
                || f.body
                    .iter()
                    .flatten()
                    .any(|o| contains_identifier(o, target))
        }
        Obj::ArithmeticOperator(operator) => match operator {
            ArithmeticOperator::Add(v) => {
                contains_identifier(&v.left, target) || contains_identifier(&v.right, target)
            }
            ArithmeticOperator::Sub(v) => {
                contains_identifier(&v.left, target) || contains_identifier(&v.right, target)
            }
            ArithmeticOperator::Mul(v) => {
                contains_identifier(&v.left, target) || contains_identifier(&v.right, target)
            }
            ArithmeticOperator::Div(v) => {
                contains_identifier(&v.left, target) || contains_identifier(&v.right, target)
            }
            ArithmeticOperator::Pow(v) => {
                contains_identifier(&v.base, target) || contains_identifier(&v.exponent, target)
            }
            ArithmeticOperator::Neg(v) => contains_identifier(&v.arg, target),
            ArithmeticOperator::Abs(v) => contains_identifier(&v.arg, target),
            _ => false,
        },
        _ => false,
    }
}
