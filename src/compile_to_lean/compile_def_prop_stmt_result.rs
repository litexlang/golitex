use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::{ExecDefPropStmtResult, ExecDefPropStmtSuccessResult};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_def_prop_statement(
        &self,
        result: &ExecDefPropStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local {
            return Err(LeanCompileError::unsupported("Prop/LocalDeclaration"));
        }
        let proof = match result {
            ExecDefPropStmtResult::Success(proof) => proof,
            ExecDefPropStmtResult::Failed(_) => {
                return Err(LeanCompileError::new(
                    "Prop/Failed",
                    "Failed predicate formation is not a definition.",
                ))
            }
        };
        let definition_position = SourcePosition {
            parent: Some(position),
            owner: SourceOwner::PropDefinition(proof),
            before: 0,
        };
        let (binders, meaning) =
            self.compile_concrete_prop_definition(proof, &definition_position)?;
        Ok(format!(
            "def prop_{index}{}{} : Prop :=\n  {}",
            self.context_header(position)?,
            if binders.is_empty() {
                String::new()
            } else {
                format!(" {}", binders.join(" "))
            },
            meaning.replace('\n', "\n  ")
        ))
    }

    fn compile_concrete_prop_definition(
        &self,
        proof: &ExecDefPropStmtSuccessResult,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String), LeanCompileError> {
        let (binders, memberships, parameter_definitions) =
            self.compile_prop_parameter_prefix(proof, position, false)?;
        let count = proof.statement.typed_parameters.ordered_param_ids().len();
        let mut clauses = Vec::new();
        for (index, (fact, assumed)) in proof
            .statement
            .iff_facts
            .iter()
            .zip(&proof.assumed_iff_facts)
            .enumerate()
        {
            if !matches!(
                fact,
                Fact::AtomicFact(_)
                    | Fact::AndFact(_)
                    | Fact::ChainFact(_)
                    | Fact::OrFact(_)
                    | Fact::ExistFact(_)
            ) {
                return Err(LeanCompileError::unsupported("Prop/CompoundClause"));
            }
            let prior = SourcePosition {
                before: count + index,
                ..*position
            };
            self.compile_fact_wd(&assumed.well_defined, fact, &prior)?;
            self.validate_store(&assumed.store_and_infer.store, fact)?;
            let formed = SourcePosition {
                parent: Some(&prior),
                owner: SourceOwner::FactWD(&assumed.well_defined),
                before: usize::MAX,
            };
            let clause = (
                self.fact_proposition(fact, &formed)?,
                format!("h_{}", fact.fact_id().value()),
            );
            let completed = SourcePosition {
                before: count + index + 1,
                ..*position
            };
            let mut derived = self.compile_set_builder_parameter_inferences(
                &assumed.store_and_infer,
                fact,
                &clause,
                &completed,
            )?;
            derived.extend(self.compile_stored_inferences(
                &assumed.store_and_infer,
                fact,
                &clause,
                &completed,
            )?);
            clauses.push((clause.1, clause.0, derived));
        }
        let (_, mut meaning, _) = clauses.pop().expect("validated nonempty predicate clauses");
        for (name, clause, derived) in clauses.into_iter().rev() {
            let suffix = self.scope_proposition(meaning, &derived);
            meaning = format!("∃ ({name} : {clause}), {suffix}");
        }
        // A proof witness retains each source domain without making it a Lean
        // parameter. Later constructor WD can depend on the exact earlier fact.
        meaning = self.scope_proposition(meaning, &parameter_definitions);
        for (name, member) in memberships.into_iter().rev() {
            meaning = format!("∃ ({name} : {member}), {meaning}");
        }
        Ok((binders, meaning))
    }
    /// Original declaration binders and their ordered membership evidence.
    /// The same prefix is replayed when an original clause is instantiated.
    pub(in crate::compile_to_lean) fn compile_prop_parameter_prefix(
        &self,
        proof: &ExecDefPropStmtSuccessResult,
        position: &SourcePosition<'_>,
        instantiate_host_universes: bool,
    ) -> Result<(Vec<String>, Vec<(String, String)>, Vec<String>), LeanCompileError> {
        let groups = &proof.statement.typed_parameters.groups;
        let parameters = groups
            .iter()
            .flat_map(|group| &group.params)
            .collect::<Vec<_>>();
        let count = parameters.len();
        if parameters.iter().enumerate().any(|(index, parameter)| {
            parameters[..index]
                .iter()
                .any(|earlier| earlier.id == parameter.id)
        }) {
            return Err(LeanCompileError::new(
                "Prop/ParameterIdentity",
                "Predicate binders repeat a source identity.",
            ));
        }
        self.validate_parameter_store_capture(&proof.defined_params)?;
        let stores = &proof.defined_params.store_and_infer_results;
        if proof.param_type_well_defined.len() != groups.len() || stores.len() != count {
            return Err(LeanCompileError::new(
                "Prop/Parameters",
                "Predicate parameter evidence has another ordered arity.",
            ));
        }
        if proof.statement.iff_facts.is_empty()
            || proof.assumed_iff_facts.len() != proof.statement.iff_facts.len()
        {
            return Err(LeanCompileError::new(
                "Prop/BodyArity",
                "A concrete predicate needs its complete nonempty ordered defining clauses.",
            ));
        }
        let mut binders = Vec::new();
        let mut memberships = Vec::new();
        let mut parameter_definitions = Vec::new();
        let mut offset = 0;
        for (group, wd) in groups.iter().zip(&proof.param_type_well_defined) {
            let set = match &group.param_type {
                ParamType::Obj(set) => set,
                _ => return Err(LeanCompileError::unsupported("Prop/ParameterCarrier")),
            };
            let group_position = SourcePosition {
                before: offset,
                ..*position
            };
            match wd {
                ParamTypeWellDefinedProof::Obj(wd) => {
                    ensure_object(set, wd)?;
                    self.compile_wd(wd, &group_position)?;
                }
                _ => {
                    return Err(LeanCompileError::new(
                        "Prop/ParameterWD",
                        "Predicate carrier evidence differs from its source header.",
                    ))
                }
            }
            for parameter in &group.params {
                let introduced = SourcePosition {
                    before: offset + 1,
                    ..*position
                };
                let formed = SourcePosition {
                    parent: Some(&introduced),
                    owner: SourceOwner::ParamTypeWD(wd),
                    before: 1,
                };
                let store = &stores[offset];
                let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
                let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
                match &fact {
                    Fact::AtomicFact(AtomicFact::InFact(member))
                        if member.element.ir() == object.ir() && member.set.ir() == set.ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "Prop/ParameterSubject",
                            "The stored predicate parameter has another object or carrier.",
                        ))
                    }
                }
                self.validate_store(&store.store, &fact)?;
                let id = parameter.id.value();
                let universe = if instantiate_host_universes {
                    "_".into()
                } else {
                    format!("v{id}")
                };
                binders.push(format!("{{_Host_i{id} : Type {universe}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id})"));
                let member = (
                    self.fact_proposition(&fact, &formed)?,
                    format!("h_{}", fact.fact_id().value()),
                );
                memberships.push((member.1.clone(), member.0.clone()));
                parameter_definitions.extend(self.compile_parameter_inferences(
                    store,
                    &fact,
                    &member,
                    &introduced,
                )?);
                offset += 1;
            }
        }
        Ok((binders, memberships, parameter_definitions))
    }
}
