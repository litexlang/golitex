use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimStmtResult, ExecProofBlockStmtResult, ExecSketchStmtResult,
};
use crate::execute::{ExecDefPropStmtResult, ExecHaveFnByInducStmtResult};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn source_universes(
        &self,
        result: &RunLitexCodeResult,
    ) -> Result<String, LeanCompileError> {
        fn parameters<'s>(fact: &'s Fact, out: &mut Vec<IdentifierId>) {
            let fact = match fact {
                Fact::ForallFact(fact) => fact,
                Fact::ForallFactWithIff(fact) => &fact.forall_fact,
                _ => return,
            };
            for group in &fact.typed_parameters.groups {
                for parameter in &group.params {
                    if !out.contains(&parameter.id) {
                        out.push(parameter.id);
                    }
                }
            }
            for premise in &fact.dom_facts {
                parameters(premise, out);
            }
        }
        fn verify(result: &VerifyFactResult, out: &mut Vec<IdentifierId>) {
            if let VerifyFactResult::ForallFactWithIff(result) = result {
                if let VerifyForallFactWithIffResult::Success(proof) = result.as_ref() {
                    verify(&proof.then_implies_iff, out);
                    verify(&proof.iff_implies_then, out);
                }
            }
            if let VerifyFactResult::ForallFact(result) = result {
                if let VerifyForallFactResult::Success(proof) = result.as_ref() {
                    parameters(&Fact::ForallFact(proof.fact().clone()), out);
                }
            }
        }
        fn statement(result: &ExecStmtResult, out: &mut Vec<IdentifierId>) {
            match result {
                ExecStmtResult::Definition(ExecDefinitionStmtResult::DefTemplate(crate::execute::ExecDefTemplateStmtResult::Success(p))) => {
                    out.extend(p.statement.template_arg_def.ordered_param_ids());
                    statement(&p.body, out);
                }
                ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(ExecDefineObjStmtResult::HaveByReplacementAxiom(
                    crate::execute::ExecHaveByReplacementAxiomStmtResult::Success(p)))) => {
                    for store in [&p.introduction, &p.elimination] {
                        if let StoreFactResult::ForallFact(f) = &store.store { parameters(&Fact::ForallFact(f.fact.clone()), out); }
                    }
                }

                ExecStmtResult::Trust(_) | ExecStmtResult::Definition(ExecDefinitionStmtResult::Axiom(_)) => {
                    for (fact, _, _) in super::compile_assumption_stmt_result::assumption_stages(result) { parameters(&fact, out); }
                    if let Some((groups, _)) = super::source_position::context_parameter_parts(result) {
                        out.extend(groups.iter().flat_map(|g| g.params.iter().map(|p| p.id)));
                    }
                }
                ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStruct(crate::execute::ExecDefStructStmtResult::Success(p))) => {
                    out.extend(p.statement.fields.iter().map(|field| field.binding.id));
                }
                ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(ExecSketchStmtResult::Success(p))) => {
                    for step in &p.proof_steps { statement(step, out); }
                }
                ExecStmtResult::By(crate::execute::execute_by_stmt::ExecByStmtResult::Contra(
                    crate::execute::execute_by_stmt::ExecByContraStmtResult::Success(p),
                )) => {
                    parameters(&p.goal, out);
                    parameters(&p.reverse_assumption, out);
                    for step in &p.proof_steps { statement(step, out); }
                    verify(&p.closing.impossible, out);
                    verify(&p.closing.negated_impossible, out);
                }
                ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByForallExistUnique(
                    crate::execute::ExecHaveFnByForallExistUniqueStmtResult::Success(p),
                )) => {
                    verify(&p.source_forall, out);
                    for store in [&p.property, &p.uniqueness] {
                        if let StoreFactResult::ForallFact(stored) = &store.store {
                            parameters(&Fact::ForallFact(stored.fact.clone()), out);
                        }
                    }
                }
                ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(crate::execute::ExecHaveFnEqualCaseByCaseStmtResult::Success(p))) => {
                    for store in &p.store_and_infer_result.case_defining {
                        if let StoreFactResult::ForallFact(stored) = &store.store { parameters(&Fact::ForallFact(stored.fact.clone()), out); }
                    }
                }
                ExecStmtResult::Register(result) => {
                    if let Ok(proof) = crate::compile_to_lean::compile_register_stmt_result::registration_proof(result) {
                        verify(proof, out);
                    }
                }
                ExecStmtResult::Witness(crate::execute::execute_witness_stmt::ExecWitnessStmtResult::WitnessNonemptySet(crate::execute::execute_witness_stmt::ExecWitnessNonemptySetStmtResult::Success(proof))) => {
                    for step in &proof.proof_steps { statement(step, out); }
                }

                ExecStmtResult::Witness(crate::execute::execute_witness_stmt::ExecWitnessStmtResult::WitnessAtomicFact(crate::execute::execute_witness_stmt::ExecWitnessAtomicFactStmtResult::Success(proof))) => {
                    for step in &proof.proof_steps { statement(step, out); }
                }
                ExecStmtResult::Witness(crate::execute::execute_witness_stmt::ExecWitnessStmtResult::WitnessExistFact(crate::execute::execute_witness_stmt::ExecWitnessExistFactStmtResult::Success(proof))) => {
                    for step in &proof.proof_steps { statement(step, out); }
                }

                ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
                    ExecHaveFnByInducStmtResult::Success(proof),
                )) => {
                    for group in &proof.statement.fn_set_clause.set_bound_parameters.groups {
                        for parameter in &group.params {
                            if !out.contains(&parameter.id) {
                                out.push(parameter.id);
                            }
                        }
                    }
                }
                ExecStmtResult::By(crate::execute::execute_by_stmt::ExecByStmtResult::Induc(
                    crate::execute::execute_by_stmt::ExecByInducStmtResult::Success(proof),
                )) => {
                    if !out.contains(&proof.parameter.id) {
                        out.push(proof.parameter.id);
                    }
                    let (base, step) = match &proof.body {
                        crate::execute::execute_by_stmt::ByInducBodySuccess::Unstructured {
                            base,
                            step,
                        }
                        | crate::execute::execute_by_stmt::ByInducBodySuccess::Structured {
                            base,
                            step,
                        } => (base, step),
                    };
                    for result in base.proof_steps.iter().chain(&step.proof_steps) {
                        statement(result, out);
                    }
                }
                ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
                    ExecClaimStmtResult::Success(proof),
                )) => {
                    parameters(&proof.statement.fact, out);
                    for step in proof.body.proof_steps() {
                        statement(step, out);
                    }
                }
                ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => {
                    verify(&proof.verify_result, out)
                }
                ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                    ExecDefThmStmtResult::Success(proof),
                )) => {
                    parameters(&proof.statement.fact, out);
                    let steps = match &proof.body {
                        ExecDefThmBodyProof::Forall(body) => &body.proof_steps,
                        ExecDefThmBodyProof::NonForall(body) => &body.proof_steps,
                    };
                    for step in steps {
                        statement(step, out);
                    }
                }
                ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
                    ExecDefPropStmtResult::Success(proof),
                )) => {
                    for group in &proof.statement.typed_parameters.groups {
                        for parameter in &group.params {
                            if !out.contains(&parameter.id) {
                                out.push(parameter.id);
                            }
                        }
                    }
                }
                ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                    ExecDefineObjStmtResult::HaveObjInNonemptySet(
                        ExecHaveObjInNonemptySetStmtResult::Success(proof),
                    ),
                )) => {
                    for group in &proof.statement.param_def.groups {
                        for parameter in &group.params {
                            if !out.contains(&parameter.id) {
                                out.push(parameter.id);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        let mut ids = Vec::new();
        for result in &result.statement_results {
            statement(result, &mut ids);
        }
        Ok(if ids.is_empty() {
            "u".into()
        } else {
            format!(
                "u {}",
                ids.into_iter()
                    .map(|id| format!("v{}", id.value()))
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        })
    }

    pub(in crate::compile_to_lean) fn emit_fact(
        &self,
        source: &Fact,
        fact: (String, String),
        _index: usize,
        local: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let name = format!("h_{}", source.fact_id().value());
        let kind = if local { "have" } else { "theorem" };
        let declaration = format!(
            "{kind} {name}{} : {} :=\n  {}",
            if local {
                String::new()
            } else {
                self.context_header(position)?
            },
            fact.0,
            self.share_local_proof(&fact.1, local).replace('\n', "\n  ")
        );
        Ok(declaration)
    }

    pub(in crate::compile_to_lean) fn context_header(
        &self,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let mut binders = position
            .context_abstract_props()
            .into_iter()
            .map(|(declaration, index)| {
                format!(
                    "(abstract_prop_{index} : (Fin {} → M.Value) → Prop)",
                    declaration.params.len()
                )
            })
            .collect::<Vec<_>>();
        for (run, index, statement, before) in position.context_statements() {
            if super::source_position::context_parameter_parts(statement).is_some() {
                let mut parameters = Vec::new();
                super::source_position::append_have_parameters(statement, before, &mut parameters);
                for (parameter, set, fact_id) in parameters {
                    let id = parameter.id.value();
                    let fact_id = fact_id.value();
                    let proposition = match set {
                        Some(set) => format!(
                            "Litex.In _value_i{id} {}",
                            self.compile_object_reference(set, position)?
                        ),
                        None => format!("Litex.IsSet _value_i{id}"),
                    };
                    binders.push(format!("{{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id}) (h_{fact_id} : {proposition})"));
                }
            }
            let prior =
                SourcePosition::new(None, super::source_position::SourceOwner::Run(run), index);
            binders.extend(self.assumption_binders(statement, before, &prior)?);
            binders.extend(self.closed_assumption_binders(statement, &prior)?);
        }
        Ok(if binders.is_empty() {
            String::new()
        } else {
            format!(" {}", binders.join(" "))
        })
    }

    pub(in crate::compile_to_lean) fn context_application(
        &self,
        name: &str,
        position: &SourcePosition<'_>,
    ) -> String {
        position.context_application(name)
    }

    /// Local producer names used inside constructor WD must also be in scope
    /// when the public proposition is formed. These values are the actual
    /// checked producer proofs, not extra mathematical premises or a proof cache.
    pub(in crate::compile_to_lean) fn scope_proposition(
        &self,
        proposition: String,
        definitions: &[String],
    ) -> String {
        if definitions.is_empty() {
            return proposition;
        }
        // These are temporary output slices, not source/target semantic records.
        // Delimiter depth distinguishes actual declarations from a nested
        // producer's already-scoped proposition or parenthesized tactic proof.
        let text = definitions.join("\n");
        let mut boundaries = Vec::new();
        let mut depth = 0usize;
        let mut offset = 0usize;
        for line in text.split_inclusive('\n') {
            if depth == 0 && (line.starts_with("have ") || line.starts_with("let ")) {
                boundaries.push(offset);
            }
            for character in line.chars() {
                match character {
                    '(' | '[' | '{' => depth += 1,
                    ')' | ']' | '}' => depth = depth.saturating_sub(1),
                    _ => {}
                }
            }
            offset += line.len();
        }
        let chunks = boundaries
            .iter()
            .enumerate()
            .map(|(index, start)| {
                text[*start..boundaries.get(index + 1).copied().unwrap_or(text.len())].trim_end()
            })
            .collect::<Vec<_>>();
        let tokens = |text: &str| {
            text.split(|character: char| !character.is_ascii_alphanumeric() && character != '_')
                .filter(|token| {
                    token.starts_with("h_")
                        || token.starts_with("_value_i")
                        || token.starts_with("_object_i")
                        || token.starts_with("_object_w")
                        || token.starts_with("_object_h")
                })
                .map(str::to_string)
                .collect::<Vec<_>>()
        };
        let mut needed = tokens(&proposition);
        let mut selected = Vec::new();
        // Source order already guarantees that a producer can cite only earlier
        // local declarations. A reverse pass selects the lexical dependencies.
        for chunk in chunks.into_iter().rev() {
            let head = chunk
                .strip_prefix("have ")
                .or_else(|| chunk.strip_prefix("let "))
                .expect("compiler-controlled local declaration");
            let name = head
                .split_whitespace()
                .next()
                .expect("local declaration name");
            if needed.iter().any(|token| token == name) {
                needed.extend(tokens(chunk));
                selected.push(chunk);
            }
        }
        if selected.is_empty() {
            return proposition;
        }
        selected.reverse();
        // Finish each producer before introducing the next one. Turning these
        // into nested term-level lets leaves their tactic proofs as synthetic
        // metavariables. Lean then repeatedly abstracts their growing local
        // contexts while forming the proposition, before running the proofs.
        // Tactic let/have retain the same values and original proof terms.
        format!(
            "(by\n  {}\n  exact {}\n)",
            selected.join("\n").replace('\n', "\n  "),
            proposition.replace('\n', "\n  "),
        )
    }

    pub(in crate::compile_to_lean) fn emit_internal_fact(
        &self,
        fact: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let name = format!("h_{}", fact.fact_id().value());
        let local = position.is_local();
        Ok(format!(
            "{} {name}{} : {} :=\n  {}",
            if local { "have" } else { "theorem" },
            if local {
                String::new()
            } else {
                self.context_header(position)?
            },
            compiled.0,
            self.share_local_proof(&compiled.1, local)
                .replace('\n', "\n  ")
        ))
    }

    /// Keep a checked local proof opaque to later elaboration. The Lean helper
    /// closes over the actual local definitions, including constructor WD.
    /// Exported theorems already provide this boundary; inferred references
    /// remain direct citations through `emit_internal_fact_reference`.
    pub(in crate::compile_to_lean) fn share_local_proof(&self, proof: &str, local: bool) -> String {
        let checker = if local {
            "litex_checked_step"
        } else {
            "litex_complete"
        };
        format!(
            "(by\n  {checker} =>\n    exact (\n      {}\n    )\n)",
            proof.replace('\n', "\n      ")
        )
    }

    /// A projection or composition of typed citations determines its own type.
    /// Retain explicit statements on exported declarations, while local facts
    /// reuse that type without elaborating their constructors a second time.
    pub(in crate::compile_to_lean) fn emit_internal_fact_reference(
        &self,
        fact: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !position.is_local() {
            return self.emit_internal_fact(fact, compiled, position);
        }
        Ok(format!(
            "have h_{} :=\n  {}",
            fact.fact_id().value(),
            compiled.1.replace('\n', "\n  ")
        ))
    }

    pub(in crate::compile_to_lean) fn introduce_member_parameter(
        &self,
        parameter: &BoundName,
        set: &Obj,
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let id = parameter.id;
        let host = format!("_Host_i{}", id.value());
        let universe = position.parameter_universe(id);

        let instance = format!("_rep_i{}", id.value());
        let value = format!("_value_i{}", id.value());
        let hypothesis = format!("h_{}", store.primary_fact_id().value());
        let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let fact = self.resolve_fact(store.primary_fact_id(), position)?;
        match &fact {
            Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == object.ir() && f.set.ir() == set.ir() => {}
            _ => {
                return Err(LeanCompileError::new(
                    "Parameters/Subject",
                    "The actual parameter store differs from its source header.",
                ))
            }
        }
        self.validate_store(&store.store, &fact)?;
        let proposition = self.fact_proposition(&fact, position)?;

        let member = (proposition.clone(), hypothesis.clone());

        let _ = member;
        Ok((vec![format!("{{{host} : Type {universe}}} [{instance} : Litex.Representation M {host}] ({value} : Litex.Obj (M := M) {host})"), format!("({hypothesis} : {proposition})")], vec![host, instance, value, hypothesis]))
    }

    pub(in crate::compile_to_lean) fn introduce_set_kind_parameter(
        &self,
        parameter: &BoundName,
        kind: &ParamType,
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let fact = self.resolve_fact(store.primary_fact_id(), position)?;
        let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let predicate = match (kind, &fact) {
            (ParamType::Set(_), Fact::AtomicFact(AtomicFact::IsSetFact(f)))
                if f.set.ir() == object.ir() =>
            {
                "Litex.IsSet"
            }
            (ParamType::FiniteSet(_), Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)))
                if f.set.ir() == object.ir() =>
            {
                "Litex.IsFiniteSet"
            }
            (ParamType::NonemptySet(_), Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)))
                if f.set.ir() == object.ir() =>
            {
                "Litex.IsNonempty"
            }
            _ => {
                return Err(LeanCompileError::new(
                    "Parameters/SetKindSubject",
                    "The original store must match the declared set kind and parameter.",
                ))
            }
        };
        if !matches!(&store.infer, Some(crate::store_fact_and_infer::InferResult::AtomicFact(infer))
            if matches!((kind, infer),
                (ParamType::Set(_), crate::store_fact_and_infer::InferAtomicFactResult::IsSetFact(r)) if r.is_empty())
                || matches!((kind, infer),
                (ParamType::NonemptySet(_), crate::store_fact_and_infer::InferAtomicFactResult::IsNonemptySetFact(r)) if r.is_empty())
                || matches!((kind, infer), (ParamType::FiniteSet(_), crate::store_fact_and_infer::InferAtomicFactResult::IsFiniteSetFact(r)) if r.is_empty()))
        {
            return Err(LeanCompileError::new(
                "Parameters/SetKindInference",
                "A set-kind parameter must retain its original empty inference stage.",
            ));
        }
        self.validate_store(&store.store, &fact)?;
        let id = parameter.id.value();
        let name = format!("h_{}", fact.fact_id().value());
        let universe = position.parameter_universe(parameter.id);
        let binders = vec![format!("{{_Host_i{id} : Type {universe}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id})"), format!("({name} : {predicate} _value_i{id})")];
        Ok((
            binders,
            vec![
                format!("_Host_i{id}"),
                format!("_rep_i{id}"),
                format!("_value_i{id}"),
                name,
            ],
        ))
    }

    pub(in crate::compile_to_lean) fn fact_proposition(
        &self,
        fact: &Fact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match fact {
            Fact::AtomicFact(atomic) => self.atomic_proposition(atomic, position),
            Fact::AndFact(fact) => {
                let propositions = fact
                    .facts
                    .iter()
                    .map(|atomic| self.atomic_proposition(atomic, position))
                    .collect::<Result<Vec<_>, _>>()?;
                conjunction_proposition(propositions)
            }
            Fact::ChainFact(fact) => {
                let propositions = (0..fact.prop_names.len())
                    .map(|index| {
                        let edge = crate::compile_to_lean::compile_compound_fact::chain_edge(
                            fact,
                            index,
                            fact.fact_id,
                        )?;
                        self.atomic_proposition(&edge, position)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                conjunction_proposition(propositions)
            }
            Fact::OrFact(fact) => {
                let mut branches = fact
                    .facts
                    .iter()
                    .map(|branch| {
                        self.fact_proposition(
                            &crate::ast::fact::and_chain_as_fact(branch),
                            position,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let Some(mut proposition) = branches.pop() else {
                    return Err(LeanCompileError::unsupported("Or/Empty"));
                };
                while let Some(branch) = branches.pop() {
                    proposition = format!("(({branch}) ∨ ({proposition}))");
                }
                Ok(proposition)
            }
            Fact::ExistFact(fact) => self.exist_proposition(fact, position),
            Fact::ExistUniqueFact(fact) => Ok(format!(
                "({}) ∧ ({})",
                self.exist_proposition(fact, position)?,
                self.unique_signature(fact, position)?.0
            )),
            Fact::NotExistFact(fact) => {
                Ok(format!("¬ ({})", self.exist_proposition(fact, position)?))
            }
            Fact::ForallFact(fact) => {
                let mut cursor = Some(position);
                while let Some(p) = cursor {
                    if let SourceOwner::FactWD(FactWellDefinedProof::ForallFact(wd)) = p.owner {
                        return self.compile_canonical_forall_formation(fact, wd, position);
                    }
                    cursor = p.parent;
                }
                Err(LeanCompileError::unsupported("Forall/FormationOwner"))
            }
            Fact::NotForall(fact) => self.not_forall_proposition(fact, position),
            _ => Err(LeanCompileError::unsupported("Declaration/CompoundFact")),
        }
    }

    pub(in crate::compile_to_lean) fn atomic_proposition(
        &self,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match fact {
            AtomicFact::EqualFact(fact) => Ok(format!(
                "Litex.Same {} {}",
                self.compile_object_reference(&fact.left, position)?,
                self.compile_object_reference(&fact.right, position)?
            )),
            AtomicFact::NotEqualFact(fact) => Ok(format!(
                "¬ Litex.Same {} {}",
                self.compile_object_reference(&fact.left, position)?,
                self.compile_object_reference(&fact.right, position)?
            )),
            AtomicFact::InFact(fact) => Ok(format!(
                "Litex.In {} {}",
                self.compile_object_reference(&fact.element, position)?,
                self.compile_object_reference(&fact.set, position)?
            )),
            AtomicFact::NotInFact(fact) => Ok(format!(
                "¬ Litex.In {} {}",
                self.compile_object_reference(&fact.element, position)?,
                self.compile_object_reference(&fact.set, position)?
            )),
            AtomicFact::SubsetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                self.compile_object_reference(&fact.left, position)?,
                self.compile_object_reference(&fact.right, position)?
            )),
            AtomicFact::NotSubsetFact(fact) => Ok(format!(
                "¬ Litex.Subset {} {}",
                self.compile_object_reference(&fact.left, position)?,
                self.compile_object_reference(&fact.right, position)?
            )),
            AtomicFact::IsFiniteSetFact(fact) => Ok(format!(
                "Litex.IsFiniteSet {}",
                self.compile_object_reference(&fact.set, position)?
            )),
            AtomicFact::IsSetFact(fact) => Ok(format!(
                "Litex.IsSet {}",
                self.compile_object_reference(&fact.set, position)?
            )),
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => self.compile_order_proposition(fact, position),
            AtomicFact::NotLessFact(f) => Ok(format!(
                "¬ Litex.Lt {} {}",
                self.compile_object_reference(&f.left, position)?,
                self.compile_object_reference(&f.right, position)?
            )),
            AtomicFact::NotGreaterFact(f) => Ok(format!(
                "¬ Litex.Lt {} {}",
                self.compile_object_reference(&f.right, position)?,
                self.compile_object_reference(&f.left, position)?
            )),
            AtomicFact::NotLessEqualFact(f) => Ok(format!(
                "¬ Litex.Le {} {}",
                self.compile_object_reference(&f.left, position)?,
                self.compile_object_reference(&f.right, position)?
            )),
            AtomicFact::NotGreaterEqualFact(f) => Ok(format!(
                "¬ Litex.Le {} {}",
                self.compile_object_reference(&f.right, position)?,
                self.compile_object_reference(&f.left, position)?
            )),
            AtomicFact::IsChoiceFunctionForFact(f) => Ok(format!(
                "Litex.IsChoiceFunctionFor {} {} {} {}",
                self.compile_object_reference(&f.index, position)?,
                self.compile_object_reference(&f.set, position)?,
                self.compile_object_reference(&f.family, position)?,
                self.compile_object_reference(&f.choice, position)?
            )),
            AtomicFact::NotIsChoiceFunctionForFact(f) => Ok(format!(
                "¬ Litex.IsChoiceFunctionFor {} {} {} {}",
                self.compile_object_reference(&f.index, position)?,
                self.compile_object_reference(&f.set, position)?,
                self.compile_object_reference(&f.family, position)?,
                self.compile_object_reference(&f.choice, position)?
            )),
            AtomicFact::IsNonemptySetFact(f) => Ok(format!(
                "Litex.IsNonempty {}",
                self.compile_object_reference(&f.set, position)?
            )),
            AtomicFact::NormalAtomicFact(normal) => {
                self.compile_normal_atomic_proposition(normal, position)
            }
            AtomicFact::NotNormalAtomicFact(normal) => {
                let positive = NormalAtomicFact {
                    fact_id: normal.fact_id,
                    predicate: normal.predicate.clone(),
                    body: normal.body.clone(),
                    line_file: normal.line_file.clone(),
                };
                Ok(format!(
                    "¬ ({})",
                    self.compile_normal_atomic_proposition(&positive, position)?
                ))
            }
            fact if crate::compile_to_lean::compile_mapping_properties::mapping_parts(fact)
                .is_some() =>
            {
                let arguments = atomic_fact_args_ref(fact)
                    .iter()
                    .map(|obj| {
                        self.compile_object_reference(obj, position)
                            .map(|term| format!("(Litex.denote {term})"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                self.compile_atomic_raw_proposition(fact, &arguments, position)
            }
            AtomicFact::HasRiemannIntegralFact(_)
            | AtomicFact::NotHasRiemannIntegralFact(_)
            | AtomicFact::FunctionRiemannIntegrableFact(_)
            | AtomicFact::NotFunctionRiemannIntegrableFact(_)
            | AtomicFact::MultivariableAnalysisFact(_)
            | AtomicFact::NotMultivariableAnalysisFact(_)
            | AtomicFact::HasDerivativeAtFact(_)
            | AtomicFact::NotHasDerivativeAtFact(_)
            | AtomicFact::FunctionDifferentiableAtFact(_)
            | AtomicFact::NotFunctionDifferentiableAtFact(_)
            | AtomicFact::RealSetBoundFact(_)
            | AtomicFact::NotRealSetBoundFact(_)
            | AtomicFact::RealSetBoundedFact(_)
            | AtomicFact::NotRealSetBoundedFact(_)
            | AtomicFact::SequenceAnalysisFact(_)
            | AtomicFact::NotSequenceAnalysisFact(_)
            | AtomicFact::RealAccumulationFact(_)
            | AtomicFact::NotRealAccumulationFact(_)
            | AtomicFact::FunctionContinuousAtFact(_)
            | AtomicFact::NotFunctionContinuousAtFact(_)
            | AtomicFact::FunctionContinuousFact(_)
            | AtomicFact::NotFunctionContinuousFact(_)
            | AtomicFact::FunctionLipschitzFact(_)
            | AtomicFact::NotFunctionLipschitzFact(_)
            | AtomicFact::SupersetFact(_)
            | AtomicFact::ProperSubsetFact(_)
            | AtomicFact::ProperSupersetFact(_)
            | AtomicFact::PrimeFact(_)
            | AtomicFact::CoprimeFact(_)
            | AtomicFact::HasFunctionLimitFact(_)
            | AtomicFact::NotHasFunctionLimitFact(_)
            | AtomicFact::HasSequenceLimsupFact(_)
            | AtomicFact::HasSequenceLiminfFact(_)
            | AtomicFact::HasSequenceLimitFact(_)
            | AtomicFact::NotHasSequenceLimsupFact(_)
            | AtomicFact::NotHasSequenceLiminfFact(_)
            | AtomicFact::NotHasSequenceLimitFact(_)
            | AtomicFact::DvdFact(_)
            | AtomicFact::InjectiveFact(_)
            | AtomicFact::SurjectiveFact(_)
            | AtomicFact::BijectiveFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotSupersetFact(_)
            | AtomicFact::NotProperSubsetFact(_)
            | AtomicFact::NotProperSupersetFact(_)
            | AtomicFact::NotPrimeFact(_)
            | AtomicFact::NotCoprimeFact(_)
            | AtomicFact::NotDvdFact(_)
            | AtomicFact::NotInjectiveFact(_)
            | AtomicFact::NotSurjectiveFact(_)
            | AtomicFact::NotBijectiveFact(_) => {
                Err(LeanCompileError::unsupported("Atomic/PropositionFamily"))
            }
        }
    }

    pub(in crate::compile_to_lean) fn compile_object_reference(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let Obj::InstantiatedTemplateObj(instance) = object {
            if let Some(term) = self.template_self_reference(instance, position)? {
                return Ok(term);
            }
        }
        if let Some(number) = position.enumeration_literal(object) {
            return Ok(format!(
                "(Litex.number (M := M) {})",
                number_literal(number, "ℂ")?
            ));
        }
        if let Some(term) = position.bound_object_child(object) {
            return Ok(term);
        }
        if let Some(term) = position.registered_wd_reference(object, None)? {
            return Ok(term);
        }
        if let Some(term) =
            position.with_visible_alias(object, &mut |parameter, _, _, producer| {
                let name = format!("_object_i{}", parameter.id.value());
                Ok(if producer.is_local() {
                    name
                } else {
                    self.context_application(&name, producer)
                })
            })?
        {
            return Ok(term);
        }
        if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = object {
            if let Some((_, producer)) = position.visible_replacement(*id) {
                return Ok(self.context_application(&format!("_object_i{}", id.value()), &producer));
            }

            if let Ok((_, producer)) = position.visible_piecewise_function(id) {
                return Ok(self.context_application(&format!("_object_i{}", id.value()), &producer));
            }
            if let Ok((_, producer)) = position.visible_selected_function(id) {
                return Ok(self.context_application(&format!("_object_i{}", id.value()), &producer));
            }
            if let Ok((proof, _)) = position.visible_recursive_self(id) {
                return Ok(format!("_object_i{}", proof.statement.name.id.value()));
            }
            if let Ok((proof, producer, _)) = position.visible_recursive_function(id) {
                let name = format!("_object_i{}", proof.statement.name.id.value());
                return Ok(if producer.is_local() {
                    name
                } else {
                    self.context_application(&name, &producer)
                });
            }
            if let Ok((proof, producer, _)) = position.visible_function(id) {
                return Ok(self.context_application(
                    &format!("_object_i{}", proof.statement.name.id.value()),
                    &producer,
                ));
            }
            return self.compile_parameter_reference(*id, position);
        }
        if let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access)) = object {
            return self.compile_struct_field_reference(access, position);
        }
        if let Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(carrier)) = object {
            return self.compile_struct_reference(carrier, position);
        }
        if let Some(carrier) = self.compile_released_struct_carrier(object, position)? {
            return Ok(carrier);
        }
        if let Some(term) = self.compile_recursive_signature_reference(object, position)? {
            return Ok(term);
        }
        if is_literal_coordinate_call(object) {
            if let Some(term) = position
                .with_visible_inferred_subject_filter(object, &mut |store, producer| {
                    self.compile_cart_inferred_subject(object, store, producer)
                })?
            {
                return Ok(term);
            }
        }
        if let Some(term) =
            position.with_visible_wd(object, &mut |wd, producer| self.compile_wd(wd, producer))?
        {
            return Ok(term);
        }
        if let Some(term) = self.compile_obtain_constructor_reference(object, position)? {
            return Ok(term);
        }
        if let Some(term) =
            position.with_visible_inferred_subject(object, &mut |store, producer| {
                if let Some(carrier) = self.compile_released_struct_carrier(object, producer)? {
                    return Ok(carrier);
                }
                if let Some(term) = self.compile_cart_inferred_subject(object, store, producer)? {
                    return Ok(term);
                }
                if let Some((term, _)) =
                    self.compile_preimage_inferred_subject(object, store, producer)?
                {
                    return Ok(term);
                }
                if let Some(term) =
                    self.compile_inferred_builder_constructor(object, store, producer)?
                {
                    return Ok(term);
                }
                if let Some(term) =
                    self.compile_sequence_inferred_subject(object, store, producer)?
                {
                    return Ok(term);
                }
                // The named rule creates this primitive; its Lean constructor proves WD.
                // This is not a replacement Verify result or an arbitrary cache fallback.
                self.compile_inferred_obj(object, position)
            })?
        {
            return Ok(term);
        }
        if let Some(term) = self.compile_callee_constructor_reference(object, position)? {
            return Ok(term);
        }
        Err(LeanCompileError::new(
            "WD/Producer",
            &format!(
                "No preceding original constructor or certified parameter supplies `{}`.",
                object.readable_string()
            ),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_parameter_reference(
        &self,
        id: IdentifierId,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        position
            .visible_parameter(id, &self.runtime)
            .map(|(parameter, _, _, _)| {
                let name = format!("_value_i{}", parameter.id.value());
                match position.global_obtain_position(id) {
                    Some(producer) => self.context_application(&name, &producer),
                    None => name,
                }
            })
            .map_err(|_| {
                LeanCompileError::new(
                    "Identifier/Producer",
                    "The identifier has no preceding parameter producer in this original ancestry.",
                )
            })
    }
}
