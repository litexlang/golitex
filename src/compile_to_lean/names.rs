use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::ExecDefPropStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn source_universes(
        &self,
        result: &RunLitexCodeResult,
    ) -> Result<String, LeanCompileError> {
        fn parameters<'s>(fact: &'s Fact, out: &mut Vec<IdentifierId>) {
            if let Fact::ForallFact(fact) = fact {
                for group in &fact.typed_parameters.groups {
                    for parameter in &group.params {
                        if !out.contains(&parameter.id) {
                            out.push(parameter.id);
                        }
                    }
                }
            }
        }
        fn verify(result: &VerifyFactResult, out: &mut Vec<IdentifierId>) {
            if let VerifyFactResult::ForallFact(result) = result {
                if let VerifyForallFactResult::Success(proof) = result.as_ref() {
                    parameters(&Fact::ForallFact(proof.fact().clone()), out);
                }
            }
        }
        fn statement(result: &ExecStmtResult, out: &mut Vec<IdentifierId>) {
            match result {
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
    ) -> String {
        let name = format!("h_{}", source.fact_id().value());
        let kind = if local { "have" } else { "theorem" };
        let declaration = format!(
            "{kind} {name}{} : {} :=\n  {}",
            if local {
                String::new()
            } else {
                self.context_header(position)
            },
            fact.0,
            fact.1.replace('\n', "\n  ")
        );
        declaration
    }

    pub(in crate::compile_to_lean) fn context_header(
        &self,
        position: &SourcePosition<'_>,
    ) -> String {
        let binders = position.context_parameters().into_iter().map(|(parameter, set, fact_id)| {
            let id = parameter.id.value();
            let fact_id = fact_id.value();
            let proposition = match set {
                Some(Obj::StandardSet(set)) => format!("Litex.In _value_i{id} {}", standard_term(set).expect("validated numeric carrier")),
                None => format!("Litex.IsSet _value_i{id}"),
                _ => unreachable!("validated context carrier"),
            };
            format!("{{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id}) (h_{fact_id} : {proposition})")
        }).collect::<Vec<_>>();
        if binders.is_empty() {
            String::new()
        } else {
            format!(" {}", binders.join(" "))
        }
    }

    pub(in crate::compile_to_lean) fn context_application(
        &self,
        name: &str,
        position: &SourcePosition<'_>,
    ) -> String {
        let arguments = position.context_arguments();
        if arguments.is_empty() {
            format!("({name} (M := M))")
        } else {
            let arguments = arguments.split_whitespace().collect::<Vec<_>>();
            let arguments = arguments
                .chunks_exact(4)
                .map(|group| {
                    format!(
                        "({} := {}) ({} := {}) {} {}",
                        group[0], group[0], group[1], group[1], group[2], group[3]
                    )
                })
                .collect::<Vec<_>>()
                .join(" ");
            format!("({name} (M := M) {arguments})")
        }
    }

    /// Local producer names used inside constructor WD must also be in scope
    /// when the public proposition is formed. These let values are the actual
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
                .filter(|token| token.starts_with("h_") || token.starts_with("_object_i"))
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
        let declarations = selected
            .into_iter()
            .map(|chunk| {
                if let Some(body) = chunk.strip_prefix("have ") {
                    format!("let {body}")
                } else {
                    chunk.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join(";\n");
        format!("({declarations};\n{proposition})")
    }

    pub(in crate::compile_to_lean) fn emit_internal_fact(
        &self,
        fact: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> String {
        let name = format!("h_{}", fact.fact_id().value());
        let local = position.is_local();
        format!(
            "{} {name}{} : {} :=\n  {}",
            if local { "have" } else { "theorem" },
            if local {
                String::new()
            } else {
                self.context_header(position)
            },
            compiled.0,
            compiled.1.replace('\n', "\n  ")
        )
    }

    pub(in crate::compile_to_lean) fn introduce_numeric_parameter(
        &self,
        parameter: &BoundName,
        set: &Obj,
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let id = parameter.id;
        let host = format!("_Host_i{}", id.value());
        let universe = format!("v{}", id.value());

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

    pub(in crate::compile_to_lean) fn introduce_set_parameter(
        &self,
        parameter: &BoundName,
        store: &StoreFactAndInferResult,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let fact = self.resolve_fact(store.primary_fact_id(), position)?;
        let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        if !matches!(&fact, Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir() == object.ir())
        {
            return Err(LeanCompileError::new(
                "Parameters/SetSubject",
                "The set-kind parameter has another original sethood store.",
            ));
        }
        self.validate_store(&store.store, &fact)?;
        let id = parameter.id.value();
        let name = format!("h_{}", fact.fact_id().value());
        let binders = vec![format!("{{_Host_i{id} : Type v{id}}} [_rep_i{id} : Litex.Representation M _Host_i{id}] (_value_i{id} : Litex.Obj (M := M) _Host_i{id})"), format!("({name} : Litex.IsSet _value_i{id})")];
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
            AtomicFact::SubsetFact(fact) => Ok(format!(
                "Litex.Subset {} {}",
                self.compile_object_reference(&fact.left, position)?,
                self.compile_object_reference(&fact.right, position)?
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
            AtomicFact::IsNonemptySetFact(f) => Ok(format!(
                "Litex.IsNonempty {}",
                self.compile_object_reference(&f.set, position)?
            )),
            AtomicFact::NormalAtomicFact(normal) => {
                self.compile_normal_atomic_proposition(normal, position)
            }
            AtomicFact::IsFiniteSetFact(_)
            | AtomicFact::SupersetFact(_)
            | AtomicFact::ProperSubsetFact(_)
            | AtomicFact::ProperSupersetFact(_)
            | AtomicFact::PrimeFact(_)
            | AtomicFact::CoprimeFact(_)
            | AtomicFact::DvdFact(_)
            | AtomicFact::InjectiveFact(_)
            | AtomicFact::SurjectiveFact(_)
            | AtomicFact::BijectiveFact(_)
            | AtomicFact::IsChoiceFunctionForFact(_)
            | AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotInFact(_)
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
            | AtomicFact::NotProperSubsetFact(_)
            | AtomicFact::NotProperSupersetFact(_)
            | AtomicFact::NotPrimeFact(_)
            | AtomicFact::NotCoprimeFact(_)
            | AtomicFact::NotDvdFact(_)
            | AtomicFact::NotInjectiveFact(_)
            | AtomicFact::NotSurjectiveFact(_)
            | AtomicFact::NotBijectiveFact(_)
            | AtomicFact::NotIsChoiceFunctionForFact(_) => {
                Err(LeanCompileError::unsupported("Atomic/PropositionFamily"))
            }
        }
    }

    pub(in crate::compile_to_lean) fn compile_object_reference(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
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
            if let Ok((proof, producer, _)) = position.visible_function(id) {
                return Ok(self.context_application(
                    &format!("_object_i{}", proof.statement.name.id.value()),
                    &producer,
                ));
            }
            return self.compile_parameter_reference(*id, position);
        }
        if let Some(term) =
            position.with_visible_wd(object, &mut |wd, producer| self.compile_wd(wd, producer))?
        {
            return Ok(term);
        }
        if let Some(term) = position.with_visible_inferred_subject(object, &mut |_, _| {
            // The named rule creates this primitive; its Lean constructor proves WD.
            // This is not a replacement Verify result or an arbitrary cache fallback.
            self.compile_inferred_obj(object, position)
        })? {
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
            .map(|(parameter, _, _, _)| format!("_value_i{}", parameter.id.value()))
            .map_err(|_| {
                LeanCompileError::new(
                    "Identifier/Producer",
                    "The identifier has no preceding parameter producer in this original ancestry.",
                )
            })
    }
}
