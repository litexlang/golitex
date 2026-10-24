use crate::compile_to_lean::compile_callee_constructor::exact_constructor_pattern;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactWellDefinedProof;
use crate::execute::{
    ExecObtainObjFromAtomicFactStmtResult, ExecObtainObjFromExistFactStmtResult,
    ObtainExistVerifySuccess,
};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    /// Instantiate an original existential constructor at its obtained names.
    /// The producer stores renamed clauses, but does not run their WD again.
    pub(in crate::compile_to_lean) fn compile_obtain_constructor_reference(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        self.compile_obtain_expression_reference(object, position, false)
    }

    pub(in crate::compile_to_lean) fn compile_obtain_expression_reference(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
        observe_numeric: bool,
    ) -> Result<Option<String>, LeanCompileError> {
        if !matches!(
            object,
            Obj::ArithmeticOperator(_) | Obj::FnObj(_) | Obj::SetFormer(SetFormer::ListSet(_))
        ) {
            return Ok(None);
        }
        position.with_visible_obtain(&mut |obtain, current| match obtain {
            ExecDefineObjStmtResult::ObtainObjFromExistFact(
                ExecObtainObjFromExistFactStmtResult::Success(obtain),
            ) => {
                let (source, formation) = match &obtain.verify_exist {
                    ObtainExistVerifySuccess::Exist(p) => (p.fact.plain(), &p.well_defined_proof),
                    ObtainExistVerifySuccess::ExistUnique(p) => {
                        (p.fact.plain(), &p.well_defined_proof)
                    }
                };
                self.compile_obtain_constructor_in_source(
                    object,
                    source,
                    formation,
                    &obtain.statement.equal_tos,
                    &obtain.store_and_infer_result,
                    &HashMap::new(),
                    current,
                    current,
                    observe_numeric,
                )
                .map(|found| {
                    found.map(|(factory, arguments)| apply_constructor(factory, arguments))
                })
            }
            ExecDefineObjStmtResult::ObtainObjFromAtomicFact(
                ExecObtainObjFromAtomicFactStmtResult::Success(obtain),
            ) => {
                let (declaration, parent, _) =
                    current.visible_prop(&obtain.statement.fact.predicate)?;
                let (source, formation) = match (
                    declaration.statement.iff_facts.as_slice(),
                    declaration.assumed_iff_facts.as_slice(),
                ) {
                    ([Fact::ExistFact(source)], [captured]) => match &captured.well_defined {
                        FactWellDefinedProof::ExistFact(formation) => (source, formation),
                        _ => return Err(LeanCompileError::unsupported("ObtainAtomic/Formation")),
                    },
                    _ => return Err(LeanCompileError::unsupported("ObtainAtomic/Definition")),
                };
                let substitution =
                    self.prop_argument_substitution(declaration, &obtain.statement.fact)?;
                let original = SourcePosition::new(
                    Some(&parent),
                    SourceOwner::PropDefinition(declaration),
                    declaration
                        .statement
                        .typed_parameters
                        .ordered_param_ids()
                        .len(),
                );
                let Some((body, arguments)) = self.compile_obtain_constructor_in_source(
                    object,
                    source,
                    formation,
                    &obtain.statement.equal_tos,
                    &obtain.store_and_infer_result,
                    &substitution,
                    &original,
                    current,
                    observe_numeric,
                )?
                else {
                    return Ok(None);
                };
                let prior = SourcePosition {
                    before: 0,
                    ..*current
                };
                let (_, predicate) = self.compile_verify(&obtain.verify_atomic, &prior)?;
                self.compile_prop_parameter_instance(
                    declaration,
                    &obtain.statement.fact,
                    body,
                    &predicate,
                    &original,
                    current,
                )
                .map(|factory| Some(apply_constructor(factory, arguments)))
            }
            ExecDefineObjStmtResult::HaveObjByExistFacts(
                crate::execute::ExecHaveObjByExistFactsStmtResult::Success(have),
            ) => {
                let ExistShapedFact::Exist(source) = &have.verify_exist.fact else {
                    return Ok(None);
                };
                let outputs: Vec<_> = have
                    .statement
                    .param_def
                    .groups
                    .iter()
                    .flat_map(|g| g.params.iter().cloned())
                    .collect();
                self.compile_obtain_constructor_in_source(
                    object,
                    source,
                    &have.verify_exist.well_defined_proof,
                    &outputs,
                    &have.store_and_infer_result,
                    &HashMap::new(),
                    current,
                    current,
                    observe_numeric,
                )
                .map(|found| {
                    found.map(|(factory, arguments)| apply_constructor(factory, arguments))
                })
            }
            ExecDefineObjStmtResult::HaveByFnPreimage(
                crate::execute::ExecHaveByFnPreimageStmtResult::Success(p),
            ) => self.compile_preimage_call_reference(object, p, current, observe_numeric),
            _ => Ok(None),
        })
    }

    fn compile_obtain_constructor_in_source(
        &self,
        object: &Obj,
        source: &PlainExistFact,
        formation: &ExistShapedFactWellDefinedProof,
        outputs: &[BoundName],
        captured: &StoreHaveObjAndInferResult,
        outer_substitution: &HashMap<IdentifierId, Obj>,
        original_parent: &SourcePosition<'_>,
        current: &SourcePosition<'_>,
        observe_numeric: bool,
    ) -> Result<Option<(String, Vec<String>)>, LeanCompileError> {
        let ids = source.typed_parameters.ordered_param_ids();
        let renaming: HashMap<_, _> = ids
            .iter()
            .copied()
            .zip(
                outputs
                    .iter()
                    .map(|name| Obj::Identifier(IdentifierObj::from_bound_name(name))),
            )
            .collect();
        if renaming.len() != ids.len() || ids.len() != outputs.len() {
            return Err(LeanCompileError::unsupported("Obtain/ConstructorArguments"));
        }
        let mut substitution = outer_substitution.clone();
        substitution.extend(renaming);
        let original = SourcePosition::new(
            Some(original_parent),
            SourceOwner::ExistWD(source, formation),
            0,
        );
        let mut parameter_count = 0;
        for (group, wd) in source
            .typed_parameters
            .groups
            .iter()
            .zip(&formation.introduced_params.param_type_well_defined)
        {
            if current.before < parameter_count + 2 {
                break;
            }
            if let ParamType::Obj(carrier) = &group.param_type {
                if let Some(pattern) = exact_constructor_pattern(carrier, object, &substitution) {
                    let prior = SourcePosition {
                        before: parameter_count,
                        ..original
                    };
                    let formed =
                        SourcePosition::new(Some(&prior), SourceOwner::ParamTypeWD(wd), usize::MAX);
                    return formed.with_visible_wd(pattern, &mut |checked, site| {
                        self.compile_obtain_constructor_factory(
                            source,
                            formation,
                            outputs,
                            captured,
                            original_parent,
                            parameter_count,
                            0,
                            checked,
                            site,
                            current,
                            observe_numeric,
                        )
                    });
                }
            }
            parameter_count += group.params.len();
        }
        for (index, (clause, stage)) in source
            .facts
            .iter()
            .zip(&formation.assumed_body_facts)
            .enumerate()
        {
            if current.before < ids.len() + index + 2 {
                break;
            }
            let roots: Vec<&Obj> = match clause {
                QuantifierFreeFact::AtomicFact(fact) => atomic_fact_args_ref(fact),
                QuantifierFreeFact::AndFact(fact) => {
                    fact.facts.iter().flat_map(atomic_fact_args_ref).collect()
                }
                QuantifierFreeFact::ChainFact(fact) => fact.objs.iter().collect(),
                QuantifierFreeFact::OrFact(_) => Vec::new(),
            };
            if let Some(pattern) = roots
                .into_iter()
                .find_map(|root| exact_constructor_pattern(root, object, &substitution))
            {
                let prior = SourcePosition {
                    before: ids.len() + index,
                    ..original
                };
                let formed = SourcePosition::new(
                    Some(&prior),
                    SourceOwner::FactWD(&stage.well_defined),
                    usize::MAX,
                );
                return formed.with_visible_wd(pattern, &mut |checked, site| {
                    self.compile_obtain_constructor_factory(
                        source,
                        formation,
                        outputs,
                        captured,
                        original_parent,
                        ids.len(),
                        index,
                        checked,
                        site,
                        current,
                        observe_numeric,
                    )
                });
            }
        }
        Ok(None)
    }

    fn compile_obtain_constructor_factory(
        &self,
        source: &PlainExistFact,
        formation: &ExistShapedFactWellDefinedProof,
        outputs: &[BoundName],
        captured: &StoreHaveObjAndInferResult,
        original_parent: &SourcePosition<'_>,
        parameter_count: usize,
        clause_count: usize,
        checked: &ObjWellDefinedProof,
        site: &SourcePosition<'_>,
        caller: &SourcePosition<'_>,
        observe_numeric: bool,
    ) -> Result<(String, Vec<String>), LeanCompileError> {
        let (binders, definitions) = self.compile_exist_constructor_prefix(
            source,
            formation,
            parameter_count,
            clause_count,
            original_parent,
        )?;
        let constructor = self.compile_wd(checked, site)?;
        let body = if definitions.is_empty() {
            constructor
        } else {
            format!(
                "(show Litex.Obj (M := M) _ from by\n  {}\n  exact {constructor}\n)",
                definitions.join("\n").replace('\n', "\n  ")
            )
        };
        let body = if observe_numeric {
            // The same retained WD factory supplies the scalar observation;
            // obtained names have renamed stores, not a second WD proof tree.
            let (value, denotation, member, _) = self.numeric_wd(checked, site)?;
            // Keep the scalar field transparent to definitional reduction.
            // A tactic-generated subtype term defers its value behind a fresh
            // metavariable at each use of .val / .property.
            let definitions = if definitions.is_empty() {
                String::new()
            } else {
                format!("{};\n", definitions.join(";\n"))
            };
            format!("(let _obtained_object := {body};\n{definitions}show {{ _z : ℂ // Litex.denote _obtained_object = M.number _z ∧ Litex.In _obtained_object Litex.C }} from ⟨{value}, {denotation}, {member}⟩)")
        } else {
            body
        };
        let factory = if binders.is_empty() {
            body
        } else {
            format!("(fun {} => {body})", binders.join(" "))
        };
        let stores = &captured.store_and_infer_results;
        let mut arguments = Vec::new();
        for (index, parameter) in outputs.iter().take(parameter_count).enumerate() {
            arguments.push(self.compile_parameter_reference(parameter.id, caller)?);
            arguments.push(
                self.cited_fact_reference(stores[index].primary_fact_id(), caller)?
                    .1,
            );
        }
        let all_parameters = source.typed_parameters.ordered_param_ids().len();
        for store in stores.iter().skip(all_parameters).take(clause_count) {
            arguments.push(
                self.cited_fact_reference(store.primary_fact_id(), caller)?
                    .1,
            );
        }
        Ok((factory, arguments))
    }

    /// Only assumptions preceding the selected source constructor are binders.
    /// Their actual inference results are local definitions inside the factory.
    pub(in crate::compile_to_lean) fn compile_exist_constructor_prefix(
        &self,
        source: &PlainExistFact,
        formation: &ExistShapedFactWellDefinedProof,
        parameter_count: usize,
        clause_count: usize,
        parent: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let scope = SourcePosition::new(Some(parent), SourceOwner::ExistWD(source, formation), 0);
        self.validate_parameter_store_capture(&formation.introduced_params.defined_params)?;
        let mut binders = Vec::new();
        let mut definitions = Vec::new();
        let mut index = 0;
        for (group, wd) in source
            .typed_parameters
            .groups
            .iter()
            .zip(&formation.introduced_params.param_type_well_defined)
        {
            if index >= parameter_count {
                break;
            }
            let prior = SourcePosition {
                before: index,
                ..scope
            };
            match (&group.param_type, wd) {
                (ParamType::Obj(carrier), ParamTypeWellDefinedProof::Obj(checked)) => {
                    ensure_object(carrier, checked)?;
                    self.compile_wd(checked, &prior)?;
                }
                (ParamType::Set(_), ParamTypeWellDefinedProof::Set) => {}
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "Obtain/ConstructorParameterKind",
                    ))
                }
            }
            for parameter in &group.params {
                if index >= parameter_count {
                    break;
                }
                let introduced = SourcePosition {
                    before: index + 1,
                    ..scope
                };
                let formed = SourcePosition::new(
                    Some(&introduced),
                    SourceOwner::ParamTypeWD(wd),
                    usize::MAX,
                );
                let store = &formation
                    .introduced_params
                    .defined_params
                    .store_and_infer_results[index];
                let fact = self.resolve_fact(store.primary_fact_id(), &introduced)?;
                self.validate_store(&store.store, &fact)?;
                let proposition = self.fact_proposition(&fact, &formed)?;
                let name = format!("h_{}", fact.fact_id().value());
                binders.push(format!(
                    "(_value_i{} : Litex.Obj (M := M) M.Value)",
                    parameter.id.value()
                ));
                binders.push(format!(
                    "({name} : {})",
                    self.scope_proposition(proposition.clone(), &definitions)
                ));
                definitions.extend(self.compile_parameter_inferences(
                    store,
                    &fact,
                    &(proposition, name),
                    &introduced,
                )?);
                index += 1;
            }
        }
        if index != parameter_count
            || clause_count > source.facts.len()
            || clause_count > formation.assumed_body_facts.len()
        {
            return Err(LeanCompileError::unsupported("Obtain/ConstructorPrefix"));
        }
        for (index, (clause, captured)) in source
            .facts
            .iter()
            .zip(&formation.assumed_body_facts)
            .take(clause_count)
            .enumerate()
        {
            let fact = crate::instantiate::quantifier_free_fact_to_fact(clause.clone());
            let prior = SourcePosition {
                before: parameter_count + index,
                ..scope
            };
            self.compile_fact_wd(&captured.well_defined, &fact, &prior)?;
            self.validate_store(&captured.store_and_infer.store, &fact)?;
            let formed = SourcePosition::new(
                Some(&prior),
                SourceOwner::FactWD(&captured.well_defined),
                usize::MAX,
            );
            let proposition = self.fact_proposition(&fact, &formed)?;
            let name = format!("h_{}", fact.fact_id().value());
            binders.push(format!(
                "({name} : {})",
                self.scope_proposition(proposition.clone(), &definitions)
            ));
            let completed = SourcePosition {
                before: parameter_count + index + 1,
                ..scope
            };
            definitions.extend(self.compile_stored_inferences(
                &captured.store_and_infer,
                &fact,
                &(proposition, name),
                &completed,
            )?);
        }
        Ok((binders, definitions))
    }
}

fn apply_constructor(factory: String, arguments: Vec<String>) -> String {
    if arguments.is_empty() {
        factory
    } else {
        format!("({factory} {})", arguments.join(" "))
    }
}
