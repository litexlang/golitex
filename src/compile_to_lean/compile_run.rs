use super::LeanCompileError;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite;
use crate::prelude::*;
use crate::rational_expression::ClosedNumericExpr;
use crate::store_fact_and_infer::{InferFactResult, InferAtomicFactResult, InferAtomicExceptEqualityResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::AtomicExceptEqualityFactSearchProofByBuiltinOrderDual;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
    greater::GreaterFactSearchProofByBuiltinRule,
    greater_equal::GreaterEqualFactSearchProofByBuiltinRule,
    less::LessFactSearchProofByBuiltinRule,
    less_equal::LessEqualFactSearchProofByBuiltinRule,
    not_equal::NotEqualFactSearchProofByBuiltinRule,
};
use crate::rational_expression::NumberCompareResult;

use std::collections::HashMap;

/// Replay a successful typed execution result while its citation context is live.
/// The complete artifact is returned only after every selected route succeeds.
pub fn compile_run(
    result: &RunLitexCodeResult,
    runtime: &Runtime,
    artifact_namespace: &str,
) -> Result<String, LeanCompileError> {
    validate_namespace(artifact_namespace)?;
    if !result.success
        || result.session_error.is_some()
        || result
            .statement_results
            .iter()
            .any(ExecStmtResult::is_failed)
    {
        return Err(LeanCompileError::new(
            "source_failed",
            "Only a complete successful source run can be compiled.",
        ));
    }
    let mut compiler = LeanCompiler::new();
    let mut declarations = Vec::new();
    for (index, result) in result.statement_results.iter().enumerate() {
        let compiled = compiler
            .compile_statement(result, runtime, index + 1)
            .map_err(|mut error| {
                error.statement_index = Some(index + 1);
                error
            })?;
        declarations.push(compiled);
    }
    let universes = if compiler.universes.is_empty() {
        "u".to_string()
    } else {
        format!("u {}", compiler.universes.join(" "))
    };
    Ok(format!("import Litex\n\nnamespace LitexCompiled.{artifact_namespace}\n\nuniverse {universes}\nvariable {{M : Litex.Semantics.{{u}}}}\n\n{}\nend LitexCompiled.{artifact_namespace}\n", declarations.join("\n\n")))
}

#[derive(Clone)]
struct ObjectTerm {
    object: Obj,
    term: String,
    numeric: Option<NumericTerm>,
}

#[derive(Clone)]
struct NumericTerm {
    value: String,
    denotation: String,
    member: String,
    closed: Option<EvalRational>,
}

#[derive(Clone)]
struct NamedTheorem {
    declaration: DefThmStmt,
    term: String,
}

#[derive(Clone)]
struct FactTerm {
    fact: Fact,
    proposition: String,
    proof: String,
}

#[derive(Default)]
struct CompilerScope {
    env: Option<Box<ExecEnv>>,
    identifiers: HashMap<IdentifierId, ObjectTerm>,
    objects: HashMap<ObjIR, ObjectTerm>,
    facts: HashMap<FactId, FactTerm>,
    wds: HashMap<WellDefinednessId, ObjectTerm>,
    theorems: HashMap<String, NamedTheorem>,
    real_members: HashMap<ObjIR, String>,
}

struct LeanCompiler {
    scopes: Vec<CompilerScope>,
    universes: Vec<String>,
    context_binders: Vec<String>,
    context_arguments: Vec<String>,
}

impl LeanCompiler {
    fn new() -> Self {
        Self {
            scopes: vec![CompilerScope::default()],
            universes: Vec::new(),
            context_binders: Vec::new(),
            context_arguments: Vec::new(),
        }
    }

    fn compile_statement(
        &mut self,
        result: &ExecStmtResult,
        runtime: &Runtime,
        index: usize,
    ) -> Result<String, LeanCompileError> {
        self.compile_statement_in_scope(result, runtime, index, false)
    }

    fn compile_statement_in_scope(
        &mut self,
        result: &ExecStmtResult,
        runtime: &Runtime,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        match result {
            ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => {
                let compiled = self.compile_verify(&success.verify_result, runtime)?;
                self.validate_store(&success.store_and_infer_result, &compiled.fact)?;
                Ok(self.emit_fact(compiled, index, local))
            }
            ExecStmtResult::Fact(ExecFactStmtResult::Failed(_)) => Err(LeanCompileError::new(
                "Fact/Failed",
                "A failed fact is not proof evidence.",
            )),
            ExecStmtResult::Definition(result) => match result {
                ExecDefinitionStmtResult::DefineObj(result) => match result {
                    ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)) => {
                        self.compile_let(proof, runtime, local)
                    }
                    ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(
                        proof,
                    )) => self.compile_have_equal(proof, runtime, local),
                    ExecDefineObjStmtResult::HaveObjInNonemptySet(
                        ExecHaveObjInNonemptySetStmtResult::Success(proof),
                    ) => self.compile_arbitrary_have(proof, runtime, local),
                    _ => Err(LeanCompileError::unsupported("Definition/DefineObj")),
                },
                ExecDefinitionStmtResult::DefThm(ExecDefThmStmtResult::Success(proof))
                    if !local =>
                {
                    self.compile_named_theorem(proof, runtime, index)
                }
                _ => Err(LeanCompileError::unsupported("Definition")),
            },
            ExecStmtResult::Witness(_) => Err(LeanCompileError::unsupported("Witness")),
            ExecStmtResult::Trust(_) => Err(LeanCompileError::unsupported("Trust")),
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) => {
                let compiled = self.compile_by_theorem(proof, runtime)?;
                Ok(self.emit_fact(compiled, index, local))
            }
            ExecStmtResult::By(_) => Err(LeanCompileError::unsupported("By")),
            ExecStmtResult::Register(_) => Err(LeanCompileError::unsupported("Register")),
            ExecStmtResult::ReleaseAndExpand(_) => {
                Err(LeanCompileError::unsupported("ReleaseAndExpand"))
            }
            ExecStmtResult::ProofBlock(_) => Err(LeanCompileError::unsupported("ProofBlock")),
            ExecStmtResult::Command(_) => Err(LeanCompileError::unsupported("Command")),
        }
    }

    fn emit_fact(&mut self, mut fact: FactTerm, index: usize, local: bool) -> String {
        let name = if local {
            format!("_fact_f{}", fact.fact.fact_id().value())
        } else {
            format!("fact_{index}")
        };
        let kind = if local { "have" } else { "theorem" };
        let declaration = format!(
            "{kind} {name}{} : {} :=\n  {}",
            if local {
                String::new()
            } else {
                self.context_header()
            },
            fact.proposition,
            fact.proof.replace('\n', "\n  ")
        );
        fact.proof = if local {
            name
        } else {
            self.context_application(&name)
        };
        self.remember_fact(fact);
        declaration
    }

    fn context_header(&self) -> String {
        if self.context_binders.is_empty() {
            String::new()
        } else {
            format!(" {}", self.context_binders.join(" "))
        }
    }

    fn context_application(&self, name: &str) -> String {
        if self.context_arguments.is_empty() {
            format!("({name} (M := M))")
        } else {
            format!("(@{name} M {})", self.context_arguments.join(" "))
        }
    }

    fn compile_arbitrary_have(
        &mut self,
        proof: &ExecHaveObjInNonemptySetStmtSuccessResult,
        runtime: &Runtime,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        if local
            || self.scopes.len() != 1
            || proof.auto_opened_struct_layers.is_some()
            || proof.groups.len() != proof.statement.param_def.groups.len()
        {
            return Err(LeanCompileError::unsupported("Have/ContextProfile"));
        }
        let aggregate: Vec<_> = proof
            .groups
            .iter()
            .flat_map(|g| g.defined_params.stored_fact_ids.iter().copied())
            .collect();
        if aggregate != proof.store_and_infer_result.stored_fact_ids {
            return Err(LeanCompileError::new(
                "Have/Aggregate",
                "The group stores do not equal the ordered statement stores.",
            ));
        }
        let grouped: Vec<_> = proof
            .groups
            .iter()
            .flat_map(|g| &g.defined_params.store_and_infer_results)
            .collect();
        if grouped.len() != proof.store_and_infer_result.store_and_infer_results.len()
            || grouped
                .iter()
                .zip(&proof.store_and_infer_result.store_and_infer_results)
                .any(|(group, aggregate)| !std::rc::Rc::ptr_eq(group, aggregate))
        {
            return Err(LeanCompileError::new(
                "Have/SharedStores",
                "Group and aggregate capture do not refer to the same parameter-store executions.",
            ));
        }
        self.validate_parameter_store_capture(&proof.store_and_infer_result)?;
        let mut declarations = Vec::new();
        for (group, captured) in proof.statement.param_def.groups.iter().zip(&proof.groups) {
            let set = match &group.param_type {
                ParamType::Obj(Obj::StandardSet(set)) => set,
                _ => return Err(LeanCompileError::unsupported("Have/NumericCarrier")),
            };
            standard_term(set)?;
            let carrier = Obj::StandardSet(set.clone());
            match &captured.param_type_well_defined {
                ParamTypeWellDefinedProof::Obj(wd) => {
                    self.compile_wd(success_object_wd(wd, &carrier)?, runtime)?;
                }
                _ => return Err(LeanCompileError::unsupported("Have/CarrierWD")),
            }
            let nonempty = match &captured.nonempty_check {
                ParamTypeFactCheckResult::Obj(result) => self.compile_verify(result, runtime)?,
                _ => return Err(LeanCompileError::unsupported("Have/NonemptyCheck")),
            };
            match &nonempty.fact {
                Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact))
                    if fact.set.ir() == carrier.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "Have/NonemptySubject",
                        "The captured nonempty check proves another carrier.",
                    ))
                }
            }
            let check_name = format!("_nonempty_f{}", nonempty.fact.fact_id().value());
            declarations.push(format!(
                "theorem {check_name}{} : {} := {}",
                self.context_header(),
                nonempty.proposition,
                nonempty.proof
            ));
            self.validate_parameter_store_capture(&captured.defined_params)?;
            if captured.defined_params.store_and_infer_results.len() != group.params.len() {
                return Err(LeanCompileError::new(
                    "Have/ParameterStores",
                    "Each declared parameter needs its own actual store.",
                ));
            }
            for (parameter, store) in group
                .params
                .iter()
                .zip(&captured.defined_params.store_and_infer_results)
            {
                let (binders, arguments) =
                    self.introduce_numeric_parameter(parameter, &carrier, store, runtime)?;
                declarations.push(format!("variable {}", binders.join(" ")));
                self.context_binders.extend(binders);
                self.context_arguments.extend(arguments);
            }
        }
        Ok(declarations.join("\n\n"))
    }

    fn validate_parameter_store_capture(
        &self,
        result: &StoreHaveObjAndInferResult,
    ) -> Result<(), LeanCompileError> {
        let ids: Vec<_> = result
            .store_and_infer_results
            .iter()
            .flat_map(|store| store.stored_fact_ids())
            .collect();
        if ids != result.stored_fact_ids {
            return Err(LeanCompileError::new(
                "Parameters/StoreCapture",
                "The actual ordered store trees do not match their ID view.",
            ));
        }
        Ok(())
    }

    fn introduce_numeric_parameter(
        &mut self,
        parameter: &BoundName,
        set: &Obj,
        store: &StoreFactAndInferResult,
        runtime: &Runtime,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let id = parameter.id;
        let host = format!("_Host_i{}", id.value());
        let universe = format!("v{}", id.value());
        if !self.universes.contains(&universe) {
            self.universes.push(universe.clone());
        }
        let instance = format!("_rep_i{}", id.value());
        let value = format!("_value_i{}", id.value());
        let hypothesis = format!("_h_param_i{}", id.value());
        let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let fact = self.resolve_fact(store.primary_fact_id(), runtime)?;
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
        self.validate_store(store, &fact)?;
        let term = ObjectTerm {
            object: object.clone(),
            term: value.clone(),
            numeric: None,
        };
        let scope = self.scopes.last_mut().expect("compiler scope");
        if scope.identifiers.contains_key(&id) || scope.objects.contains_key(&object.ir()) {
            return Err(LeanCompileError::new(
                "Parameters/Identity",
                "Duplicate parameter identity.",
            ));
        }
        scope.identifiers.insert(id, term.clone());
        scope.objects.insert(object.ir(), term);
        let proposition = self.fact_proposition(&fact)?;
        if set == &Obj::StandardSet(StandardSet::C) {
            self.remember_complex_member(&object, &hypothesis)?;
        }
        let member = FactTerm {
            fact,
            proposition: proposition.clone(),
            proof: hypothesis.clone(),
        };
        self.remember_fact(member.clone());
        if set == &Obj::StandardSet(StandardSet::R) {
            self.remember_real_member(&object, &hypothesis);
        }
        self.compile_parameter_inferences(store, &member, runtime)?;
        Ok((vec![format!("{{{host} : Type {universe}}} [{instance} : Litex.Representation M {host}] ({value} : Litex.Obj (M := M) {host})"), format!("({hypothesis} : {proposition})")], vec![host, instance, value, hypothesis]))
    }

    fn real_member(&self, object: &Obj) -> Result<String, LeanCompileError> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.real_members.get(&object.ir()).cloned())
            .ok_or_else(|| {
                LeanCompileError::new(
                    "Real/Producer",
                    "No real-membership certificate was replayed for this object.",
                )
            })
    }

    fn remember_real_member(&mut self, object: &Obj, proof: &str) {
        self.scopes
            .last_mut()
            .expect("compiler scope")
            .real_members
            .insert(object.ir(), proof.to_string());
    }

    fn compile_parameter_inferences(
        &mut self,
        store: &StoreFactAndInferResult,
        member: &FactTerm,
        runtime: &Runtime,
    ) -> Result<(), LeanCompileError> {
        let rules = match &store.infer {
            InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) => rules,
            _ => return Ok(()),
        };
        for rule in rules {
            if let InferAtomicExceptEqualityResult::InFactSignedStandardSetSign(sign) = rule {
                let source = match &member.fact {
                    Fact::AtomicFact(AtomicFact::InFact(f))
                        if f.set == Obj::StandardSet(StandardSet::N) =>
                    {
                        f
                    }
                    _ => return Err(LeanCompileError::unsupported("Inference/SignedCarrier")),
                };
                if sign.derived.len() != 1 {
                    return Err(LeanCompileError::new(
                        "Inference/NaturalArity",
                        "Natural membership has exactly one nonnegative projection.",
                    ));
                }
                let derived = &sign.derived[0];
                let fact = self.resolve_fact(derived.primary_fact_id(), runtime)?;
                let bound = match &fact {
                    Fact::AtomicFact(AtomicFact::LessEqualFact(f))
                        if is_exact_zero(&f.left) && f.right.ir() == source.element.ir() =>
                    {
                        f
                    }
                    _ => {
                        return Err(LeanCompileError::new(
                            "Inference/NaturalSubject",
                            "The natural nonnegative projection has another endpoint.",
                        ))
                    }
                };
                self.validate_store(derived, &fact)?;
                let zero = bound.left.clone();
                let term = "(Litex.number (M := M) (0 : ℂ))".to_string();
                self.scopes
                    .last_mut()
                    .expect("compiler scope")
                    .objects
                    .entry(zero.ir())
                    .or_insert(ObjectTerm {
                        object: zero,
                        term,
                        numeric: Some(NumericTerm {
                            value: "(0 : ℂ)".into(),
                            denotation: "(Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))".into(),
                            member: "(Litex.numberInC (M := M) (0 : ℂ))".into(),
                            closed: Some(EvalRational::new(0, 1).expect("constant zero rational")),
                        }),
                    });
                self.remember_fact(FactTerm {
                    proposition: self.fact_proposition(&fact)?,
                    fact,
                    proof: format!(
                        "(Litex.naturalNonnegative {} {})",
                        self.object_term(&source.element)?,
                        member.proof
                    ),
                });
            }
        }
        Ok(())
    }

    fn compile_let(
        &mut self,
        proof: &ExecLetObjStmtSuccessResult,
        runtime: &Runtime,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let wd = success_object_wd(&proof.value_well_defined, &proof.statement.value)?;
        let value = self.compile_wd(wd, runtime)?;
        if proof.stored_fact_ids.len() != 1 {
            return Err(LeanCompileError::unsupported("Let/Inference"));
        }
        let fact = self.resolve_fact(proof.stored_fact_ids[0], runtime)?;
        let left = alias_equality_subject(&fact, &proof.statement.name, &proof.statement.value)?;
        let declaration = self.bind_alias(
            &proof.statement.name,
            left,
            &proof.statement.value,
            &value,
            local,
        )?;
        let compiled = FactTerm {
            proposition: self.fact_proposition(&fact)?,
            fact,
            proof: format!("(Litex.sameRefl {value})"),
        };
        self.remember_fact(compiled);
        Ok(declaration)
    }

    fn compile_have_equal(
        &mut self,
        proof: &ExecHaveObjEqualStmtSuccessResult,
        runtime: &Runtime,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let groups = &proof.statement.param_def.groups;
        let parameters: Vec<_> = groups.iter().flat_map(|group| &group.params).collect();
        let count = parameters.len();
        if count == 0
            || count != proof.statement.objs_equal_to.len()
            || count != proof.equal_to_well_defined.len()
            || count != proof.membership_checks.len()
            || proof.type_preflight.param_type_well_defined.len() != groups.len()
            || proof.type_preflight.auto_opened_struct_layers.is_some()
            || proof.auto_opened_struct_layers.is_some()
        {
            return Err(LeanCompileError::new(
                "HaveEqual/Stages",
                "Typed definition evidence has different parameter, value or membership stages.",
            ));
        }
        self.validate_parameter_store_capture(&proof.store_and_infer_result)?;
        let stores = &proof.store_and_infer_result.store_and_infer_results;
        if stores.len() != 2 * count {
            return Err(LeanCompileError::new(
                "HaveEqual/Stores",
                "Typed definitions need ordered membership and equality stores.",
            ));
        }
        self.scopes.push(CompilerScope {
            env: Some(proof.type_local_env.clone()),
            ..CompilerScope::default()
        });
        let type_check = (|| {
            for (group, wd) in groups
                .iter()
                .zip(&proof.type_preflight.param_type_well_defined)
            {
                match (&group.param_type, wd) {
                    (ParamType::Obj(set), ParamTypeWellDefinedProof::Obj(result)) => {
                        self.compile_wd(success_object_wd(result, set)?, runtime)?;
                        standard_term(match set {
                            Obj::StandardSet(set) => set,
                            _ => {
                                return Err(LeanCompileError::unsupported(
                                    "HaveEqual/DependentCarrier",
                                ))
                            }
                        })?;
                    }
                    _ => return Err(LeanCompileError::unsupported("HaveEqual/ParameterKind")),
                }
            }
            Ok(())
        })();
        self.scopes.pop();
        type_check?;
        let mut values = Vec::new();
        for (value, wd) in proof
            .statement
            .objs_equal_to
            .iter()
            .zip(&proof.equal_to_well_defined)
        {
            values.push(self.compile_wd(success_object_wd(wd, value)?, runtime)?);
        }
        let mut members = Vec::new();
        let mut offset = 0;
        for group in groups {
            let set = match &group.param_type {
                ParamType::Obj(set) => set,
                _ => return Err(LeanCompileError::unsupported("HaveEqual/ParameterKind")),
            };
            for _ in &group.params {
                let member = self.compile_verify(&proof.membership_checks[offset], runtime)?;
                match &member.fact {
                    Fact::AtomicFact(AtomicFact::InFact(f))
                        if f.element.ir() == proof.statement.objs_equal_to[offset].ir()
                            && f.set.ir() == set.ir() => {}
                    _ => {
                        return Err(LeanCompileError::new(
                            "HaveEqual/Membership",
                            "The value proof does not certify the declared value and carrier.",
                        ))
                    }
                }
                members.push(member);
                offset += 1;
            }
        }
        let mut declarations = Vec::new();
        for (index, parameter) in parameters.iter().enumerate() {
            let equal = self.resolve_fact(stores[count + index].primary_fact_id(), runtime)?;
            self.validate_store(&stores[count + index], &equal)?;
            let left =
                alias_equality_subject(&equal, parameter, &proof.statement.objs_equal_to[index])?;
            declarations.push(self.bind_alias(
                parameter,
                left,
                &proof.statement.objs_equal_to[index],
                &values[index],
                local,
            )?);
            let member_fact = self.resolve_fact(stores[index].primary_fact_id(), runtime)?;
            match (&member_fact, &members[index].fact) {
                (
                    Fact::AtomicFact(AtomicFact::InFact(stored)),
                    Fact::AtomicFact(AtomicFact::InFact(checked)),
                ) if stored.element.ir() == left.ir() && stored.set.ir() == checked.set.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "HaveEqual/Store",
                        "The stored member does not belong to this declaration.",
                    ))
                }
            }
            self.validate_store(&stores[index], &member_fact)?;
            let member = FactTerm {
                proposition: self.fact_proposition(&member_fact)?,
                fact: member_fact,
                proof: members[index].proof.clone(),
            };
            self.remember_fact(member.clone());
            if let Fact::AtomicFact(AtomicFact::InFact(f)) = &member.fact {
                if f.set == Obj::StandardSet(StandardSet::R) {
                    self.remember_real_member(&f.element, &member.proof);
                }
            }
            self.compile_parameter_inferences(&stores[index], &member, runtime)?;
            self.remember_fact(FactTerm {
                proposition: self.fact_proposition(&equal)?,
                fact: equal,
                proof: format!("(Litex.sameRefl {})", values[index]),
            });
        }
        Ok(declarations.join("\n"))
    }

    fn bind_alias(
        &mut self,
        parameter: &BoundName,
        object: &Obj,
        value_object: &Obj,
        value: &str,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let name = format!("_object_i{}", parameter.id.value());
        let numeric = self
            .scopes
            .iter()
            .rev()
            .find_map(|scope| scope.objects.get(&value_object.ir()))
            .and_then(|entry| entry.numeric.clone());
        let term = if local {
            name.clone()
        } else {
            self.context_application(&name)
        };
        let alias = ObjectTerm {
            object: object.clone(),
            term,
            numeric,
        };
        let scope = self.scopes.last_mut().expect("compiler scope");
        if scope.identifiers.contains_key(&parameter.id) || scope.objects.contains_key(&object.ir())
        {
            return Err(LeanCompileError::new(
                "Declaration/Identity",
                "The declaration identifier already has a compiled producer.",
            ));
        }
        scope.identifiers.insert(parameter.id, alias.clone());
        scope.objects.insert(object.ir(), alias);
        Ok(if local {
            format!("let {name} := {value}")
        } else {
            format!(
                "noncomputable def {name}{} := {value}",
                self.context_header()
            )
        })
    }

    fn fact_proposition(&self, fact: &Fact) -> Result<String, LeanCompileError> {
        match fact {
            Fact::AtomicFact(atomic) => self.atomic_proposition(atomic),
            _ => Err(LeanCompileError::unsupported("Declaration/CompoundFact")),
        }
    }

    fn compile_named_theorem(
        &mut self,
        proof: &ExecDefThmStmtSuccess,
        runtime: &Runtime,
        index: usize,
    ) -> Result<String, LeanCompileError> {
        let goal_wd = match &proof.goal_wd {
            VerifyFactWellDefinedResult::Success(wd) => wd,
            VerifyFactWellDefinedResult::Failed(_) => {
                return Err(LeanCompileError::new(
                    "Theorem/GoalWD",
                    "A successful theorem has failed goal-formation evidence.",
                ))
            }
        };
        self.compile_fact_wd(goal_wd, &proof.statement.fact, runtime)?;
        self.scopes.push(CompilerScope {
            env: Some(proof.local_env.clone()),
            ..CompilerScope::default()
        });
        let compiled = self.compile_named_theorem_body(proof, runtime);
        self.scopes.pop();
        let mut compiled = compiled?;
        self.validate_store(&proof.stored, &compiled.fact)?;
        let name = format!("named_thm_{index}");
        let declaration = format!(
            "theorem {name}{} : {} :=\n  {}",
            self.context_header(),
            compiled.proposition,
            compiled.proof.replace('\n', "\n  ")
        );
        let term = self.context_application(&name);
        let scope = self.scopes.last_mut().expect("compiler scope");
        if scope
            .theorems
            .insert(
                proof.statement.name.clone(),
                NamedTheorem {
                    declaration: proof.statement.clone(),
                    term: term.clone(),
                },
            )
            .is_some()
        {
            return Err(LeanCompileError::new(
                "Theorem/Identity",
                "The named theorem already has a compiled declaration.",
            ));
        }
        compiled.proof = term;
        self.remember_fact(compiled);
        Ok(declaration)
    }

    fn compile_named_theorem_body(
        &mut self,
        proof: &ExecDefThmStmtSuccess,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let (binders, introductions, steps, results, expected) =
            match (&proof.statement.fact, &proof.body) {
                (Fact::ForallFact(fact), ExecDefThmBodyProof::Forall(body)) => {
                    let (binders, introductions) = self.compile_forall_head(
                        fact,
                        &body.introduced_params,
                        &body.assumed_dom_facts,
                        runtime,
                    )?;
                    let expected = fact
                        .then_facts
                        .iter()
                        .map(|fact| match fact {
                            ExistOrAndChainAtomicFact::AtomicFact(atomic) => {
                                Ok(Fact::AtomicFact(atomic.clone()))
                            }
                            _ => Err(LeanCompileError::unsupported("Theorem/CompoundThen")),
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    (
                        binders,
                        introductions,
                        &body.proof_steps,
                        body.conclusion_proofs.iter().collect::<Vec<_>>(),
                        expected,
                    )
                }
                (Fact::AtomicFact(_), ExecDefThmBodyProof::NonForall(body)) => (
                    Vec::new(),
                    Vec::new(),
                    &body.proof_steps,
                    vec![&body.conclusion_proof],
                    vec![proof.statement.fact.clone()],
                ),
                _ => return Err(LeanCompileError::unsupported("Theorem/GoalBodyShape")),
            };
        if steps.len() != proof.statement.prove_process.len()
            || results.len() != expected.len()
            || results.is_empty()
        {
            return Err(LeanCompileError::new(
                "Theorem/Stages",
                "The theorem body has different source steps or conclusion arity.",
            ));
        }
        let mut body_text = Vec::new();
        for (index, (source, step)) in proof.statement.prove_process.iter().zip(steps).enumerate() {
            validate_statement_capture(source, step)?;
            body_text.push(self.compile_statement_in_scope(step, runtime, index + 1, true)?);
        }
        let mut conclusions = Vec::new();
        for (expected, result) in expected.iter().zip(results) {
            let compiled = self.compile_verify(result, runtime)?;
            if &compiled.fact != expected {
                return Err(LeanCompileError::new(
                    "Theorem/Conclusion",
                    "The proof has another source conclusion.",
                ));
            }
            conclusions.push(compiled);
        }
        let mut conclusion = conclusions.pop().expect("nonempty conclusions");
        while let Some(left) = conclusions.pop() {
            conclusion.proposition = format!("({} ∧ {})", left.proposition, conclusion.proposition);
            conclusion.proof = format!("(And.intro {} {})", left.proof, conclusion.proof);
        }
        let proposition = if binders.is_empty() {
            conclusion.proposition
        } else {
            format!("∀ {}, {}", binders.join(" "), conclusion.proposition)
        };
        let mut statements = Vec::new();
        if !introductions.is_empty() {
            statements.push(format!("intro {}", introductions.join(" ")));
        }
        statements.extend(body_text);
        statements.push(format!("exact {}", conclusion.proof));
        Ok(FactTerm {
            fact: proof.statement.fact.clone(),
            proposition,
            proof: format!("(by\n  {}\n)", statements.join("\n").replace('\n', "\n  ")),
        })
    }

    fn compile_by_theorem(
        &mut self,
        proof: &ExecByThmStmtSuccess,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let declaration = match &proof.callee {
            ResolvedTheoremCallee::UserTheorem(declaration) => declaration,
            _ => return Err(LeanCompileError::unsupported("ByThm/Callee")),
        };
        let source_name = match &proof.call.name {
            AtomicName::Plain { name } => name,
            _ => return Err(LeanCompileError::unsupported("ByThm/QualifiedCallee")),
        };
        let registered = self
            .scopes
            .iter()
            .rev()
            .find_map(|scope| scope.theorems.get(source_name))
            .cloned()
            .ok_or_else(|| {
                LeanCompileError::new(
                    "ByThm/Producer",
                    "The named theorem has no earlier compiled declaration in scope.",
                )
            })?;
        if &registered.declaration != declaration
            || source_name != &declaration.name
            || proof.builtin.is_some()
            || proof.function_domain.is_some()
        {
            return Err(LeanCompileError::new(
                "ByThm/Callee",
                "The resolved declaration differs from the cited compiled theorem.",
            ));
        }
        self.scopes.push(CompilerScope {
            env: Some(proof.local_env.clone()),
            ..CompilerScope::default()
        });
        let compiled = self.compile_by_theorem_body(proof, &registered, runtime);
        self.scopes.pop();
        let compiled = compiled?;
        self.validate_store(&proof.stored, &compiled.fact)?;
        Ok(compiled)
    }

    fn compile_by_theorem_body(
        &mut self,
        proof: &ExecByThmStmtSuccess,
        registered: &NamedTheorem,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let mut substitution = HashMap::new();
        let mut application_arguments = Vec::new();
        let (domains, conclusions) = match (&registered.declaration.fact, &proof.call.arguments) {
            (Fact::ForallFact(fact), TheoremCallArguments::Parenthesized(args)) => {
                let parameters: Vec<_> = fact
                    .typed_parameters
                    .groups
                    .iter()
                    .flat_map(|group| &group.params)
                    .collect();
                if args.len() != parameters.len() || proof.type_proofs.len() != parameters.len() {
                    return Err(LeanCompileError::new(
                        "ByThm/Arguments",
                        "The invocation has different arguments or type-proof arity.",
                    ));
                }
                for (parameter, arg) in parameters.iter().zip(args) {
                    substitution.insert(parameter.id, arg.clone());
                }
                let mut offset = 0;
                for group in &fact.typed_parameters.groups {
                    let set = match &group.param_type {
                        ParamType::Obj(set) => set,
                        _ => return Err(LeanCompileError::unsupported("ByThm/ParameterKind")),
                    };
                    for _ in &group.params {
                        let arg = &args[offset];
                        let member = self.compile_verify(&proof.type_proofs[offset], runtime)?;
                        match &member.fact {
                            Fact::AtomicFact(AtomicFact::InFact(f))
                                if f.element.ir() == arg.ir()
                                    && instantiated_object_matches(set, &f.set, &substitution) => {}
                            _ => {
                                return Err(LeanCompileError::new(
                                    "ByThm/TypeProof",
                                    "The membership proves another parameter or carrier.",
                                ))
                            }
                        }
                        application_arguments.push(self.object_term(arg)?);
                        application_arguments.push(member.proof.clone());
                        self.remember_fact(member);
                        offset += 1;
                    }
                }
                let conclusions = fact
                    .then_facts
                    .iter()
                    .map(|fact| match fact {
                        ExistOrAndChainAtomicFact::AtomicFact(atomic) => {
                            Ok(Fact::AtomicFact(atomic.clone()))
                        }
                        _ => Err(LeanCompileError::unsupported("ByThm/CompoundConclusion")),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                (fact.dom_facts.iter().collect::<Vec<_>>(), conclusions)
            }
            (Fact::AtomicFact(_), TheoremCallArguments::Bare) if proof.type_proofs.is_empty() => {
                (Vec::new(), vec![registered.declaration.fact.clone()])
            }
            _ => return Err(LeanCompileError::unsupported("ByThm/CallShape")),
        };
        if domains.len() != proof.dom_proofs.len()
            || conclusions.len() != proof.returned_conclusions.len()
            || conclusions.len() != proof.conclusions_wd.len()
            || conclusions.is_empty()
        {
            return Err(LeanCompileError::new(
                "ByThm/Stages",
                "The invocation has different premise, returned-store or WD stages.",
            ));
        }
        for (domain, result) in domains.iter().zip(&proof.dom_proofs) {
            let compiled = self.compile_verify(result, runtime)?;
            if !instantiated_fact_matches(domain, &compiled.fact, &substitution) {
                return Err(LeanCompileError::new(
                    "ByThm/Domain",
                    "A premise proves another instantiated source requirement.",
                ));
            }
            application_arguments.push(compiled.proof.clone());
            self.remember_fact(compiled);
        }
        let application = if application_arguments.is_empty() {
            registered.term.clone()
        } else {
            format!("({} {})", registered.term, application_arguments.join(" "))
        };
        for (index, ((expected, stored), wd)) in conclusions
            .iter()
            .zip(&proof.returned_conclusions)
            .zip(&proof.conclusions_wd)
            .enumerate()
        {
            let fact = match &stored.store {
                StoreFactResult::AtomicFact(stored) => Fact::AtomicFact(stored.fact.clone()),
                _ => return Err(LeanCompileError::unsupported("ByThm/ReturnedPackage")),
            };
            self.validate_store(stored, &fact)?;
            if !instantiated_fact_matches(expected, &fact, &substitution) {
                return Err(LeanCompileError::new(
                    "ByThm/ReturnedSubject",
                    "The returned producer differs from this theorem instance.",
                ));
            }
            self.compile_fact_wd(wd, &fact, runtime)?;
            self.remember_fact(FactTerm {
                proposition: self.fact_proposition(&fact)?,
                fact,
                proof: conjunction_projection(&application, index, conclusions.len()),
            });
        }
        let returned_ids: Vec<_> = proof
            .returned_conclusions
            .iter()
            .map(StoreFactAndInferResult::primary_fact_id)
            .collect();
        let allowed = match &proof.selected_proof {
            VerifyFactResult::Equality(result) => match result.as_ref() {
                VerifyEqualityResult::Success(selected) => match &selected.searched_proof {
                    EqualFactSearchedProof::ByEquivalenceClass(
                        EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(p),
                    ) => !p.reversed && returned_ids.contains(&p.cited.fact_id),
                    _ => false,
                },
                _ => false,
            },
            VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
                VerifyAtomicExceptEqualityFactResult::Success(selected) => {
                    match &selected.searched_proof {
                        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
                            returned_ids.contains(&p.cite_fact_id)
                                && p.why_parameters_of_known_fact_are_equal_to_givens
                                    .iter()
                                    .all(|proof| {
                                        matches!(proof, EqualFactSearchedProof::ByTheyAreTheSame(_))
                                    })
                        }
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        };
        if !allowed {
            return Err(LeanCompileError::new("ByThm/SelectionProvenance", "The selection does not directly cite an unreversed atom returned by this invocation."));
        }
        self.compile_verify(&proof.selected_proof, runtime)
    }

    fn compile_verify(
        &mut self,
        result: &VerifyFactResult,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        match result {
            VerifyFactResult::Equality(result) => match result.as_ref() {
                VerifyEqualityResult::Success(success) => {
                    let left = self.compile_wd(&success.well_defined_proof.left, runtime)?;
                    let right = self.compile_wd(&success.well_defined_proof.right, runtime)?;
                    ensure_object(&success.fact.left, &success.well_defined_proof.left)?;
                    ensure_object(&success.fact.right, &success.well_defined_proof.right)?;
                    let proof = self.compile_equality_search(
                        &success.fact,
                        &success.searched_proof,
                        runtime,
                    )?;
                    Ok(FactTerm {
                        fact: Fact::AtomicFact(AtomicFact::EqualFact(success.fact.clone())),
                        proposition: format!("Litex.Same {left} {right}"),
                        proof,
                    })
                }
                VerifyEqualityResult::Failed(_) => Err(LeanCompileError::new(
                    "Equality/Failed",
                    "Failed verification is not proof evidence.",
                )),
            },
            VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
                VerifyAtomicExceptEqualityFactResult::Success(success) => {
                    self.compile_atomic_wd(&success.well_defined_proof, &success.fact, runtime)?;
                    let proposition = self.atomic_proposition(&success.fact)?;
                    let proof = match &success.searched_proof {
                        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
                            match &success.fact {
                                AtomicFact::InFact(fact)
                                    if fact.element.ir() == proof.element.ir()
                                        && fact.set.ir()
                                            == Obj::StandardSet(proof.set.clone()).ir() => {}
                                _ => {
                                    return Err(LeanCompileError::new(
                                        "StructuralMembership",
                                        "Evidence does not describe the verified membership.",
                                    ))
                                }
                            }
                            self.compile_structural(proof, runtime)?
                        }
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
                            ClosedAtomicExceptEqualityCalculationProof::In(proof),
                        ) => match &success.fact {
                            AtomicFact::InFact(fact) => {
                                self.compile_closed_membership(&fact.element, &fact.set, proof)?
                            }
                            _ => {
                                return Err(LeanCompileError::new(
                                    "ClosedMembership",
                                    "Membership calculation has another fact family.",
                                ))
                            }
                        },
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(ClosedAtomicExceptEqualityCalculationProof::NotEqual(proof)) =>
                            self.compile_closed_not_equal(&success.fact, proof)?,
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(certificate @ (ClosedAtomicExceptEqualityCalculationProof::Less(_) | ClosedAtomicExceptEqualityCalculationProof::Greater(_) | ClosedAtomicExceptEqualityCalculationProof::LessEqual(_) | ClosedAtomicExceptEqualityCalculationProof::GreaterEqual(_))) => self.compile_closed_order(&success.fact, certificate)?,
                        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Atomic/ClosedCalculationNonMembership",
                            ))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
                            self.compile_known_atomic(proof, &success.fact, runtime)?
                        }
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(rule) => match rule {
                            AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(
                                IsSetFactSearchProofByBuiltinRule::AlwaysTrue(_),
                            ) => match &success.fact {
                                AtomicFact::IsSetFact(fact) => {
                                    format!("(Litex.isSet {})", self.object_term(&fact.set)?)
                                }
                                _ => {
                                    return Err(LeanCompileError::new(
                                        "IsSetAlwaysTrue",
                                        "Sethood evidence has another fact family.",
                                    ))
                                }
                            },
                            AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(IsNonemptySetFactSearchProofByBuiltinRule::StandardSetNonempty(p)) => {
                                match &success.fact {
                                    AtomicFact::IsNonemptySetFact(f) if f.set == Obj::StandardSet(p.target_set.clone()) => {},
                                    _ => return Err(LeanCompileError::new("Nonempty/Subject", "Standard nonempty evidence describes another target.")),
                                }
                                standard_term(&p.target_set)?;
                                format!("(Litex.standardNonempty (M := M) Litex.StandardSetValue.{})", standard_value_constructor(&p.target_set)?)
                            },
                            rule @ (AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(_) | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(_)) => self.compile_order_builtin(&success.fact, rule, runtime)?,
                            other => return Err(unsupported_atomic_builtin(other)),
                        },
                        AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(_) => {
                            return Err(LeanCompileError::unsupported(
                                "Atomic/KnownSpecialProperty",
                            ))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonzeroProduct(proof)) =>
                            self.compile_nonzero_product(&success.fact, &proof.requirement_facts, &proof.proof_of_requirement_facts, runtime)?,
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/BuiltinStrategy"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/KnownStrategy"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByDefinition(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/Definition"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/KnownForallFact"))
                        }
                        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(proof) =>
                            self.compile_atomic_builtin_rewrite(&success.fact, proof, runtime)?,
                        AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(_) => {
                            return Err(LeanCompileError::unsupported("Atomic/KnownRewrite"))
                        }
                    };
                    if let AtomicFact::InFact(member) = &success.fact {
                        if member.set == Obj::StandardSet(StandardSet::C) {
                            self.remember_complex_member(&member.element, &proof)?;
                        }
                        if member.set == Obj::StandardSet(StandardSet::R) {
                            self.remember_real_member(&member.element, &proof);
                        }
                    }
                    Ok(FactTerm {
                        fact: Fact::AtomicFact(success.fact.clone()),
                        proposition,
                        proof,
                    })
                }
                VerifyAtomicExceptEqualityFactResult::Failed(_) => Err(LeanCompileError::new(
                    "Atomic/Failed",
                    "Failed verification is not proof evidence.",
                )),
            },
            VerifyFactResult::ForallFact(result) => match result.as_ref() {
                VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(
                    proof,
                )) => self.compile_forall(proof, runtime),
                VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(
                    proof,
                )) => self.compile_known_forall(proof, runtime),
                VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(
                    _,
                )) => Err(LeanCompileError::unsupported("Forall/EmptyParameterDomain")),
                VerifyForallFactResult::Failed(_) => Err(LeanCompileError::new(
                    "Forall/Failed",
                    "Failed verification is not proof evidence.",
                )),
            },
            VerifyFactResult::AndFact(_) => Err(LeanCompileError::unsupported("AndFact")),
            VerifyFactResult::ChainFact(_) => Err(LeanCompileError::unsupported("ChainFact")),
            VerifyFactResult::OrFact(_) => Err(LeanCompileError::unsupported("OrFact")),
            VerifyFactResult::ExistShapedFact(_) => {
                Err(LeanCompileError::unsupported("ExistShapedFact"))
            }
            VerifyFactResult::ForallFactWithIff(_) => {
                Err(LeanCompileError::unsupported("ForallFactWithIff"))
            }
            VerifyFactResult::NotForall(_) => Err(LeanCompileError::unsupported("NotForall")),
        }
    }

    fn compile_closed_equality(
        &self,
        fact: &EqualFact,
        proof: &ClosedEqualityCalculationProof,
    ) -> Result<String, LeanCompileError> {
        let left = self
            .numeric_term(&fact.left)?
            .closed
            .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
        let right = self
            .numeric_term(&fact.right)?
            .closed
            .ok_or_else(|| LeanCompileError::unsupported("ClosedEquality/Expression"))?;
        let matching = match &proof.values {
            ClosedValuePair::Decimal { left: a, right: b } => {
                scalar_decimal(a)? == left && scalar_decimal(b)? == right
            }
            ClosedValuePair::Rational { left: a, right: b } => a == &left && b == &right,
            ClosedValuePair::Complex {
                left_real: a,
                left_imaginary: ai,
                right_real: b,
                right_imaginary: bi,
            } => a == &left && b == &right && ai.is_zero() && bi.is_zero(),
            ClosedValuePair::Radical { .. } => {
                return Err(LeanCompileError::unsupported("ClosedEquality/Radical"))
            }
        };
        if !matching || left != right {
            return Err(LeanCompileError::new("ClosedEquality/Values", "Closed equality values differ from their exact source endpoints or from each other."));
        }
        let x = self.numeric_term(&fact.left)?;
        let y = self.numeric_term(&fact.right)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} (by norm_num))",
            self.object_term(&fact.left)?,
            self.object_term(&fact.right)?,
            x.value,
            y.value,
            x.denotation,
            y.denotation
        ))
    }

    fn compile_arithmetic_congruence(
        &mut self,
        fact: &EqualFact,
        children: &[VerifyFactResult],
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (operation, pairs) =
            arithmetic_constructor_pairs(&fact.left, &fact.right).ok_or_else(|| {
                LeanCompileError::unsupported("Equality/MatchingOneArgByOne/Constructor")
            })?;
        if children.len() != pairs.len() {
            return Err(LeanCompileError::new(
                "ArithmeticCongruence/Children",
                "Constructor congruence has the wrong ordered child arity.",
            ));
        }
        let mut compiled = Vec::new();
        for (child, (left, right)) in children.iter().zip(pairs) {
            let child = self.compile_verify(child, runtime)?;
            match &child.fact {
                Fact::AtomicFact(AtomicFact::EqualFact(eq))
                    if eq.left.ir() == left.ir() && eq.right.ir() == right.ir() => {}
                _ => {
                    return Err(LeanCompileError::new(
                        "ArithmeticCongruence/ChildSubject",
                        "Congruence child does not prove this exact ordered operand pair.",
                    ))
                }
            }
            compiled.push(child.proof);
        }
        if compiled.len() == 1 {
            Ok(format!("(congrArg M.{operation} {})", compiled[0]))
        } else {
            Ok(format!(
                "(congrArg₂ M.{operation} {} {})",
                compiled[0], compiled[1]
            ))
        }
    }

    fn compile_scalar_division_relation(
        &mut self,
        fact: &EqualFact,
        proof: &ScalarDivisionRelationProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (child, product_from_division) = match proof {
            ScalarDivisionRelationProof::ProductFromDivision(p) => (&p.division_equation, true),
            ScalarDivisionRelationProof::DivisionFromProduct(p) => (&p.product_equation, false),
        };
        let compiled = self.compile_verify(child, runtime)?;
        let equation = match &compiled.fact {
            Fact::AtomicFact(AtomicFact::EqualFact(x)) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "ScalarDivisionRelation/Child",
                    "The source equation is not an equality.",
                ))
            }
        };
        let (_numerator, denominator, factor, quotient, reversed, commuted) =
            if product_from_division {
                let quotient = match &equation.left {
                    Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => x,
                    _ => {
                        return Err(LeanCompileError::new(
                            "ScalarDivisionRelation/DivisionSubject",
                            "ProductFromDivision must cite a quotient equation.",
                        ))
                    }
                };
                let mut matched = None;
                for (other, product, reversed) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = product {
                        if other.ir() != quotient.left.ir() {
                            continue;
                        }
                        if p.left.ir() == equation.right.ir() && p.right.ir() == quotient.right.ir()
                        {
                            matched = Some((reversed, false));
                            break;
                        }
                        if p.right.ir() == equation.right.ir() && p.left.ir() == quotient.right.ir()
                        {
                            matched = Some((reversed, true));
                            break;
                        }
                    }
                }
                let (reversed, commuted) = matched.ok_or_else(|| LeanCompileError::new("ScalarDivisionRelation/ParentSubject", "The source quotient equation does not describe the parent product endpoints."))?;
                (
                    quotient.left.as_ref(),
                    quotient.right.as_ref(),
                    &equation.right,
                    &equation.left,
                    reversed,
                    commuted,
                )
            } else {
                let mut matched = None;
                for (quotient_obj, factor, reversed) in [
                    (&fact.left, &fact.right, false),
                    (&fact.right, &fact.left, true),
                ] {
                    if let Obj::ArithmeticOperator(ArithmeticOperator::Div(q)) = quotient_obj {
                        if equation.left.ir() != q.left.ir() {
                            continue;
                        }
                        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = &equation.right
                        {
                            if p.left.ir() == factor.ir() && p.right.ir() == q.right.ir() {
                                matched = Some((q, factor, quotient_obj, reversed, false));
                                break;
                            }
                            if p.right.ir() == factor.ir() && p.left.ir() == q.right.ir() {
                                matched = Some((q, factor, quotient_obj, reversed, true));
                                break;
                            }
                        }
                    }
                }
                let (q, factor, quotient_obj, reversed, commuted) = matched.ok_or_else(|| LeanCompileError::new("ScalarDivisionRelation/ParentSubject", "The source product equation does not describe the parent quotient endpoints."))?;
                (
                    q.left.as_ref(),
                    q.right.as_ref(),
                    factor,
                    quotient_obj,
                    reversed,
                    commuted,
                )
            };
        let b = self.numeric_term(denominator)?;
        let c = self.numeric_term(factor)?;
        let x = self.numeric_term(&equation.left)?;
        let y = self.numeric_term(&equation.right)?;
        let source_eq = format!(
            "(Litex.NativeBridge.nativeEqOfDenoteNumber {} {} {} {} {} {} {})",
            self.object_term(&equation.left)?,
            self.object_term(&equation.right)?,
            x.value,
            y.value,
            x.denotation,
            y.denotation,
            compiled.proof
        );
        let guard = format!(
            "(Litex.NativeBridge.nativeNonzeroOfDenote {} {} {} ({}).wd.2.2)",
            self.object_term(denominator)?,
            b.value,
            b.denotation,
            self.object_term(quotient)?
        );
        let native_proof = if product_from_division {
            let product = format!("((div_eq_iff {guard}).mp {source_eq})");
            let oriented = if commuted {
                format!("({product}.trans (mul_comm {} {}))", c.value, b.value)
            } else {
                product
            };
            if reversed {
                format!("({oriented}.symm)")
            } else {
                oriented
            }
        } else {
            let product = if commuted {
                format!("({source_eq}.trans (mul_comm {} {}))", b.value, c.value)
            } else {
                source_eq
            };
            let quotient = format!("((div_eq_iff {guard}).mpr {product})");
            if reversed {
                format!("({quotient}.symm)")
            } else {
                quotient
            }
        };
        let left = self.numeric_term(&fact.left)?;
        let right = self.numeric_term(&fact.right)?;
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {} {} {} {} {} {} {native_proof})",
            self.object_term(&fact.left)?,
            self.object_term(&fact.right)?,
            left.value,
            right.value,
            left.denotation,
            right.denotation
        ))
    }

    fn compile_rational(
        &mut self,
        fact: &EqualFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        guarded: bool,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        validate_arithmetic_expression(&fact.left)?;
        validate_arithmetic_expression(&fact.right)?;
        let expected = normalization_nonzero_subjects(&fact.left, &fact.right)?;
        if requirements.len() != expected.len()
            || proofs.len() != expected.len()
            || guarded != !expected.is_empty()
        {
            return Err(LeanCompileError::new("Rational/Requirements", "The selected normalization family or ordered guard arity differs from the source expression."));
        }
        let mut native_guards = Vec::new();
        for (index, ((requirement, proof), object)) in
            requirements.iter().zip(proofs).zip(expected).enumerate()
        {
            ensure_nonzero_subject(requirement, &object)?;
            let proved = self.compile_verify(proof, runtime)?;
            if &proved.fact != requirement {
                return Err(LeanCompileError::new(
                    "Rational/RequirementSubject",
                    "A guard's verify result differs from its exact ordered requirement.",
                ));
            }
            let term = self.object_term(&object)?;
            let native = self.numeric_term(&object)?;
            native_guards.push(format!("have _litex_nz_{index} : {} ≠ 0 := Litex.NativeBridge.nativeNonzeroOfDenote {term} {} {} {}", native.value, native.value, native.denotation, proved.proof));
        }
        let left = self.object_term(&fact.left)?;
        let right = self.object_term(&fact.right)?;
        let x = self.numeric_term(&fact.left)?;
        let y = self.numeric_term(&fact.right)?;
        // The empty Rational tag contains no monomial trace. The Lean kernel
        // checks the fixed normalization proof, including forged false tags.
        let normalization = if guarded {
            let guard_names = (0..native_guards.len())
                .map(|i| format!("_litex_nz_{i}"))
                .collect::<Vec<_>>();
            let exact_guards = guard_names
                .iter()
                .map(|n| format!("exact {n}"))
                .collect::<Vec<_>>()
                .join(" | ");
            format!("(by\n  {}\n  litex_normalize_rational (disch := repeat' first | {exact_guards} | apply mul_ne_zero | apply div_ne_zero | apply pow_ne_zero | apply zpow_ne_zero)\n)", native_guards.join("\n  "))
        } else {
            "(by ring)".to_string()
        };
        Ok(format!(
            "(Litex.NativeBridge.sameOfDenoteNumber {left} {right} {} {} {} {} {normalization})",
            x.value, y.value, x.denotation, y.denotation
        ))
    }

    fn compile_nonzero_product(
        &mut self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let goal = match fact {
            AtomicFact::NotEqualFact(x) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/Subject",
                    "Product nonzero evidence has another fact family.",
                ))
            }
        };
        let (expression, reversed) = if is_zero(&goal.right) {
            (&goal.left, false)
        } else if is_zero(&goal.left) {
            (&goal.right, true)
        } else {
            return Err(LeanCompileError::new(
                "NonzeroProduct/Subject",
                "The product guard does not compare with zero.",
            ));
        };
        let product = match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/Subject",
                    "The certified nonzero object is not a product.",
                ))
            }
        };
        if requirements.len() != 2 || proofs.len() != 2 {
            return Err(LeanCompileError::new(
                "NonzeroProduct/Requirements",
                "The product needs two ordered factor proofs.",
            ));
        }
        let mut compiled = Vec::new();
        for ((requirement, proof), child) in requirements
            .iter()
            .zip(proofs)
            .zip([product.left.as_ref(), product.right.as_ref()])
        {
            ensure_nonzero_subject(requirement, child)?;
            let proved = self.compile_verify(proof, runtime)?;
            if &proved.fact != requirement {
                return Err(LeanCompileError::new(
                    "NonzeroProduct/RequirementSubject",
                    "A factor proof differs from its ordered requirement.",
                ));
            }
            let native = self.numeric_term(child)?;
            compiled.push(format!(
                "(Litex.NativeBridge.nativeNonzeroOfDenote {} {} {} {})",
                self.object_term(child)?,
                native.value,
                native.denotation,
                proved.proof
            ));
        }
        let native = self.numeric_term(expression)?;
        let proof = format!("(Litex.NativeBridge.notSameOfDenoteNumber {} (Litex.number (M := M) (0 : ℂ)) {} (0 : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ)) (mul_ne_zero {} {}))", self.object_term(expression)?, native.value, native.denotation, compiled[0], compiled[1]);
        Ok(if reversed {
            format!("(fun h => {proof} h.symm)")
        } else {
            proof
        })
    }

    fn compile_closed_not_equal(
        &self,
        fact: &AtomicFact,
        proof: &ClosedNotEqualCalculationProof,
    ) -> Result<String, LeanCompileError> {
        let goal = match fact {
            AtomicFact::NotEqualFact(x) => x,
            _ => {
                return Err(LeanCompileError::new(
                    "ClosedNotEqual/Subject",
                    "Closed inequality evidence has another fact family.",
                ))
            }
        };
        let left = EvalRational::from_obj(&goal.left)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedNotEqual/Expression"))?;
        let right = EvalRational::from_obj(&goal.right)
            .ok_or_else(|| LeanCompileError::unsupported("ClosedNotEqual/Expression"))?;
        let matching = match &proof.values {
            ClosedValuePair::Decimal { left: a, right: b } => {
                scalar_decimal(a)? == left && scalar_decimal(b)? == right
            }
            ClosedValuePair::Rational { left: a, right: b } => a == &left && b == &right,
            ClosedValuePair::Complex {
                left_real: a,
                left_imaginary: ai,
                right_real: b,
                right_imaginary: bi,
            } => a == &left && b == &right && ai.is_zero() && bi.is_zero(),
            ClosedValuePair::Radical { .. } => {
                return Err(LeanCompileError::unsupported("ClosedNotEqual/Radical"))
            }
        };
        if !matching || left == right {
            return Err(LeanCompileError::new(
                "ClosedNotEqual/Values",
                "Closed scalar values differ from the source endpoints or are equal.",
            ));
        }
        let x = self.numeric_term(&goal.left)?;
        let y = self.numeric_term(&goal.right)?;
        Ok(format!(
            "(Litex.NativeBridge.notSameOfDenoteNumber {} {} {} {} {} {} (by norm_num))",
            self.object_term(&goal.left)?,
            self.object_term(&goal.right)?,
            x.value,
            y.value,
            x.denotation,
            y.denotation
        ))
    }

    fn compile_known_forall(
        &mut self,
        proof: &VerifyKnownForallFactProof,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let resolved = self.resolve_fact(proof.cite_fact_id, runtime)?;
        let source = match &resolved {
            Fact::ForallFact(source) if source.fact_id == proof.cite_fact_id => source,
            _ => {
                return Err(LeanCompileError::new(
                    "KnownForall/Citation",
                    "The whole-proposition citation is not this source forall identity.",
                ))
            }
        };
        let registered = self.fact_term(proof.cite_fact_id)?.clone();
        if registered.fact != resolved {
            return Err(LeanCompileError::new(
                "KnownForall/Producer",
                "The source forall differs from its active compiled producer.",
            ));
        }
        let source_parameters: Vec<_> = source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|param| (param, &group.param_type)))
            .collect();
        let target_parameters: Vec<_> = proof
            .fact
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|param| (param, &group.param_type)))
            .collect();
        if source_parameters.len() != target_parameters.len()
            || proof.parameter_renamings.len() != source_parameters.len()
            || source.dom_facts.len() != proof.fact.dom_facts.len()
            || source.then_facts.len() != proof.fact.then_facts.len()
            || source.then_facts.is_empty()
        {
            return Err(LeanCompileError::new(
                "KnownForall/Arity",
                "Whole-forall reuse has different ordered parameter, premise or conclusion arity.",
            ));
        }
        let mut substitution = HashMap::new();
        let mut targets = std::collections::HashSet::new();
        for (((source, _), (target, _)), renaming) in source_parameters
            .iter()
            .zip(&target_parameters)
            .zip(&proof.parameter_renamings)
        {
            if renaming.source != source.id
                || renaming.target != target.id
                || substitution
                    .insert(
                        source.id,
                        Obj::Identifier(IdentifierObj::from_bound_name(target)),
                    )
                    .is_some()
                || !targets.insert(target.id)
            {
                return Err(LeanCompileError::new(
                    "KnownForall/Renaming",
                    "The recorded renaming must be the exact ordered bijection of declared binders.",
                ));
            }
        }
        for ((_, source), (_, target)) in source_parameters.iter().zip(&target_parameters) {
            match (source, target) {
                (ParamType::Obj(source), ParamType::Obj(target))
                    if instantiated_object_matches(source, target, &substitution) => {}
                (ParamType::Obj(_), ParamType::Obj(_)) => {
                    return Err(LeanCompileError::new(
                        "KnownForall/Carrier",
                        "A parameter carrier changes under the recorded renaming.",
                    ))
                }
                _ => return Err(LeanCompileError::unsupported("KnownForall/ParameterKind")),
            }
        }
        for (source, target) in source.dom_facts.iter().zip(&proof.fact.dom_facts) {
            if !instantiated_fact_matches(source, target, &substitution) {
                return Err(LeanCompileError::new(
                    "KnownForall/Domain",
                    "A domain proposition changes under the recorded exact renaming.",
                ));
            }
        }
        for (source, target) in source.then_facts.iter().zip(&proof.fact.then_facts) {
            if !instantiated_fact_matches(
                &source.clone().into(),
                &target.clone().into(),
                &substitution,
            ) {
                return Err(LeanCompileError::new(
                    "KnownForall/Conclusion",
                    "A conclusion or free reference changes under the recorded exact renaming.",
                ));
            }
        }
        self.scopes.push(CompilerScope {
            env: Some(proof.well_defined.local_env.clone()),
            ..CompilerScope::default()
        });
        let compiled = self.compile_known_forall_body(proof, &registered, runtime);
        self.scopes.pop();
        compiled
    }

    fn compile_known_forall_body(
        &mut self,
        proof: &VerifyKnownForallFactProof,
        registered: &FactTerm,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let (binders, introductions) = self.compile_forall_head(
            &proof.fact,
            &proof.well_defined.introduced_params,
            &proof.well_defined.assumed_dom_facts,
            runtime,
        )?;
        if proof.well_defined.then.len() != proof.fact.then_facts.len() {
            return Err(LeanCompileError::new(
                "KnownForall/ConclusionWD",
                "The recorded whole-proposition WD omits or adds a conclusion stage.",
            ));
        }
        let mut propositions = Vec::new();
        for (source, wd) in proof.fact.then_facts.iter().zip(&proof.well_defined.then) {
            let fact: Fact = source.clone().into();
            self.compile_fact_wd(wd, &fact, runtime)?;
            propositions.push(self.fact_proposition(&fact)?);
        }
        let mut arguments = Vec::new();
        let mut offset = 0;
        let ids = &proof
            .well_defined
            .introduced_params
            .defined_params
            .stored_fact_ids;
        for group in &proof.fact.typed_parameters.groups {
            for parameter in &group.params {
                let object = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
                arguments.push(self.object_term(&object)?);
                arguments.push(self.fact_term(ids[offset])?.proof.clone());
                offset += 1;
            }
        }
        for domain in &proof.fact.dom_facts {
            let registered = self.fact_term(domain.fact_id())?;
            if registered.fact != *domain {
                return Err(LeanCompileError::new(
                    "KnownForall/DomainProducer",
                    "A domain hypothesis differs from the current scoped source requirement.",
                ));
            }
            arguments.push(registered.proof.clone());
        }
        let application = if arguments.is_empty() {
            registered.proof.clone()
        } else {
            format!("({} {})", registered.proof, arguments.join(" "))
        };
        let mut conclusion = propositions.pop().expect("validated nonempty conclusions");
        while let Some(left) = propositions.pop() {
            conclusion = format!("({left} ∧ {conclusion})");
        }
        let proposition = if binders.is_empty() {
            conclusion
        } else {
            format!("∀ {}, {conclusion}", binders.join(" "))
        };
        let introduction = if introductions.is_empty() {
            String::new()
        } else {
            format!("  intro {}\n", introductions.join(" "))
        };
        Ok(FactTerm {
            fact: Fact::ForallFact(proof.fact.clone()),
            proposition,
            proof: format!("(by\n{introduction}  exact {application}\n)"),
        })
    }

    fn compile_forall(
        &mut self,
        proof: &VerifyForallFactSuccess,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let scope = CompilerScope {
            env: Some(proof.local_env.clone()),
            ..CompilerScope::default()
        };
        self.scopes.push(scope);
        let compiled = self.compile_forall_body(proof, runtime);
        self.scopes.pop();
        compiled
    }

    fn compile_forall_head(
        &mut self,
        fact: &ForallFact,
        introduced: &IntroduceTypedParametersResult,
        assumed: &[AssumeDomFactResult],
        runtime: &Runtime,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let groups = &fact.typed_parameters.groups;
        if introduced.param_type_well_defined.len() != groups.len()
            || introduced.auto_opened_struct_layers.is_some()
        {
            return Err(LeanCompileError::new(
                "Forall/Parameters",
                "Parameter evidence does not match the supported plain groups.",
            ));
        }
        let expected_count: usize = groups.iter().map(|group| group.params.len()).sum();
        self.validate_parameter_store_capture(&introduced.defined_params)?;
        let stores = &introduced.defined_params.store_and_infer_results;
        if stores.len() != expected_count {
            return Err(LeanCompileError::new(
                "Forall/ParameterStores",
                "Parameter introduction needs its actual ordered stores.",
            ));
        }
        let mut binders = Vec::new();
        let mut introductions = Vec::new();
        let mut offset = 0;
        for (group, wd) in groups.iter().zip(&introduced.param_type_well_defined) {
            let set = match &group.param_type {
                ParamType::Obj(set) => set,
                ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    return Err(LeanCompileError::unsupported("Forall/ParameterKind"))
                }
            };
            match wd {
                ParamTypeWellDefinedProof::Obj(VerifyObjWellDefinedResult::Success(wd)) => {
                    ensure_object(set, wd)?;
                    self.compile_wd(wd, runtime)?;
                }
                ParamTypeWellDefinedProof::Obj(VerifyObjWellDefinedResult::Failed { .. }) => {
                    return Err(LeanCompileError::new(
                        "Forall/ParameterWD",
                        "Parameter WD failed.",
                    ))
                }
                ParamTypeWellDefinedProof::Set
                | ParamTypeWellDefinedProof::NonemptySet
                | ParamTypeWellDefinedProof::FiniteSet => {
                    return Err(LeanCompileError::unsupported("Forall/ParameterKindWD"))
                }
            }
            for parameter in &group.params {
                let (new_binders, new_arguments) =
                    self.introduce_numeric_parameter(parameter, set, &stores[offset], runtime)?;
                binders.extend(new_binders);
                introductions.extend(new_arguments);
                offset += 1;
            }
        }
        if assumed.len() != fact.dom_facts.len() {
            return Err(LeanCompileError::new(
                "Forall/Domain",
                "Domain evidence has the wrong arity.",
            ));
        }
        for (fact, assumed) in fact.dom_facts.iter().zip(assumed) {
            self.compile_fact_wd(&assumed.well_defined, fact, runtime)?;
            self.validate_store(&assumed.store_and_infer, fact)?;
            let atomic = match fact {
                Fact::AtomicFact(atomic) => atomic,
                _ => return Err(LeanCompileError::unsupported("Forall/CompoundDomain")),
            };
            let proposition = self.atomic_proposition(atomic)?;
            let hypothesis = format!("_h_dom_f{}", fact.fact_id().value());
            binders.push(format!("({hypothesis} : {proposition})"));
            introductions.push(hypothesis.clone());
            self.remember_fact(FactTerm {
                fact: fact.clone(),
                proposition,
                proof: hypothesis,
            });
        }
        Ok((binders, introductions))
    }

    fn compile_forall_body(
        &mut self,
        proof: &VerifyForallFactSuccess,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let (binders, introductions) = self.compile_forall_head(
            &proof.fact,
            &proof.introduced_params,
            &proof.assumed_dom_facts,
            runtime,
        )?;
        if proof.proved_then_facts.len() != proof.fact.then_facts.len()
            || proof.proved_then_facts.is_empty()
        {
            return Err(LeanCompileError::new(
                "Forall/Then",
                "Conclusion evidence has the wrong arity.",
            ));
        }
        let mut conclusions = Vec::new();
        for (fact, proved) in proof.fact.then_facts.iter().zip(&proof.proved_then_facts) {
            let expected = match fact {
                ExistOrAndChainAtomicFact::AtomicFact(atomic) => Fact::AtomicFact(atomic.clone()),
                ExistOrAndChainAtomicFact::AndFact(_)
                | ExistOrAndChainAtomicFact::ChainFact(_)
                | ExistOrAndChainAtomicFact::OrFact(_)
                | ExistOrAndChainAtomicFact::ExistFact(_)
                | ExistOrAndChainAtomicFact::ExistUniqueFact(_)
                | ExistOrAndChainAtomicFact::NotExistFact(_) => {
                    return Err(LeanCompileError::unsupported("Forall/CompoundThen"))
                }
            };
            let compiled = self.compile_verify(&proved.verify_result, runtime)?;
            if compiled.fact != expected {
                return Err(LeanCompileError::new(
                    "Forall/Then",
                    "Verified conclusion differs from the source conclusion.",
                ));
            }
            self.validate_store(&proved.store_and_infer, &compiled.fact)?;
            self.remember_fact(compiled.clone());
            conclusions.push(compiled);
        }
        let mut conclusion = conclusions.pop().expect("nonempty conclusions");
        while let Some(left) = conclusions.pop() {
            conclusion.proposition = format!("({} ∧ {})", left.proposition, conclusion.proposition);
            conclusion.proof = format!("(And.intro {} {})", left.proof, conclusion.proof);
        }
        let proposition = if binders.is_empty() {
            conclusion.proposition
        } else {
            format!("∀ {}, {}", binders.join(" "), conclusion.proposition)
        };
        let intro = if introductions.is_empty() {
            String::new()
        } else {
            format!("  intro {}\n", introductions.join(" "))
        };
        Ok(FactTerm {
            fact: Fact::ForallFact(proof.fact.clone()),
            proposition,
            proof: format!("(by\n{intro}  exact {}\n)", conclusion.proof),
        })
    }

    fn compile_wd(
        &mut self,
        proof: &ObjWellDefinedProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        match proof {
            ObjWellDefinedProof::ByKnown { obj, wd_id } => {
                let recorded = self.resolve_wd(*wd_id, runtime)?;
                if recorded.ir() != obj.ir() {
                    return Err(LeanCompileError::new(
                        "WD/ByKnown",
                        "WD id resolves to another object.",
                    ));
                }
                // A cache record is not a proof. Only an earlier replayed constructor
                // or an explicitly introduced certified parameter supplies this term.
                let term = self.object_term(obj)?;
                self.scopes.last_mut().expect("compiler scope").wds.insert(
                    *wd_id,
                    ObjectTerm {
                        object: obj.clone(),
                        term: term.clone(),
                        numeric: None,
                    },
                );
                Ok(term)
            }
            ObjWellDefinedProof::ByDef { obj, proof } => {
                let (term, numeric) = match (obj, proof) {
                    (
                        Obj::Identifier(IdentifierObj::Plain { id, .. }),
                        ObjWellDefinedProofByDef::Identifier(_),
                    ) => (self.identifier_term(*id)?, None),
                    (
                        Obj::Literal(Literal::Number(number)),
                        ObjWellDefinedProofByDef::Literal(LiteralObjWellDefinedProofByDef::Number(
                            _,
                        )),
                    ) => {
                        let value = number_literal(number, "ℂ")?;
                        (
                            format!("(Litex.number (M := M) {value})"),
                            Some(NumericTerm {
                                closed: EvalRational::from_obj(obj),
                                denotation: format!(
                                    "(Litex.NativeBridge.denoteNumber (M := M) {value})"
                                ),
                                member: format!("(Litex.numberInC (M := M) {value})"),
                                value,
                            }),
                        )
                    }
                    (Obj::StandardSet(set), ObjWellDefinedProofByDef::StandardSet(_)) => {
                        (standard_term(set)?, None)
                    }
                    (
                        Obj::ArithmeticOperator(operator),
                        ObjWellDefinedProofByDef::ArithmeticOperator(wd),
                    ) => {
                        let (term, numeric) = match (operator, wd) {
                            (
                                ArithmeticOperator::Add(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Add(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Add,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Sub(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Sub(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Sub,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Mul(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Mul(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Mul,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Div(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
                            ) => self.compile_binary_wd(
                                &x.left,
                                &x.right,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                BinaryArithmetic::Div,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Neg(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Neg(p),
                            ) => self.compile_neg_wd(
                                &x.arg,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                runtime,
                            )?,
                            (
                                ArithmeticOperator::Pow(x),
                                ArithmeticOperatorObjWellDefinedProofByDef::Pow(p),
                            ) => self.compile_pow_wd(
                                &x.base,
                                &x.exponent,
                                &p.child_obj_well_defined,
                                &p.requirement_fact_verified,
                                runtime,
                            )?,
                            _ => {
                                return Err(LeanCompileError::unsupported("WD/ArithmeticOperator"))
                            }
                        };
                        (term, Some(numeric))
                    }
                    (_, unsupported) => return Err(unsupported_wd_definition(unsupported)),
                };
                // Only replayed closed leaves leave a binder scope.
                let closed_leaf =
                    matches!(obj, Obj::Literal(Literal::Number(_)) | Obj::StandardSet(_));
                let scope = if closed_leaf {
                    &mut self.scopes[0]
                } else {
                    self.scopes.last_mut().expect("compiler scope")
                };
                let entry = scope.objects.entry(obj.ir()).or_insert(ObjectTerm {
                    object: obj.clone(),
                    term,
                    numeric,
                });
                Ok(entry.term.clone())
            }
        }
    }

    fn compile_binary_wd(
        &mut self,
        left: &Obj,
        right: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        operation: BinaryArithmetic,
        runtime: &Runtime,
    ) -> Result<(String, NumericTerm), LeanCompileError> {
        let division = matches!(operation, BinaryArithmetic::Div);
        if children.len() != 2 || requirements.len() != if division { 3 } else { 2 } {
            return Err(LeanCompileError::new(
                "WD/Arithmetic",
                "Arithmetic evidence has the wrong stage arity.",
            ));
        }
        ensure_object(left, &children[0])?;
        ensure_object(right, &children[1])?;
        let a = self.compile_wd(&children[0], runtime)?;
        let b = self.compile_wd(&children[1], runtime)?;
        let mut proofs = Vec::new();
        for requirement in requirements {
            proofs.push(self.compile_verify(requirement, runtime)?);
        }
        let offset = usize::from(division);
        ensure_complex_member(&proofs[offset].fact, left)?;
        ensure_complex_member(&proofs[offset + 1].fact, right)?;
        let guard = if division {
            ensure_nonzero_subject(&proofs[0].fact, right)?;
            format!(" {}", proofs[0].proof)
        } else {
            String::new()
        };
        let (name, symbol, bridge) = match operation {
            BinaryArithmetic::Add => ("add", "+", "Add"),
            BinaryArithmetic::Sub => ("sub", "-", "Sub"),
            BinaryArithmetic::Mul => ("mul", "*", "Mul"),
            BinaryArithmetic::Div => ("div", "/", "Div"),
        };
        let arguments = format!(
            "{a} {b} {} {}{guard}",
            proofs[offset].proof,
            proofs[offset + 1].proof
        );
        let x = self.numeric_term(left)?;
        let y = self.numeric_term(right)?;
        Ok((
            format!("(Litex.{name} {arguments})"),
            NumericTerm {
                closed: match (&x.closed, &y.closed) {
                    (Some(x), Some(y)) => match operation {
                        BinaryArithmetic::Add => x.add(y),
                        BinaryArithmetic::Sub => x.sub(y),
                        BinaryArithmetic::Mul => x.mul(y),
                        BinaryArithmetic::Div => x.div(y),
                    },
                    _ => None,
                },
                value: format!("({} {symbol} {})", x.value, y.value),
                denotation: format!(
                    "(Litex.NativeBridge.denote{bridge} {arguments} {} {} {} {})",
                    x.value, y.value, x.denotation, y.denotation
                ),
                member: format!("(Litex.{name}InC {arguments})"),
            },
        ))
    }

    fn compile_neg_wd(
        &mut self,
        argument: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        runtime: &Runtime,
    ) -> Result<(String, NumericTerm), LeanCompileError> {
        if children.len() != 1 || requirements.len() != 1 {
            return Err(LeanCompileError::new(
                "WD/Neg",
                "Negation evidence has the wrong stage arity.",
            ));
        }
        ensure_object(argument, &children[0])?;
        let a = self.compile_wd(&children[0], runtime)?;
        let member = self.compile_verify(&requirements[0], runtime)?;
        ensure_complex_member(&member.fact, argument)?;
        let x = self.numeric_term(argument)?;
        Ok((
            format!("(Litex.neg {a} {})", member.proof),
            NumericTerm {
                closed: x
                    .closed
                    .as_ref()
                    .and_then(|value| EvalRational::new(0, 1)?.sub(value)),
                value: format!("(- {})", x.value),
                denotation: format!(
                    "(Litex.NativeBridge.denoteNeg {a} {} {} {})",
                    member.proof, x.value, x.denotation
                ),
                member: format!("(Litex.negInC {a} {})", member.proof),
            },
        ))
    }

    fn compile_pow_wd(
        &mut self,
        base: &Obj,
        exponent: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        runtime: &Runtime,
    ) -> Result<(String, NumericTerm), LeanCompileError> {
        if children.len() != 2 || !(requirements.len() == 2 || requirements.len() == 3) {
            return Err(LeanCompileError::new(
                "WD/Pow",
                "Integer-power evidence has the wrong stage arity.",
            ));
        }
        ensure_object(base, &children[0])?;
        ensure_object(exponent, &children[1])?;
        let a = self.compile_wd(&children[0], runtime)?;
        let e = self.compile_wd(&children[1], runtime)?;
        let integer = closed_integer(exponent)
            .ok_or_else(|| LeanCompileError::unsupported("WD/Pow/NonClosedIntegerExponent"))?;
        let mut proved = Vec::new();
        for requirement in requirements {
            proved.push(self.compile_verify(requirement, runtime)?);
        }
        let base_set = membership_subject(&proved[0].fact, base)?;
        let exponent_set = membership_subject(&proved[1].fact, exponent)?;
        let (name, bridge, exponent_value) =
            match (base_set.clone(), exponent_set, requirements.len()) {
                (StandardSet::R, StandardSet::N, 2) if integer >= 0 => {
                    ("powNatReal", "PowNatReal", format!("({integer} : ℕ)"))
                }
                (StandardSet::C, StandardSet::N, 2) if integer >= 0 => {
                    ("powNat", "PowNat", format!("({integer} : ℕ)"))
                }
                (StandardSet::C, StandardSet::Z, 3) => {
                    ensure_nonzero_subject(&proved[2].fact, base)?;
                    ("powInt", "PowInt", format!("({integer} : ℤ)"))
                }
                _ => return Err(LeanCompileError::unsupported("WD/Pow/Domain")),
            };
        if base_set == StandardSet::R {
            self.remember_complex_member(
                base,
                &format!("(Litex.realToComplex {a} {})", proved[0].proof),
            )?;
        }
        // The exponent remains its own owned object; this proof connects its
        // checked closed arithmetic denotation to the exact integer argument.
        let exp_native = self.numeric_term(exponent)?;
        let integer_complex = format!("({exponent_value} : ℂ)");
        let he_value = format!("(Litex.NativeBridge.sameOfDenoteNumber {e} (Litex.number (M := M) {integer_complex}) {} {integer_complex} {} (Litex.NativeBridge.denoteNumber (M := M) {integer_complex}) (by norm_num))", exp_native.value, exp_native.denotation);
        let guard = if requirements.len() == 3 {
            format!(" {}", proved[2].proof)
        } else {
            String::new()
        };
        let arguments = format!(
            "{a} {e} {exponent_value} {} {}{guard} {he_value}",
            proved[0].proof, proved[1].proof
        );
        let x = self.numeric_term(base)?;
        Ok((
            format!("(Litex.{name} {arguments})"),
            NumericTerm {
                closed: x
                    .closed
                    .as_ref()
                    .and_then(|value| value.pow_integer(integer)),
                value: format!("({} ^ {exponent_value})", x.value),
                denotation: format!(
                    "(Litex.NativeBridge.denote{bridge} {arguments} {} {})",
                    x.value, x.denotation
                ),
                member: format!("(Litex.{name}InC {arguments})"),
            },
        ))
    }

    fn compile_atomic_wd(
        &mut self,
        wd: &AtomicFactWellDefinedProof,
        fact: &AtomicFact,
        runtime: &Runtime,
    ) -> Result<(), LeanCompileError> {
        let args = atomic_fact_args_ref(fact);
        if wd.well_defined_of_each_parameter.len() != args.len() {
            return Err(LeanCompileError::new(
                "WD/Atomic",
                "Object WD evidence has the wrong argument arity.",
            ));
        }
        for (arg, proof) in args.iter().zip(&wd.well_defined_of_each_parameter) {
            ensure_object(arg, proof)?;
            self.compile_wd(proof, runtime)?;
        }
        match &wd.predicate_signature {
            PredicateSignatureWellDefinedProof::Builtin => {}
            PredicateSignatureWellDefinedProof::Prop { .. }
            | PredicateSignatureWellDefinedProof::AbstractProp { .. } => {
                return Err(LeanCompileError::unsupported("WD/UserPredicate"))
            }
        }
        match &wd.predicate_domain {
            PredicateDomainProof::ByRequirements(requirements) => {
                if matches!(
                    fact,
                    AtomicFact::LessFact(_)
                        | AtomicFact::GreaterFact(_)
                        | AtomicFact::LessEqualFact(_)
                        | AtomicFact::GreaterEqualFact(_)
                        | AtomicFact::NotLessFact(_)
                        | AtomicFact::NotGreaterFact(_)
                        | AtomicFact::NotLessEqualFact(_)
                        | AtomicFact::NotGreaterEqualFact(_)
                ) {
                    if requirements.len() != 2 || requirements.iter().zip(&args).any(|(requirement, argument)| !matches!(&requirement.requirement, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == argument.ir() && f.set == Obj::StandardSet(StandardSet::R))) {
                        return Err(LeanCompileError::new("WD/OrderRealDomain", "The order predicate needs its two exact ordered real-membership stages."));
                    }
                }
                for requirement in requirements {
                    let compiled = self.compile_verify(&requirement.result, runtime)?;
                    if compiled.fact != requirement.requirement {
                        return Err(LeanCompileError::new(
                            "WD/PredicateDomain",
                            "Verified domain requirement has another subject.",
                        ));
                    }
                }
            }
            PredicateDomainProof::ByKnownFact(proof) => {
                let known = self.compile_known_atomic(proof, fact, runtime)?;
                if source_order_parts(fact).is_ok() {
                    let (left, right) = self.order_real_members_from_known(fact, &known)?;
                    self.remember_real_member(args[0], &left);
                    self.remember_real_member(args[1], &right);
                }
            }
        }
        Ok(())
    }

    fn compile_fact_wd(
        &mut self,
        wd: &FactWellDefinedProof,
        fact: &Fact,
        runtime: &Runtime,
    ) -> Result<(), LeanCompileError> {
        match (wd, fact) {
            (FactWellDefinedProof::AtomicExceptEquality(wd), Fact::AtomicFact(atomic)) => {
                self.compile_atomic_wd(wd, atomic, runtime)
            }
            (
                FactWellDefinedProof::Equality(wd),
                Fact::AtomicFact(AtomicFact::EqualFact(equal)),
            ) => {
                ensure_object(&equal.left, &wd.left)?;
                ensure_object(&equal.right, &wd.right)?;
                self.compile_wd(&wd.left, runtime)?;
                self.compile_wd(&wd.right, runtime)?;
                Ok(())
            }
            (FactWellDefinedProof::Equality(_), _) => Err(LeanCompileError::new(
                "WD/Fact",
                "Equality WD has another subject.",
            )),
            (FactWellDefinedProof::AtomicExceptEquality(_), _) => Err(LeanCompileError::new(
                "WD/Fact",
                "Atomic WD has another subject.",
            )),
            (FactWellDefinedProof::ForallFact(proof), Fact::ForallFact(fact)) => {
                self.compile_forall_wd(fact, proof, runtime)
            }
            (FactWellDefinedProof::ForallFact(_), _) => Err(LeanCompileError::new(
                "WD/ForallSubject",
                "Quantified WD evidence has another source fact family.",
            )),
            (
                FactWellDefinedProof::AndFact { .. }
                | FactWellDefinedProof::ChainFact { .. }
                | FactWellDefinedProof::OrFact(_)
                | FactWellDefinedProof::ExistFact(_)
                | FactWellDefinedProof::ForallFactWithIff(_)
                | FactWellDefinedProof::NotForall(_),
                _,
            ) => Err(LeanCompileError::unsupported("WD/CompoundFact")),
        }
    }

    // The goal's WD scope predates the named theorem's separate truth scope.
    // Its actual parameter/domain producers cannot be replaced by body IDs.
    fn compile_forall_wd(
        &mut self,
        fact: &ForallFact,
        proof: &ForallFactWellDefinedProof,
        runtime: &Runtime,
    ) -> Result<(), LeanCompileError> {
        self.scopes.push(CompilerScope {
            env: Some(proof.local_env.clone()),
            ..CompilerScope::default()
        });
        let compiled = self.compile_forall_wd_body(fact, proof, runtime);
        self.scopes.pop();
        compiled
    }

    fn compile_forall_wd_body(
        &mut self,
        fact: &ForallFact,
        proof: &ForallFactWellDefinedProof,
        runtime: &Runtime,
    ) -> Result<(), LeanCompileError> {
        // Reuse the same binder/domain replay, but emit no declaration or
        // truth proof. In particular, then-WD never assumes a conclusion.
        self.compile_forall_head(
            fact,
            &proof.introduced_params,
            &proof.assumed_dom_facts,
            runtime,
        )?;
        if proof.then.len() != fact.then_facts.len() {
            return Err(LeanCompileError::new(
                "WD/ForallThenArity",
                "Quantified conclusion WD has the wrong ordered stage arity.",
            ));
        }
        for (fact, wd) in fact.then_facts.iter().zip(&proof.then) {
            let fact: Fact = fact.clone().into();
            self.compile_fact_wd(wd, &fact, runtime)?;
        }
        Ok(())
    }

    // Endpoints have already been certified by the owning verify/argument stage.
    // Reuse the exact selected search route, never another proof of its target.
    fn compile_equality_search(
        &mut self,
        fact: &EqualFact,
        proof: &EqualFactSearchedProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let left = self.object_term(&fact.left)?;
        self.object_term(&fact.right)?;
        let proof = match proof {
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_)) => {
                if fact.left.ir() != fact.right.ir() {
                    return Err(LeanCompileError::new(
                        "SameIr",
                        "Identity evidence has different endpoints.",
                    ));
                }
                format!("(Litex.sameRefl {left})")
            }
            EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameFreeParamShape(
                _,
            )) => return Err(LeanCompileError::unsupported("Equality/SameFreeParamShape")),
            EqualFactSearchedProof::ByClosedCalculation(proof) => {
                self.compile_closed_equality(fact, proof)?
            }
            EqualFactSearchedProof::ByKnownSpecialProperty(_) => {
                return Err(LeanCompileError::unsupported(
                    "Equality/KnownSpecialProperty",
                ))
            }
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::Calculation(
                    EqualitySearchProofByCalculation::Rational {},
                ),
            ) => self.compile_rational(fact, &[], &[], false, runtime)?,
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(proof),
            ) => self.compile_scalar_division_relation(fact, proof, runtime)?,
            EqualFactSearchedProof::ByBuiltinRule(_) => {
                return Err(LeanCompileError::unsupported("Equality/BuiltinRule"))
            }
            EqualFactSearchedProof::ByEquivalenceClass(proof) => {
                self.compile_equivalence_class(fact, proof, runtime)?
            }
            EqualFactSearchedProof::ByObjectDefinition(_) => {
                return Err(LeanCompileError::unsupported("Equality/ObjectDefinition"))
            }
            EqualFactSearchedProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ) => self.compile_rational(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                true,
                runtime,
            )?,
            EqualFactSearchedProof::ByBuiltinStrategy(_) => {
                return Err(LeanCompileError::unsupported("Equality/BuiltinStrategy"))
            }
            EqualFactSearchedProof::ByMatchingOneArgByOne(proof) => self
                .compile_arithmetic_congruence(
                    fact,
                    &proof.corresponding_arg_equal_proofs,
                    runtime,
                )?,
            EqualFactSearchedProof::ByKnownForallFact(_) => {
                return Err(LeanCompileError::unsupported("Equality/KnownForallFact"))
            }
            EqualFactSearchedProof::ByKnownForallFactViaSymmetry(_) => {
                return Err(LeanCompileError::unsupported(
                    "Equality/KnownForallFactViaSymmetry",
                ))
            }
            EqualFactSearchedProof::ByBuiltinRewrite(
                EqualitySearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof),
            ) => self.compile_closed_equality_substitution(fact, proof, runtime)?,
        };
        Ok(proof)
    }

    fn compile_identity(
        &self,
        left: &Obj,
        right: &Obj,
        proof: &TheyAreTheSameProof,
    ) -> Result<String, LeanCompileError> {
        match proof {
            TheyAreTheSameProof::SameIr(_) if left.ir() == right.ir() => {
                Ok(format!("(Litex.sameRefl {})", self.object_term(left)?))
            }
            TheyAreTheSameProof::SameIr(_) => Err(LeanCompileError::new(
                "Equality/IdentitySubject",
                "Exact identity evidence has different source endpoints.",
            )),
            TheyAreTheSameProof::SameFreeParamShape(_) => {
                Err(LeanCompileError::unsupported("Equality/SameFreeParamShape"))
            }
        }
    }

    fn compile_equivalence_class(
        &mut self,
        fact: &EqualFact,
        proof: &EqualFactSearchedProofByEquivalenceClass,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        match proof {
            EqualFactSearchedProofByEquivalenceClass::KnownPath(path) => {
                self.compile_equality_path(&fact.left, &fact.right, path, runtime)
            }
            EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof) => {
                let resolved = self.resolve_fact(proof.cited.fact_id, runtime)?;
                if resolved != Fact::AtomicFact(AtomicFact::EqualFact(proof.cited.clone())) {
                    return Err(LeanCompileError::new(
                        "Equality/AlphaCitation",
                        "Alpha endpoint evidence changes its cited source equality.",
                    ));
                }
                let (left, right) = if proof.reversed {
                    (&proof.cited.right, &proof.cited.left)
                } else {
                    (&proof.cited.left, &proof.cited.right)
                };
                let cited =
                    self.compile_registered_equality(proof.cited.fact_id, left, right, runtime)?;
                let left_identity =
                    self.compile_identity(left, &fact.left, &proof.left_identity)?;
                let right_identity =
                    self.compile_identity(right, &fact.right, &proof.right_identity)?;
                Ok(format!(
                    "(({left_identity}).symm.trans (({cited}).trans {right_identity}))"
                ))
            }
            EqualFactSearchedProofByEquivalenceClass::AlphaPaths(proof) => {
                let left_path =
                    self.compile_equality_path(&fact.left, &proof.left, &proof.left_path, runtime)?;
                let identity = self.compile_identity(&proof.left, &proof.right, &proof.identity)?;
                let right_path = self.compile_equality_path(
                    &proof.right,
                    &fact.right,
                    &proof.right_path,
                    runtime,
                )?;
                Ok(format!(
                    "(({left_path}).trans (({identity}).trans {right_path}))"
                ))
            }
            EqualFactSearchedProofByEquivalenceClass::ViaPeers(proof) => {
                ensure_object(
                    &proof.bridge.fact.left,
                    &proof.bridge.well_defined_proof.left,
                )?;
                ensure_object(
                    &proof.bridge.fact.right,
                    &proof.bridge.well_defined_proof.right,
                )?;
                self.compile_wd(&proof.bridge.well_defined_proof.left, runtime)?;
                self.compile_wd(&proof.bridge.well_defined_proof.right, runtime)?;
                let left_path = self.compile_equality_path(
                    &fact.left,
                    &proof.bridge.fact.left,
                    &proof.left_path,
                    runtime,
                )?;
                let bridge = self.compile_equality_search(
                    &proof.bridge.fact,
                    &proof.bridge.searched_proof,
                    runtime,
                )?;
                let right_path = self.compile_equality_path(
                    &proof.bridge.fact.right,
                    &fact.right,
                    &proof.right_path,
                    runtime,
                )?;
                Ok(format!(
                    "(({left_path}).trans (({bridge}).trans {right_path}))"
                ))
            }
        }
    }

    fn compile_equality_path(
        &self,
        left: &Obj,
        right: &Obj,
        proof: &KnownEqualityPathProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let mut current = left;
        let mut compiled = format!("(Litex.sameRefl {})", self.object_term(left)?);
        self.object_term(right)?;
        for (from, to, id) in &proof.path {
            if from.ir() != current.ir() {
                return Err(LeanCompileError::new(
                    "Equality/PathOrder",
                    "An equality edge does not continue the recorded ordered path.",
                ));
            }
            let step = self.compile_registered_equality(*id, from, to, runtime)?;
            compiled = format!("(({compiled}).trans {step})");
            current = to;
        }
        if current.ir() != right.ir() {
            return Err(LeanCompileError::new(
                "Equality/PathEndpoint",
                "The recorded equality path does not end at the requested endpoint.",
            ));
        }
        Ok(compiled)
    }

    fn compile_registered_equality(
        &self,
        id: FactId,
        from: &Obj,
        to: &Obj,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let resolved = self.resolve_fact(id, runtime)?;
        let equality = match &resolved {
            Fact::AtomicFact(AtomicFact::EqualFact(equal)) if equal.fact_id == id => equal,
            _ => {
                return Err(LeanCompileError::new(
                    "Equality/PathCitation",
                    "The equality path cites another fact family or identity.",
                ))
            }
        };
        let registered = self.fact_term(id)?;
        if registered.fact != resolved {
            return Err(LeanCompileError::new(
                "Equality/PathProducer",
                "The cited equality differs from its active compiled producer.",
            ));
        }
        self.object_term(from)?;
        self.object_term(to)?;
        if equality.left.ir() == from.ir() && equality.right.ir() == to.ir() {
            Ok(registered.proof.clone())
        } else if equality.right.ir() == from.ir() && equality.left.ir() == to.ir() {
            Ok(format!("({}).symm", registered.proof))
        } else {
            Err(LeanCompileError::new(
                "Equality/PathSubject",
                "The cited equality does not prove the recorded oriented edge.",
            ))
        }
    }

    fn compile_closed_equality_substitution(
        &mut self,
        goal: &EqualFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_rewrite_result::ClosedNumericEqualSubstitutionBuiltinRewriteProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        if proof.cited_equal_fact_ids.is_empty() {
            return Err(LeanCompileError::new(
                "EqualityRewrite/Citations",
                "The selected substitution must cite a source equality.",
            ));
        }
        let mut equalities = Vec::new();
        for (index, id) in proof.cited_equal_fact_ids.iter().enumerate() {
            if proof.cited_equal_fact_ids[..index].contains(id) {
                return Err(LeanCompileError::new(
                    "EqualityRewrite/Citations",
                    "Substitution citations are unique in source order.",
                ));
            }
            let resolved = self.resolve_fact(*id, runtime)?;
            let equality = match &resolved {
                Fact::AtomicFact(AtomicFact::EqualFact(eq)) if eq.fact_id == *id => eq,
                _ => {
                    return Err(LeanCompileError::new(
                        "EqualityRewrite/CitationFamily",
                        "Substitution cites another fact family or identity.",
                    ))
                }
            };
            if self.fact_term(*id)?.fact != resolved {
                return Err(LeanCompileError::new(
                    "EqualityRewrite/Producer",
                    "The equality citation differs from its compiled producer.",
                ));
            }
            equalities.push((*id, equality.clone()));
        }
        let residual = self.compile_verify(&proof.residual_equal, runtime)?;
        match &residual.fact {
            Fact::AtomicFact(AtomicFact::EqualFact(eq))
                if eq.left.ir() == proof.rewritten_left.ir()
                    && eq.right.ir() == proof.rewritten_right.ir() => {}
            _ => {
                return Err(LeanCompileError::new(
                    "EqualityRewrite/Residual",
                    "The actual residual proof has different ordered endpoints.",
                ))
            }
        }
        let mut used = Vec::new();
        let left = self.compile_cited_closed_substitution(
            &goal.left,
            &proof.rewritten_left,
            &equalities,
            &mut used,
            runtime,
        )?;
        let right = self.compile_cited_closed_substitution(
            &goal.right,
            &proof.rewritten_right,
            &equalities,
            &mut used,
            runtime,
        )?;
        if used != proof.cited_equal_fact_ids {
            return Err(LeanCompileError::new(
                "EqualityRewrite/CitationOrder",
                "Every source equality must be used in the recorded substitution order.",
            ));
        }
        Ok(format!(
            "(({left}).trans (({}).trans ({right}).symm))",
            residual.proof
        ))
    }

    fn compile_cited_closed_substitution(
        &self,
        original: &Obj,
        residual: &Obj,
        equalities: &[(FactId, EqualFact)],
        used: &mut Vec<FactId>,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        self.object_term(original)?;
        self.object_term(residual)?;
        if original.ir() == residual.ir() {
            return Ok(format!("(Litex.sameRefl {})", self.object_term(original)?));
        }
        let direct: Vec<_> = equalities
            .iter()
            .filter(|(_, eq)| {
                (eq.left.ir() == original.ir()
                    && eq.right.ir() == residual.ir()
                    && ClosedNumericExpr::try_from_obj(&eq.right).is_some())
                    || (eq.right.ir() == original.ir()
                        && eq.left.ir() == residual.ir()
                        && ClosedNumericExpr::try_from_obj(&eq.left).is_some())
            })
            .collect();
        if direct.len() > 1 {
            return Err(LeanCompileError::new(
                "EqualityRewrite/AmbiguousEndpoint",
                "A changed subtree has multiple recorded source substitutions.",
            ));
        }
        if let Some((id, _)) = direct.first() {
            if !used.contains(id) {
                used.push(*id);
            }
            return self.compile_registered_equality(*id, original, residual, runtime);
        }
        let (operation, pairs) = arithmetic_constructor_pairs(original, residual).ok_or_else(|| LeanCompileError::new("EqualityRewrite/Subterm", "The changed subtree has no exact recorded closed endpoint or matching owned arithmetic constructor."))?;
        let mut children = Vec::new();
        for (a, b) in pairs {
            children.push(self.compile_cited_closed_substitution(a, b, equalities, used, runtime)?);
        }
        Ok(if children.len() == 1 {
            format!("(congrArg M.{operation} {})", children[0])
        } else {
            format!("(congrArg₂ M.{operation} {} {})", children[0], children[1])
        })
    }

    fn compile_atomic_builtin_rewrite(
        &mut self,
        goal: &AtomicFact,
        proof: &AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        match proof {
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof) =>
                self.compile_atomic_equality_rewrite(
                    goal,
                    &proof.rewritten_fact,
                    &proof.cited_equal_fact_ids,
                    &proof.proof_of_rewritten_fact,
                    true,
                    runtime,
                ),
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(proof) =>
                self.compile_atomic_equality_rewrite(
                    goal,
                    &proof.rewritten_fact,
                    &proof.cited_equal_fact_ids,
                    &proof.proof_of_rewritten_fact,
                    false,
                    runtime,
                ),
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(_) =>
                Err(LeanCompileError::unsupported("Atomic/BuiltinRewrite/FnUnfold")),
            AtomicExceptEqualityFactSearchProofByBuiltinRewrite::OrderDual(proof) => self.compile_order_dual(goal, proof, runtime),
        }
    }

    fn compile_atomic_equality_rewrite(
        &mut self,
        goal: &AtomicFact,
        rewritten: &Fact,
        cited_ids: &[FactId],
        child: &VerifyFactResult,
        closed_numeric: bool,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        if !matches!(
            goal,
            AtomicFact::InFact(_) | AtomicFact::IsSetFact(_) | AtomicFact::NotEqualFact(_)
        ) {
            return Err(LeanCompileError::unsupported(
                "Atomic/BuiltinRewrite/PredicateTransport",
            ));
        }
        let residual = match rewritten {
            Fact::AtomicFact(fact) if same_atomic_family(goal, fact) => fact,
            _ => {
                return Err(LeanCompileError::new(
                    "AtomicRewrite/Family",
                    "The residual changes the source predicate family, polarity or arity.",
                ))
            }
        };
        if cited_ids.is_empty()
            || cited_ids
                .iter()
                .enumerate()
                .any(|(index, id)| cited_ids[..index].contains(id))
        {
            return Err(LeanCompileError::new(
                "AtomicRewrite/Citations",
                "A substitution needs nonempty, nonduplicated recorded equality citations.",
            ));
        }
        let mut equalities = Vec::new();
        for id in cited_ids {
            let fact = self.resolve_fact(*id, runtime)?;
            let equality = match &fact {
                Fact::AtomicFact(AtomicFact::EqualFact(equality)) if equality.fact_id == *id => {
                    equality
                }
                _ => {
                    return Err(LeanCompileError::new(
                        "AtomicRewrite/CitationFamily",
                        "A substitution citation is not the recorded source equality.",
                    ))
                }
            };
            if self.fact_term(*id)?.fact != fact {
                return Err(LeanCompileError::new(
                    "AtomicRewrite/CitationProducer",
                    "A substitution equality differs from its active compiled producer.",
                ));
            }
            equalities.push(equality.clone());
        }
        let child = self.compile_verify(child, runtime)?;
        if child.fact != *rewritten {
            return Err(LeanCompileError::new(
                "AtomicRewrite/ChildSubject",
                "The successful child does not prove the exact recorded residual fact.",
            ));
        }
        let original_args = atomic_fact_args_ref(goal);
        let residual_args = atomic_fact_args_ref(residual);
        let changed = original_args
            .iter()
            .zip(&residual_args)
            .filter(|(original, residual)| original.ir() != residual.ir())
            .count();
        if changed == 0 || (!closed_numeric && changed != 1) {
            return Err(LeanCompileError::new(
                "AtomicRewrite/ChangedArguments",
                "The selected substitution has no changed argument or changes more than its one recorded path.",
            ));
        }
        let mut arguments = Vec::new();
        let mut used_ids = Vec::new();
        for (original, residual) in original_args.iter().zip(&residual_args) {
            if original.ir() == residual.ir() {
                arguments.push(format!("(Litex.sameRefl {})", self.object_term(residual)?));
                continue;
            }
            if closed_numeric {
                // A whole-argument alias keeps the exact closed endpoint of
                // its selected source equality. The source producer preserves
                // that closed AST rather than replacing it by a computed value.
                if ClosedNumericExpr::try_from_obj(original).is_some()
                    || ClosedNumericExpr::try_from_obj(residual).is_none()
                {
                    return Err(LeanCompileError::unsupported(
                        "AtomicRewrite/ClosedTopLevelSubject",
                    ));
                }
                let matching: Vec<_> = equalities
                    .iter()
                    .enumerate()
                    .filter(|(_, equality)| {
                        (equality.left.ir() == original.ir()
                            && equality.right.ir() == residual.ir())
                            || (equality.right.ir() == original.ir()
                                && equality.left.ir() == residual.ir())
                    })
                    .collect();
                if matching.len() != 1 {
                    return Err(LeanCompileError::new(
                        "AtomicRewrite/ClosedTopLevelCitation",
                        "A changed whole argument needs one selected equality with those exact original and closed residual endpoints.",
                    ));
                }
                let id = cited_ids[matching[0].0];
                if !used_ids.contains(&id) {
                    used_ids.push(id);
                }
                arguments.push(self.compile_registered_equality(id, residual, original, runtime)?);
            } else {
                // KnownEqualObj records one ordered path for one top-level
                // argument. Only its listed edges can choose the next endpoint.
                let mut current: Obj = (**original).clone();
                let mut path = format!("(Litex.sameRefl {})", self.object_term(original)?);
                for (id, equality) in cited_ids.iter().zip(&equalities) {
                    let next = if equality.left.ir() == current.ir() {
                        &equality.right
                    } else if equality.right.ir() == current.ir() {
                        &equality.left
                    } else {
                        return Err(LeanCompileError::new(
                            "AtomicRewrite/PathOrder",
                            "The recorded equality does not continue the ordered substitution path.",
                        ));
                    };
                    if next.ir() == current.ir() {
                        return Err(LeanCompileError::new(
                            "AtomicRewrite/PathProgress",
                            "A substitution path edge does not change its source endpoint.",
                        ));
                    }
                    let edge = self.compile_registered_equality(*id, &current, next, runtime)?;
                    path = format!("(({path}).trans {edge})");
                    current = next.clone();
                    used_ids.push(*id);
                }
                if current.ir() != residual.ir() {
                    return Err(LeanCompileError::new(
                        "AtomicRewrite/PathEndpoint",
                        "The recorded substitution path does not end at this residual argument.",
                    ));
                }
                arguments.push(format!("({path}).symm"));
            }
        }
        if used_ids.as_slice() != cited_ids {
            return Err(LeanCompileError::new(
                "AtomicRewrite/CitationOrder",
                "Every recorded equality must be used in its source substitution order.",
            ));
        }
        match (residual, goal) {
            (AtomicFact::InFact(from), AtomicFact::InFact(to)) => Ok(format!(
                "(Litex.inOfSame {} {} {} {} {} {} {})",
                self.object_term(&from.element)?,
                self.object_term(&to.element)?,
                self.object_term(&from.set)?,
                self.object_term(&to.set)?,
                arguments[0],
                arguments[1],
                child.proof,
            )),
            (AtomicFact::IsSetFact(from), AtomicFact::IsSetFact(to)) => Ok(format!(
                "(Litex.isSetOfSame {} {} {} {})",
                self.object_term(&from.set)?,
                self.object_term(&to.set)?,
                arguments[0],
                child.proof,
            )),
            (AtomicFact::NotEqualFact(from), AtomicFact::NotEqualFact(to)) => Ok(format!(
                "(Litex.notSameOfSame {} {} {} {} {} {} {})",
                self.object_term(&from.left)?,
                self.object_term(&to.left)?,
                self.object_term(&from.right)?,
                self.object_term(&to.right)?,
                arguments[0],
                arguments[1],
                child.proof,
            )),
            _ => Err(LeanCompileError::unsupported(
                "Atomic/BuiltinRewrite/PredicateTransport",
            )),
        }
    }

    fn compile_known_atomic(
        &mut self,
        proof: &AtomicExceptEqualityFactSearchProofByKnownAtomicFact,
        goal: &AtomicFact,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        if matches!(goal, AtomicFact::EqualFact(_)) {
            return Err(LeanCompileError::new(
                "KnownAtomic/Family",
                "Non-equality citation evidence cannot select the equality family.",
            ));
        }
        let resolved = self.resolve_fact(proof.cite_fact_id, runtime)?;
        let cited = match &resolved {
            Fact::AtomicFact(cited) => cited,
            _ => {
                return Err(LeanCompileError::new(
                    "KnownAtomic",
                    "Citation resolves to a non-atomic fact.",
                ))
            }
        };
        let registered = self.fact_term(proof.cite_fact_id)?.clone();
        if registered.fact != resolved || !same_atomic_family(cited, goal) {
            return Err(LeanCompileError::new(
                "KnownAtomic",
                "Citation differs from its registered producer or target family.",
            ));
        }
        let cited_args = atomic_fact_args_ref(cited);
        let goal_args = atomic_fact_args_ref(goal);
        if proof.why_parameters_of_known_fact_are_equal_to_givens.len() != goal_args.len() {
            return Err(LeanCompileError::new(
                "KnownAtomic",
                "Argument equality evidence has the wrong ordered arity.",
            ));
        }
        let mut arguments = Vec::new();
        let mut exact_identity = true;
        for ((cited, given), equality) in cited_args
            .iter()
            .zip(&goal_args)
            .zip(&proof.why_parameters_of_known_fact_are_equal_to_givens)
        {
            // This source stage retains a winner rather than a second fact/WD
            // wrapper. Its exact endpoints come from the citation and target.
            // The local obligation view is never registered as a source fact.
            let obligation = EqualFact {
                fact_id: goal.fact_id(),
                left: (*cited).clone(),
                right: (*given).clone(),
                line_file: None,
            };
            arguments.push(self.compile_equality_search(&obligation, equality, runtime)?);
            exact_identity &= cited.ir() == given.ir()
                && matches!(
                    equality,
                    EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
                );
        }
        if exact_identity {
            return Ok(registered.proof);
        }
        match (cited, goal) {
            (AtomicFact::InFact(known), AtomicFact::InFact(given)) => Ok(format!(
                "(Litex.inOfSame {} {} {} {} {} {} {})",
                self.object_term(&known.element)?,
                self.object_term(&given.element)?,
                self.object_term(&known.set)?,
                self.object_term(&given.set)?,
                arguments[0],
                arguments[1],
                registered.proof,
            )),
            (AtomicFact::IsSetFact(known), AtomicFact::IsSetFact(given)) => Ok(format!(
                "(Litex.isSetOfSame {} {} {} {})",
                self.object_term(&known.set)?,
                self.object_term(&given.set)?,
                arguments[0],
                registered.proof,
            )),
            (AtomicFact::NotEqualFact(known), AtomicFact::NotEqualFact(given)) => Ok(format!(
                "(Litex.notSameOfSame {} {} {} {} {} {} {})",
                self.object_term(&known.left)?,
                self.object_term(&given.left)?,
                self.object_term(&known.right)?,
                self.object_term(&given.right)?,
                arguments[0],
                arguments[1],
                registered.proof,
            )),
            (
                known @ (AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)),
                given @ (AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_)),
            ) => self.compile_order_known_atomic_transport(
                known,
                given,
                &arguments,
                &registered.proof,
            ),
            _ => Err(LeanCompileError::unsupported(
                "KnownAtomic/PredicateTransport",
            )),
        }
    }

    fn compile_structural(
        &mut self,
        proof: &StructuralMembershipProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let compiled = match &proof.reason {
            StructuralMembershipReason::Known(known) => {
                let mut fact = match self.resolve_fact(known.cite_fact_id, runtime)? {
                    Fact::AtomicFact(AtomicFact::InFact(fact)) => fact,
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/Known",
                            "The structural citation is not a membership fact.",
                        ))
                    }
                };
                // Known membership may target an equal alias. Replay the exact
                // argument certificates against the structural node's subject.
                fact.element = proof.element.clone();
                fact.set = Obj::StandardSet(proof.set.clone());
                self.compile_known_atomic(known, &AtomicFact::InFact(fact), runtime)
            }
            StructuralMembershipReason::Closed(closed) => self.compile_closed_membership(
                &proof.element,
                &Obj::StandardSet(proof.set.clone()),
                closed,
            ),
            StructuralMembershipReason::StandardSuperset(child) => {
                if child.element.ir() != proof.element.ir() {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/SupersetSubject",
                        "Standard inclusion evidence changes its element.",
                    ));
                }
                let bridge = match (&child.set, &proof.set) {
                    (StandardSet::R, StandardSet::C) => "realToComplex",
                    (StandardSet::Z, StandardSet::C) => "integerToComplex",
                    (StandardSet::N, StandardSet::C) => "naturalToComplex",
                    (StandardSet::N, StandardSet::Z) => "naturalToInteger",
                    (StandardSet::N, StandardSet::R) => "naturalToReal",
                    (StandardSet::Z, StandardSet::R) => "integerToReal",
                    (StandardSet::N, StandardSet::Q) => "naturalToRational",
                    (StandardSet::Z, StandardSet::Q) => "integerToRational",
                    (StandardSet::Q, StandardSet::R) => "rationalToReal",
                    (StandardSet::Q, StandardSet::C) => "rationalToComplex",
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "StructuralMembership/StandardSuperset",
                        ))
                    }
                };
                let child = self.compile_structural(child, runtime)?;
                Ok(format!(
                    "(Litex.{bridge} {} {child})",
                    self.object_term(&proof.element)?
                ))
            }
            StructuralMembershipReason::KnownSubset(_) => Err(LeanCompileError::unsupported(
                "StructuralMembership/KnownSubset",
            )),
            StructuralMembershipReason::Add { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Add, runtime)
            }
            StructuralMembershipReason::Sub { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Sub, runtime)
            }
            StructuralMembershipReason::Mul { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Mul, runtime)
            }
            StructuralMembershipReason::Div { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Div, runtime)
            }
            StructuralMembershipReason::Neg { argument } => {
                let operand = match &proof.element {
                    Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => x.arg.as_ref(),
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/NegSubject",
                            "Negation membership evidence has another constructor.",
                        ))
                    }
                };
                if operand.ir() != argument.element.ir() || proof.set != argument.set {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/NegChild",
                        "Negation membership changes its operand or carrier.",
                    ));
                }
                let child = self.compile_structural(argument, runtime)?;
                match proof.set {
                    StandardSet::C => Ok(format!(
                        "(Litex.negInC {} {child})",
                        self.object_term(operand)?
                    )),
                    StandardSet::R => Ok(format!(
                        "(Litex.negInR {} {child})",
                        self.object_term(operand)?
                    )),
                    StandardSet::Q => Ok(format!(
                        "(Litex.negInQ {} {child})",
                        self.object_term(operand)?
                    )),
                    StandardSet::Z => Ok(format!(
                        "(Litex.negInZ {} {child})",
                        self.object_term(operand)?
                    )),
                    _ => Err(LeanCompileError::unsupported(
                        "StructuralMembership/NegCarrier",
                    )),
                }
            }
            StructuralMembershipReason::Abs { .. } => {
                Err(LeanCompileError::unsupported("StructuralMembership/Abs"))
            }
            StructuralMembershipReason::Pow { base, exponent } => {
                let power = match &proof.element {
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => x,
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/PowSubject",
                            "Power membership evidence has another constructor.",
                        ))
                    }
                };
                let expected_exponent = if matches!(proof.set, StandardSet::N | StandardSet::Z) {
                    StandardSet::N
                } else {
                    StandardSet::Z
                };
                if power.base.ir() != base.element.ir()
                    || power.exponent.ir() != exponent.element.ir()
                    || base.set != proof.set
                    || exponent.set != expected_exponent
                {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/PowChild",
                        "Power membership changes its operand or integer carrier.",
                    ));
                }
                let ha_c = self.compile_structural(base, runtime)?;
                let he_z = self.compile_structural(exponent, runtime)?;
                match proof.set {
                    StandardSet::C => Ok(format!(
                        "(Litex.powStructuralInC {} {ha_c} {he_z})",
                        self.object_term(&proof.element)?
                    )),
                    StandardSet::R | StandardSet::Q => {
                        let suffix = if proof.set == StandardSet::Q {
                            "Q"
                        } else {
                            "R"
                        };
                        // Replay the actual integer-child certificate even though the
                        // owned power WD already proves exponent identification.
                        Ok(format!("(by\n  have _recorded_exp : Litex.In {} (Litex.Z (M := M)) := {he_z}\n  exact Litex.powStructuralIn{suffix} {} {ha_c}\n)", self.object_term(&power.exponent)?, self.object_term(&proof.element)?))
                    }
                    _ => Err(LeanCompileError::unsupported(
                        "StructuralMembership/PowCarrier",
                    )),
                }
            }
            StructuralMembershipReason::Intrinsic(_) => Err(LeanCompileError::unsupported(
                "StructuralMembership/Intrinsic",
            )),
        }?;
        if proof.set == StandardSet::R {
            self.remember_real_member(&proof.element, &compiled);
        }
        Ok(compiled)
    }

    fn compile_structural_binary(
        &mut self,
        root: &StructuralMembershipProof,
        left: &StructuralMembershipProof,
        right: &StructuralMembershipProof,
        operation: BinaryArithmetic,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (a, b, name) = match (&root.element, operation) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Add(x)), BinaryArithmetic::Add) => {
                (x.left.as_ref(), x.right.as_ref(), "add")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)), BinaryArithmetic::Sub) => {
                (x.left.as_ref(), x.right.as_ref(), "sub")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)), BinaryArithmetic::Mul) => {
                (x.left.as_ref(), x.right.as_ref(), "mul")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Div(x)), BinaryArithmetic::Div) => {
                (x.left.as_ref(), x.right.as_ref(), "div")
            }
            _ => {
                return Err(LeanCompileError::new(
                    "StructuralMembership/ArithmeticSubject",
                    "Arithmetic membership evidence has another constructor.",
                ))
            }
        };
        if left.element.ir() != a.ir()
            || right.element.ir() != b.ir()
            || left.set != root.set
            || right.set != root.set
        {
            return Err(LeanCompileError::new(
                "StructuralMembership/ArithmeticChild",
                "Arithmetic membership changes its exact children or carrier.",
            ));
        }
        let ha = self.compile_structural(left, runtime)?;
        let hb = self.compile_structural(right, runtime)?;
        match root.set {
            StandardSet::C => {
                let guard = if matches!(operation, BinaryArithmetic::Div) {
                    format!(" ({}).wd.2.2", self.object_term(&root.element)?)
                } else {
                    String::new()
                };
                Ok(format!(
                    "(Litex.{name}InC {} {} {ha} {hb}{guard})",
                    self.object_term(a)?,
                    self.object_term(b)?
                ))
            }
            StandardSet::R | StandardSet::Q => {
                let suffix = if root.set == StandardSet::Q { "Q" } else { "R" };
                let guard = if matches!(operation, BinaryArithmetic::Div) {
                    format!(" ({}).wd.2.2", self.object_term(&root.element)?)
                } else {
                    String::new()
                };
                Ok(format!(
                    "(Litex.{name}In{suffix} {} {} {ha} {hb}{guard})",
                    self.object_term(a)?,
                    self.object_term(b)?
                ))
            }
            _ => Err(LeanCompileError::unsupported(
                "StructuralMembership/ArithmeticCarrier",
            )),
        }
    }

    fn compile_closed_membership(
        &self,
        element: &Obj,
        set: &Obj,
        proof: &ClosedMembershipCalculationProof,
    ) -> Result<String, LeanCompileError> {
        let (value, target) = match proof {
            ClosedMembershipCalculationProof::StandardSet { value, set: target }
                if set.ir() == Obj::StandardSet(target.clone()).ir() =>
            {
                (value, target)
            }
            ClosedMembershipCalculationProof::StandardSet { .. } => {
                return Err(LeanCompileError::new(
                    "ClosedMembership/Set",
                    "Closed membership changes the target set.",
                ))
            }
            ClosedMembershipCalculationProof::IntegerRange { .. } => {
                return Err(LeanCompileError::unsupported(
                    "ClosedMembership/IntegerRange",
                ))
            }
        };
        // Existing literal membership is unbounded integer syntax. It must not
        // inherit the i128 bound of the new closed-arithmetic evaluator.
        if let (Obj::Literal(Literal::Number(number)), ClosedScalarValue::Decimal(recorded)) =
            (element, value)
        {
            if &number.normalized_value != recorded {
                return Err(LeanCompileError::new(
                    "ClosedMembership/Value",
                    "The literal certificate records another numeric payload.",
                ));
            }
            let native = self.numeric_term(element)?;
            if *target == StandardSet::C {
                return Ok(format!("(Litex.numberInC (M := M) {})", native.value));
            }
            let (bridge, representative) = match target {
                StandardSet::R => ("numberInROfEq", number_literal(number, "ℝ")?),
                StandardSet::Q => ("numberInQOfEq", number_literal(number, "ℚ")?),
                StandardSet::N | StandardSet::Z => {
                    let value = &number.normalized_value;
                    let unsigned = value.strip_prefix('-').unwrap_or(value);
                    if !unsigned.bytes().all(|b| b.is_ascii_digit())
                        || (*target == StandardSet::N && value.starts_with('-'))
                    {
                        return Err(LeanCompileError::unsupported(
                            "ClosedMembership/IntegerLiteral",
                        ));
                    }
                    if *target == StandardSet::N {
                        ("numberInNOfEq", format!("({value} : ℕ)"))
                    } else {
                        ("numberInZOfEq", format!("({value} : ℤ)"))
                    }
                }
                _ => return Err(LeanCompileError::unsupported("ClosedMembership/Carrier")),
            };
            return Ok(format!("(Litex.NativeBridge.inOfDenoteNumber {} {} {} {} (Litex.NativeBridge.{bridge} {} {representative} (by norm_num)))", self.object_term(element)?, native.value, standard_term(target)?, native.denotation, native.value));
        }
        let calculated = self
            .numeric_term(element)?
            .closed
            .ok_or_else(|| LeanCompileError::unsupported("ClosedMembership/Expression"))?;
        let scalar = match value {
            ClosedScalarValue::Decimal(value) => scalar_decimal(value)?,
            ClosedScalarValue::ExactComplex { real, imaginary } if imaginary.is_zero() => {
                real.clone()
            }
            ClosedScalarValue::ExactComplex { .. } => {
                return Err(LeanCompileError::unsupported(
                    "ClosedMembership/ComplexScalar",
                ))
            }
        };
        if calculated != scalar {
            return Err(LeanCompileError::new(
                "ClosedMembership/Value",
                "The recorded exact scalar differs from its source arithmetic.",
            ));
        }
        let object = self.object_term(element)?;
        let native = self.numeric_term(element)?;
        if *target == StandardSet::C {
            let scalar = exact_rational_literal(&scalar, "ℂ")?;
            let denotation = format!(
                "({}).trans (congrArg M.number (by norm_num : {} = {scalar}))",
                native.denotation, native.value
            );
            return Ok(format!("(Litex.NativeBridge.inOfDenoteNumber {object} {scalar} {} ({denotation}) (Litex.numberInC (M := M) {scalar}))", standard_term(target)?));
        }
        let (bridge, representative) = match target {
            StandardSet::N => {
                let integer = scalar
                    .to_i128_if_integer()
                    .filter(|n| *n >= 0)
                    .ok_or_else(|| {
                        LeanCompileError::new(
                            "ClosedMembership/N",
                            "A natural certificate has no exact natural value.",
                        )
                    })?;
                ("numberInNOfEq", format!("({integer} : ℕ)"))
            }
            StandardSet::Z => {
                let integer = scalar.to_i128_if_integer().ok_or_else(|| {
                    LeanCompileError::new(
                        "ClosedMembership/Z",
                        "An integer certificate has no exact integer value.",
                    )
                })?;
                ("numberInZOfEq", format!("({integer} : ℤ)"))
            }
            StandardSet::R => ("numberInROfEq", exact_rational_literal(&scalar, "ℝ")?),
            StandardSet::Q => ("numberInQOfEq", exact_rational_literal(&scalar, "ℚ")?),
            _ => return Err(LeanCompileError::unsupported("ClosedMembership/Carrier")),
        };
        let number_member = format!(
            "(Litex.NativeBridge.{bridge} {} {representative} (by norm_num))",
            native.value
        );
        Ok(format!(
            "(Litex.NativeBridge.inOfDenoteNumber {object} {} {} {} {number_member})",
            native.value,
            standard_term(target)?,
            native.denotation
        ))
    }

    fn compile_order_proposition(&self, fact: &AtomicFact) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(fact)?;
        Ok(format!(
            "Litex.{} {} {}",
            if strict { "Lt" } else { "Le" },
            self.object_term(low)?,
            self.object_term(high)?
        ))
    }

    fn compile_closed_order(
        &self,
        goal: &AtomicFact,
        proof: &ClosedAtomicExceptEqualityCalculationProof,
    ) -> Result<String, LeanCompileError> {
        match (goal, proof) {
            (AtomicFact::LessFact(_), ClosedAtomicExceptEqualityCalculationProof::Less(p))
            | (
                AtomicFact::GreaterFact(_),
                ClosedAtomicExceptEqualityCalculationProof::Greater(p),
            )
            | (
                AtomicFact::LessEqualFact(_),
                ClosedAtomicExceptEqualityCalculationProof::LessEqual(p),
            )
            | (
                AtomicFact::GreaterEqualFact(_),
                ClosedAtomicExceptEqualityCalculationProof::GreaterEqual(p),
            ) => self.compile_closed_comparison(goal, p),
            _ => Err(LeanCompileError::new(
                "Order/ClosedFamily",
                "The typed closed comparison variant has another source predicate family.",
            )),
        }
    }

    fn compile_closed_comparison(
        &self,
        goal: &AtomicFact,
        proof: &ClosedComparisonCalculationProof,
    ) -> Result<String, LeanCompileError> {
        let (kind, left, right) = source_order_parts(goal)?;
        let x = self.numeric_term(left)?;
        let y = self.numeric_term(right)?;
        let a = x
            .closed
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("Order/ClosedExpression"))?;
        let b = y
            .closed
            .as_ref()
            .ok_or_else(|| LeanCompileError::unsupported("Order/ClosedExpression"))?;
        // Exact typed values are the certificate owner. The normal strings are
        // presentation fields, never proof subjects or evaluation instructions.
        let values_match = match &proof.values {
            ClosedValuePair::Decimal { left, right } => {
                scalar_decimal(left)? == *a && scalar_decimal(right)? == *b
            }
            ClosedValuePair::Rational { left, right } => left == a && right == b,
            ClosedValuePair::Complex {
                left_real,
                left_imaginary,
                right_real,
                right_imaginary,
            } => {
                left_real == a
                    && right_real == b
                    && left_imaginary.is_zero()
                    && right_imaginary.is_zero()
            }
            ClosedValuePair::Radical { .. } => {
                return Err(LeanCompileError::unsupported("Order/ClosedRadical"))
            }
        };
        let comparison = a
            .compare(b)
            .ok_or_else(|| LeanCompileError::unsupported("Order/ClosedEvaluationBound"))?;
        let true_order = match kind {
            SourceOrderKind::Less => comparison == NumberCompareResult::Less,
            SourceOrderKind::Greater => comparison == NumberCompareResult::Greater,
            SourceOrderKind::LessEqual => comparison != NumberCompareResult::Greater,
            SourceOrderKind::GreaterEqual => comparison != NumberCompareResult::Less,
        };
        if !values_match || comparison != proof.comparison || !true_order {
            return Err(LeanCompileError::new(
                "Order/ClosedValues",
                "Typed comparison values, comparison tag or source orientation do not agree.",
            ));
        }
        let r = exact_rational_literal(a, "ℝ")?;
        let s = exact_rational_literal(b, "ℝ")?;
        // These are the actual real-domain facts replayed before truth. A
        // numeric view alone does not classify an arbitrary complex as real.
        let ha = self.real_member(left)?;
        let hb = self.real_member(right)?;
        let lhs = self.object_term(left)?;
        let rhs = self.object_term(right)?;
        let (low, high, strict) = source_order_oriented(goal)?;
        let (low_r, high_r, low_value, high_value) = match kind {
            SourceOrderKind::Less | SourceOrderKind::LessEqual => {
                (&ha, &hb, "_litex_left_value", "_litex_right_value")
            }
            SourceOrderKind::Greater | SourceOrderKind::GreaterEqual => {
                (&hb, &ha, "_litex_right_value", "_litex_left_value")
            }
        };
        let observation = if strict {
            "lt_iff_asReal"
        } else {
            "le_iff_asReal"
        };
        let relation = if strict { "<" } else { "≤" };
        Ok(format!(
            "((Litex.NativeBridge.{observation} {} {} {low_r} {high_r}).mpr (by\n  have _litex_left_value : Litex.NativeBridge.asReal {lhs} {ha} = {r} := by\n    apply Complex.ofReal_injective\n    exact M.number_injective ((Litex.NativeBridge.asReal_spec {lhs} {ha}).symm.trans (({}).trans (congrArg M.number (by norm_num : {} = ({r} : ℂ)))))\n  have _litex_right_value : Litex.NativeBridge.asReal {rhs} {hb} = {s} := by\n    apply Complex.ofReal_injective\n    exact M.number_injective ((Litex.NativeBridge.asReal_spec {rhs} {hb}).symm.trans (({}).trans (congrArg M.number (by norm_num : {} = ({s} : ℂ)))))\n  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => _litex_r {relation} _litex_s) {low_value} {high_value}) (by norm_num)))",
            self.object_term(low)?, self.object_term(high)?, x.denotation, x.value, y.denotation, y.value,
        ))
    }

    fn compile_order_builtin(
        &mut self,
        goal: &AtomicFact,
        rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        match (goal, rule) {
            (
                AtomicFact::LessEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(rule),
            ) => match rule {
                LessEqualFactSearchProofByBuiltinRule::OrderReflexivity(p) => {
                    self.compile_order_reflexivity(goal, &p.repeated_object)
                }
                LessEqualFactSearchProofByBuiltinRule::FromKnownGreaterEqual(p) => self
                    .compile_order_known_conversion(
                        goal,
                        &p.premise_proof,
                        SourceOrderKind::GreaterEqual,
                        false,
                        runtime,
                    ),
                LessEqualFactSearchProofByBuiltinRule::FromKnownLess(p) => self
                    .compile_order_known_conversion(
                        goal,
                        &p.premise_proof,
                        SourceOrderKind::Less,
                        true,
                        runtime,
                    ),
                LessEqualFactSearchProofByBuiltinRule::EvenPowNonnegative(p) => {
                    self.compile_even_power_nonnegative(goal, &p.base_in_real_proof, runtime)
                }
                LessEqualFactSearchProofByBuiltinRule::AddRightCongruence(p) => {
                    self.compile_weak_add_congruence(goal, &p.premise_proof, false, runtime)
                }
                LessEqualFactSearchProofByBuiltinRule::AddLeftCongruence(p) => {
                    self.compile_weak_add_congruence(goal, &p.premise_proof, true, runtime)
                }
                LessEqualFactSearchProofByBuiltinRule::LessEqualTransitivity(p) => self
                    .compile_weak_order_transitivity(
                        goal,
                        p.left_to_mid_cite_fact_id,
                        p.mid_to_right_cite_fact_id,
                        runtime,
                    ),
                _ => Err(LeanCompileError::unsupported("Order/LessEqualBuiltin")),
            },
            (
                AtomicFact::GreaterEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(rule),
            ) => match rule {
                GreaterEqualFactSearchProofByBuiltinRule::OrderReflexivity(p) => {
                    self.compile_order_reflexivity(goal, &p.repeated_object)
                }
                GreaterEqualFactSearchProofByBuiltinRule::FromKnownLessEqual(p) => self
                    .compile_order_known_conversion(
                        goal,
                        &p.premise_proof,
                        SourceOrderKind::LessEqual,
                        false,
                        runtime,
                    ),
                GreaterEqualFactSearchProofByBuiltinRule::FromKnownGreater(p) => self
                    .compile_order_known_conversion(
                        goal,
                        &p.premise_proof,
                        SourceOrderKind::Greater,
                        true,
                        runtime,
                    ),
                _ => Err(LeanCompileError::unsupported("Order/GreaterEqualBuiltin")),
            },
            (
                AtomicFact::LessFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::FromKnownGreater(p),
                ),
            ) => self.compile_order_known_conversion(
                goal,
                &p.premise_proof,
                SourceOrderKind::Greater,
                false,
                runtime,
            ),
            (
                AtomicFact::GreaterFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
                    GreaterFactSearchProofByBuiltinRule::FromKnownLess(p),
                ),
            ) => self.compile_order_known_conversion(
                goal,
                &p.premise_proof,
                SourceOrderKind::Less,
                false,
                runtime,
            ),
            (
                AtomicFact::NotEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                    NotEqualFactSearchProofByBuiltinRule::FromKnownStrictOrder(p),
                ),
            ) => self.compile_not_equal_from_known_strict_order(goal, &p.premise_proof, runtime),
            _ => Err(LeanCompileError::unsupported("Order/BuiltinFamilyOrRule")),
        }
    }

    fn compile_order_reflexivity(
        &self,
        goal: &AtomicFact,
        repeated: &Obj,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict || low.ir() != high.ir() || repeated.ir() != low.ir() {
            return Err(LeanCompileError::new(
                "Order/ReflexivitySubject",
                "Reflexivity must repeat the exact weak-order source object.",
            ));
        }
        Ok(format!(
            "(Litex.leRefl {} {})",
            self.object_term(low)?,
            self.real_member(low)?
        ))
    }

    fn compile_order_known_premise(
        &mut self,
        premise: &AtomicExceptEqualityFactKnownProof,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        source_order_parts(&premise.fact)?;
        let proof = match premise.searched_proof.as_ref() {
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
                self.compile_known_atomic(p, &premise.fact, runtime)?
            }
            _ => return Err(LeanCompileError::unsupported("Order/KnownPremiseRoute")),
        };
        Ok(FactTerm {
            fact: Fact::AtomicFact(premise.fact.clone()),
            proposition: self.compile_order_proposition(&premise.fact)?,
            proof,
        })
    }

    fn compile_order_known_conversion(
        &mut self,
        goal: &AtomicFact,
        premise: &AtomicExceptEqualityFactKnownProof,
        expected_kind: SourceOrderKind,
        weaken: bool,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (kind, _, _) = source_order_parts(&premise.fact)?;
        let (low, high, strict) = source_order_oriented(goal)?;
        let (known_low, known_high, known_strict) = source_order_oriented(&premise.fact)?;
        if kind != expected_kind
            || low.ir() != known_low.ir()
            || high.ir() != known_high.ir()
            || if weaken {
                strict || !known_strict
            } else {
                strict != known_strict
            }
        {
            return Err(LeanCompileError::new(
                "Order/KnownPremiseSubject",
                "The exact recorded converse or strict premise does not justify this source order.",
            ));
        }
        let proved = self.compile_order_known_premise(premise, runtime)?;
        if weaken {
            Ok(format!(
                "(Litex.ltToLe {} {} {})",
                self.object_term(low)?,
                self.object_term(high)?,
                proved.proof
            ))
        } else {
            Ok(proved.proof)
        }
    }

    fn compile_even_power_nonnegative(
        &mut self,
        goal: &AtomicFact,
        base_proof: &VerifyFactResult,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (zero, value, strict) = source_order_oriented(goal)?;
        if strict || !is_zero(zero) {
            return Err(LeanCompileError::new(
                "Order/EvenPowerSubject",
                "The selected certificate must prove the weak lower bound zero.",
            ));
        }
        let base = match value {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) if p.left.ir() == p.right.ir() => {
                p.left.as_ref()
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => p.base.as_ref(),
            _ => return Err(LeanCompileError::unsupported("Order/EvenPowerConstructor")),
        };
        let proved = self.compile_verify(base_proof, runtime)?;
        if membership_subject(&proved.fact, base)? != StandardSet::R {
            return Err(LeanCompileError::new(
                "Order/EvenPowerBase",
                "The recorded child must prove this exact base belongs to R.",
            ));
        }
        match value {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(_)) => Ok(format!(
                "(Litex.mulSelfNonnegative {} {})",
                self.object_term(base)?,
                proved.proof
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => {
                if !matches!(p.exponent.as_ref(), Obj::Literal(Literal::Number(_))) {
                    return Err(LeanCompileError::unsupported(
                        "Order/EvenPowerLiteralExponent",
                    ));
                }
                let n = closed_integer(&p.exponent)
                    .filter(|n| *n >= 0 && n % 2 == 0)
                    .ok_or_else(|| {
                        LeanCompileError::new(
                            "Order/EvenPowerExponent",
                            "The exact source literal must be an even natural integer.",
                        )
                    })?;
                let exponent = self.numeric_term(&p.exponent)?;
                let he = format!("(Litex.NativeBridge.sameOfDenoteNumber {} (Litex.number (M := M) (({n} : ℕ) : ℂ)) {} (({n} : ℕ) : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (({n} : ℕ) : ℂ)) (by norm_num))",
                    self.object_term(&p.exponent)?, exponent.value, exponent.denotation);
                Ok(format!(
                    "(Litex.powStructuralNonnegativeOfEven {} {} ({n} : ℕ) {he} (by norm_num))",
                    self.object_term(value)?,
                    proved.proof
                ))
            }
            _ => unreachable!("the supported constructor was checked before replaying its child"),
        }
    }

    fn compile_weak_add_congruence(
        &mut self,
        goal: &AtomicFact,
        premise: &VerifyFactResult,
        common_left: bool,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict {
            return Err(LeanCompileError::unsupported("Order/StrictAddCongruence"));
        }
        let (lhs, rhs) = match (low, high) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(lhs)),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(rhs)),
            ) => (lhs, rhs),
            _ => {
                return Err(LeanCompileError::new(
                    "Order/AddConstructor",
                    "The selected add congruence requires two exact owned Add constructions.",
                ))
            }
        };
        let (a, b, c, d) = if common_left {
            (
                lhs.right.as_ref(),
                rhs.right.as_ref(),
                lhs.left.as_ref(),
                rhs.left.as_ref(),
            )
        } else {
            (
                lhs.left.as_ref(),
                rhs.left.as_ref(),
                lhs.right.as_ref(),
                rhs.right.as_ref(),
            )
        };
        if c.ir() != d.ir() {
            return Err(LeanCompileError::new(
                "Order/AddCommonArgument",
                "The exact common source addend differs between the two sums.",
            ));
        }
        let proved = self.compile_verify(premise, runtime)?;
        match &proved.fact {
            Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir() == a.ir() && f.right.ir() == b.ir() =>
                {},
            _ => return Err(LeanCompileError::new("Order/AddPremise", "The recorded child must prove the exact ordered weak comparison between the noncommon addends.")),
        };
        // Parent predicate WD and its recursively replayed real membership
        // children provide this common addend's real classification. Each
        // complex certificate comes from an already certified operand object.
        let function = if common_left {
            "leAddLeft"
        } else {
            "leAddRight"
        };
        Ok(format!(
            "(Litex.{function} {} {} {} {} {} {} {} {})",
            self.object_term(a)?,
            self.object_term(b)?,
            self.object_term(c)?,
            self.numeric_term(a)?.member,
            self.numeric_term(b)?.member,
            self.numeric_term(c)?.member,
            self.real_member(c)?,
            proved.proof
        ))
    }

    fn order_real_members_from_known(
        &self,
        fact: &AtomicFact,
        order_proof: &str,
    ) -> Result<(String, String), LeanCompileError> {
        // Use only at the actual predicate-domain ByKnownFact stage after its
        // citation and argument transport have been replayed successfully.
        let (kind, _, _) = source_order_parts(fact)?;
        let (low, high, _) = source_order_oriented(fact)?;
        let low_member = format!("(by obtain ⟨_litex_real, _, _litex_value, _, _⟩ := {order_proof}; exact (M.real_members (Litex.denote {})).mpr ⟨_litex_real, _litex_value⟩)", self.object_term(low)?);
        let high_member = format!("(by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := {order_proof}; exact (M.real_members (Litex.denote {})).mpr ⟨_litex_real, _litex_value⟩)", self.object_term(high)?);
        match kind {
            SourceOrderKind::Less | SourceOrderKind::LessEqual => Ok((low_member, high_member)),
            SourceOrderKind::Greater | SourceOrderKind::GreaterEqual => {
                Ok((high_member, low_member))
            }
        }
    }

    fn compile_registered_order(
        &self,
        id: FactId,
        runtime: &Runtime,
    ) -> Result<FactTerm, LeanCompileError> {
        let fact = self.resolve_fact(id, runtime)?;
        let atomic = match &fact {
            Fact::AtomicFact(fact) if fact.fact_id() == id => fact,
            _ => {
                return Err(LeanCompileError::new(
                    "Order/CitationFamily",
                    "The recorded order citation has another fact family or identity.",
                ))
            }
        };
        source_order_parts(atomic)?;
        let registered = self.fact_term(id)?;
        if registered.fact != fact {
            return Err(LeanCompileError::new(
                "Order/CitationProducer",
                "The order citation differs from its active compiled producer.",
            ));
        }
        Ok(registered.clone())
    }

    fn compile_weak_order_transitivity(
        &mut self,
        goal: &AtomicFact,
        first_id: FactId,
        second_id: FactId,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (left, right, strict) = source_order_oriented(goal)?;
        if strict {
            return Err(LeanCompileError::unsupported("Order/StrictTransitivity"));
        }
        let first = self.compile_registered_order(first_id, runtime)?;
        let second = self.compile_registered_order(second_id, runtime)?;
        let first_atomic = match &first.fact {
            Fact::AtomicFact(f) => f,
            _ => unreachable!(),
        };
        let second_atomic = match &second.fact {
            Fact::AtomicFact(f) => f,
            _ => unreachable!(),
        };
        let (a, b, first_strict) = source_order_oriented(first_atomic)?;
        let (b2, c, second_strict) = source_order_oriented(second_atomic)?;
        if a.ir() != left.ir() || b.ir() != b2.ir() || c.ir() != right.ir() {
            return Err(LeanCompileError::new("Order/TransitivitySubject", "The exact two recorded citations do not form this ordered left-middle-right chain."));
        }
        let first_proof = if first_strict {
            format!(
                "(Litex.ltToLe {} {} {})",
                self.object_term(a)?,
                self.object_term(b)?,
                first.proof
            )
        } else {
            first.proof
        };
        let second_proof = if second_strict {
            format!(
                "(Litex.ltToLe {} {} {})",
                self.object_term(b2)?,
                self.object_term(c)?,
                second.proof
            )
        } else {
            second.proof
        };
        Ok(format!(
            "(Litex.leTrans {} {} {} {first_proof} {second_proof})",
            self.object_term(a)?,
            self.object_term(b)?,
            self.object_term(c)?
        ))
    }

    fn compile_order_dual(
        &mut self,
        goal: &AtomicFact,
        proof: &AtomicExceptEqualityFactSearchProofByBuiltinOrderDual,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (kind, left, right) = source_order_parts(goal)?;
        let alternate = match &proof.alternate_fact {
            Fact::AtomicFact(f) => f,
            _ => {
                return Err(LeanCompileError::new(
                    "Order/DualFamily",
                    "The recorded alternate is not an atomic order fact.",
                ))
            }
        };
        let (alternate_kind, alternate_left, alternate_right) = source_order_parts(alternate)?;
        let expected = match kind {
            SourceOrderKind::Less => SourceOrderKind::Greater,
            SourceOrderKind::Greater => SourceOrderKind::Less,
            SourceOrderKind::LessEqual => SourceOrderKind::GreaterEqual,
            SourceOrderKind::GreaterEqual => SourceOrderKind::LessEqual,
        };
        if alternate_kind != expected
            || left.ir() != alternate_right.ir()
            || right.ir() != alternate_left.ir()
        {
            return Err(LeanCompileError::new(
                "Order/DualSubject",
                "The recorded alternate changes the exact transposed family or source endpoints.",
            ));
        }
        let child = self.compile_verify(&proof.proof_of_alternate_fact, runtime)?;
        if child.fact != proof.alternate_fact {
            return Err(LeanCompileError::new(
                "Order/DualChild",
                "The successful child does not prove the exact recorded alternate fact.",
            ));
        }
        Ok(child.proof)
    }

    fn compile_not_equal_from_known_strict_order(
        &mut self,
        goal: &AtomicFact,
        premise: &AtomicExceptEqualityFactKnownProof,
        runtime: &Runtime,
    ) -> Result<String, LeanCompileError> {
        let (left, right) = match goal {
            AtomicFact::NotEqualFact(f) => (&f.left, &f.right),
            _ => {
                return Err(LeanCompileError::new(
                    "Order/NotEqualFamily",
                    "Strict-order inequality evidence has another target predicate.",
                ))
            }
        };
        let (low, high, strict) = source_order_oriented(&premise.fact)?;
        if !strict
            || !((low.ir() == left.ir() && high.ir() == right.ir())
                || (low.ir() == right.ir() && high.ir() == left.ir()))
        {
            return Err(LeanCompileError::new(
                "Order/NotEqualPremise",
                "The recorded strict-order premise must have exactly these two source endpoints.",
            ));
        }
        let child = self.compile_order_known_premise(premise, runtime)?;
        let inequality = format!(
            "(Litex.ltNotSame {} {} {})",
            self.object_term(low)?,
            self.object_term(high)?,
            child.proof
        );
        if low.ir() == left.ir() && high.ir() == right.ir() {
            Ok(inequality)
        } else {
            Ok(format!(
                "(fun _litex_equal => {inequality} _litex_equal.symm)"
            ))
        }
    }

    fn compile_order_known_atomic_transport(
        &self,
        cited: &AtomicFact,
        goal: &AtomicFact,
        argument_equalities: &[String],
        citation_proof: &str,
    ) -> Result<String, LeanCompileError> {
        let (kind, _, _) = source_order_parts(cited)?;
        let (goal_kind, _, _) = source_order_parts(goal)?;
        if kind != goal_kind || argument_equalities.len() != 2 {
            return Err(LeanCompileError::new(
                "Order/KnownTransportFamily",
                "Recorded order transport changes its source family or ordered argument arity.",
            ));
        }
        let (old_low, old_high, strict) = source_order_oriented(cited)?;
        let (new_low, new_high, _) = source_order_oriented(goal)?;
        let (low_equality, high_equality) = match kind {
            SourceOrderKind::Less | SourceOrderKind::LessEqual => {
                (&argument_equalities[0], &argument_equalities[1])
            }
            SourceOrderKind::Greater | SourceOrderKind::GreaterEqual => {
                (&argument_equalities[1], &argument_equalities[0])
            }
        };
        Ok(format!(
            "(Litex.{} {} {} {} {} {low_equality} {high_equality} {citation_proof})",
            if strict { "ltOfSame" } else { "leOfSame" },
            self.object_term(old_low)?,
            self.object_term(new_low)?,
            self.object_term(old_high)?,
            self.object_term(new_high)?
        ))
    }

    fn atomic_proposition(&self, fact: &AtomicFact) -> Result<String, LeanCompileError> {
        match fact {
            AtomicFact::EqualFact(fact) => Ok(format!(
                "Litex.Same {} {}",
                self.object_term(&fact.left)?,
                self.object_term(&fact.right)?
            )),
            AtomicFact::NotEqualFact(fact) => Ok(format!(
                "¬ Litex.Same {} {}",
                self.object_term(&fact.left)?,
                self.object_term(&fact.right)?
            )),
            AtomicFact::InFact(fact) => Ok(format!(
                "Litex.In {} {}",
                self.object_term(&fact.element)?,
                self.object_term(&fact.set)?
            )),
            AtomicFact::IsSetFact(fact) => {
                Ok(format!("Litex.IsSet {}", self.object_term(&fact.set)?))
            }
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => self.compile_order_proposition(fact),
            AtomicFact::NotLessFact(f) => Ok(format!(
                "¬ Litex.Lt {} {}",
                self.object_term(&f.left)?,
                self.object_term(&f.right)?
            )),
            AtomicFact::NotGreaterFact(f) => Ok(format!(
                "¬ Litex.Lt {} {}",
                self.object_term(&f.right)?,
                self.object_term(&f.left)?
            )),
            AtomicFact::NotLessEqualFact(f) => Ok(format!(
                "¬ Litex.Le {} {}",
                self.object_term(&f.left)?,
                self.object_term(&f.right)?
            )),
            AtomicFact::NotGreaterEqualFact(f) => Ok(format!(
                "¬ Litex.Le {} {}",
                self.object_term(&f.right)?,
                self.object_term(&f.left)?
            )),
            AtomicFact::IsNonemptySetFact(f) => {
                Ok(format!("Litex.IsNonempty {}", self.object_term(&f.set)?))
            }
            AtomicFact::NormalAtomicFact(_)
            | AtomicFact::IsFiniteSetFact(_)
            | AtomicFact::SubsetFact(_)
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

    fn validate_store(
        &self,
        store: &StoreFactAndInferResult,
        expected: &Fact,
    ) -> Result<(), LeanCompileError> {
        let actual = match &store.store {
            StoreFactResult::AtomicFact(stored) => Fact::AtomicFact(stored.fact.clone()),
            StoreFactResult::ForallFact(stored) => Fact::ForallFact(stored.fact.clone()),
            StoreFactResult::AndFact(_)
            | StoreFactResult::ChainFact(_)
            | StoreFactResult::OrFact(_)
            | StoreFactResult::ExistShapedFact(_)
            | StoreFactResult::NotForallFact(_)
            | StoreFactResult::ForallFactWithIff(_) => {
                return Err(LeanCompileError::unsupported("Store/Compound"))
            }
        };
        if &actual != expected || store.primary_fact_id() != expected.fact_id() {
            return Err(LeanCompileError::new(
                "Store/Subject",
                "The stored target differs from the replayed verification.",
            ));
        }
        // Additional inferred facts are not promoted to assumptions. A future
        // citation of an uncompiled inference fails the producer-registry lookup.
        Ok(())
    }

    fn remember_complex_member(
        &mut self,
        object: &Obj,
        member: &str,
    ) -> Result<(), LeanCompileError> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(entry) = scope.objects.get_mut(&object.ir()) {
                if entry.numeric.is_none() {
                    entry.numeric = Some(NumericTerm {
                        closed: None,
                        value: format!("(Litex.NativeBridge.asComplex {} {member})", entry.term),
                        denotation: format!(
                            "(Litex.NativeBridge.asComplex_spec {} {member})",
                            entry.term
                        ),
                        member: member.to_string(),
                    });
                }
                return Ok(());
            }
        }
        Err(LeanCompileError::new(
            "Arithmetic/Producer",
            "A membership proof has no previously certified object.",
        ))
    }

    fn numeric_term(&self, object: &Obj) -> Result<NumericTerm, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.objects.get(&object.ir()) {
                return entry.numeric.clone().ok_or_else(|| LeanCompileError::new("Arithmetic/NumericEvidence", "No recorded numeric construction or C-membership proof supplies this denotation."));
            }
        }
        Err(LeanCompileError::new(
            "Arithmetic/Producer",
            "No replayed object supplies this numeric denotation.",
        ))
    }

    fn remember_fact(&mut self, fact: FactTerm) {
        self.scopes
            .last_mut()
            .expect("compiler scope")
            .facts
            .insert(fact.fact.fact_id(), fact);
    }

    fn object_term(&self, object: &Obj) -> Result<String, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.objects.get(&object.ir()) {
                if entry.object.ir() == object.ir() {
                    return Ok(entry.term.clone());
                }
            }
        }
        Err(LeanCompileError::new(
            "WD/Producer",
            "No earlier replayed constructor or certified parameter supplies this object.",
        ))
    }

    fn identifier_term(&self, id: IdentifierId) -> Result<String, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.identifiers.get(&id) {
                return Ok(entry.term.clone());
            }
        }
        Err(LeanCompileError::new(
            "Identifier/Producer",
            "The identifier was not introduced in an active compiled scope.",
        ))
    }

    fn fact_term(&self, id: FactId) -> Result<&FactTerm, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.facts.get(&id) {
                return Ok(entry);
            }
        }
        Err(LeanCompileError::new(
            "FactId/Producer",
            &format!(
                "FactId {} has no compiled proof or active source assumption.",
                id.value()
            ),
        ))
    }

    fn resolve_fact(&self, id: FactId, runtime: &Runtime) -> Result<Fact, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(env) = &scope.env {
                if let Some(fact) = env.facts.facts_by_id.get(&id) {
                    return Ok(fact.clone());
                }
            }
        }
        runtime.fact_by_id_in_stack(id).cloned().ok_or_else(|| {
            LeanCompileError::new(
                "FactId/Resolution",
                "The cited fact is absent from the live scope context.",
            )
        })
    }

    fn resolve_wd(
        &self,
        id: WellDefinednessId,
        runtime: &Runtime,
    ) -> Result<Obj, LeanCompileError> {
        for scope in self.scopes.iter().rev() {
            if let Some(env) = &scope.env {
                if let Some(object) = env.well_defined_objects.wd_id_to_object.get(&id) {
                    return Ok(object.clone());
                }
            }
        }
        for env in runtime.execution_environments_stack.iter().rev() {
            if let Some(object) = env.well_defined_objects.wd_id_to_object.get(&id) {
                return Ok(object.clone());
            }
        }
        Err(LeanCompileError::new(
            "WdId/Resolution",
            "The cited WD record is absent from the live scope context.",
        ))
    }
}

#[derive(Clone, Copy)]
enum BinaryArithmetic {
    Add,
    Sub,
    Mul,
    Div,
}

fn ensure_nonzero_subject(fact: &Fact, object: &Obj) -> Result<(), LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotEqualFact(x)) if x.left.ir() == object.ir() && is_zero(&x.right) => Ok(()),
        _ => Err(LeanCompileError::new("Arithmetic/NonzeroSubject", "The requirement must be this exact object's inequality with zero, in source orientation.")),
    }
}

fn membership_subject(fact: &Fact, object: &Obj) -> Result<StandardSet, LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(x)) if x.element.ir() == object.ir() => match &x.set {
            Obj::StandardSet(set) => Ok(set.clone()),
            _ => Err(LeanCompileError::unsupported(
                "Arithmetic/NonstandardDomain",
            )),
        },
        _ => Err(LeanCompileError::new(
            "Arithmetic/MembershipSubject",
            "Membership evidence describes another operand.",
        )),
    }
}

fn closed_integer(object: &Obj) -> Option<i128> {
    EvalRational::from_obj(object)?.to_i128_if_integer()
}

fn validate_arithmetic_expression(object: &Obj) -> Result<(), LeanCompileError> {
    match object {
        Obj::Identifier(IdentifierObj::Plain { .. }) => Ok(()),
        Obj::Literal(Literal::Number(n)) => number_literal(n, "ℂ").map(|_| ()),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => {
            validate_arithmetic_expression(&x.left)?;
            validate_arithmetic_expression(&x.right)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => {
            validate_arithmetic_expression(&x.arg)
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => {
            validate_arithmetic_expression(&x.base)?;
            validate_arithmetic_expression(&x.exponent)?;
            closed_integer(&x.exponent)
                .ok_or_else(|| LeanCompileError::unsupported("Rational/NonClosedIntegerPower"))?;
            Ok(())
        }
        _ => Err(LeanCompileError::unsupported("Rational/ExpressionDomain")),
    }
}

fn normalization_nonzero_subjects(left: &Obj, right: &Obj) -> Result<Vec<Obj>, LeanCompileError> {
    fn collect(object: &Obj, subjects: &mut Vec<Obj>) -> Result<(), LeanCompileError> {
        match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => {
                collect(&x.left, subjects)?;
                collect(&x.right, subjects)?;
                if !subjects.iter().any(|o| o.ir() == x.right.ir()) {
                    subjects.push(x.right.as_ref().clone());
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => collect(&x.arg, subjects)?,
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => {
                collect(&x.base, subjects)?;
                collect(&x.exponent, subjects)?;
                let value = evaluate_obj_to_normalized_decimal_number(&x.exponent)
                    .and_then(|n| n.normalized_value.parse::<i128>().ok());
                if closed_integer(&x.exponent).is_some_and(|z| z < 0) && value.is_none() {
                    return Err(LeanCompileError::unsupported(
                        "Rational/NegativePowerGuardProfile",
                    ));
                }
                if value.is_some_and(|z| z < 0) && !subjects.iter().any(|o| o.ir() == x.base.ir()) {
                    subjects.push(x.base.as_ref().clone());
                }
            }
            _ => {}
        }
        Ok(())
    }
    fn factors(object: &Obj, result: &mut Vec<Obj>) {
        if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)) = object {
            factors(&x.left, result);
            factors(&x.right, result);
        } else if !result.iter().any(|o| o.ir() == object.ir()) {
            result.push(object.clone());
        }
    }
    let mut subjects = Vec::new();
    collect(left, &mut subjects)?;
    collect(right, &mut subjects)?;
    let mut result = Vec::new();
    for subject in subjects {
        factors(&subject, &mut result);
    }
    Ok(result)
}

fn exact_rational_literal(value: &EvalRational, ty: &str) -> Result<String, LeanCompileError> {
    match value.to_obj() {
        Obj::Literal(Literal::Number(n)) => number_literal(&n, ty),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(x)) => match (*x.left, *x.right) {
            (Obj::Literal(Literal::Number(a)), Obj::Literal(Literal::Number(b))) => Ok(format!(
                "({} / {})",
                number_literal(&a, ty)?,
                number_literal(&b, ty)?
            )),
            _ => Err(LeanCompileError::new(
                "Number/ExactRational",
                "The exact scalar has an unexpected canonical shape.",
            )),
        },
        _ => Err(LeanCompileError::new(
            "Number/ExactRational",
            "The exact scalar has an unexpected canonical shape.",
        )),
    }
}

fn scalar_decimal(value: &str) -> Result<EvalRational, LeanCompileError> {
    let number = Number::new(value.to_string());
    number_literal(&number, "ℂ")?;
    EvalRational::from_obj(&Obj::Literal(Literal::Number(number)))
        .ok_or_else(|| LeanCompileError::unsupported("Number/ExactEvaluationBound"))
}

fn number_literal(number: &Number, ty: &str) -> Result<String, LeanCompileError> {
    let value = &number.normalized_value;
    let unsigned = value.strip_prefix('-').unwrap_or(value);
    let mut parts = unsigned.split('.');
    let whole = parts.next().unwrap_or("");
    let fractional = parts.next();
    if whole.is_empty()
        || !whole.bytes().all(|b| b.is_ascii_digit())
        || fractional.is_some_and(|s| s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()))
        || parts.next().is_some()
    {
        return Err(LeanCompileError::unsupported("Number/FiniteDecimalLiteral"));
    }
    Ok(format!("({value} : {ty})"))
}

fn ensure_object(object: &Obj, proof: &ObjWellDefinedProof) -> Result<(), LeanCompileError> {
    if object.ir() != proof.obj().ir() {
        return Err(LeanCompileError::new(
            "WD/Subject",
            "Object WD describes a different subject.",
        ));
    }
    Ok(())
}

fn ensure_complex_member(fact: &Fact, object: &Obj) -> Result<(), LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(fact))
            if fact.element.ir() == object.ir() && fact.set == Obj::StandardSet(StandardSet::C) =>
        {
            Ok(())
        }
        _ => Err(LeanCompileError::new(
            "WD/ArithmeticDomain",
            "An operand requirement is not membership of this operand in C.",
        )),
    }
}

fn same_atomic_family(left: &AtomicFact, right: &AtomicFact) -> bool {
    std::mem::discriminant(left) == std::mem::discriminant(right)
        && left.prop_name() == right.prop_name()
        && atomic_fact_has_positive_polarity(left) == atomic_fact_has_positive_polarity(right)
        && atomic_fact_args_ref(left).len() == atomic_fact_args_ref(right).len()
}

fn is_zero(object: &Obj) -> bool {
    matches!(object, Obj::Literal(Literal::Number(number)) if number.normalized_value == "0")
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SourceOrderKind {
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
}

fn source_order_parts(
    fact: &AtomicFact,
) -> Result<(SourceOrderKind, &Obj, &Obj), LeanCompileError> {
    match fact {
        AtomicFact::LessFact(f) => Ok((SourceOrderKind::Less, &f.left, &f.right)),
        AtomicFact::GreaterFact(f) => Ok((SourceOrderKind::Greater, &f.left, &f.right)),
        AtomicFact::LessEqualFact(f) => Ok((SourceOrderKind::LessEqual, &f.left, &f.right)),
        AtomicFact::GreaterEqualFact(f) => Ok((SourceOrderKind::GreaterEqual, &f.left, &f.right)),
        _ => Err(LeanCompileError::unsupported("Order/PredicateFamily")),
    }
}

fn source_order_oriented(fact: &AtomicFact) -> Result<(&Obj, &Obj, bool), LeanCompileError> {
    let (kind, left, right) = source_order_parts(fact)?;
    match kind {
        SourceOrderKind::Less => Ok((left, right, true)),
        SourceOrderKind::Greater => Ok((right, left, true)),
        SourceOrderKind::LessEqual => Ok((left, right, false)),
        SourceOrderKind::GreaterEqual => Ok((right, left, false)),
    }
}

fn arithmetic_constructor_pairs<'a>(
    left: &'a Obj,
    right: &'a Obj,
) -> Option<(&'static str, Vec<(&'a Obj, &'a Obj)>)> {
    use ArithmeticOperator::*;
    match (left, right) {
        (Obj::ArithmeticOperator(Add(a)), Obj::ArithmeticOperator(Add(b))) => {
            Some(("addValue", vec![(&a.left, &b.left), (&a.right, &b.right)]))
        }
        (Obj::ArithmeticOperator(Sub(a)), Obj::ArithmeticOperator(Sub(b))) => {
            Some(("subValue", vec![(&a.left, &b.left), (&a.right, &b.right)]))
        }
        (Obj::ArithmeticOperator(Mul(a)), Obj::ArithmeticOperator(Mul(b))) => {
            Some(("mulValue", vec![(&a.left, &b.left), (&a.right, &b.right)]))
        }
        (Obj::ArithmeticOperator(Div(a)), Obj::ArithmeticOperator(Div(b))) => {
            Some(("divValue", vec![(&a.left, &b.left), (&a.right, &b.right)]))
        }
        (Obj::ArithmeticOperator(Pow(a)), Obj::ArithmeticOperator(Pow(b))) => Some((
            "powValue",
            vec![(&a.base, &b.base), (&a.exponent, &b.exponent)],
        )),
        (Obj::ArithmeticOperator(Neg(a)), Obj::ArithmeticOperator(Neg(b))) => {
            Some(("negValue", vec![(&a.arg, &b.arg)]))
        }
        _ => None,
    }
}

fn is_exact_zero(object: &Obj) -> bool {
    matches!(object, Obj::Literal(Literal::Number(number)) if number.normalized_value == "0")
}

fn standard_value_constructor(set: &StandardSet) -> Result<&'static str, LeanCompileError> {
    Ok(match set {
        StandardSet::N => "natural",
        StandardSet::Z => "integer",
        StandardSet::Q => "rational",
        StandardSet::R => "real",
        StandardSet::C => "complex",
        _ => return Err(LeanCompileError::unsupported("Standard/NumericCarrier")),
    })
}

fn standard_term(set: &StandardSet) -> Result<String, LeanCompileError> {
    let name = match set {
        StandardSet::N => "N",
        StandardSet::Z => "Z",
        StandardSet::Q => "Q",
        StandardSet::R => "R",
        StandardSet::C => "C",
        StandardSet::NPos
        | StandardSet::QPos
        | StandardSet::RPos
        | StandardSet::QNeg
        | StandardSet::ZNeg
        | StandardSet::RNeg
        | StandardSet::QStar
        | StandardSet::ZStar
        | StandardSet::RStar
        | StandardSet::CStar => {
            return Err(LeanCompileError::unsupported("StandardSet/SignedOrNonzero"))
        }
    };
    Ok(format!("(Litex.{name} (M := M))"))
}

fn unsupported_wd_definition(proof: &ObjWellDefinedProofByDef) -> LeanCompileError {
    match proof {
        ObjWellDefinedProofByDef::Identifier(_) => {
            LeanCompileError::unsupported("WD/IdentifierShape")
        }
        ObjWellDefinedProofByDef::Literal(_) => LeanCompileError::unsupported("WD/Literal"),
        ObjWellDefinedProofByDef::StandardSet(_) => LeanCompileError::new(
            "WD/StandardSet",
            "Definition evidence has another object family.",
        ),
        ObjWellDefinedProofByDef::ArithmeticOperator(_) => {
            LeanCompileError::unsupported("WD/ArithmeticOperator")
        }
        ObjWellDefinedProofByDef::FnObj(_) => LeanCompileError::unsupported("WD/FnObj"),
        ObjWellDefinedProofByDef::IntegerOperator(_) => {
            LeanCompileError::unsupported("WD/IntegerOperator")
        }
        ObjWellDefinedProofByDef::TrigOperator(_) => {
            LeanCompileError::unsupported("WD/TrigOperator")
        }
        ObjWellDefinedProofByDef::ExpLogOperator(_) => {
            LeanCompileError::unsupported("WD/ExpLogOperator")
        }
        ObjWellDefinedProofByDef::ComplexOperator(_) => {
            LeanCompileError::unsupported("WD/ComplexOperator")
        }
        ObjWellDefinedProofByDef::SetOperator(_) => LeanCompileError::unsupported("WD/SetOperator"),
        ObjWellDefinedProofByDef::SetFormer(_) => LeanCompileError::unsupported("WD/SetFormer"),
        ObjWellDefinedProofByDef::ProductShape(_) => {
            LeanCompileError::unsupported("WD/ProductShape")
        }
        ObjWellDefinedProofByDef::FunctionSpace(_) => {
            LeanCompileError::unsupported("WD/FunctionSpace")
        }
        ObjWellDefinedProofByDef::IteratedOperator(_) => {
            LeanCompileError::unsupported("WD/IteratedOperator")
        }
        ObjWellDefinedProofByDef::FiniteSetStat(_) => {
            LeanCompileError::unsupported("WD/FiniteSetStat")
        }
        ObjWellDefinedProofByDef::Structish(_) => LeanCompileError::unsupported("WD/Structish"),
        ObjWellDefinedProofByDef::InstantiatedTemplateObj(_) => {
            LeanCompileError::unsupported("WD/InstantiatedTemplateObj")
        }
    }
}

fn unsupported_atomic_builtin(
    proof: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
) -> LeanCompileError {
    match proof {
        AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact(_) => LeanCompileError::new(
            "Builtin/IsSet",
            "Sethood certificate does not match its subject.",
        ),
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NormalAtomicFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::CoprimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::DvdFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::InjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::SurjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::BijectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::IsChoiceFunctionForFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotNormalAtomicFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSubsetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSupersetFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotPrimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotCoprimeFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotDvdFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSurjectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotBijectiveFact(_)
        | AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsChoiceFunctionForFact(_) => {
            LeanCompileError::unsupported("Atomic/BuiltinRule")
        }
    }
}

fn success_object_wd<'a>(
    result: &'a VerifyObjWellDefinedResult,
    expected: &Obj,
) -> Result<&'a ObjWellDefinedProof, LeanCompileError> {
    match result {
        VerifyObjWellDefinedResult::Success(wd) => {
            ensure_object(expected, wd)?;
            Ok(wd)
        }
        VerifyObjWellDefinedResult::Failed { .. } => Err(LeanCompileError::new(
            "Declaration/WD",
            "A successful declaration has failed value WD.",
        )),
    }
}

fn alias_equality_subject<'a>(
    fact: &'a Fact,
    parameter: &BoundName,
    value: &Obj,
) -> Result<&'a Obj, LeanCompileError> {
    match fact {
        Fact::AtomicFact(AtomicFact::EqualFact(equal)) if equal.right.ir() == value.ir() => {
            match &equal.left {
                Obj::Identifier(IdentifierObj::Plain { id, name })
                    if *id == parameter.id && name == &parameter.name =>
                {
                    Ok(&equal.left)
                }
                _ => Err(LeanCompileError::new(
                    "Declaration/StoreSubject",
                    "The stored equality names another declaration.",
                )),
            }
        }
        _ => Err(LeanCompileError::new(
            "Declaration/StoreSubject",
            "The stored equality has another value or orientation.",
        )),
    }
}

fn verified_subject(result: &VerifyFactResult) -> Option<Fact> {
    match result {
        VerifyFactResult::Equality(result) => match result.as_ref() {
            VerifyEqualityResult::Success(proof) => {
                Some(Fact::AtomicFact(AtomicFact::EqualFact(proof.fact.clone())))
            }
            _ => None,
        },
        VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => {
                Some(Fact::AtomicFact(proof.fact.clone()))
            }
            _ => None,
        },
        VerifyFactResult::ForallFact(result) => match result.as_ref() {
            VerifyForallFactResult::Success(proof) => Some(Fact::ForallFact(proof.fact().clone())),
            _ => None,
        },
        _ => None,
    }
}

fn validate_statement_capture(
    source: &Stmt,
    result: &ExecStmtResult,
) -> Result<(), LeanCompileError> {
    let matches = match (source, result) {
        (Stmt::Fact(fact), ExecStmtResult::Fact(ExecFactStmtResult::Success(proof))) => {
            verified_subject(&proof.verify_result).as_ref() == Some(fact)
        }
        (
            Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::LetObjStmt(stmt))),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)),
            )),
        ) => stmt == &proof.statement,
        (
            Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::HaveObjEqualStmt(stmt))),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
                ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
            )),
        ) => stmt == &proof.statement,
        (
            Stmt::By(ByStmt::ByThmStmt(stmt)),
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))),
        ) => {
            stmt.call == proof.call
                && verified_subject(&proof.selected_proof).as_ref()
                    == Some(&Fact::AtomicFact(stmt.selected_fact.clone()))
        }
        _ => return Err(LeanCompileError::unsupported("Theorem/ProofStepCapture")),
    };
    if matches {
        Ok(())
    } else {
        Err(LeanCompileError::new(
            "Theorem/ProofStepCapture",
            "The executed statement differs from this source proof step.",
        ))
    }
}

// Validate substitution against captured objects only. This neither creates
// fresh source IDs nor invokes Runtime instantiation or verification.
fn instantiated_object_matches(
    expected: &Obj,
    actual: &Obj,
    substitution: &HashMap<IdentifierId, Obj>,
) -> bool {
    if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = expected {
        if let Some(argument) = substitution.get(id) {
            return argument.ir() == actual.ir();
        }
    }
    match (expected, actual) {
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Add(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(b)),
        ) => {
            instantiated_object_matches(&a.left, &b.left, substitution)
                && instantiated_object_matches(&a.right, &b.right, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(b)),
        ) => {
            instantiated_object_matches(&a.left, &b.left, substitution)
                && instantiated_object_matches(&a.right, &b.right, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
        ) => {
            instantiated_object_matches(&a.left, &b.left, substitution)
                && instantiated_object_matches(&a.right, &b.right, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Div(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(b)),
        ) => {
            instantiated_object_matches(&a.left, &b.left, substitution)
                && instantiated_object_matches(&a.right, &b.right, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(b)),
        ) => {
            instantiated_object_matches(&a.base, &b.base, substitution)
                && instantiated_object_matches(&a.exponent, &b.exponent, substitution)
        }
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(b)),
        ) => instantiated_object_matches(&a.arg, &b.arg, substitution),
        _ => expected.ir() == actual.ir(),
    }
}

fn instantiated_fact_matches(
    expected: &Fact,
    actual: &Fact,
    substitution: &HashMap<IdentifierId, Obj>,
) -> bool {
    match (expected, actual) {
        (Fact::AtomicFact(expected), Fact::AtomicFact(actual))
            if expected.prop_name() == actual.prop_name()
                && atomic_fact_has_positive_polarity(expected)
                    == atomic_fact_has_positive_polarity(actual) =>
        {
            let left = atomic_fact_args_ref(expected);
            let right = atomic_fact_args_ref(actual);
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(a, b)| instantiated_object_matches(a, b, substitution))
        }
        _ => false,
    }
}

fn conjunction_projection(proof: &str, index: usize, count: usize) -> String {
    let mut proof = proof.to_string();
    for _ in 0..index {
        proof = format!("(And.right {proof})");
    }
    if index + 1 < count {
        proof = format!("(And.left {proof})");
    }
    proof
}

fn validate_namespace(value: &str) -> Result<(), LeanCompileError> {
    let mut bytes = value.bytes();
    let valid_start = bytes
        .next()
        .map(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        .unwrap_or(false);
    let reserved = [
        "_",
        "axiom",
        "by",
        "class",
        "def",
        "do",
        "else",
        "end",
        "example",
        "export",
        "false",
        "forall",
        "from",
        "fun",
        "if",
        "import",
        "in",
        "inductive",
        "instance",
        "let",
        "macro",
        "match",
        "mutual",
        "namespace",
        "noncomputable",
        "opaque",
        "open",
        "partial",
        "private",
        "protected",
        "section",
        "set_option",
        "structure",
        "syntax",
        "then",
        "theorem",
        "true",
        "universe",
        "unsafe",
        "variable",
        "where",
        "with",
    ];
    if !valid_start
        || !bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        || reserved.contains(&value)
    {
        return Err(LeanCompileError::new(
            "artifact_namespace",
            "The artifact namespace must be a simple nonreserved ASCII Lean identifier.",
        ));
    }
    Ok(())
}
