use crate::compile_to_lean::helper::{instantiated_fact_matches, instantiated_object_matches, source_subject};
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{InferExistUniqueFactResult, InferResult};
use std::collections::{HashMap, HashSet};

impl LitexToLeanCompiler {
    /// Canonical pairwise uniqueness. The two candidates are semantic objects;
    /// equality of their denotations is Litex.Same, not equality of host payloads.
    pub(in crate::compile_to_lean) fn unique_signature(
        &self,
        source: &PlainExistFact,
        position: &SourcePosition<'_>,
    ) -> Result<(String, Vec<String>), LeanCompileError> {
        let mut binders = Vec::new();
        let mut arguments = Vec::new();
        let mut copies = Vec::new();
        let mut values = Vec::new();
        for side in ["left", "right"] {
            let mut bindings = HashMap::new();
            let mut denotations = Vec::new();
            for group in &source.typed_parameters.groups {
                for parameter in &group.params {
                    let id = parameter.id.value();
                    let name = format!("_unique_{side}_i{id}");
                    let member = match &group.param_type {
                        ParamType::Obj(carrier) => format!(
                            "M.mem (Litex.denote {name}) {}",
                            self.compile_function_raw_expression_bound(
                                carrier, position, &bindings
                            )?
                        ),
                        ParamType::Set(_) => format!("M.isSet (Litex.denote {name})"),
                        _ => {
                            return Err(LeanCompileError::unsupported("ExistUnique/ParameterKind"))
                        }
                    };
                    binders.push(format!(
                        "({name} : Litex.Obj (M := M) M.Value) (_member_{side}_i{id} : {member})"
                    ));
                    arguments.extend([name.clone(), format!("_member_{side}_i{id}")]);
                    let denote = format!("(Litex.denote {name})");
                    if bindings.insert(parameter.id, denote.clone()).is_some() {
                        return Err(LeanCompileError::unsupported(
                            "ExistUnique/ParameterIdentity",
                        ));
                    }
                    denotations.push(denote);
                }
            }
            copies.push(bindings);
            values.push(denotations);
        }
        if values[0].is_empty() {
            return Err(LeanCompileError::unsupported("ExistUnique/EmptyParameters"));
        }
        for (index, clause) in source.facts.iter().enumerate() {
            let fact = crate::instantiate::quantifier_free_fact_to_fact(clause.clone());
            for (side, bindings) in ["left", "right"].into_iter().zip(&copies) {
                let name = format!("_body_{side}_{index}");
                let predicate = self.compile_function_raw_predicate(&fact, position, bindings)?;
                binders.push(format!("({name} : {predicate})"));
                arguments.push(name);
            }
        }
        let conclusion = format!(
            "{} = {}",
            candidate_value(&values[0]),
            candidate_value(&values[1])
        );
        Ok((format!("∀ {}, {conclusion}", binders.join(" ")), arguments))
    }

    pub(in crate::compile_to_lean) fn compile_unique_witness_check(
        &self,
        source: &PlainExistFact,
        result: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let Fact::ForallFact(fact) = source_subject(result)? else {
            return Err(LeanCompileError::unsupported(
                "ExistUnique/UniquenessFamily",
            ));
        };
        validate_unique_forall(source, &fact, false)?;
        let checked = self.compile_verify(result, position)?;
        let (proposition, arguments) = self.unique_signature(source, position)?;
        Ok((
            proposition,
            format!(
                "(by\n  intro {}\n  exact (show {} from {}) {})",
                arguments.join(" "),
                checked.0,
                checked.1,
                arguments.join(" ")
            ),
        ))
    }

    pub(in crate::compile_to_lean) fn compile_verify_unique_success(
        &self,
        proof: &VerifyExistUniqueFactSuccess,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let ExistShapedFact::ExistUnique(source) = &proof.fact else {
            return Err(LeanCompileError::unsupported("ExistUnique/Family"));
        };
        let existence =
            self.compile_exist_formation(source, &proof.well_defined_proof, position)?;
        let (unique, _) = self.unique_signature(source, position)?;
        if let ExistShapedFactSearchedProof::ByBuiltinRule(
            crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchProofByBuiltinRule::BijectivePreimage(evidence)
        ) = &proof.searched_proof {
            return Ok((format!("({existence}) ∧ ({unique})"), self.compile_bijective_preimage(source, evidence, position)?));
        }
        if let ExistShapedFactSearchedProof::ByKnownForallFact(known) = &proof.searched_proof {
            let evidence = self.compile_exist_known_forall(
                &proof.fact,
                &proof.well_defined_proof,
                known,
                position,
            )?;
            return Ok((format!("({existence}) ∧ ({unique})"), evidence));
        }
        let ExistShapedFactSearchedProof::ByKnownExistShapedFact(known) = &proof.searched_proof
        else {
            return Err(LeanCompileError::unsupported("ExistUnique/ProofRoute"));
        };
        let (cited, reference) = self.cited_fact_reference(known.cite_fact_id, position)?;
        let Fact::ExistUniqueFact(cited) = cited else {
            return Err(LeanCompileError::unsupported("ExistUnique/CitationFamily"));
        };
        if cited.fact_id != known.cite_fact_id || !plain_exist_facts_alpha_equal(cited, source) {
            return Err(LeanCompileError::unsupported("ExistUnique/CitationSubject"));
        }
        Ok((format!("({existence}) ∧ ({unique})"), reference))
    }

    pub(in crate::compile_to_lean) fn compile_unique_inference(
        &self,
        store: &StoreFactAndInferResult,
        source: &PlainExistFact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Some(InferResult::ExistUniqueFact(InferExistUniqueFactResult::UniquenessForall(infer))) =
            &store.infer
        else {
            return Err(LeanCompileError::unsupported(
                "ExistUnique/InferenceCapture",
            ));
        };
        self.compile_unique_forall_store(
            source,
            &infer.derived.store,
            &format!("({}).2", compiled.1),
            true,
            position,
        )
        .map(|s| vec![s])
    }

    /// Inference/obtain only store this logical consequence; they do not run a
    /// second forall WD check. Validate the actual stored shape, then apply the
    /// existing uniqueness proof to denotations of arbitrary host objects.
    pub(in crate::compile_to_lean) fn compile_unique_forall_store(
        &self,
        source: &PlainExistFact,
        store: &StoreFactResult,
        unique_proof: &str,
        componentwise: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let StoreFactResult::ForallFact(stored) = store else {
            return Err(LeanCompileError::unsupported("ExistUnique/StoredFamily"));
        };
        let target = &stored.fact;
        validate_unique_forall(source, target, componentwise)?;
        self.validate_store(store, &Fact::ForallFact(target.clone()))?;
        let mut bindings = HashMap::new();
        let mut binders = Vec::new();
        let mut introductions = Vec::new();
        let mut arguments = Vec::new();
        for group in &target.typed_parameters.groups {
            for parameter in &group.params {
                let id = parameter.id.value();
                let name = format!("_value_i{id}");
                let denotation = format!("(Litex.denote {name})");
                let member = match &group.param_type {
                    ParamType::Obj(carrier) => format!(
                        "M.mem {denotation} {}",
                        self.compile_function_raw_expression_bound(carrier, position, &bindings)?
                    ),
                    ParamType::Set(_) => format!("M.isSet {denotation}"),
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "ExistUnique/StoredParameterKind",
                        ))
                    }
                };
                binders.push(format!("{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({name} : Litex.Obj (M := M) _Host_i{id}) (_membership_i{id} : {member})"));
                introductions.extend([
                    format!("_Host_i{id}"),
                    format!("_rep_i{id}"),
                    name.clone(),
                    format!("_membership_i{id}"),
                ]);
                arguments.extend([
                    format!("(Litex.semanticObject {denotation} (Litex.isSet {name}))"),
                    format!("_membership_i{id}"),
                ]);
                bindings.insert(parameter.id, denotation);
            }
        }
        for domain in &target.dom_facts {
            let name = format!("h_{}", domain.fact_id().value());
            binders.push(format!(
                "({name} : {})",
                self.compile_function_raw_predicate(domain, position, &bindings)?
            ));
            introductions.push(name.clone());
            arguments.push(name);
        }
        let conclusion = self.compile_function_raw_predicate(
            &target.then_facts[0].clone().into(),
            position,
            &bindings,
        )?;
        let (unique, _) = self.unique_signature(source, position)?;
        let n = source.typed_parameters.ordered_param_ids().len();
        let finish = if componentwise && n > 1 {
            let components = (0..n).map(|i| {
                // Explicit successor indices let the two fixed vector laws
                // reduce every coordinate, independently of numeral notation.
                let mut index = format!("(0 : Fin {})", n - i);
                for _ in 0..i { index = format!("(Fin.succ {index})"); }
                format!("(by simpa only [Litex.FiniteFunction.call_tuple, Matrix.cons_val_zero, Matrix.cons_val_succ, Litex.semanticObject_denote] using congrArg (fun t => Litex.FunctionSemantics.callValue (M := M) t (Litex.FiniteFunction.index {index})) _same)")
            }).collect::<Vec<_>>();
            format!("exact ⟨{}⟩", components.join(", "))
        } else {
            "exact _same".to_string()
        };
        let term = format!("(by\n  intro {}\n  have _unique : {unique} := {unique_proof}\n  have _same := _unique {}\n  {finish})", introductions.join(" "), arguments.join(" "));
        self.emit_internal_fact(
            &Fact::ForallFact(target.clone()),
            &(format!("∀ {}, {conclusion}", binders.join(" ")), term),
            position,
        )
    }
}

fn candidate_value(values: &[String]) -> String {
    if values.len() == 1 {
        values[0].clone()
    } else {
        format!(
            "(Litex.FiniteFunction.tupleValue (M := M) ![{}])",
            values.join(", ")
        )
    }
}

fn validate_unique_forall(
    source: &PlainExistFact,
    target: &ForallFact,
    componentwise: bool,
) -> Result<(), LeanCompileError> {
    let groups = source.typed_parameters.groups.len();
    let count = source.typed_parameters.ordered_param_ids().len();
    if count == 0
        || target.typed_parameters.groups.len() != 2 * groups
        || target.dom_facts.len() != 2 * source.facts.len()
        || target.then_facts.len() != 1
    {
        return Err(LeanCompileError::unsupported("ExistUnique/UniquenessShape"));
    }
    let mut used: HashSet<_> = source
        .typed_parameters
        .ordered_param_ids()
        .into_iter()
        .collect();
    let mut copies = Vec::new();
    let mut values = Vec::new();
    for side in 0..2 {
        let mut substitution = HashMap::new();
        let mut objects = Vec::new();
        for (old, new) in source
            .typed_parameters
            .groups
            .iter()
            .zip(&target.typed_parameters.groups[side * groups..(side + 1) * groups])
        {
            let carrier_matches = match (&old.param_type, &new.param_type) {
                (ParamType::Obj(a), ParamType::Obj(b)) => {
                    instantiated_object_matches(a, b, &substitution)
                }
                (ParamType::Set(_), ParamType::Set(_)) => true,
                _ => false,
            };
            if !carrier_matches || old.params.len() != new.params.len() {
                return Err(LeanCompileError::unsupported(
                    "ExistUnique/UniquenessCarrier",
                ));
            }
            for (old, new) in old.params.iter().zip(&new.params) {
                if !used.insert(new.id) {
                    return Err(LeanCompileError::unsupported(
                        "ExistUnique/UniquenessIdentity",
                    ));
                }
                let object = Obj::Identifier(IdentifierObj::from_bound_name(new));
                substitution.insert(old.id, object.clone());
                objects.push(object);
            }
        }
        copies.push(substitution);
        values.push(objects);
    }
    for (i, fact) in source.facts.iter().enumerate() {
        let original = crate::instantiate::quantifier_free_fact_to_fact(fact.clone());
        for side in 0..2 {
            if !instantiated_fact_matches(&original, &target.dom_facts[2 * i + side], &copies[side])
            {
                return Err(LeanCompileError::unsupported(
                    "ExistUnique/UniquenessPremise",
                ));
            }
        }
    }
    let matches_pair = |fact: &AtomicFact, index: usize| matches!(fact, AtomicFact::EqualFact(f) if f.left.ir() == values[0][index].ir() && f.right.ir() == values[1][index].ir());
    let valid = match (&target.then_facts[0], count, componentwise) {
        (ExistOrAndChainAtomicFact::AtomicFact(fact), 1, _) => matches_pair(fact, 0),
        (ExistOrAndChainAtomicFact::AndFact(fact), _, true) => {
            fact.facts.len() == count
                && fact
                    .facts
                    .iter()
                    .enumerate()
                    .all(|(i, f)| matches_pair(f, i))
        }
        (ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(fact)), _, false) => {
            let tuple_matches = |obj: &Obj, side: usize| match obj {
                Obj::ProductShape(ProductShape::Tuple(tuple)) => {
                    tuple.args.len() == count
                        && tuple
                            .args
                            .iter()
                            .zip(&values[side])
                            .all(|(a, b)| a.ir() == b.ir())
                }
                _ => false,
            };
            tuple_matches(&fact.left, 0) && tuple_matches(&fact.right, 1)
        }
        _ => false,
    };
    if !valid {
        return Err(LeanCompileError::unsupported(
            "ExistUnique/UniquenessConclusion",
        ));
    }
    Ok(())
}
