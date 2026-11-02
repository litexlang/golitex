use crate::compile_to_lean::compile_compound_fact::chain_edge;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedForallConclusionArgMatchProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    ForallConclusionArgMatchProof, SearchProofByKnownForallFact, StrictEqualArgProof,
    StrictEqualWithFact,
};
use crate::execute::execute_fact_stmt::verify_or_fact::OrFactSearchProofByKnownOrFact;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

/// Borrowed stages of an actual proved-forall application. This carries no
/// synthetic citation, verification result or mutable compiler state.
pub(super) struct ForallApplicationInput<'a> {
    pub arguments: &'a [Obj],
    pub matches: &'a [ForallConclusionArgMatchProof],
    pub requirements: &'a crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::ProveForallInstantiationRequirementsProof,
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_known_or_fact(
        &self,
        goal: &OrFact,
        proof: &OrFactSearchProofByKnownOrFact,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let resolved = self.resolve_fact(proof.cite_fact_id, position)?;
        let Fact::OrFact(source) = &resolved else {
            return Err(LeanCompileError::unsupported("Or/KnownCitationFamily"));
        };
        let registered = self.cited_fact_reference(proof.cite_fact_id, position)?;
        if source.fact_id != proof.cite_fact_id || *registered.0 != resolved {
            return Err(LeanCompileError::unsupported("Or/KnownCitationIdentity"));
        }
        if source.facts.len() != goal.facts.len()
            || !source
                .facts
                .iter()
                .zip(&goal.facts)
                .all(|(source, goal)| same_or_branch_shape(source, goal))
        {
            return Err(LeanCompileError::unsupported("Or/KnownShape"));
        }
        let source_args = or_fact_args_ref(source);
        let goal_args = or_fact_args_ref(goal);
        if source_args.len() != goal_args.len()
            || proof.why_parameters_of_known_fact_are_equal_to_givens.len() != goal_args.len()
        {
            return Err(LeanCompileError::unsupported("Or/KnownArgumentArity"));
        }
        let mut equalities = Vec::new();
        let mut exact_identity = true;
        for ((source, goal_arg), equality) in source_args
            .iter()
            .zip(&goal_args)
            .zip(&proof.why_parameters_of_known_fact_are_equal_to_givens)
        {
            // Known-Or lookup records only a direct identity comparison or a
            // path through preceding equality stores; it performs no new search.
            if !matches!(
                equality,
                EqualFactSearchedProof::ByTheyAreTheSame(_)
                    | EqualFactSearchedProof::ByEquivalenceClass(
                        EqualFactSearchedProofByEquivalenceClass::KnownPath(_)
                    )
            ) {
                return Err(LeanCompileError::unsupported("Or/KnownArgumentRoute"));
            }
            let obligation = EqualFact {
                fact_id: goal.fact_id,
                left: (*source).clone(),
                right: (*goal_arg).clone(),
                line_file: None,
            };
            // Enumeration stores signed integer literals; source `-n` is a
            // negation object with the same Litex IR. Their Lean denotations
            // agree by the retained numeric constructor, not by reduction.
            if let Obj::Literal(Literal::Number(number)) = source {
                if !matches!(goal_arg, Obj::Literal(Literal::Number(_)))
                    && source.ir() == goal_arg.ir()
                    && matches!(
                        equality,
                        EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
                    )
                {
                    let target = self.compile_numeric_observation(goal_arg, position)?;
                    if target.3.is_none() || target.3 != EvalRational::from_obj(source) {
                        return Err(LeanCompileError::unsupported("Or/KnownLiteralIdentity"));
                    }
                    let literal = number_literal(number, "ℂ")?;
                    equalities.push(format!(
                        "((congrArg M.number (by norm_num : {literal} = {})).trans ({}).symm)",
                        target.0, target.1
                    ));
                    exact_identity = false;
                    continue;
                }
            }
            equalities.push(self.compile_equality_search(&obligation, equality, position)?);
            exact_identity &= source.ir() == goal_arg.ir()
                && matches!(
                    equality,
                    EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
                );
        }
        let goal = Fact::OrFact(goal.clone());
        let term = if exact_identity {
            registered.1
        } else {
            self.compile_known_compound_transport(
                &resolved,
                &goal,
                &equalities,
                &registered.1,
                position,
            )?
        };
        Ok((self.fact_proposition(&goal, position)?, term))
    }

    pub(in crate::compile_to_lean) fn compile_known_application(
        &self,
        goal: &Fact,
        proof: &SearchProofByKnownForallFact,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let resolved = self.resolve_fact(proof.detailed_ref().cite.fact_id, position)?;
        let Fact::ForallFact(source) = &resolved else {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/CitationFamily",
            ));
        };
        let registered = self.cited_fact_reference(proof.detailed_ref().cite.fact_id, position)?;
        if *registered.0 != resolved || source.fact_id != proof.detailed_ref().cite.fact_id {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/CitationIdentity",
            ));
        }
        self.compile_proved_forall_application(
            goal,
            source,
            registered.1,
            &proof.detailed_ref().cite.location,
            ForallApplicationInput {
                arguments: &proof.detailed_ref().forall_parameters_match_what_args,
                matches: &proof.detailed_ref().arg_match_proofs,
                requirements: &proof.detailed_ref().instantiation_requirements,
            },
            SourceOwner::KnownApplication(proof),
            SourceOwner::CalleeInstance(proof),
            position,
        )
    }

    pub(in crate::compile_to_lean) fn compile_proved_forall_application(
        &self,
        goal: &Fact,
        source: &ForallFact,
        reference: String,
        location: &ForallConclusionLocation,
        input: ForallApplicationInput<'_>,
        owner: SourceOwner<'_>,
        formation_owner: SourceOwner<'_>,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let (then_index, component) = match location {
            ForallConclusionLocation::DirectThenFact(p) => (p.then_fact_index, None),
            ForallConclusionLocation::AndFactComponent(p) => {
                (p.then_fact_index, Some(p.component_index))
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "CompoundKnown/ConclusionLocation",
                ))
            }
        };
        let selected: Fact = source
            .then_facts
            .get(then_index)
            .ok_or_else(|| LeanCompileError::unsupported("CompoundKnown/ConclusionLocation"))?
            .clone()
            .into();
        let (selected, projection) = if let Some(index) = component {
            let Fact::AndFact(and) = selected else {
                return Err(LeanCompileError::unsupported(
                    "CompoundKnown/ConclusionLocation",
                ));
            };
            let atomic = and
                .facts
                .get(index)
                .ok_or_else(|| LeanCompileError::unsupported("CompoundKnown/ConclusionLocation"))?;
            (
                Fact::AtomicFact(atomic.clone()),
                Some((index, and.facts.len())),
            )
        } else {
            (selected, None)
        };
        let pattern_args = compound_arguments(&selected)?;
        let goal_args = compound_arguments(goal)?;
        let same_shape = match (&selected, goal) {
            (Fact::AtomicFact(a), Fact::AtomicFact(b)) => same_atomic_family(a, b),
            (Fact::AndFact(a), Fact::AndFact(b)) => {
                a.facts.len() == b.facts.len()
                    && a.facts
                        .iter()
                        .zip(&b.facts)
                        .all(|(a, b)| same_atomic_family(a, b))
            }
            (Fact::ChainFact(a), Fact::ChainFact(b)) => {
                a.prop_names == b.prop_names && a.objs.len() == b.objs.len()
            }
            (Fact::OrFact(a), Fact::OrFact(b)) => {
                a.facts.len() == b.facts.len()
                    && a.facts
                        .iter()
                        .zip(&b.facts)
                        .all(|(a, b)| same_or_branch_shape(a, b))
            }
            _ => false,
        };
        let parameters: Vec<_> = source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|param| (param, &group.param_type)))
            .collect();
        let requirements = input.requirements.detailed_ref();
        if !same_shape
            || pattern_args.is_empty()
            || pattern_args.len() != goal_args.len()
            || input.matches.len() != goal_args.len()
            || input.arguments.len() != parameters.len()
            || requirements.param_type_requirements.len() != parameters.len()
            || requirements.dom_facts.len() != source.dom_facts.len()
            || requirements.proof_of_dom_facts.len() != source.dom_facts.len()
        {
            return Err(LeanCompileError::unsupported("CompoundKnown/OrderedArity"));
        }
        let substitution: HashMap<_, _> = parameters
            .iter()
            .zip(input.arguments)
            .map(|((param, _), arg)| (param.id, arg.clone()))
            .collect();
        if substitution.len() != parameters.len() {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/ParameterIdentity",
            ));
        }
        let current = SourcePosition::new(Some(position), owner, 0);
        let mut requirement_ids = HashSet::new();
        for fact in requirements
            .param_type_requirements
            .iter()
            .map(|item| &item.type_fact)
            .chain(&requirements.dom_facts)
        {
            if !requirement_ids.insert(fact.fact_id())
                || self.resolve_fact(fact.fact_id(), &current)? != *fact
            {
                return Err(LeanCompileError::unsupported(
                    "CompoundKnown/RequirementIdentity",
                ));
            }
        }
        let mut instantiated_args = Vec::new();
        let mut bound = HashSet::new();
        for ((pattern, goal), matched) in pattern_args.iter().zip(&goal_args).zip(input.matches) {
            let (argument, _) = self.compile_forall_argument_match(
                pattern,
                goal,
                matched,
                &substitution,
                &mut bound,
                None,
            )?;
            instantiated_args.push(argument);
        }
        let (definitions, arguments) = self.compile_instantiation_requirements(
            source,
            input.arguments,
            input.matches.len(),
            input.requirements,
            &current,
        )?;
        let head = input.matches.len();
        // Check the original match record before requirements. Its Lean terms
        // are rendered afterward, with only certified constructor formation
        // added to the original match-before truth-citation scope.
        let mut equalities = Vec::new();
        let mut bound = HashSet::new();
        for (index, ((pattern, goal), matched)) in pattern_args
            .iter()
            .zip(&goal_args)
            .zip(input.matches)
            .enumerate()
        {
            let prior = SourcePosition {
                before: index,
                ..current
            };
            let formation = SourcePosition::new(Some(&prior), formation_owner, usize::MAX);
            let (_, equality) = self.compile_forall_argument_match(
                pattern,
                goal,
                matched,
                &substitution,
                &mut bound,
                Some(&formation),
            )?;
            equalities.push(equality);
        }
        let formed = SourcePosition {
            before: head + parameters.len() + requirements.dom_facts.len(),
            ..current
        };
        let complete_formation = SourcePosition::new(Some(&formed), formation_owner, usize::MAX);
        let formed = &complete_formation;
        let application = if arguments.is_empty() {
            reference
        } else {
            format!("({} {})", reference, arguments.join(" "))
        };
        let application = conjunction_projection(&application, then_index, source.then_facts.len());
        let application = match projection {
            Some((index, count)) => conjunction_projection(&application, index, count),
            None => application,
        };
        let instantiated = replace_compound_arguments(&selected, &instantiated_args)?;
        let checked = self.compile_known_compound_transport(
            &instantiated,
            goal,
            &equalities,
            &application,
            formed,
        )?;
        let proposition = self.fact_proposition(goal, &formed)?;
        Ok((
            self.scope_proposition(proposition, &definitions),
            format!(
                "(by\n  {}\n  exact {checked}\n)",
                definitions.join("\n").replace('\n', "\n  ")
            ),
        ))
    }

    fn compile_known_compound_transport(
        &self,
        old: &Fact,
        goal: &Fact,
        equalities: &[String],
        application: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if let (Fact::OrFact(a), Fact::OrFact(b)) = (old, goal) {
            if a.facts.len() != b.facts.len() || a.facts.len() < 2 {
                return Err(LeanCompileError::unsupported("CompoundKnown/OrArity"));
            }
            let mut transported = Vec::new();
            let mut offset = 0;
            for (index, (left, right)) in a.facts.iter().zip(&b.facts).enumerate() {
                let left = crate::ast::fact::and_chain_as_fact(left);
                let right = crate::ast::fact::and_chain_as_fact(right);
                let arity = compound_arguments(&right)?.len();
                let slice = equalities
                    .get(offset..offset + arity)
                    .ok_or_else(|| LeanCompileError::unsupported("CompoundKnown/OrArguments"))?;
                let name = format!("_known_or_{index}");
                transported.push((
                    name.clone(),
                    self.compile_known_compound_transport(&left, &right, slice, &name, position)?,
                ));
                offset += arity;
            }
            if offset != equalities.len() {
                return Err(LeanCompileError::unsupported("CompoundKnown/OrArguments"));
            }
            let (last_name, last) = transported.pop().expect("nonempty Or");
            let mut result = format!("(fun {last_name} => {last})");
            while let Some((name, left)) = transported.pop() {
                result = format!("(fun _known_tail => Or.elim _known_tail (fun {name} => Or.inl {left}) (fun _known_rest => Or.inr ({result} _known_rest)))");
            }
            return Ok(format!("({result} {application})"));
        }
        let old_atomics = compound_atomics(old)?;
        let new_atomics = compound_atomics(goal)?;
        if old_atomics.len() != new_atomics.len()
            || compound_arguments(goal)?.len() != equalities.len()
        {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/TransportArity",
            ));
        }
        let mut pieces = Vec::new();
        let mut offset = 0;
        for (index, (old, new)) in old_atomics.iter().zip(&new_atomics).enumerate() {
            let component = conjunction_projection(&application, index, old_atomics.len());
            let arity = atomic_fact_args_ref(new).len();
            let equalities = if matches!(goal, Fact::ChainFact(_)) {
                &equalities[index..index + 2]
            } else {
                &equalities[offset..offset + arity]
            };
            pieces.push(
                self.compile_compound_atomic_transport(old, new, equalities, &component, position)?,
            );
            offset += arity;
        }
        compound_proof(pieces)
    }

    pub(in crate::compile_to_lean) fn compile_known_application_requirements(
        &self,
        source: &ForallFact,
        proof: &SearchProofByKnownForallFact,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        self.compile_instantiation_requirements(
            source,
            &proof.detailed_ref().forall_parameters_match_what_args,
            proof.detailed_ref().arg_match_proofs.len(),
            &proof.detailed_ref().instantiation_requirements,
            position,
        )
    }

    fn compile_instantiation_requirements(
        &self,
        source: &ForallFact,
        matched_arguments: &[Obj],
        match_count: usize,
        requirements: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::ProveForallInstantiationRequirementsProof,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let parameters: Vec<_> = source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|param| (param, &group.param_type)))
            .collect();
        let requirements = requirements.detailed_ref();
        if parameters.len() != matched_arguments.len()
            || parameters.len() != requirements.param_type_requirements.len()
            || source.dom_facts.len() != requirements.dom_facts.len()
            || source.dom_facts.len() != requirements.proof_of_dom_facts.len()
        {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/RequirementArity",
            ));
        }
        let substitution: HashMap<_, _> = parameters
            .iter()
            .zip(matched_arguments)
            .map(|((param, _), arg)| (param.id, arg.clone()))
            .collect();
        let mut ids = HashSet::new();
        for fact in requirements
            .param_type_requirements
            .iter()
            .map(|item| &item.type_fact)
            .chain(&requirements.dom_facts)
        {
            if !ids.insert(fact.fact_id()) || self.resolve_fact(fact.fact_id(), position)? != *fact
            {
                return Err(LeanCompileError::unsupported(
                    "CompoundKnown/RequirementIdentity",
                ));
            }
        }
        let mut definitions = Vec::new();
        let mut arguments = Vec::new();
        let head = match_count;
        for (index, (((parameter, kind), argument), requirement)) in parameters
            .iter()
            .zip(matched_arguments)
            .zip(&requirements.param_type_requirements)
            .enumerate()
        {
            if requirement.param_id != parameter.id
                || requirement.arg.ir() != argument.ir()
                || source_subject(&requirement.proof)? != requirement.type_fact
            {
                return Err(LeanCompileError::unsupported("CompoundKnown/TypeIdentity"));
            }
            let valid =
                parameter_type_fact_matches(kind, argument, &requirement.type_fact, &substitution);
            if !valid {
                return Err(LeanCompileError::unsupported("CompoundKnown/TypeSubject"));
            }
            let prior = SourcePosition {
                before: head + index,
                ..*position
            };
            let compiled = self.compile_verify(&requirement.proof, &prior)?;
            definitions.push(local_verified_fact(&requirement.type_fact, &compiled));
            // Stored universals may quantify over semantic objects. A generic
            // universal accepts the same representation, and all source facts
            // depend only on its unchanged denotation.
            let value = self.compile_object_reference(argument, &prior)?;
            // Finish the original object once before using its denotation and
            // WD together. This is a Lean local value,not another source owner.
            let name = format!("_known_argument_{index}");
            definitions.push(format!("let {name} := {value}"));
            arguments.push(format!(
                "(Litex.semanticObject (Litex.denote {name}) (Litex.isSet {name}))"
            ));
            arguments.push(format!("h_{}", requirement.type_fact.fact_id().value()));
        }
        for (index, ((expected, actual), checked)) in source
            .dom_facts
            .iter()
            .zip(&requirements.dom_facts)
            .zip(&requirements.proof_of_dom_facts)
            .enumerate()
        {
            if !instantiated_fact_matches(expected, actual, &substitution)
                || source_subject(checked)? != *actual
            {
                return Err(LeanCompileError::unsupported("CompoundKnown/DomainSubject"));
            }
            let prior = SourcePosition {
                before: head + parameters.len() + index,
                ..*position
            };
            let compiled = self.compile_verify(checked, &prior)?;
            definitions.push(local_verified_fact(actual, &compiled));
            arguments.push(format!("h_{}", actual.fact_id().value()));
        }
        Ok((definitions, arguments))
    }

    pub(in crate::compile_to_lean) fn compile_forall_argument_match(
        &self,
        pattern: &Obj,
        goal: &Obj,
        matched: &ForallConclusionArgMatchProof,
        substitution: &HashMap<IdentifierId, Obj>,
        bound: &mut HashSet<IdentifierId>,
        position: Option<&SourcePosition<'_>>,
    ) -> Result<(Obj, String), LeanCompileError> {
        match matched.detailed_ref() {
            DetailedForallConclusionArgMatchProof::BoundParam {
                param_id,
                pattern: captured,
                goal_arg,
            } => {
                if !matches!(pattern,Obj::Identifier(IdentifierObj::Plain{id,..}) if id == param_id)
                    || captured.ir() != pattern.ir()
                    || goal_arg.ir() != goal.ir()
                    || substitution.get(param_id).map(Obj::ir) != Some(goal.ir())
                    || !bound.insert(*param_id)
                {
                    return Err(LeanCompileError::unsupported(
                        "CompoundKnown/BoundParameter",
                    ));
                }
                Ok((
                    goal.clone(),
                    position
                        .map(|position| {
                            self.compile_object_reference(goal, position)
                                .map(|term| format!("(by\n  let _matched := {term}\n  exact Litex.sameRefl _matched)"))
                        })
                        .transpose()?
                        .unwrap_or_default(),
                ))
            }
            DetailedForallConclusionArgMatchProof::ReboundParamEqual {
                param_id,
                previous,
                goal_arg,
                equal,
            } => {
                if !matches!(pattern,Obj::Identifier(IdentifierObj::Plain{id,..}) if id == param_id)
                    || !bound.contains(param_id)
                    || substitution.get(param_id).map(Obj::ir) != Some(previous.ir())
                    || goal_arg.ir() != goal.ir()
                {
                    return Err(LeanCompileError::unsupported(
                        "CompoundKnown/ReboundParameter",
                    ));
                }
                Ok((
                    previous.clone(),
                    self.render_strict_match_equal(previous, goal, equal, position)?,
                ))
            }
            DetailedForallConclusionArgMatchProof::NonParamEqual {
                pattern: captured,
                pattern_after_subst,
                goal_arg,
                equal,
            } => {
                if matches!(pattern,Obj::Identifier(IdentifierObj::Plain{id,..}) if substitution.contains_key(id))
                    || captured.ir() != pattern.ir()
                    || goal_arg.ir() != goal.ir()
                    || !instantiated_object_matches(pattern, pattern_after_subst, substitution)
                {
                    return Err(LeanCompileError::unsupported(
                        "CompoundKnown/NonParameterSubject",
                    ));
                }
                Ok((
                    pattern_after_subst.clone(),
                    self.render_strict_match_equal(pattern_after_subst, goal, equal, position)?,
                ))
            }
            DetailedForallConclusionArgMatchProof::ByStructure {
                pattern: captured,
                goal_arg,
                child_matches,
            } => {
                if captured.ir() != pattern.ir() || goal_arg.ir() != goal.ir() {
                    return Err(LeanCompileError::unsupported(
                        "CompoundKnown/StructureSubject",
                    ));
                }
                let integer_operation = |closed| {
                    format!("(fun (a b : M.Value) => Litex.SetSemantics.sepValue (M := M) (M.standard .integer) (fun z => ∃ lower upper k : ℤ, a = M.number (lower : ℂ) ∧ b = M.number (upper : ℂ) ∧ z = M.number (k : ℂ) ∧ lower ≤ k ∧ k {} upper))",if closed{"≤"}else{"<"})
                };
                let interval_constructor = match (pattern, goal) {
                    (Obj::SetFormer(SetFormer::Range(p)), Obj::SetFormer(SetFormer::Range(g))) => {
                        Some((
                            vec![
                                (p.start.as_ref(), g.start.as_ref()),
                                (p.end.as_ref(), g.end.as_ref()),
                            ],
                            integer_operation(false),
                        ))
                    }
                    (
                        Obj::SetFormer(SetFormer::ClosedRange(p)),
                        Obj::SetFormer(SetFormer::ClosedRange(g)),
                    ) => Some((
                        vec![
                            (p.start.as_ref(), g.start.as_ref()),
                            (p.end.as_ref(), g.end.as_ref()),
                        ],
                        integer_operation(true),
                    )),
                    (
                        Obj::SetFormer(SetFormer::IntervalObj(p)),
                        Obj::SetFormer(SetFormer::IntervalObj(g)),
                    ) => {
                        let (a, b, lc, rc) = real_interval_parts(p);
                        let (c, d, glc, grc) = real_interval_parts(g);
                        if (lc, rc) != (glc, grc) {
                            return Err(LeanCompileError::unsupported(
                                "CompoundKnown/IntervalKind",
                            ));
                        }
                        Some((vec![(a,c),(b,d)],format!("(fun (a b : M.Value) => Litex.SetSemantics.sepValue (M := M) (M.standard .real) (fun z => Litex.realBound {lc} a z ∧ Litex.realBound {rc} z b))")))
                    }
                    (
                        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)),
                        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(g)),
                    ) => {
                        let (a, lower, closed) = real_ray_parts(p);
                        let (b, glower, gclosed) = real_ray_parts(g);
                        if (lower, closed) != (glower, gclosed) {
                            return Err(LeanCompileError::unsupported(
                                "CompoundKnown/IntervalKind",
                            ));
                        }
                        Some((vec![(a,b)],format!("(fun (a : M.Value) => Litex.SetSemantics.sepValue (M := M) (M.standard .real) (fun z => if {lower} then Litex.realBound {closed} a z else Litex.realBound {closed} z a))")))
                    }
                    _ => None,
                };
                if let Some((pairs, operation)) = interval_constructor {
                    if child_matches.len() != pairs.len() {
                        return Err(LeanCompileError::unsupported("CompoundKnown/IntervalArity"));
                    }
                    let mut values = Vec::with_capacity(pairs.len());
                    let mut equalities = Vec::with_capacity(pairs.len());
                    for ((pattern_child, goal_child), matched) in
                        pairs.into_iter().zip(child_matches)
                    {
                        let (value, equality) = self.compile_forall_argument_match(
                            pattern_child,
                            goal_child,
                            matched,
                            substitution,
                            bound,
                            position,
                        )?;
                        values.push(value);
                        equalities.push(equality);
                    }
                    let mut old = goal.clone();
                    let mut values = values.into_iter();
                    match &mut old {
                        Obj::SetFormer(SetFormer::Range(p)) => {
                            p.start = Box::new(values.next().unwrap());
                            p.end = Box::new(values.next().unwrap());
                        }
                        Obj::SetFormer(SetFormer::ClosedRange(p)) => {
                            p.start = Box::new(values.next().unwrap());
                            p.end = Box::new(values.next().unwrap());
                        }
                        Obj::SetFormer(SetFormer::IntervalObj(p)) => {
                            let p = match p {
                                IntervalObj::LeftOpenRightOpen(p)
                                | IntervalObj::LeftOpenRightClosed(p)
                                | IntervalObj::LeftClosedRightOpen(p)
                                | IntervalObj::LeftClosedRightClosed(p) => p,
                            };
                            p.start = Box::new(values.next().unwrap());
                            p.end = Box::new(values.next().unwrap());
                        }
                        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)) => {
                            let p = match p {
                                OneSideInfinityIntervalObj::LowerOpen(p)
                                | OneSideInfinityIntervalObj::LowerClosed(p)
                                | OneSideInfinityIntervalObj::UpperOpen(p)
                                | OneSideInfinityIntervalObj::UpperClosed(p) => p,
                            };
                            p.start = Box::new(values.next().unwrap());
                        }
                        _ => unreachable!(),
                    }
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    // The cited universal forms its substituted source. Matching
                    // creates no hypothetical WD; the actual goal retains its
                    // original complete formation and endpoint membership.
                    self.compile_object_reference(goal, position)?;
                    return Ok((
                        old,
                        if equalities.len() == 1 {
                            format!("(congrArg {operation} {})", equalities[0])
                        } else {
                            format!(
                                "(congrArg₂ {operation} {} {})",
                                equalities[0], equalities[1]
                            )
                        },
                    ));
                }
                if let (
                    Obj::SetFormer(SetFormer::FiniteSeqSet(pattern_sequence)),
                    Obj::SetFormer(SetFormer::FiniteSeqSet(goal_sequence)),
                ) = (pattern, goal)
                {
                    if child_matches.len() != 2 {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/FiniteSequenceArity",
                        ));
                    }
                    let (carrier, carrier_equal) = self.compile_forall_argument_match(
                        &pattern_sequence.set,
                        &goal_sequence.set,
                        &child_matches[0],
                        substitution,
                        bound,
                        position,
                    )?;
                    let (length, length_equal) = self.compile_forall_argument_match(
                        &pattern_sequence.n,
                        &goal_sequence.n,
                        &child_matches[1],
                        substitution,
                        bound,
                        position,
                    )?;
                    let mut old = goal.clone();
                    let Obj::SetFormer(SetFormer::FiniteSeqSet(previous)) = &mut old else {
                        unreachable!()
                    };
                    previous.set = Box::new(carrier);
                    previous.n = Box::new(length);
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    // Both constructors keep the original scoped formation evidence.
                    let previous = self.compile_object_reference(&old, position)?;
                    let target = self.compile_object_reference(goal, position)?;
                    return Ok((old, format!(
                        "(Litex.finiteSeqSameOfArgs {previous} {target} {carrier_equal} {length_equal})"
                    )));
                }
                if let (
                    Obj::SetFormer(SetFormer::SeqSet(pattern_sequence)),
                    Obj::SetFormer(SetFormer::SeqSet(goal_sequence)),
                ) = (pattern, goal)
                {
                    let [carrier_match] = child_matches.as_slice() else {
                        return Err(LeanCompileError::unsupported("CompoundKnown/SequenceArity"));
                    };
                    let (carrier, carrier_equal) = self.compile_forall_argument_match(
                        &pattern_sequence.set,
                        &goal_sequence.set,
                        carrier_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let mut old = goal.clone();
                    let Obj::SetFormer(SetFormer::SeqSet(previous)) = &mut old else {
                        unreachable!()
                    };
                    previous.set = Box::new(carrier);
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    let previous = self.compile_object_reference(&old, position)?;
                    let target = self.compile_object_reference(goal, position)?;
                    return Ok((
                        old,
                        format!("(Litex.seqSetSameOfCarrier {previous} {target} {carrier_equal})"),
                    ));
                }
                if let (
                    Obj::FunctionSpace(FunctionSpace::FnRange(pattern_range)),
                    Obj::FunctionSpace(FunctionSpace::FnRange(goal_range)),
                ) = (pattern, goal)
                {
                    let [function_match] = child_matches.as_slice() else {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/FunctionRangeArity",
                        ));
                    };
                    let (function, function_equal) = self.compile_forall_argument_match(
                        &pattern_range.function,
                        &goal_range.function,
                        function_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let mut old = goal.clone();
                    let Obj::FunctionSpace(FunctionSpace::FnRange(previous)) = &mut old else {
                        unreachable!()
                    };
                    previous.function = Box::new(function);
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    // Formation of the substituted source stays in the cited theorem.
                    self.compile_object_reference(goal, position)?;
                    return Ok((
                        old,
                        format!("(Litex.functionRangeValueCongr (M := M) {function_equal})"),
                    ));
                }
                if let (
                    Obj::FunctionSpace(FunctionSpace::Composition(pattern_composition)),
                    Obj::FunctionSpace(FunctionSpace::Composition(goal_composition)),
                ) = (pattern, goal)
                {
                    let [outer_match, inner_match] = child_matches.as_slice() else {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/CompositionArity",
                        ));
                    };
                    let (outer, outer_equal) = self.compile_forall_argument_match(
                        &pattern_composition.outer,
                        &goal_composition.outer,
                        outer_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let (inner, inner_equal) = self.compile_forall_argument_match(
                        &pattern_composition.inner,
                        &goal_composition.inner,
                        inner_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let mut old = goal.clone();
                    let Obj::FunctionSpace(FunctionSpace::Composition(previous)) = &mut old else {
                        unreachable!()
                    };
                    previous.outer = Box::new(outer);
                    previous.inner = Box::new(inner);
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    // Replay the actual target construction,interfaces and compatibility.
                    self.compile_object_reference(goal, position)?;
                    return Ok((
                        old,
                        format!(
                            "(Litex.compositionValueCongr (M := M) {outer_equal} {inner_equal})"
                        ),
                    ));
                }
                let preimage_constructor = match (pattern, goal) {
                    (
                        Obj::FunctionSpace(FunctionSpace::Preimage(p)),
                        Obj::FunctionSpace(FunctionSpace::Preimage(g)),
                    ) => Some((
                        &p.function,
                        &p.value,
                        &g.function,
                        &g.value,
                        "pointPreimageValueCongr",
                    )),
                    (
                        Obj::FunctionSpace(FunctionSpace::PreimageSet(p)),
                        Obj::FunctionSpace(FunctionSpace::PreimageSet(g)),
                    ) => Some((
                        &p.function,
                        &p.target_set,
                        &g.function,
                        &g.target_set,
                        "setPreimageValueCongr",
                    )),
                    _ => None,
                };
                if let Some((pattern_function, pattern_target, goal_function, goal_target, lemma)) =
                    preimage_constructor
                {
                    let [function_match, target_match] = child_matches.as_slice() else {
                        return Err(LeanCompileError::unsupported("CompoundKnown/PreimageArity"));
                    };
                    let (function, function_equal) = self.compile_forall_argument_match(
                        pattern_function,
                        goal_function,
                        function_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let (target, target_equal) = self.compile_forall_argument_match(
                        pattern_target,
                        goal_target,
                        target_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let mut old = goal.clone();
                    match &mut old {
                        Obj::FunctionSpace(FunctionSpace::Preimage(p)) => {
                            p.function = Box::new(function);
                            p.value = Box::new(target);
                        }
                        Obj::FunctionSpace(FunctionSpace::PreimageSet(p)) => {
                            p.function = Box::new(function);
                            p.target_set = Box::new(target);
                        }
                        _ => unreachable!(),
                    }
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    // Equality-target and membership-target predicates keep distinct laws.
                    self.compile_object_reference(goal, position)?;
                    return Ok((
                        old,
                        format!("(Litex.{lemma} (M := M) {function_equal} {target_equal})"),
                    ));
                }
                let set_constructor = match (pattern, goal) {
                    (Obj::SetOperator(SetOperator::Union(p)), Obj::SetOperator(SetOperator::Union(g))) =>
                        Some((&p.left, &p.right, &g.left, &g.right, "(Litex.SetSemantics.unionValue (M := M))")),
                    (Obj::SetOperator(SetOperator::Intersect(p)), Obj::SetOperator(SetOperator::Intersect(g))) =>
                        Some((&p.left, &p.right, &g.left, &g.right, "(fun a b => Litex.SetSemantics.sepValue (M := M) a (fun z => M.mem z b))")),
                    (Obj::SetOperator(SetOperator::SetMinus(p)), Obj::SetOperator(SetOperator::SetMinus(g))) =>
                        Some((&p.left, &p.right, &g.left, &g.right, "(fun a b => Litex.SetSemantics.sepValue (M := M) a (fun z => ¬ M.mem z b))")),
                    (Obj::SetOperator(SetOperator::SymmetricDifference(p)), Obj::SetOperator(SetOperator::SymmetricDifference(g))) =>
                        Some((&p.left, &p.right, &g.left, &g.right, "(Litex.symmetricDifferenceValue (M := M))")),
                    _ => None,
                };
                if let Some((pattern_left, pattern_right, goal_left, goal_right, lemma)) =
                    set_constructor
                {
                    let [left_match, right_match] = child_matches.as_slice() else {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/BinarySetArity",
                        ));
                    };
                    let (left, left_equal) = self.compile_forall_argument_match(
                        pattern_left,
                        goal_left,
                        left_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let (right, right_equal) = self.compile_forall_argument_match(
                        pattern_right,
                        goal_right,
                        right_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let mut old = goal.clone();
                    match &mut old {
                        Obj::SetOperator(SetOperator::Union(p)) => {
                            p.left = Box::new(left);
                            p.right = Box::new(right);
                        }
                        Obj::SetOperator(SetOperator::Intersect(p)) => {
                            p.left = Box::new(left);
                            p.right = Box::new(right);
                        }
                        Obj::SetOperator(SetOperator::SetMinus(p)) => {
                            p.left = Box::new(left);
                            p.right = Box::new(right);
                        }
                        Obj::SetOperator(SetOperator::SymmetricDifference(p)) => {
                            p.left = Box::new(left);
                            p.right = Box::new(right);
                        }
                        _ => unreachable!(),
                    }
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    self.compile_object_reference(goal, position)?;
                    return Ok((
                        old,
                        format!("(congrArg₂ {lemma} {left_equal} {right_equal})"),
                    ));
                }
                let unary_set_constructor = match (pattern, goal) {
                    (
                        Obj::SetOperator(SetOperator::PowerSet(p)),
                        Obj::SetOperator(SetOperator::PowerSet(g)),
                    ) => Some((&p.set, &g.set, "(Litex.SetSemantics.powerValue (M := M))")),
                    (
                        Obj::SetOperator(SetOperator::FamilyUnion(p)),
                        Obj::SetOperator(SetOperator::FamilyUnion(g)),
                    ) => Some((
                        &p.left,
                        &g.left,
                        "(fun A => Litex.IndexedUnionSemantics.indexedUnionValue (M := M) A id)",
                    )),
                    _ => None,
                };
                if let Some((pattern_child, goal_child, lemma)) = unary_set_constructor {
                    let [child_match] = child_matches.as_slice() else {
                        return Err(LeanCompileError::unsupported("CompoundKnown/UnarySetArity"));
                    };
                    let (child, child_equal) = self.compile_forall_argument_match(
                        pattern_child,
                        goal_child,
                        child_match,
                        substitution,
                        bound,
                        position,
                    )?;
                    let mut old = goal.clone();
                    match &mut old {
                        Obj::SetOperator(SetOperator::PowerSet(p)) => p.set = Box::new(child),
                        Obj::SetOperator(SetOperator::FamilyUnion(p)) => p.left = Box::new(child),
                        _ => unreachable!(),
                    }
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    self.compile_object_reference(goal, position)?;
                    return Ok((old, format!("(congrArg {lemma} {child_equal})")));
                }
                if let (
                    Obj::SetFormer(SetFormer::ListSet(pattern_set)),
                    Obj::SetFormer(SetFormer::ListSet(goal_set)),
                ) = (pattern, goal)
                {
                    if pattern_set.list.is_empty()
                        || pattern_set.list.len() != goal_set.list.len()
                        || child_matches.len() != goal_set.list.len()
                    {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/LiteralSetArity",
                        ));
                    }
                    let mut elements = Vec::new();
                    let mut equalities = Vec::new();
                    for ((pattern_element, goal_element), child_match) in pattern_set
                        .list
                        .iter()
                        .zip(&goal_set.list)
                        .zip(child_matches)
                    {
                        let (element, equality) = self.compile_forall_argument_match(
                            pattern_element,
                            goal_element,
                            child_match,
                            substitution,
                            bound,
                            position,
                        )?;
                        elements.push(Box::new(element));
                        equalities.push(equality);
                    }
                    let mut old = goal.clone();
                    let Obj::SetFormer(SetFormer::ListSet(previous)) = &mut old else {
                        unreachable!()
                    };
                    previous.list = elements;
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    let previous = self.compile_object_reference(&old, position)?;
                    let target = self.compile_object_reference(goal, position)?;
                    let mut equality =
                        "(Eq.refl (Litex.SetSemantics.emptyValue (M := M)))".to_string();
                    for element_equal in equalities.into_iter().rev() {
                        equality = format!("(congrArg₂ (Litex.SetSemantics.insertValue (M := M)) {element_equal} {equality})");
                    }
                    return Ok((
                        old,
                        format!("(show Litex.Same {previous} {target} from {equality})"),
                    ));
                }
                if let (Obj::FnObj(pattern), Obj::FnObj(_)) = (pattern, goal) {
                    return self.compile_known_function_match(
                        pattern,
                        goal,
                        child_matches,
                        substitution,
                        bound,
                        position,
                    );
                }
                if let (
                    Obj::IntegerOperator(IntegerOperator::Mod(pattern)),
                    Obj::IntegerOperator(IntegerOperator::Mod(target)),
                ) = (pattern, goal)
                {
                    if child_matches.len() != 2 {
                        return Err(LeanCompileError::unsupported("CompoundKnown/ModArity"));
                    }
                    let (left, left_equal) = self.compile_forall_argument_match(
                        &pattern.left,
                        &target.left,
                        &child_matches[0],
                        substitution,
                        bound,
                        position,
                    )?;
                    let (right, right_equal) = self.compile_forall_argument_match(
                        &pattern.right,
                        &target.right,
                        &child_matches[1],
                        substitution,
                        bound,
                        position,
                    )?;
                    let old = Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                        left: Box::new(left),
                        right: Box::new(right),
                    }));
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    // Match evidence composes denotation equalities. Both
                    // constructors must still have original scoped WD evidence.
                    self.compile_object_reference(&old, position)?;
                    self.compile_object_reference(goal, position)?;
                    return Ok((old, format!(
                        "(congrArg₂ (Litex.integerDivisionValue (M := M) false) {left_equal} {right_equal})"
                    )));
                }
                if let (
                    Obj::ProductShape(ProductShape::Cart(pattern_cart)),
                    Obj::ProductShape(ProductShape::Cart(goal_cart)),
                ) = (pattern, goal)
                {
                    if pattern_cart.args.len() != goal_cart.args.len()
                        || child_matches.len() != goal_cart.args.len()
                    {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/CartesianArity",
                        ));
                    }
                    let mut values = Vec::with_capacity(child_matches.len());
                    let mut equalities = Vec::with_capacity(child_matches.len());
                    for ((pattern_child, goal_child), child) in pattern_cart
                        .args
                        .iter()
                        .zip(&goal_cart.args)
                        .zip(child_matches)
                    {
                        let (value, equality) = self.compile_forall_argument_match(
                            pattern_child,
                            goal_child,
                            child,
                            substitution,
                            bound,
                            position,
                        )?;
                        values.push(Box::new(value));
                        equalities.push(format!("(show @Eq M.Value _ _ from {equality})"));
                    }
                    let old = Obj::ProductShape(ProductShape::Cart(Cart { args: values }));
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    // The cited universal forms its substituted source. Keep
                    // the actual target WD;no hypothetical parent is invented.
                    self.compile_object_reference(goal, position)?;
                    return Ok((
                        old,
                        format!(
                            "(congrArg (Litex.FiniteFunction.cartValue (M := M)) {})",
                            finite_vector_equality(&equalities),
                        ),
                    ));
                }
                if let (
                    Obj::ProductShape(ProductShape::Tuple(pattern)),
                    Obj::ProductShape(ProductShape::Tuple(goal)),
                ) = (pattern, goal)
                {
                    if pattern.args.len() != goal.args.len()
                        || child_matches.len() != goal.args.len()
                    {
                        return Err(LeanCompileError::unsupported("CompoundKnown/TupleArity"));
                    }
                    let mut values = Vec::new();
                    let mut proofs = Vec::new();
                    for ((pattern, goal), captured) in
                        pattern.args.iter().zip(&goal.args).zip(child_matches)
                    {
                        let (value, equality) = self.compile_forall_argument_match(
                            pattern,
                            goal,
                            captured,
                            substitution,
                            bound,
                            position,
                        )?;
                        if let Some(position) = position {
                            proofs.push(format!(
                                "(show @Eq M.Value {} {} from {equality})",
                                self.compile_normalization_value(&value, position)?,
                                self.compile_normalization_value(goal, position)?
                            ));
                        }
                        values.push(Box::new(value));
                    }
                    let old = Obj::ProductShape(ProductShape::Tuple(Tuple { args: values }));
                    let Some(_) = position else {
                        return Ok((old, String::new()));
                    };
                    return Ok((
                        old,
                        format!(
                            "(congrArg (Litex.FiniteFunction.tupleValue (M := M)) (funext {}))",
                            finite_vector_proof(&proofs)
                        ),
                    ));
                }
                if let (
                    Obj::MatrixOperator(MatrixOperator::Determinant(pattern)),
                    Obj::MatrixOperator(MatrixOperator::Determinant(target)),
                ) = (pattern, goal)
                {
                    if child_matches.len() != 2 {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/DeterminantArity",
                        ));
                    }
                    let (matrix, matrix_eq) = self.compile_forall_argument_match(
                        &pattern.matrix,
                        &target.matrix,
                        &child_matches[0],
                        substitution,
                        bound,
                        position,
                    )?;
                    let (order, order_eq) = self.compile_forall_argument_match(
                        &pattern.order,
                        &target.order,
                        &child_matches[1],
                        substitution,
                        bound,
                        position,
                    )?;
                    let old = Obj::MatrixOperator(MatrixOperator::Determinant(Determinant {
                        matrix: Box::new(matrix),
                        order: Box::new(order),
                    }));
                    let Some(position) = position else {
                        return Ok((old, String::new()));
                    };
                    // Structural matching transports existing determinant values;
                    // it does not establish their matrix or natural-order WD.
                    self.compile_object_reference(&old, position)?;
                    self.compile_object_reference(goal, position)?;
                    return Ok((old, format!(
                        "(congrArg₂ (fun (a n : M.Value) => M.number (Litex.matrixComplexOn a (Litex.NativeBridge.naturalValue n) (Litex.NativeBridge.naturalValue n)).det) {matrix_eq} {order_eq})"
                    )));
                }
                if let (
                    Obj::InstantiatedTemplateObj(pattern),
                    Obj::InstantiatedTemplateObj(target),
                ) = (pattern, goal)
                {
                    if pattern.template_name != target.template_name
                        || pattern.args.len() != target.args.len()
                        || child_matches.len() != pattern.args.len()
                    {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/TemplateConstructor",
                        ));
                    }
                    let mut old = target.clone();
                    let mut proofs = Vec::new();
                    for (index, ((a, b), evidence)) in pattern
                        .args
                        .iter()
                        .zip(&target.args)
                        .zip(child_matches)
                        .enumerate()
                    {
                        let (argument, equal) = self.compile_forall_argument_match(
                            a,
                            b,
                            evidence,
                            substitution,
                            bound,
                            position,
                        )?;
                        old.args[index] = argument;
                        proofs.push(equal);
                    }
                    let object = Obj::InstantiatedTemplateObj(old.clone());
                    let Some(position) = position else {
                        return Ok((object, String::new()));
                    };
                    let target_term = self.compile_object_reference(goal, position)?;
                    if object.ir() == goal.ir() {
                        let mut checks = Vec::new();
                        for (index, (argument, proof)) in old.args.iter().zip(&proofs).enumerate() {
                            let value = self.compile_normalization_value(argument, position)?;
                            checks.push(format!(
                                "have _template_match_{index} : {value} = {value} := {proof}"
                            ));
                        }
                        return Ok((
                            object,
                            format!(
                                "(by\n  {}\n  exact Litex.sameRefl {target_term}\n)",
                                checks.join("\n  ")
                            ),
                        ));
                    }
                    let (declaration, _, _) = position.visible_template(&target.template_name)?;
                    let parameters = declaration
                        .statement
                        .template_arg_def
                        .groups
                        .iter()
                        .flat_map(|g| &g.params)
                        .collect::<Vec<_>>();
                    if parameters.len() != proofs.len() {
                        return Err(LeanCompileError::unsupported("CompoundKnown/TemplateArity"));
                    }
                    let instance = InstantiatedTemplateObj {
                        template_name: target.template_name.clone(),
                        args: parameters
                            .iter()
                            .map(|p| Obj::Identifier(IdentifierObj::from_bound_name(p)))
                            .collect(),
                    };
                    let bindings = parameters
                        .iter()
                        .enumerate()
                        .map(|(i, p)| (p.id, format!("_template_match_arg_{i}")))
                        .collect();
                    let expression =
                        self.compile_template_raw_value(&instance, position, &bindings)?;
                    let names = parameters
                        .iter()
                        .enumerate()
                        .map(|(i, _)| format!("(_template_match_arg_{i} : M.Value)"))
                        .collect::<Vec<_>>();
                    let operation = format!("(fun {} => {expression})", names.join(" "));
                    return Ok((object, curried_value_congruence(&operation, &proofs)?));
                }
                if let (
                    Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(a)),
                    Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(b)),
                ) = (pattern, goal)
                {
                    if a.fields != b.fields || child_matches.len() != 1 {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/FieldConstructor",
                        ));
                    }
                    let (receiver, equal) = self.compile_forall_argument_match(
                        &a.obj,
                        &b.obj,
                        &child_matches[0],
                        substitution,
                        bound,
                        position,
                    )?;
                    let old = FieldAccess {
                        obj: Box::new(receiver),
                        fields: a.fields.clone(),
                    };
                    let object = Obj::StructAndFieldAccessObj(
                        StructAndFieldAccessObj::FieldAccess(old.clone()),
                    );
                    let Some(position) = position else {
                        return Ok((object, String::new()));
                    };
                    self.compile_object_reference(&object, position)?;
                    self.compile_object_reference(goal, position)?;
                    let coordinates = self.struct_field_coordinates(&old, position)?;
                    if coordinates != self.struct_field_coordinates(b, position)? {
                        return Err(LeanCompileError::unsupported(
                            "CompoundKnown/FieldCoordinates",
                        ));
                    }
                    let mut value = "_field_receiver".to_string();
                    for coordinate in coordinates {
                        value = format!("(Litex.FunctionSemantics.callValue (M := M) {value} (M.number ({coordinate} : ℂ)))");
                    }
                    return Ok((
                        object,
                        format!("(congrArg (fun (_field_receiver : M.Value) => {value}) {equal})"),
                    ));
                }
                let (operation, pairs) =
                    arithmetic_constructor_pairs(pattern, goal).ok_or_else(|| {
                        LeanCompileError::unsupported("CompoundKnown/StructureConstructor")
                    })?;
                if pairs.len() != child_matches.len() {
                    return Err(LeanCompileError::unsupported(
                        "CompoundKnown/StructureArity",
                    ));
                }
                let mut old = goal.clone();
                let mut children = Vec::new();
                let mut proofs = Vec::new();
                for ((a, b), proof) in pairs.iter().zip(child_matches) {
                    let (child, equality) = self.compile_forall_argument_match(
                        a,
                        b,
                        proof,
                        substitution,
                        bound,
                        position,
                    )?;
                    children.push(child);
                    proofs.push(equality);
                }
                replace_arithmetic_children(&mut old, &children)?;
                // Formation is read from existing scoped evidence, never rebuilt
                // from structural matching. A missing goal constructor stays a gap.
                let Some(position) = position else {
                    return Ok((old, String::new()));
                };
                self.compile_object_reference(&old, position)?;
                self.compile_object_reference(goal, position)?;
                let operation_term = arithmetic_operation_term(operation);
                let equality = if proofs.len() == 1 {
                    format!("(congrArg {operation_term} {})", proofs[0])
                } else if proofs.len() == 2 {
                    format!("(congrArg₂ {operation_term} {} {})", proofs[0], proofs[1])
                } else {
                    curried_value_congruence(&operation_term, &proofs)?
                };
                Ok((old, equality))
            }
        }
    }

    fn compile_known_function_match(
        &self,
        pattern: &FnObj,
        goal_object: &Obj,
        matches: &[ForallConclusionArgMatchProof],
        substitution: &HashMap<IdentifierId, Obj>,
        bound: &mut HashSet<IdentifierId>,
        position: Option<&SourcePosition<'_>>,
    ) -> Result<(Obj, String), LeanCompileError> {
        let Obj::FnObj(goal) = goal_object else {
            return Err(LeanCompileError::unsupported(
                "KnownApplication/FunctionConstructor",
            ));
        };
        use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs;
        let shared = pattern.body.len().min(goal.body.len());
        let widths = pattern
            .body
            .iter()
            .rev()
            .zip(goal.body.iter().rev())
            .map(|(left, right)| (left.len(), right.len()))
            .collect::<Vec<_>>();
        if shared == 0
            || widths
                .iter()
                .any(|(left, right)| left != right || *left == 0)
        {
            return Err(LeanCompileError::unsupported(
                "KnownApplication/FunctionArity",
            ));
        }
        // Reuse the producer's flattened correspondence, including unequal
        // group counts. The final slot is the complete unmatched prefix.
        let pairs = corresponding_arg_pairs(&Obj::FnObj(pattern.clone()), goal_object)
            .ok_or_else(|| LeanCompileError::unsupported("KnownApplication/FunctionArity"))?;
        if matches.len() != pairs.len() {
            return Err(LeanCompileError::unsupported(
                "KnownApplication/FunctionArity",
            ));
        }
        let prefix = pairs.last().expect("nonempty function correspondence");
        // Native matching executes the prefix first, then saved outer-to-inner
        // arguments. Repeated parameters depend on this execution order.
        let (prefix, mut equality) = self.compile_forall_argument_match(
            &prefix.0,
            &prefix.1,
            matches.last().unwrap(),
            substitution,
            bound,
            position,
        )?;
        let mut groups = Vec::with_capacity(shared);
        let mut offset = 0;
        for (width, _) in widths {
            let mut children = Vec::with_capacity(width);
            let mut proofs = Vec::with_capacity(width);
            for index in offset..offset + width {
                let (child, proof) = self.compile_forall_argument_match(
                    &pairs[index].0,
                    &pairs[index].1,
                    &matches[index],
                    substitution,
                    bound,
                    position,
                )?;
                children.push(Box::new(child));
                proofs.push(proof);
            }
            groups.push((children, proofs));
            offset += width;
        }
        let goal_prefix_len = goal.body.len() - shared;
        let mut old_call = if goal_prefix_len > 0 {
            match prefix {
                Obj::FnObj(call) => call,
                prefix => FnObj {
                    head: Box::new(FnObjHead::from_obj(prefix)),
                    body: Vec::new(),
                },
            }
        } else {
            FnObj {
                head: Box::new(FnObjHead::from_obj(prefix)),
                body: Vec::new(),
            }
        };
        let old_prefix_len = old_call.body.len();
        for (children, _) in groups.iter().rev() {
            old_call.body.push(children.clone());
        }
        let old = Obj::FnObj(old_call);
        let Some(position) = position else {
            return Ok((old, String::new()));
        };
        self.compile_object_reference(&old, position)?;
        self.compile_object_reference(goal_object, position)?;
        // Evidence was checked in native order. Compose the already checked
        // group equalities from the innermost call outward.
        let Obj::FnObj(old_call) = &old else {
            unreachable!()
        };
        for (index, (_, proofs)) in groups.iter().rev().enumerate() {
            let argument_equal = if proofs.len() == 1 {
                proofs[0].clone()
            } else if proofs.len() == 2 {
                format!(
                    "(congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) {} {})",
                    proofs[0], proofs[1]
                )
            } else {
                let typed = old_call.body[old_prefix_len + index]
                    .iter()
                    .zip(&goal.body[goal_prefix_len + index])
                    .zip(proofs)
                    .map(|((left, right), proof)| {
                        Ok(format!(
                            "(show @Eq M.Value {} {} from {proof})",
                            self.compile_normalization_value(left, position)?,
                            self.compile_normalization_value(right, position)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, LeanCompileError>>()?;
                format!(
                    "(congrArg (Litex.FiniteFunction.tupleValue (M := M)) {})",
                    finite_vector_equality(&typed)
                )
            };
            equality = format!("(congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) {equality} {argument_equal})");
        }
        Ok((old, equality))
    }

    fn render_strict_match_equal(
        &self,
        left: &Obj,
        right: &Obj,
        proof: &StrictEqualWithFact,
        position: Option<&SourcePosition<'_>>,
    ) -> Result<String, LeanCompileError> {
        if proof.equal_fact.left.ir() != left.ir() || proof.equal_fact.right.ir() != right.ir() {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/StrictEqualitySubject",
            ));
        }
        match position {
            // Preserve the caller's expected equality for tactic-generated terms.
            // An untyped intermediate `have` loses that expected proposition.
            Some(position) => self.compile_strict_match_equal(left, right, proof, position),
            None => Ok(String::new()),
        }
    }

    fn compile_strict_match_equal(
        &self,
        left: &Obj,
        right: &Obj,
        proof: &StrictEqualWithFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let fact = &proof.equal_fact;
        if fact.left.ir() != left.ir() || fact.right.ir() != right.ir() {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/StrictEqualitySubject",
            ));
        }
        self.compile_object_reference(left, position)?;
        self.compile_object_reference(right, position)?;
        match &proof.equal_proof {
            StrictEqualArgProof::ByTheyAreTheSame(proof) => {
                self.compile_identity(left, right, proof, position)
            }
            StrictEqualArgProof::ByClosedCalculation(proof) => {
                self.compile_closed_equality(fact, proof, position)
            }
            StrictEqualArgProof::ByEquivalenceClass(proof) => {
                self.compile_equivalence_class(fact, proof, position)
            }
            StrictEqualArgProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
                EqualitySearchProofByCalculation::Rational {},
            )) => self.compile_rational(fact, &[], &[], false, position),
            StrictEqualArgProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
                proof @ (EqualitySearchProofByCalculation::ClosedDecimal { .. }
                | EqualitySearchProofByCalculation::ClosedRational { .. }),
            )) => self.compile_builtin_closed_equality(fact, proof, position),
            StrictEqualArgProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(proof),
            ) => self.compile_scalar_division_relation(fact, proof, position),
            StrictEqualArgProof::ByObjectDefinition(proof) => {
                self.compile_function_definition(fact, proof, None, position)
            }
            StrictEqualArgProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::ArithmeticCongruence(proof),
            ) => self.compile_arithmetic_congruence_strategy(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                position,
            ),
            StrictEqualArgProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ) => self.compile_rational(
                fact,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
                true,
                position,
            ),
            StrictEqualArgProof::ByMatchingOneArgByOne(proof) => self
                .compile_matching_one_arg_by_one(
                    fact,
                    &proof.corresponding_arg_equal_proofs,
                    position,
                ),
            _ => Err(LeanCompileError::unsupported(
                "CompoundKnown/StrictEqualityRoute",
            )),
        }
    }

    fn compile_compound_atomic_transport(
        &self,
        old: &AtomicFact,
        new: &AtomicFact,
        equalities: &[String],
        proof: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !same_atomic_family(old, new) || atomic_fact_args_ref(old).len() != equalities.len() {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/TransportArity",
            ));
        }
        if matches!(
            (old, new),
            (AtomicFact::EqualFact(_), AtomicFact::EqualFact(_))
        ) {
            return Ok(format!(
                "(Eq.trans (Eq.symm {}) (Eq.trans {proof} {}))",
                equalities[0], equalities[1]
            ));
        }
        // These predicates depend only on the denotations. The cited theorem
        // forms its substituted source;only the actual goal has a new WD record.
        let transport = match (old, new) {
            (AtomicFact::NotEqualFact(_), AtomicFact::NotEqualFact(_)) => Some(format!(
                "(congrArg₂ (fun (x y : M.Value) => x ≠ y) {} {})",
                equalities[0], equalities[1]
            )),
            (AtomicFact::InFact(_), AtomicFact::InFact(_)) => Some(format!(
                "(congrArg₂ M.mem {} {})",
                equalities[0], equalities[1]
            )),
            (AtomicFact::IsSetFact(_), AtomicFact::IsSetFact(_)) => {
                Some(format!("(congrArg M.isSet {})", equalities[0]))
            }
            (AtomicFact::IsNonemptySetFact(_), AtomicFact::IsNonemptySetFact(_)) => Some(format!(
                "(congrArg (fun (s : M.Value) => ∃ x : M.Value, M.mem x s) {})",
                equalities[0]
            )),
            (AtomicFact::SubsetFact(_), AtomicFact::SubsetFact(_)) => Some(format!(
                "(congrArg₂ (fun (a b : M.Value) => ∀ x : M.Value, M.mem x a → M.mem x b) {} {})",
                equalities[0], equalities[1]
            )),
            _ => None,
        };
        if let Some(equality) = transport {
            return Ok(format!("(Eq.mp {equality} {proof})"));
        }
        match (old, new) {
            (
                AtomicFact::LessFact(_)
                | AtomicFact::GreaterFact(_)
                | AtomicFact::LessEqualFact(_)
                | AtomicFact::GreaterEqualFact(_),
                _,
            ) => self.compile_order_known_atomic_transport(old, new, equalities, proof, position),
            _ if atomic_fact_args_ref(old)
                .iter()
                .zip(atomic_fact_args_ref(new))
                .all(|(a, b)| a.ir() == b.ir()) =>
            {
                Ok(proof.to_string())
            }
            _ => Err(LeanCompileError::unsupported(
                "CompoundKnown/PredicateTransport",
            )),
        }
    }
}

fn local_verified_fact(fact: &Fact, compiled: &(String, String)) -> String {
    format!(
        "have h_{} : {} :=\n  {}",
        fact.fact_id().value(),
        compiled.0,
        compiled.1.replace('\n', "\n  ")
    )
}

fn compound_arguments(fact: &Fact) -> Result<Vec<&Obj>, LeanCompileError> {
    match fact {
        Fact::AtomicFact(fact) => Ok(atomic_fact_args_ref(fact)),
        Fact::AndFact(fact) => Ok(fact.facts.iter().flat_map(atomic_fact_args_ref).collect()),
        Fact::ChainFact(fact) => Ok(fact.objs.iter().collect()),
        Fact::OrFact(fact) => Ok(fact.facts.iter().flat_map(or_branch_arguments).collect()),
        _ => Err(LeanCompileError::unsupported("CompoundKnown/FactFamily")),
    }
}

fn compound_atomics(fact: &Fact) -> Result<Vec<AtomicFact>, LeanCompileError> {
    match fact {
        Fact::AtomicFact(fact) => Ok(vec![fact.clone()]),
        Fact::AndFact(fact) => Ok(fact.facts.clone()),
        Fact::ChainFact(fact) => (0..fact.prop_names.len())
            .map(|index| chain_edge(fact, index, fact.fact_id))
            .collect(),
        _ => Err(LeanCompileError::unsupported("CompoundKnown/FactFamily")),
    }
}

fn replace_compound_arguments(fact: &Fact, args: &[Obj]) -> Result<Fact, LeanCompileError> {
    let mut fact = fact.clone();
    match &mut fact {
        Fact::AtomicFact(atomic) if atomic_fact_args_ref(atomic).len() == args.len() => {
            replace_atomic_arguments(atomic, args)?;
        }
        Fact::ChainFact(chain) if chain.objs.len() == args.len() => {
            chain.objs.clone_from_slice(args)
        }
        Fact::AndFact(and) => {
            let mut offset = 0;
            for atomic in &mut and.facts {
                let arity = atomic_fact_args_ref(atomic).len();
                replace_atomic_arguments(atomic, &args[offset..offset + arity])?;
                offset += arity;
            }
            if offset != args.len() {
                return Err(LeanCompileError::unsupported(
                    "CompoundKnown/InstantiatedArity",
                ));
            }
        }
        Fact::OrFact(or) => {
            let mut offset = 0;
            for branch in &mut or.facts {
                let arity = or_branch_arguments(branch).len();
                let branch_fact = crate::ast::fact::and_chain_as_fact(branch);
                let changed = replace_compound_arguments(
                    &branch_fact,
                    args.get(offset..offset + arity).ok_or_else(|| {
                        LeanCompileError::unsupported("CompoundKnown/InstantiatedArity")
                    })?,
                )?;
                *branch = match changed {
                    Fact::AtomicFact(f) => AndChainAtomicFact::AtomicFact(f),
                    Fact::AndFact(f) => AndChainAtomicFact::AndFact(f),
                    Fact::ChainFact(f) => AndChainAtomicFact::ChainFact(f),
                    _ => unreachable!(),
                };
                offset += arity;
            }
            if offset != args.len() {
                return Err(LeanCompileError::unsupported(
                    "CompoundKnown/InstantiatedArity",
                ));
            }
        }
        _ => {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/InstantiatedArity",
            ))
        }
    }
    Ok(fact)
}

fn or_branch_arguments(fact: &AndChainAtomicFact) -> Vec<&Obj> {
    match fact {
        AndChainAtomicFact::AtomicFact(f) => atomic_fact_args_ref(f),
        AndChainAtomicFact::AndFact(f) => f.facts.iter().flat_map(atomic_fact_args_ref).collect(),
        AndChainAtomicFact::ChainFact(f) => f.objs.iter().collect(),
    }
}

fn same_or_branch_shape(a: &AndChainAtomicFact, b: &AndChainAtomicFact) -> bool {
    match (a, b) {
        (AndChainAtomicFact::AtomicFact(a), AndChainAtomicFact::AtomicFact(b)) => {
            same_atomic_family(a, b)
        }
        (AndChainAtomicFact::AndFact(a), AndChainAtomicFact::AndFact(b)) => {
            a.facts.len() == b.facts.len()
                && a.facts
                    .iter()
                    .zip(&b.facts)
                    .all(|(a, b)| same_atomic_family(a, b))
        }
        (AndChainAtomicFact::ChainFact(a), AndChainAtomicFact::ChainFact(b)) => {
            a.prop_names == b.prop_names && a.objs.len() == b.objs.len()
        }
        _ => false,
    }
}

fn replace_atomic_arguments(fact: &mut AtomicFact, args: &[Obj]) -> Result<(), LeanCompileError> {
    macro_rules! binary {
        ($f:expr) => {{
            $f.left = args[0].clone();
            $f.right = args[1].clone();
        }};
    }
    macro_rules! function_limit {
        ($f:expr) => {{
            $f.function = args[0].clone();
            match &mut $f.approach {
                LimitApproach::AtPoint(point)
                | LimitApproach::FromLeft(point)
                | LimitApproach::FromRight(point) => {
                    **point = args[1].clone();
                    $f.value = args[2].clone();
                }
                LimitApproach::AtPositiveInfinity | LimitApproach::AtNegativeInfinity => {
                    $f.value = args[1].clone();
                }
            }
        }};
    }
    match fact {
        AtomicFact::EqualFact(f) => binary!(f),
        AtomicFact::NotEqualFact(f) => binary!(f),
        AtomicFact::LessFact(f) => binary!(f),
        AtomicFact::GreaterFact(f) => binary!(f),
        AtomicFact::LessEqualFact(f) => binary!(f),
        AtomicFact::GreaterEqualFact(f) => binary!(f),
        AtomicFact::NotLessFact(f) => binary!(f),
        AtomicFact::NotGreaterFact(f) => binary!(f),
        AtomicFact::NotLessEqualFact(f) => binary!(f),
        AtomicFact::NotGreaterEqualFact(f) => binary!(f),
        AtomicFact::SubsetFact(f) => binary!(f),
        AtomicFact::InFact(f) => {
            f.element = args[0].clone();
            f.set = args[1].clone();
        }
        AtomicFact::IsSetFact(f) => f.set = args[0].clone(),
        AtomicFact::IsNonemptySetFact(f) => f.set = args[0].clone(),
        AtomicFact::IsFiniteSetFact(f) => f.set = args[0].clone(),
        AtomicFact::HasFunctionLimitFact(f) => function_limit!(f),
        AtomicFact::NotHasFunctionLimitFact(f) => function_limit!(f),
        AtomicFact::NormalAtomicFact(f) => f.body.clone_from_slice(args),
        _ => {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/InstantiatedPredicate",
            ))
        }
    }
    Ok(())
}

fn replace_arithmetic_children(object: &mut Obj, args: &[Obj]) -> Result<(), LeanCompileError> {
    macro_rules! binary {
        ($f:expr) => {{
            $f.left = Box::new(args[0].clone());
            $f.right = Box::new(args[1].clone());
        }};
    }
    match object {
        Obj::MatrixOperator(MatrixOperator::Trace(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.order = Box::new(args[1].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Determinant(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.order = Box::new(args[1].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Adjugate(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.order = Box::new(args[1].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Inverse(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.order = Box::new(args[1].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Power(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.order = Box::new(args[1].clone());
            m.exponent = Box::new(args[2].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Rank(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.rows = Box::new(args[1].clone());
            m.cols = Box::new(args[2].clone());
        }
        Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.rows = Box::new(args[1].clone());
            m.cols = Box::new(args[2].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Apply(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.vector = Box::new(args[1].clone());
            m.rows = Box::new(args[2].clone());
            m.cols = Box::new(args[3].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Minor(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.order = Box::new(args[1].clone());
            m.row = Box::new(args[2].clone());
            m.col = Box::new(args[3].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Cofactor(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.order = Box::new(args[1].clone());
            m.row = Box::new(args[2].clone());
            m.col = Box::new(args[3].clone());
        }
        Obj::MatrixOperator(MatrixOperator::InnerProduct(m)) => {
            m.left = Box::new(args[0].clone());
            m.right = Box::new(args[1].clone());
            m.dimension = Box::new(args[2].clone());
        }
        Obj::MatrixOperator(MatrixOperator::EuclideanNorm(m)) => {
            m.vector = Box::new(args[0].clone());
            m.dimension = Box::new(args[1].clone());
        }
        Obj::MatrixOperator(MatrixOperator::ZeroMatrix(m)) => {
            m.rows = Box::new(args[0].clone());
            m.cols = Box::new(args[1].clone());
        }
        Obj::MatrixOperator(MatrixOperator::IdentityMatrix(m)) => {
            m.order = Box::new(args[0].clone());
        }
        Obj::MatrixOperator(MatrixOperator::ConjugateTranspose(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.rows = Box::new(args[1].clone());
            m.cols = Box::new(args[2].clone());
        }
        Obj::MatrixOperator(MatrixOperator::OuterProduct(m)) => {
            m.left = Box::new(args[0].clone());
            m.right = Box::new(args[1].clone());
            m.rows = Box::new(args[2].clone());
            m.cols = Box::new(args[3].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Diagonal(m)) => {
            m.vector = Box::new(args[0].clone());
            m.order = Box::new(args[1].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Multiply(m)) => {
            m.left = Box::new(args[0].clone());
            m.right = Box::new(args[1].clone());
            m.rows = Box::new(args[2].clone());
            m.inner = Box::new(args[3].clone());
            m.cols = Box::new(args[4].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Subtract(m)) => {
            m.left = Box::new(args[0].clone());
            m.right = Box::new(args[1].clone());
            m.rows = Box::new(args[2].clone());
            m.cols = Box::new(args[3].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Scale(m)) => {
            m.scalar = Box::new(args[0].clone());
            m.matrix = Box::new(args[1].clone());
            m.rows = Box::new(args[2].clone());
            m.cols = Box::new(args[3].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Add(m)) => {
            m.left = Box::new(args[0].clone());
            m.right = Box::new(args[1].clone());
            m.rows = Box::new(args[2].clone());
            m.cols = Box::new(args[3].clone());
        }
        Obj::MatrixOperator(MatrixOperator::Transpose(m)) => {
            m.matrix = Box::new(args[0].clone());
            m.rows = Box::new(args[1].clone());
            m.cols = Box::new(args[2].clone());
        }
        Obj::TrigOperator(TrigOperator::Sin(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Cos(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Tan(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Cot(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Sec(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Csc(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Arcsin(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Arccos(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Arctan(f)) => f.arg = Box::new(args[0].clone()),
        Obj::TrigOperator(TrigOperator::Arccot(f)) => f.arg = Box::new(args[0].clone()),
        Obj::HyperbolicOperator(HyperbolicOperator::Sinh(f)) => f.arg = Box::new(args[0].clone()),
        Obj::HyperbolicOperator(HyperbolicOperator::Cosh(f)) => f.arg = Box::new(args[0].clone()),
        Obj::HyperbolicOperator(HyperbolicOperator::Tanh(f)) => f.arg = Box::new(args[0].clone()),
        Obj::HyperbolicOperator(HyperbolicOperator::Coth(f)) => f.arg = Box::new(args[0].clone()),
        Obj::HyperbolicOperator(HyperbolicOperator::Sech(f)) => f.arg = Box::new(args[0].clone()),
        Obj::HyperbolicOperator(HyperbolicOperator::Csch(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ExpLogOperator(ExpLogOperator::Exp(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ExpLogOperator(ExpLogOperator::Ln(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ComplexOperator(ComplexOperator::Conjugate(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ComplexOperator(ComplexOperator::RealPart(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(f)) => {
            f.arg = Box::new(args[0].clone())
        }
        Obj::ComplexOperator(ComplexOperator::ComplexAbs(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ArithmeticOperator(ArithmeticOperator::Add(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(f)) => {
            f.base = Box::new(args[0].clone());
            f.exponent = Box::new(args[1].clone());
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(f)) => f.arg = Box::new(args[0].clone()),
        // These constructors were selected by arithmetic_constructor_pairs.
        // The caller already checked their exact ordered original child matches.
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ArithmeticOperator(ArithmeticOperator::Min(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Max(f)) => binary!(f),
        Obj::IntegerOperator(IntegerOperator::Factorial(f)) => f.arg = Box::new(args[0].clone()),
        Obj::IntegerOperator(IntegerOperator::Gcd(f)) => binary!(f),
        Obj::IntegerOperator(IntegerOperator::Lcm(f)) => binary!(f),
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(f)) => f.arg = Box::new(args[0].clone()),
        Obj::ExpLogOperator(ExpLogOperator::Log(f)) => {
            f.base = Box::new(args[0].clone());
            f.arg = Box::new(args[1].clone());
        }
        _ => {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/StructureConstructor",
            ))
        }
    }
    Ok(())
}

fn compound_proof(mut proofs: Vec<String>) -> Result<String, LeanCompileError> {
    let Some(mut proof) = proofs.pop() else {
        return Err(LeanCompileError::unsupported("CompoundKnown/Empty"));
    };
    while let Some(left) = proofs.pop() {
        proof = format!("(And.intro {left} {proof})");
    }
    Ok(proof)
}
