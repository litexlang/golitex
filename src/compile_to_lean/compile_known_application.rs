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
        let ForallConclusionLocation::DirectThenFact(location) =
            &proof.detailed_ref().cite.location
        else {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/ConclusionLocation",
            ));
        };
        let selected: Fact = source
            .then_facts
            .get(location.then_fact_index)
            .ok_or_else(|| LeanCompileError::unsupported("CompoundKnown/ConclusionLocation"))?
            .clone()
            .into();
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
        let requirements = proof
            .detailed_ref()
            .instantiation_requirements
            .detailed_ref();
        if !same_shape
            || pattern_args.is_empty()
            || pattern_args.len() != goal_args.len()
            || proof.detailed_ref().arg_match_proofs.len() != goal_args.len()
            || proof.detailed_ref().forall_parameters_match_what_args.len() != parameters.len()
            || requirements.param_type_requirements.len() != parameters.len()
            || requirements.dom_facts.len() != source.dom_facts.len()
            || requirements.proof_of_dom_facts.len() != source.dom_facts.len()
        {
            return Err(LeanCompileError::unsupported("CompoundKnown/OrderedArity"));
        }
        let substitution: HashMap<_, _> = parameters
            .iter()
            .zip(&proof.detailed_ref().forall_parameters_match_what_args)
            .map(|((param, _), arg)| (param.id, arg.clone()))
            .collect();
        if substitution.len() != parameters.len() {
            return Err(LeanCompileError::unsupported(
                "CompoundKnown/ParameterIdentity",
            ));
        }
        let current = SourcePosition::new(Some(position), SourceOwner::KnownApplication(proof), 0);
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
        for ((pattern, goal), matched) in pattern_args
            .iter()
            .zip(&goal_args)
            .zip(&proof.detailed_ref().arg_match_proofs)
        {
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
        let (definitions, arguments) =
            self.compile_known_application_requirements(source, proof, &current)?;
        let head = proof.detailed_ref().arg_match_proofs.len();
        // Check the original match record before requirements. Its Lean terms
        // are rendered afterward, with only certified constructor formation
        // added to the original match-before truth-citation scope.
        let mut equalities = Vec::new();
        let mut bound = HashSet::new();
        for (index, ((pattern, goal), matched)) in pattern_args
            .iter()
            .zip(&goal_args)
            .zip(&proof.detailed_ref().arg_match_proofs)
            .enumerate()
        {
            let prior = SourcePosition {
                before: index,
                ..current
            };
            let formation =
                SourcePosition::new(Some(&prior), SourceOwner::CalleeInstance(proof), usize::MAX);
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
        let complete_formation = SourcePosition::new(
            Some(&formed),
            SourceOwner::CalleeInstance(proof),
            usize::MAX,
        );
        let formed = &complete_formation;
        let application = if arguments.is_empty() {
            registered.1
        } else {
            format!("({} {})", registered.1, arguments.join(" "))
        };
        let application = conjunction_projection(
            &application,
            location.then_fact_index,
            source.then_facts.len(),
        );
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
        let parameters: Vec<_> = source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| group.params.iter().map(|param| (param, &group.param_type)))
            .collect();
        let requirements = proof
            .detailed_ref()
            .instantiation_requirements
            .detailed_ref();
        if parameters.len() != proof.detailed_ref().forall_parameters_match_what_args.len()
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
            .zip(&proof.detailed_ref().forall_parameters_match_what_args)
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
        let head = proof.detailed_ref().arg_match_proofs.len();
        for (index, (((parameter, kind), argument), requirement)) in parameters
            .iter()
            .zip(&proof.detailed_ref().forall_parameters_match_what_args)
            .zip(&requirements.param_type_requirements)
            .enumerate()
        {
            if requirement.param_id != parameter.id
                || requirement.arg.ir() != argument.ir()
                || source_subject(&requirement.proof)? != requirement.type_fact
            {
                return Err(LeanCompileError::unsupported("CompoundKnown/TypeIdentity"));
            }
            let valid = match (kind, &requirement.type_fact) {
                (ParamType::Obj(set), Fact::AtomicFact(AtomicFact::InFact(member))) => {
                    member.element.ir() == argument.ir()
                        && instantiated_object_matches(set, &member.set, &substitution)
                }
                (ParamType::FiniteSet(_), Fact::AtomicFact(AtomicFact::IsFiniteSetFact(set))) => {
                    set.set.ir() == argument.ir()
                }
                (ParamType::Set(_), Fact::AtomicFact(AtomicFact::IsSetFact(set))) => {
                    set.set.ir() == argument.ir()
                }
                _ => false,
            };
            if !valid {
                return Err(LeanCompileError::unsupported("CompoundKnown/TypeSubject"));
            }
            let prior = SourcePosition {
                before: head + index,
                ..*position
            };
            let compiled = self.compile_verify(&requirement.proof, &prior)?;
            definitions.push(local_verified_fact(&requirement.type_fact, &compiled));
            arguments.push(self.compile_object_reference(argument, &prior)?);
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
                                .map(|term| format!("(Litex.sameRefl {term})"))
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
                } else {
                    format!("(congrArg₂ {operation_term} {} {})", proofs[0], proofs[1])
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
        let (FnObjHead::Identifier(pattern_head), FnObjHead::Identifier(goal_head)) =
            (pattern.head.as_ref(), goal.head.as_ref())
        else {
            return Err(LeanCompileError::unsupported(
                "KnownApplication/FunctionHead",
            ));
        };
        if pattern.body.len() != 1
            || goal.body.len() != 1
            || pattern.body[0].len() != goal.body[0].len()
            || !(1..=2).contains(&goal.body[0].len())
            || matches.len() != goal.body[0].len() + 1
        {
            return Err(LeanCompileError::unsupported(
                "KnownApplication/FunctionArity",
            ));
        }
        let mut children = Vec::new();
        let mut proofs = Vec::new();
        // The capture stores arguments first and the function prefix last.
        for (index, (a, b)) in pattern.body[0].iter().zip(&goal.body[0]).enumerate() {
            let (child, proof) = self.compile_forall_argument_match(
                a,
                b,
                &matches[index],
                substitution,
                bound,
                position,
            )?;
            children.push(Box::new(child));
            proofs.push(proof);
        }
        let (head, head_equal) = self.compile_forall_argument_match(
            &Obj::Identifier(pattern_head.clone()),
            &Obj::Identifier(goal_head.clone()),
            matches.last().unwrap(),
            substitution,
            bound,
            position,
        )?;
        let mut old = goal_object.clone();
        let Obj::FnObj(call) = &mut old else {
            unreachable!()
        };
        call.head = Box::new(FnObjHead::from_obj(head));
        call.body[0] = children;
        let Some(position) = position else {
            return Ok((old, String::new()));
        };
        self.compile_object_reference(&old, position)?;
        self.compile_object_reference(goal_object, position)?;
        let argument_equal = if proofs.len() == 1 {
            proofs[0].clone()
        } else {
            format!(
                "(congrArg₂ (Litex.FiniteFunction.pack2 (M := M)) {} {})",
                proofs[0], proofs[1]
            )
        };
        Ok((old, format!("(congrArg₂ (Litex.FunctionSemantics.callValue (M := M)) {head_equal} {argument_equal})")))
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
        let a = atomic_fact_args_ref(old)
            .iter()
            .map(|x| self.compile_object_reference(x, position))
            .collect::<Result<Vec<_>, _>>()?;
        let b = atomic_fact_args_ref(new)
            .iter()
            .map(|x| self.compile_object_reference(x, position))
            .collect::<Result<Vec<_>, _>>()?;
        match (old, new) {
            (AtomicFact::NotEqualFact(_), AtomicFact::NotEqualFact(_)) => Ok(format!(
                "(Litex.notSameOfSame {} {} {} {} {} {} {proof})",
                a[0], b[0], a[1], b[1], equalities[0], equalities[1]
            )),
            (AtomicFact::InFact(_), AtomicFact::InFact(_)) => Ok(format!(
                "(Litex.inOfSame {} {} {} {} {} {} {proof})",
                a[0], b[0], a[1], b[1], equalities[0], equalities[1]
            )),
            (AtomicFact::IsSetFact(_), AtomicFact::IsSetFact(_)) => Ok(format!(
                "(Litex.isSetOfSame {} {} {} {proof})",
                a[0], b[0], equalities[0]
            )),
            (AtomicFact::SubsetFact(_), AtomicFact::SubsetFact(_)) => Ok(format!(
                "(Litex.subsetOfSame {} {} {} {} {} {} {proof})",
                a[0], a[1], b[0], b[1], equalities[0], equalities[1]
            )),
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
    match fact {
        AtomicFact::EqualFact(f) => binary!(f),
        AtomicFact::NotEqualFact(f) => binary!(f),
        AtomicFact::LessFact(f) => binary!(f),
        AtomicFact::GreaterFact(f) => binary!(f),
        AtomicFact::LessEqualFact(f) => binary!(f),
        AtomicFact::GreaterEqualFact(f) => binary!(f),
        AtomicFact::SubsetFact(f) => binary!(f),
        AtomicFact::InFact(f) => {
            f.element = args[0].clone();
            f.set = args[1].clone();
        }
        AtomicFact::IsSetFact(f) => f.set = args[0].clone(),
        AtomicFact::IsFiniteSetFact(f) => f.set = args[0].clone(),
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
        Obj::ArithmeticOperator(ArithmeticOperator::Add(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(f)) => binary!(f),
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(f)) => {
            f.base = Box::new(args[0].clone());
            f.exponent = Box::new(args[1].clone());
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(f)) => f.arg = Box::new(args[0].clone()),
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
