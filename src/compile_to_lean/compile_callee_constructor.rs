use crate::compile_to_lean::compile_by_stmt_result::induction_evidence::InductionEvidence;
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::SearchProofByKnownForallFact;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_callee_constructor_reference(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<Option<String>, LeanCompileError> {
        self.compile_callee_expression_reference(object, position, false)
    }

    pub(in crate::compile_to_lean) fn compile_callee_expression_reference(
        &self,
        object: &Obj,
        position: &SourcePosition<'_>,
        observe_numeric: bool,
    ) -> Result<Option<String>, LeanCompileError> {
        if arithmetic_constructor_pairs(object, object).is_none()
            && !matches!(
                object,
                Obj::ArithmeticOperator(_)
                    | Obj::FnObj(_)
                    | Obj::InstantiatedTemplateObj(_)
                    | Obj::Literal(Literal::Number(_))
            )
        {
            return Ok(None);
        }
        position.with_visible_callee_instance(&mut |application, caller| {
            let resolved = self.resolve_fact(application.detailed_ref().cite.fact_id, caller)?;
            let Fact::ForallFact(source) = &resolved else {
                return Err(LeanCompileError::unsupported("WD/CalleeFamily"));
            };
            let registered = self.cited_fact_reference(application.detailed_ref().cite.fact_id, caller)?;
            if *registered.0 != resolved {
                return Err(LeanCompileError::unsupported("WD/CalleeIdentity"));
            }
            let (then_index, component) = match &application.detailed_ref().cite.location {
                ForallConclusionLocation::DirectThenFact(p) => (p.then_fact_index, None),
                ForallConclusionLocation::AndFactComponent(p) => (p.then_fact_index, Some(p.component_index)),
                _ => return Err(LeanCompileError::unsupported("WD/CalleeLocation")),
            };
            let selected = source.then_facts.get(then_index)
                .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeLocation"))?;
            let parameters = source.typed_parameters.ordered_param_ids();
            if parameters.len() != application.detailed_ref().forall_parameters_match_what_args.len() {
                return Err(LeanCompileError::unsupported("WD/CalleeArguments"));
            }
            let substitution: HashMap<_,_> = parameters.into_iter()
                .zip(application.detailed_ref().forall_parameters_match_what_args.iter().cloned()).collect();
            let roots: Vec<&Obj> = match (selected, component) {
                (ExistOrAndChainAtomicFact::AndFact(and), Some(index)) => atomic_fact_args_ref(and.facts.get(index)
                    .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeLocation"))?),
                (_, Some(_)) => return Err(LeanCompileError::unsupported("WD/CalleeLocation")),
                (ExistOrAndChainAtomicFact::AtomicFact(atomic), None) => atomic_fact_args_ref(atomic),
                (ExistOrAndChainAtomicFact::ChainFact(chain), None) => chain.objs.iter().collect(),
                (ExistOrAndChainAtomicFact::AndFact(and), None) => and.facts.iter().flat_map(atomic_fact_args_ref).collect(),
                _=>return Err(LeanCompileError::unsupported("WD/CalleeConclusionFamily")),
            };
            let Some(pattern) = roots.into_iter().find_map(|root| constructor_pattern(root,object,&substitution,true)) else {
                return Ok(None);
            };
            let found = caller.with_visible_forall_constructor(
                application.detailed_ref().cite.fact_id,
                then_index,
                pattern,
                &mut |fact, introduced, assumed, wd, site, _declaration| {
                    if fact != source || wd.obj().ir() != pattern.ir() {
                        return Err(LeanCompileError::unsupported("WD/CalleeConstructorSubject"));
                    }
                    self.compile_callee_constructor_factory(fact,introduced,assumed,wd,site,application,caller,observe_numeric)
                },
            )?;
            if let Some(found) = found { return Ok(Some(found)); }
            if let Some(found) = self.compile_recursive_callee_constructor(
                source, then_index, pattern, application, caller, observe_numeric)? {
                return Ok(Some(found));
            }
            self.compile_template_callee_constructor(source, then_index,
                pattern, application, caller, observe_numeric)?
                .map(Some).ok_or_else(|| LeanCompileError::new("WD/CalleeProducer", &format!("The selected forall h_{} has no original constructor for `{}` instantiated as `{}` at this exact argument stage.", source.fact_id.value(), pattern.readable_string(), object.readable_string())))
        })
    }

    fn compile_callee_constructor_factory(
        &self,
        source: &ForallFact,
        introduced: &IntroduceTypedParametersResult,
        assumed: &[AssumeDomFactResult],
        wd: &ObjWellDefinedProof,
        site: &SourcePosition<'_>,
        application: &SearchProofByKnownForallFact,
        caller: &SourcePosition<'_>,
        observe_numeric: bool,
    ) -> Result<String, LeanCompileError> {
        let header = SourcePosition {
            before: 0,
            ..*site
                .callee_header()
                .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeHeader"))?
        };
        let (binders, definitions) = match header.owner {
            SourceOwner::Induction(proof) => {
                self.compile_induction_constructor_header(source, &proof, &header)?
            }
            _ => {
                let (binders, _, definitions) =
                    self.compile_forall_head(source, introduced, assumed, &header)?;
                (binders, definitions)
            }
        };
        self.apply_callee_constructor(
            source,
            wd,
            site,
            application,
            caller,
            observe_numeric,
            binders,
            definitions,
        )
    }

    pub(super) fn apply_callee_constructor(
        &self,
        source: &ForallFact,
        wd: &ObjWellDefinedProof,
        site: &SourcePosition<'_>,
        application: &SearchProofByKnownForallFact,
        caller: &SourcePosition<'_>,
        observe_numeric: bool,
        binders: Vec<String>,
        definitions: Vec<String>,
    ) -> Result<String, LeanCompileError> {
        // `site` has the original source header and the precise WD subtree.
        // It never opens the callee's proved then facts as new assumptions.
        let constructor = self.compile_wd(wd, site)?;
        let body = self.scope_proposition(constructor, &definitions);
        let body = if observe_numeric {
            // Instantiate the original scalar certificate under the same
            // source binders and checked call arguments as the constructor.
            let (value, denotation, member, _) = self.numeric_wd(wd, site)?;
            self.scope_proposition(format!("(let _callee_object := {body};\nshow {{ _z : ℂ // Litex.denote _callee_object = M.number _z ∧ Litex.In _callee_object Litex.C }} from ⟨{value}, {denotation}, {member}⟩)"), &definitions)
        } else {
            body
        };
        self.apply_callee_body(source, application, caller, binders, body)
    }

    /// Apply a checked constructor factory in the cited forall's original
    /// binder order, retaining the recorded argument and domain evidence.
    pub(super) fn apply_callee_body(
        &self,
        source: &ForallFact,
        application: &SearchProofByKnownForallFact,
        caller: &SourcePosition<'_>,
        mut binders: Vec<String>,
        body: String,
    ) -> Result<String, LeanCompileError> {
        for parameter in source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
        {
            let level = format!("Type v{}}}", parameter.id.value());
            for binder in &mut binders {
                *binder = binder.replace(&level, "Type _}");
            }
        }
        let factory = if binders.is_empty() {
            body
        } else {
            format!("(fun {} => {body})", binders.join(" "))
        };
        let requirements =
            SourcePosition::new(Some(caller), SourceOwner::KnownApplication(application), 0);
        let (definitions, arguments) =
            self.compile_known_application_requirements(source, application, &requirements)?;
        let applied = if arguments.is_empty() {
            factory
        } else {
            format!("({factory} {})", arguments.join(" "))
        };
        if definitions.is_empty() {
            Ok(applied)
        } else {
            // Object values must reduce through the checked argument bindings.
            // A tactic-created Obj hides its payload behind a metavariable.
            Ok(format!("({};\n{applied})", definitions.join(";\n")))
        }
    }

    fn compile_induction_constructor_header(
        &self,
        source: &ForallFact,
        proof: &InductionEvidence<'_>,
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, Vec<String>), LeanCompileError> {
        let introduced = &proof.introduced_parameter;
        self.validate_parameter_store_capture(&introduced.defined_params)?;
        if source.typed_parameters.groups.len() != 1
            || source.typed_parameters.groups[0].params != vec![proof.parameter.clone()]
            || source.typed_parameters.groups[0].param_type
                != ParamType::Obj(Obj::StandardSet(StandardSet::Z))
            || source.dom_facts.len() != 1
            || introduced.param_type_well_defined.len() != 1
            || introduced.defined_params.store_and_infer_results.len() != 1
            || introduced.auto_opened_struct_layers.is_some()
        {
            return Err(LeanCompileError::new("WD/InductionHeaderCapture", "The final integer induction header differs from its retained original introduction."));
        }
        let ParamTypeWellDefinedProof::Obj(carrier) = &introduced.param_type_well_defined[0] else {
            return Err(LeanCompileError::unsupported(
                "WD/InductionCarrierFormation",
            ));
        };
        if carrier.obj() != &Obj::StandardSet(StandardSet::Z) {
            return Err(LeanCompileError::unsupported("WD/InductionCarrierSubject"));
        }
        self.compile_wd(carrier, position)?;
        let parameter_store = &introduced.defined_params.store_and_infer_results[0];
        let parameter_position = SourcePosition {
            before: 1,
            ..*position
        };
        let (mut binders, _) = self.introduce_member_parameter(
            &proof.parameter,
            carrier.obj(),
            parameter_store,
            &parameter_position,
        )?;
        let parameter_fact =
            self.resolve_fact(parameter_store.primary_fact_id(), &parameter_position)?;
        let parameter_member = (
            self.fact_proposition(&parameter_fact, &parameter_position)?,
            format!("h_{}", parameter_store.primary_fact_id().value()),
        );
        let mut definitions = self.compile_parameter_inferences(
            parameter_store,
            &parameter_fact,
            &parameter_member,
            &parameter_position,
        )?;
        let domain = &proof.goal_domain;
        let completed = SourcePosition {
            before: 2,
            ..*position
        };
        let domain_fact =
            self.resolve_fact(domain.store_and_infer.primary_fact_id(), &completed)?;
        // The final forall allocates a fresh domain FactId after the checked
        // header. Retain the checked producer's ID and validate the exact
        // regenerated predicate, rather than treating it as another proof.
        if !instantiated_fact_matches(&source.dom_facts[0], &domain_fact, &HashMap::new()) {
            return Err(LeanCompileError::new(
                "WD/InductionDomainSubject",
                "The final forall domain is not the retained original induction guard.",
            ));
        }
        self.validate_store(&domain.store_and_infer.store, &domain_fact)?;
        self.compile_fact_wd(&domain.well_defined, &domain_fact, &parameter_position)?;
        let formation = SourcePosition::new(
            Some(&parameter_position),
            SourceOwner::FactWD(&domain.well_defined),
            usize::MAX,
        );
        let proposition = self.fact_proposition(&domain_fact, &formation)?;
        let hypothesis = format!("h_{}", domain_fact.fact_id().value());
        binders.push(format!(
            "({hypothesis} : {})",
            self.scope_proposition(proposition.clone(), &definitions)
        ));
        definitions.extend(self.compile_stored_inferences(
            &domain.store_and_infer,
            &domain_fact,
            &(proposition, hypothesis),
            &completed,
        )?);
        Ok((binders, definitions))
    }
}

pub(in crate::compile_to_lean) fn exact_constructor_pattern<'a>(
    pattern: &'a Obj,
    object: &Obj,
    substitution: &HashMap<IdentifierId, Obj>,
) -> Option<&'a Obj> {
    constructor_pattern(pattern, object, substitution, false)
}

// Only the callee factory currently consumes numeric leaf constructors.
// Builder and obtain projections keep their existing constructor boundary.
fn constructor_pattern<'a>(
    pattern: &'a Obj,
    object: &Obj,
    substitution: &HashMap<IdentifierId, Obj>,
    numeric_leaves: bool,
) -> Option<&'a Obj> {
    if (matches!(
        pattern,
        Obj::ArithmeticOperator(_)
            | Obj::MatrixOperator(_)
            | Obj::FnObj(_)
            | Obj::InstantiatedTemplateObj(_)
            | Obj::SetFormer(SetFormer::ListSet(_) | SetFormer::MatrixSet(_))
    ) || numeric_leaves
        && (matches!(pattern, Obj::Literal(Literal::Number(_)))
            || arithmetic_constructor_pairs(pattern, pattern).is_some()))
        && instantiated_object_matches(pattern, object, substitution)
    {
        return Some(pattern);
    }
    // A callee's constructor tree follows the same child order as equality
    // replay. Traversal only locates original WD; it never supplies new WD.
    if numeric_leaves {
        if let Some((_, children)) = arithmetic_constructor_pairs(pattern, pattern) {
            return children.into_iter().find_map(|(child, _)| {
                constructor_pattern(child, object, substitution, numeric_leaves)
            });
        }
    }
    let children: Vec<&Obj> = match pattern {
        Obj::SetFormer(SetFormer::ListSet(set)) => set.list.iter().map(Box::as_ref).collect(),
        Obj::SetFormer(SetFormer::MatrixSet(set)) => vec![&set.set, &set.rows, &set.cols],
        Obj::MatrixOperator(_) => arithmetic_constructor_pairs(pattern, pattern)
            .map(|(_, children)| children.into_iter().map(|(child, _)| child).collect())
            .unwrap_or_default(),
        Obj::SetFormer(SetFormer::Range(p)) if numeric_leaves => vec![&p.start, &p.end],
        Obj::SetFormer(SetFormer::ClosedRange(p)) if numeric_leaves => vec![&p.start, &p.end],
        Obj::SetFormer(SetFormer::IntervalObj(p)) if numeric_leaves => {
            let (start, end, _, _) = real_interval_parts(p);
            vec![start, end]
        }
        Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)) if numeric_leaves => {
            vec![real_ray_parts(p).0]
        }
        Obj::SetOperator(SetOperator::Union(p)) if numeric_leaves => vec![&p.left, &p.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Add(value)) => vec![&value.left, &value.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(value)) => vec![&value.left, &value.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(value)) => vec![&value.left, &value.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Div(value)) => vec![&value.left, &value.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(value)) => {
            vec![&value.base, &value.exponent]
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(value)) => vec![&value.arg],
        Obj::InstantiatedTemplateObj(instance) => instance.args.iter().collect(),
        Obj::FnObj(application) => application
            .body
            .iter()
            .flatten()
            .map(|argument| argument.as_ref())
            .collect(),
        _ => vec![],
    };
    children
        .into_iter()
        .find_map(|child| constructor_pattern(child, object, substitution, numeric_leaves))
}
