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
        if !matches!(object, Obj::ArithmeticOperator(_) | Obj::FnObj(_)) {
            return Ok(None);
        }
        position.with_visible_callee_instance(&mut |application, caller| {
            let resolved = self.resolve_fact(application.cite.fact_id, caller)?;
            let Fact::ForallFact(source) = &resolved else {
                return Err(LeanCompileError::unsupported("WD/CalleeFamily"));
            };
            let registered = self.cited_fact_reference(application.cite.fact_id, caller)?;
            if *registered.0 != resolved {
                return Err(LeanCompileError::unsupported("WD/CalleeIdentity"));
            }
            let ForallConclusionLocation::DirectThenFact(location) = &application.cite.location else {
                return Err(LeanCompileError::unsupported("WD/CalleeLocation"));
            };
            let selected = source.then_facts.get(location.then_fact_index)
                .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeLocation"))?;
            let parameters = source.typed_parameters.ordered_param_ids();
            if parameters.len() != application.forall_parameters_match_what_args.len() {
                return Err(LeanCompileError::unsupported("WD/CalleeArguments"));
            }
            let substitution: HashMap<_,_> = parameters.into_iter()
                .zip(application.forall_parameters_match_what_args.iter().cloned()).collect();
            let roots: Vec<&Obj> = match selected {
                ExistOrAndChainAtomicFact::AtomicFact(atomic) => atomic_fact_args_ref(atomic),
                ExistOrAndChainAtomicFact::ChainFact(chain) => chain.objs.iter().collect(),
                ExistOrAndChainAtomicFact::AndFact(and) => and.facts.iter().flat_map(atomic_fact_args_ref).collect(),
                _=>return Err(LeanCompileError::unsupported("WD/CalleeConclusionFamily")),
            };
            let Some(pattern) = roots.into_iter().find_map(|root| exact_constructor_pattern(root,object,&substitution)) else {
                return Ok(None);
            };
            let found = caller.with_visible_forall_constructor(
                application.cite.fact_id,
                location.then_fact_index,
                pattern,
                &mut |fact, introduced, assumed, wd, site, _declaration| {
                    if fact != source || wd.obj().ir() != pattern.ir() {
                        return Err(LeanCompileError::unsupported("WD/CalleeConstructorSubject"));
                    }
                    self.compile_callee_constructor_factory(fact,introduced,assumed,wd,site,application,caller)
                },
            )?;
            found.map(Some).ok_or_else(|| LeanCompileError::new("WD/CalleeProducer", "The selected prior forall has no original constructor at this exact argument stage."))
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
    ) -> Result<String, LeanCompileError> {
        let header = SourcePosition {
            before: 0,
            ..*site
                .callee_header()
                .ok_or_else(|| LeanCompileError::unsupported("WD/CalleeHeader"))?
        };
        let (mut binders, definitions) = match header.owner {
            SourceOwner::Induction(proof) => {
                self.compile_induction_constructor_header(source, proof, &header)?
            }
            _ => {
                let (binders, _, definitions) =
                    self.compile_forall_head(source, introduced, assumed, &header)?;
                (binders, definitions)
            }
        };
        for parameter in source
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| &group.params)
        {
            let level = format!("Type v{}}}", parameter.id.value());
            for binder in &mut binders {
                *binder = binder.replace(&level, "Type _}");
            }
        }
        // `site` has the original source header and the precise WD subtree.
        // It never opens the callee's proved then facts as new assumptions.
        let constructor = self.compile_wd(wd, site)?;
        let body = if definitions.is_empty() {
            constructor
        } else {
            format!(
                "(show Litex.Obj (M := M) _ from by\n  {}\n  exact {constructor}\n)",
                definitions.join("\n").replace('\n', "\n  ")
            )
        };
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
            Ok(format!(
                "(show Litex.Obj (M := M) _ from by\n  {}\n  exact {applied}\n)",
                definitions.join("\n").replace('\n', "\n  ")
            ))
        }
    }

    fn compile_induction_constructor_header(
        &self,
        source: &ForallFact,
        proof: &crate::execute::execute_by_stmt::ExecByInducStmtSuccess,
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
    if matches!(pattern, Obj::ArithmeticOperator(_) | Obj::FnObj(_))
        && instantiated_object_matches(pattern, object, substitution)
    {
        return Some(pattern);
    }
    let children: Vec<&Obj> = match pattern {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(value)) => vec![&value.left, &value.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(value)) => vec![&value.left, &value.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(value)) => vec![&value.left, &value.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Div(value)) => vec![&value.left, &value.right],
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(value)) => {
            vec![&value.base, &value.exponent]
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(value)) => vec![&value.arg],
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
        .find_map(|child| exact_constructor_pattern(child, object, substitution))
}
