use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferBijectiveFactResult, InferInjectiveFactResult,
    InferSurjectiveFactResult,
};
use std::collections::HashMap;

/// Borrow the original predicate and arguments; membership never changes an object's host type.
pub(super) fn mapping_parts(fact: &AtomicFact) -> Option<(&'static str, bool, [&Obj; 3])> {
    Some(match fact {
        AtomicFact::InjectiveFact(f) => ("injective", false, [&f.domain, &f.codomain, &f.function]),
        AtomicFact::SurjectiveFact(f) => {
            ("surjective", false, [&f.domain, &f.codomain, &f.function])
        }
        AtomicFact::BijectiveFact(f) => ("bijective", false, [&f.domain, &f.codomain, &f.function]),
        AtomicFact::NotInjectiveFact(f) => {
            ("injective", true, [&f.domain, &f.codomain, &f.function])
        }
        AtomicFact::NotSurjectiveFact(f) => {
            ("surjective", true, [&f.domain, &f.codomain, &f.function])
        }
        AtomicFact::NotBijectiveFact(f) => {
            ("bijective", true, [&f.domain, &f.codomain, &f.function])
        }
        _ => return None,
    })
}

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(
        &format!("Mapping/{stage}"),
        "Mapping evidence has another original function, carrier, binder, clause or proof subject.",
    )
}

pub(super) fn is_parameter(obj: &Obj, id: IdentifierId) -> bool {
    matches!(obj, Obj::Identifier(IdentifierObj::Plain { id: actual, .. }) if *actual == id)
}

pub(super) fn mapping_call_matches(call: &Obj, function: &Obj, id: IdentifierId) -> bool {
    let Obj::FnObj(call) = call else { return false };
    let Some(last) = call.body.last() else {
        return false;
    };
    if last.len() != 1 || !is_parameter(&last[0], id) {
        return false;
    }
    if let Obj::FnObj(prefix) = function {
        return call.head == prefix.head && call.body[..call.body.len() - 1] == prefix.body;
    }
    call.body.len() == 1 && *call.head == FnObjHead::from_obj(function.clone())
}

fn parameters<'a>(
    source: &'a TypedParameterList,
    carrier: &Obj,
    count: usize,
) -> Result<Vec<&'a BoundName>, LeanCompileError> {
    if source
        .groups
        .iter()
        .any(|g| !matches!(&g.param_type, ParamType::Obj(o) if o.ir() == carrier.ir()))
    {
        return Err(invalid("BinderCarrier"));
    }
    let params = source
        .groups
        .iter()
        .flat_map(|g| &g.params)
        .collect::<Vec<_>>();
    if params.len() != count
        || params
            .iter()
            .enumerate()
            .any(|(i, p)| params[..i].iter().any(|q| q.id == p.id))
    {
        return Err(invalid("BinderCount"));
    }
    Ok(params)
}

fn validate_forall<'a>(
    kind: &str,
    args: [&Obj; 3],
    fact: &'a ForallFact,
) -> Result<Vec<&'a BoundName>, LeanCompileError> {
    if fact.then_facts.len() != 1 {
        return Err(invalid("ConclusionCount"));
    }
    match kind {
        "injective" => {
            let p = parameters(&fact.typed_parameters, args[0], 2)?;
            if !matches!(fact.dom_facts.as_slice(), [Fact::AtomicFact(AtomicFact::EqualFact(eq))]
                if mapping_call_matches(&eq.left,args[2],p[0].id) && mapping_call_matches(&eq.right,args[2],p[1].id))
                || !matches!(&fact.then_facts[0], ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq))
                    if is_parameter(&eq.left,p[0].id) && is_parameter(&eq.right,p[1].id))
            {
                return Err(invalid("InjectiveClauses"));
            }
            independent(args, &p.iter().map(|p| p.id).collect::<Vec<_>>())?;
            Ok(p)
        }
        "surjective" => {
            let p = parameters(&fact.typed_parameters, args[1], 1)?;
            let ExistOrAndChainAtomicFact::ExistFact(ex) = &fact.then_facts[0] else {
                return Err(invalid("PreimageExistence"));
            };
            let x = parameters(&ex.typed_parameters, args[0], 1)?;
            if !fact.dom_facts.is_empty()
                || x[0].id == p[0].id
                || !matches!(ex.facts.as_slice(), [QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq))]
                    if is_parameter(&eq.left,p[0].id) && mapping_call_matches(&eq.right,args[2],x[0].id))
            {
                return Err(invalid("SurjectiveClauses"));
            }
            independent(args, &[p[0].id, x[0].id])?;
            Ok(p)
        }
        _ => Err(invalid("DefinitionFamily")),
    }
}

fn validate_component(kind: &str, args: [&Obj; 3], fact: &Fact) -> Result<(), LeanCompileError> {
    let Fact::AtomicFact(f) = fact else {
        return Err(invalid("Component"));
    };
    let Some((actual, false, objects)) = mapping_parts(f) else {
        return Err(invalid("Component"));
    };
    if actual != kind || args.iter().zip(objects).any(|(a, b)| a.ir() != b.ir()) {
        return Err(invalid("Component"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_mapping_definition(
        &self,
        goal: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Some((kind, false, args)) = mapping_parts(goal) else {
            return Err(invalid("Family"));
        };
        let count = if kind == "bijective" { 2 } else { 1 };
        if requirements.len() != count || proofs.len() != count {
            return Err(invalid("DefinitionArity"));
        }
        let mut witnesses = Vec::new();
        for (i, (requirement, proof)) in requirements.iter().zip(proofs).enumerate() {
            if source_subject(proof)? != *requirement {
                return Err(invalid("ProofSubject"));
            }
            if kind == "bijective" {
                validate_component(["injective", "surjective"][i], args, requirement)?;
            } else {
                let Fact::ForallFact(f) = requirement else {
                    return Err(invalid("DefinitionUniversal"));
                };
                validate_forall(kind, args, f)?;
            }
            let prior = position.atomic_search_prior(i)?;
            let mut checked = self.compile_verify(proof, &prior)?;
            // This local proof is instantiated at the canonical semantic carrier.
            if let Fact::ForallFact(f) = requirement {
                for id in f.typed_parameters.ordered_param_ids() {
                    let level = format!("Type v{}}}", id.value());
                    checked.0 = checked.0.replace(&level, "Type u}");
                    checked.1 = checked.1.replace(&level, "Type u}");
                }
            }
            witnesses.push(format!("(show {} from {})", checked.0, checked.1));
        }
        if kind == "bijective" {
            return Ok(format!("⟨{}, {}⟩", witnesses[0], witnesses[1]));
        }
        let values = args
            .iter()
            .map(|o| {
                self.compile_object_reference(o, position)
                    .map(|t| format!("(Litex.denote {t})"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!(
            "((Litex.{kind}Value_iff {}).mpr (by\n  intro {}\n  exact {} {}))",
            values.join(" "),
            if kind == "injective" {
                "_x _hx _y _hy _eq"
            } else {
                "_y _hy"
            },
            witnesses[0],
            if kind == "injective" {
                "_x _hx _y _hy _eq"
            } else {
                "_y _hy"
            }
        ))
    }

    pub(super) fn compile_mapping_inferences(
        &self,
        infer: &InferAtomicFactResult,
        seed: &Fact,
        compiled: &(String, String),
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let Fact::AtomicFact(atomic) = seed else {
            return Err(invalid("InferenceSource"));
        };
        let Some((kind, false, args)) = mapping_parts(atomic) else {
            return Err(invalid("InferenceFamily"));
        };
        let mut groups = Vec::new();
        match infer {
            InferAtomicFactResult::InjectiveFact(rules) => {
                for InferInjectiveFactResult::Definition(p) in rules {
                    groups.push((p.source_fact_id, p.derived.iter().collect::<Vec<_>>()));
                }
            }
            InferAtomicFactResult::SurjectiveFact(rules) => {
                for InferSurjectiveFactResult::Definition(p) in rules {
                    groups.push((p.source_fact_id, p.derived.iter().collect::<Vec<_>>()));
                }
            }
            InferAtomicFactResult::BijectiveFact(rules) => {
                for InferBijectiveFactResult::Definition(p) in rules {
                    groups.push((p.source_fact_id, vec![&p.injective, &p.surjective]));
                }
            }
            _ => return Err(invalid("InferenceFamily")),
        }
        if groups.len() != 1 {
            return Err(invalid("InferenceArity"));
        }
        let mut declarations = Vec::new();
        for (source, stores) in groups {
            if source != seed.fact_id() || stores.len() != if kind == "bijective" { 2 } else { 1 } {
                return Err(invalid("InferenceIdentity"));
            }
            for (i, derived) in stores.into_iter().enumerate() {
                let prior = SourcePosition {
                    before: position.before + i,
                    ..*position
                };
                let fact = self.resolve_fact(derived.primary_fact_id(), &prior)?;
                self.validate_store(&derived.store, &fact)?;
                if kind == "bijective" {
                    validate_component(["injective", "surjective"][i], args, &fact)?;
                    let proposition = self.fact_proposition(&fact, &prior)?;
                    declarations.push(self.emit_internal_fact(
                        &fact,
                        &(proposition, format!("({}).{}", compiled.1, i + 1)),
                        &prior,
                    )?);
                    continue;
                }
                let Fact::ForallFact(target) = &fact else {
                    return Err(invalid("InferredUniversal"));
                };
                let params = validate_forall(kind, args, target)?;
                let mut bindings = HashMap::new();
                let mut binders = Vec::new();
                let mut intros = Vec::new();
                let mut arguments = Vec::new();
                for p in params {
                    let id = p.id.value();
                    let name = format!("_value_i{id}");
                    let value = format!("(Litex.denote {name})");
                    let carrier = self.compile_function_raw_expression_bound(
                        if kind == "injective" {
                            args[0]
                        } else {
                            args[1]
                        },
                        &prior,
                        &bindings,
                    )?;
                    binders.push(format!("{{_Host_i{id} : Type _}} [_rep_i{id} : Litex.Representation M _Host_i{id}] ({name} : Litex.Obj (M := M) _Host_i{id}) (_membership_i{id} : M.mem {value} {carrier})"));
                    intros.extend([
                        format!("_Host_i{id}"),
                        format!("_rep_i{id}"),
                        name.clone(),
                        format!("_membership_i{id}"),
                    ]);
                    arguments.extend([
                        if kind == "injective" {
                            value.clone()
                        } else {
                            format!("(Litex.semanticObject {value} (Litex.isSet {name}))")
                        },
                        format!("_membership_i{id}"),
                    ]);
                    bindings.insert(p.id, value);
                }
                for domain in &target.dom_facts {
                    let name = format!("h_{}", domain.fact_id().value());
                    binders.push(format!(
                        "({name} : {})",
                        self.compile_function_raw_predicate(domain, &prior, &bindings)?
                    ));
                    intros.push(name.clone());
                    arguments.push(name);
                }
                let conclusion = self.compile_function_raw_predicate(
                    &target.then_facts[0].clone().into(),
                    &prior,
                    &bindings,
                )?;
                let source = if kind == "injective" {
                    compiled.1.clone()
                } else {
                    let values = args
                        .iter()
                        .map(|o| {
                            self.compile_object_reference(o, &prior)
                                .map(|t| format!("(Litex.denote {t})"))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    format!(
                        "((Litex.surjectiveValue_iff {}).mp {})",
                        values.join(" "),
                        compiled.1
                    )
                };
                declarations.push(self.emit_internal_fact(
                    &fact,
                    &(
                        format!("∀ {}, {conclusion}", binders.join(" ")),
                        format!(
                            "(by\n  intro {}\n  exact {source} {})",
                            intros.join(" "),
                            arguments.join(" ")
                        ),
                    ),
                    &prior,
                )?);
            }
        }
        Ok(declarations)
    }

    /// The initial mapping slice accepts the exact unary signature WD route.
    /// Carrier-equality and finite-prefix alternatives remain explicit future consumers.
    pub(super) fn validate_mapping_domain(
        &self,
        fact: &AtomicFact,
        requirements: &[&Fact],
    ) -> Result<(), LeanCompileError> {
        let Some((_, _, args)) = mapping_parts(fact) else {
            return Ok(());
        };
        if requirements.len()!=3 || requirements[..2].iter().zip(args).any(|(f,arg)|
            !matches!(f,Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir()==arg.ir())) {
            return Err(invalid("DomainRequirements"));
        }
        let Fact::AtomicFact(AtomicFact::InFact(member)) = requirements[2] else {
            return Err(invalid("CallableSignature"));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
            return Err(invalid("CallableSignature"));
        };
        if member.element.ir() != args[2].ir()
            || signature.set_bound_parameters.groups.len() != 1
            || signature.set_bound_parameters.groups[0].params.len() != 1
            || signature.set_bound_parameters.groups[0].param_type.ir() != args[0].ir()
            || !signature.dom_facts.is_empty()
            || signature.ret_set.ir() != args[1].ir()
        {
            return Err(invalid("CallableSignature"));
        }
        Ok(())
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_bijective_preimage(
        &self,
        source: &PlainExistFact,
        evidence: &crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedBuiltinBijectivePreimage,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Some(("bijective", false, args)) = mapping_parts(&evidence.certificate.fact) else {
            return Err(invalid("PreimageCertificate"));
        };
        let params = parameters(&source.typed_parameters, args[0], 1)?;
        let id = params[0].id;
        let [QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(eq))] = source.facts.as_slice()
        else {
            return Err(invalid("PreimageBody"));
        };
        let (target, reversed) = if mapping_call_matches(&eq.left, args[2], id) {
            (&eq.right, false)
        } else if mapping_call_matches(&eq.right, args[2], id) {
            (&eq.left, true)
        } else {
            return Err(invalid("PreimageFunction"));
        };
        independent(args.into_iter().chain([target]), &[id])?;
        if !matches!(source_subject(&evidence.target_membership)?,Fact::AtomicFact(AtomicFact::InFact(ref f))
            if f.element.ir()==target.ir() && f.set.ir()==args[1].ir())
        {
            return Err(invalid("PreimageTarget"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
            evidence.certificate.searched_proof.as_ref()
        else {
            return Err(invalid("PreimageCitationRoute"));
        };
        let known = self.compile_known_atomic(citation, &evidence.certificate.fact, position)?;
        let member = self.compile_verify(&evidence.target_membership, position)?;
        let values = args
            .into_iter()
            .chain([target])
            .map(|o| self.compile_function_raw_expression_bound(o, position, &HashMap::new()))
            .collect::<Result<Vec<_>, _>>()?;
        let term = format!(
            "(Litex.bijectiveValue_preimage {} {known} {})",
            values.join(" "),
            member.1
        );
        Ok(if reversed {
            format!("(by\n  have _preimage := {term}\n  constructor\n  · obtain ⟨_x, _hx, _eq⟩ := _preimage.1\n    exact ⟨_x, _hx, _eq.symm⟩\n  · intro _x _hx _z _hz _ex _ez\n    exact _preimage.2 _x _hx _z _hz _ex.symm _ez.symm)")
        } else {
            term
        })
    }
}

fn independent<'a>(
    objects: impl IntoIterator<Item = &'a Obj>,
    bound: &[IdentifierId],
) -> Result<(), LeanCompileError> {
    let mut free = std::collections::HashSet::new();
    for obj in objects {
        crate::instantiate::collect_free_plain_ids(
            obj,
            &std::collections::HashSet::new(),
            &mut free,
        );
    }
    if bound.iter().any(|id| free.contains(id)) {
        return Err(invalid("CapturedBinder"));
    }
    Ok(())
}
