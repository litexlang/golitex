//! Replay the seven upper/lower certificate contracts from real_analysis.rs.
use super::compile_real_extrema::{
    certificate_matches, is_real_subset, validate_extremum_existence,
};
use super::compile_real_set_bounds::{contains_parameter, parameter, validate_bound};
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TheoremCall;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    BuiltinFunctionDomainProof, BuiltinThmApplication, TheoremDerivationProof,
};
use crate::prelude::*;

#[derive(Clone, Copy)]
enum Rule {
    Definition,
    Projection,
    Exists,
    Unique,
    Crosses,
    Member,
    CompareBound,
}

impl LitexToLeanCompiler {
    pub(super) fn compile_builtin_extremum_certificate_theorem(
        &self,
        call: &TheoremCall,
        builtin: &BuiltinThmApplication,
        derivation: &TheoremDerivationProof,
        type_proofs: &[VerifyFactResult],
        type_stores: &[StoreFactAndInferResult],
        function_domain: Option<&BuiltinFunctionDomainProof>,
        dom_proofs: &[VerifyFactResult],
        dom_stores: &[StoreFactAndInferResult],
        conclusions_wd: &[FactWellDefinedProof],
        position: &SourcePosition<'_>,
    ) -> Result<(Vec<String>, String, Vec<Fact>), LeanCompileError> {
        use BuiltinTheoremId::*;
        let (upper, rule) = match builtin.theorem {
            RealLeastUpperBoundFromDefinition => (true, Rule::Definition),
            RealGreatestLowerBoundFromDefinition => (false, Rule::Definition),
            RealLeastUpperBoundUpperBound => (true, Rule::Projection),
            RealGreatestLowerBoundLowerBound => (false, Rule::Projection),
            RealLeastUpperBoundExists => (true, Rule::Exists),
            RealGreatestLowerBoundExists => (false, Rule::Exists),
            RealLeastUpperBoundUnique => (true, Rule::Unique),
            RealGreatestLowerBoundUnique => (false, Rule::Unique),
            RealLeastUpperBoundCrosses => (true, Rule::Crosses),
            RealGreatestLowerBoundCrosses => (false, Rule::Crosses),
            RealMemberLeLeastUpperBound => (true, Rule::Member),
            RealGreatestLowerBoundLeMember => (false, Rule::Member),
            RealLeastUpperBoundLeUpperBound => (true, Rule::CompareBound),
            RealLowerBoundLeGreatestLowerBound => (false, Rule::CompareBound),
            _ => return Err(invalid("Id")),
        };
        let (arity, count, suffix) = match rule {
            Rule::Definition => (2, 5, "FromDefinition"),
            Rule::Projection => (2, 3, if upper { "UpperBound" } else { "LowerBound" }),
            Rule::Exists => (2, 4, "Exists"),
            Rule::Unique => (3, 5, "Unique"),
            Rule::Crosses => (3, 5, "Crosses"),
            Rule::Member => (3, 4, "Member"),
            Rule::CompareBound => (3, 5, "CompareBound"),
        };
        let TheoremCallArguments::Parenthesized(args) = &call.arguments else {
            return Err(invalid("Arguments"));
        };
        if !matches!(derivation, TheoremDerivationProof::NativeSchema)
            || !type_proofs.is_empty()
            || !type_stores.is_empty()
            || function_domain.is_some()
            || !matches!(&call.name, AtomicName::Plain { name } if name == builtin.theorem.as_str())
            || args != &builtin.arguments
            || args.len() != arity
            || builtin.requirements.len() != count
            || dom_proofs.len() != count
            || dom_stores.len() != count
            || builtin.conclusions.len() != 1
            || conclusions_wd.len() != 1
        {
            return Err(invalid("Stages"));
        }
        let (set, b) = (&args[0], &args[1]);
        let real = Obj::StandardSet(StandardSet::R);
        let direction = if upper {
            RealBoundDirection::Upper
        } else {
            RealBoundDirection::Lower
        };
        let name = if upper { "supremum" } else { "infimum" };
        let title = if upper {
            "LeastUpperBound"
        } else {
            "GreatestLowerBound"
        };
        let req = &builtin.requirements;
        let goal = &builtin.conclusions[0];
        if !is_real_subset(&req[0], set) || !member(&req[1], b, &real) {
            return Err(invalid("Carrier"));
        }
        // Only the schema's fresh internal binders are specialized to M.Value's universe.
        // Source object parameters retain their original host representations.
        let mut universe_binders: Vec<(usize, IdentifierId)> = Vec::new();
        match rule {
            Rule::Definition | Rule::Exists => {
                if !matches!(&req[2], Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir() == set.ir())
                {
                    return Err(invalid("Nonempty"));
                }
                universe_binders.push((3, validate_bound(set, b, direction, &req[3])?.id));
                if matches!(rule, Rule::Definition) {
                    let Fact::ForallFact(ext) = &req[4] else {
                        return Err(invalid("Extremality"));
                    };
                    let p = parameter(&ext.typed_parameters, &real)?;
                    let c = Obj::Identifier(IdentifierObj::from_bound_name(p));
                    let [bound] = ext.dom_facts.as_slice() else {
                        return Err(invalid("ExtremalityDomain"));
                    };
                    let inner = validate_bound(set, &c, direction, bound)?;
                    if contains_parameter(set, p.id)
                        || contains_parameter(b, p.id)
                        || contains_parameter(b, inner.id)
                        || !matches!(ext.then_facts.as_slice(), [ExistOrAndChainAtomicFact::AtomicFact(f)] if order(f, b, &c, upper, false))
                    {
                        return Err(invalid("ExtremalityConclusion"));
                    }
                    universe_binders.push((4, p.id));
                    if !certificate(goal, name, set, b) {
                        return Err(invalid("CertificateConclusion"));
                    }
                } else {
                    validate_extremum_existence(goal, name, set)?;
                }
            }
            _ => {
                if !certificate(&req[2], name, set, b) {
                    return Err(invalid("CertificatePremise"));
                }
                if matches!(rule, Rule::Projection) {
                    validate_bound(set, b, direction, goal)?;
                } else {
                    let c = &args[2];
                    if !member(
                        &req[3],
                        c,
                        if matches!(rule, Rule::Member) {
                            set
                        } else {
                            &real
                        },
                    ) {
                        return Err(invalid("ThirdArgumentCarrier"));
                    }
                    match rule {
                        Rule::Unique => {
                            if !certificate(&req[4], name, set, c)
                                || !matches!(goal, Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir() == b.ir() && f.right.ir() == c.ir())
                            {
                                return Err(invalid("Uniqueness"));
                            }
                        }
                        Rule::Crosses => {
                            if !matches!(&req[4], Fact::AtomicFact(f) if order(f, c, b, upper, true))
                            {
                                return Err(invalid("StrictComparison"));
                            }
                            let Fact::ExistFact(e) = goal else {
                                return Err(invalid("CrossingExistence"));
                            };
                            let p = parameter(&e.typed_parameters, set)?;
                            let z = Obj::Identifier(IdentifierObj::from_bound_name(p));
                            if args.iter().any(|o| contains_parameter(o, p.id))
                                || !matches!(e.facts.as_slice(), [QuantifierFreeFact::AtomicFact(f)] if order(f, c, &z, upper, true))
                            {
                                return Err(invalid("CrossingConclusion"));
                            }
                        }
                        Rule::Member => {
                            if !matches!(goal, Fact::AtomicFact(f) if order(f, c, b, upper, false))
                            {
                                return Err(invalid("MemberConclusion"));
                            }
                        }
                        Rule::CompareBound => {
                            universe_binders
                                .push((4, validate_bound(set, c, direction, &req[4])?.id));
                            if !matches!(goal, Fact::AtomicFact(f) if order(f, b, c, upper, false))
                            {
                                return Err(invalid("BoundConclusion"));
                            }
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
        let mut definitions = Vec::new();
        let mut references = Vec::new();
        for (index, ((requirement, proof), store)) in
            req.iter().zip(dom_proofs).zip(dom_stores).enumerate()
        {
            if source_subject(proof)? != *requirement {
                return Err(invalid("PremiseSubject"));
            }
            self.validate_store(&store.store, requirement)?;
            let prior = SourcePosition {
                before: index,
                ..*position
            };
            let mut compiled = self.compile_verify(proof, &prior)?;
            for (_, id) in universe_binders.iter().filter(|(stage, _)| *stage == index) {
                for universe in [format!("v{}", id.value()), "_".to_string()] {
                    let binder = format!("_Host_i{} : Type {universe}}}", id.value());
                    let semantic = format!("_Host_i{} : Type u}}", id.value());
                    compiled.0 = compiled.0.replace(&binder, &semantic);
                    compiled.1 = compiled.1.replace(&binder, &semantic);
                }
            }
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
            let reference = format!("h_{}", requirement.fact_id().value());
            definitions.extend(self.compile_stored_inferences(
                store,
                requirement,
                &(compiled.0, reference.clone()),
                &SourcePosition {
                    before: index + 1,
                    ..*position
                },
            )?);
            references.push(reference);
        }
        let formed = SourcePosition {
            before: count,
            ..*position
        };
        let wd = &conclusions_wd[0];
        self.compile_fact_wd(wd, goal, &formed)?;
        let scope = SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
        let statement = self.compile_formed_fact_proposition(wd, goal, &formed)?;
        let objects = args
            .iter()
            .map(|a| self.compile_object_reference(a, &scope))
            .collect::<Result<Vec<_>, _>>()?;
        if matches!(rule, Rule::Definition) {
            // The recorded leastness proof accepts a source forall. Project the
            // semantic bound to precisely that forall; its carrier level is
            // inferred from the recorded proof, not forced to the model level.
            references[4] = format!("(by intro _Host _rep c hc bound; exact {} c hc (by intro _X _rx x hx; exact bound (Litex.denote x) hx))", references[4]);
        }
        let law = format!(
            "(Litex.real{title}{suffix} {} {})",
            objects.join(" "),
            references.join(" ")
        );
        let term = if matches!(rule, Rule::Projection) {
            format!("(by intro _Host _rep x hx; exact ({law} (Litex.denote x) hx))")
        } else {
            law
        };
        Ok((
            definitions,
            format!("(show {statement} from {term})"),
            builtin.conclusions.clone(),
        ))
    }
}

fn member(fact: &Fact, value: &Obj, set: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == value.ir() && f.set.ir() == set.ir())
}
fn certificate(fact: &Fact, name: &str, set: &Obj, value: &Obj) -> bool {
    matches!(fact, Fact::AtomicFact(AtomicFact::NormalAtomicFact(f)) if certificate_matches(f, name, set) && f.body[1].ir() == value.ir())
}
fn order(fact: &AtomicFact, a: &Obj, b: &Obj, forward: bool, strict: bool) -> bool {
    let (left, right) = if forward { (a, b) } else { (b, a) };
    match (fact, strict) {
        (AtomicFact::LessFact(f), true) => f.left.ir() == left.ir() && f.right.ir() == right.ir(),
        (AtomicFact::LessEqualFact(f), false) => {
            f.left.ir() == left.ir() && f.right.ir() == right.ir()
        }
        _ => false,
    }
}
fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::new(&format!("ExtremumCertificate/{stage}"),
        "Extremal-certificate evidence differs in its ID, ordered premises, bound, binder or conclusion.")
}
