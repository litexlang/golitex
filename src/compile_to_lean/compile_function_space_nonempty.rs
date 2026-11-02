//! Consume original recursive function-space existence certificates.
use super::compile_function_template::function_guard_fact;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::fact::{atomic_fact_has_positive_polarity, negate_atomic_fact};
use crate::execute::execute_fact_stmt::function_domain::{
    FunctionDomainEmptyCarrierEvidence, FunctionDomainEmptyProof, FunctionSpaceNonemptyProof,
};
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

pub(in crate::compile_to_lean) enum FunctionSpaceNonemptyKind {
    FunctionSet,
    FiniteSequence,
    Sequence,
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn checked_space_signature(
        &self,
        carrier: &Obj,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, Option<&'static str>), LeanCompileError> {
        self.validate_function_carrier_signature(carrier, signature)?;
        let ids: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect();
        if ids.iter().collect::<HashSet<_>>().len() != ids.len() {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceNonempty/ParameterIdentity",
            ));
        }
        if let Obj::FunctionSpace(FunctionSpace::FnSet(actual)) = carrier {
            let actual_ids: Vec<_> = actual
                .set_bound_parameters
                .groups
                .iter()
                .flat_map(|g| g.params.iter().map(|p| p.id))
                .collect();
            if actual.ir() != signature.ir()
                || actual_ids != ids
                || actual
                    .dom_facts
                    .iter()
                    .map(function_guard_fact)
                    .collect::<Result<Vec<_>, _>>()?
                    != signature
                        .dom_facts
                        .iter()
                        .map(function_guard_fact)
                        .collect::<Result<Vec<_>, _>>()?
            {
                return Err(LeanCompileError::unsupported(
                    "FunctionSpaceNonempty/OriginalSignature",
                ));
            }
        }
        let object = self.compile_object_reference(carrier, position)?;
        let (compiled, equality) = match carrier {
            Obj::FunctionSpace(FunctionSpace::FnSet(_)) => (format!("({object}).val"), None),
            Obj::SetFormer(SetFormer::SeqSet(_)) => (
                format!("(Litex.seqSignature ({object}).val.carrier)"),
                Some("seqSet_eq_fnSet"),
            ),
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => (
                format!("(Litex.finiteSeqSignature {object})"),
                Some("finiteSeq_eq_fnSet"),
            ),
            Obj::SetFormer(SetFormer::MatrixSet(_)) => (
                format!("(Litex.matrixSignature {object})"),
                Some("matrixSet_eq_fnSet"),
            ),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FunctionSpaceNonempty/Carrier",
                ))
            }
        };
        Ok((object, compiled, equality))
    }

    fn space_nonempty_from_signature(
        &self,
        carrier: &Obj,
        signature: &FnSet,
        proof: &str,
        empty: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (object, compiled, equality) =
            self.checked_space_signature(carrier, signature, position)?;
        let law = if empty {
            "functionSpaceNonemptyOfEmptyDomain"
        } else {
            "functionSpaceNonemptyOfCodomain"
        };
        let term = format!("(Litex.{law} {compiled} {proof})");
        Ok(if let Some(equality) = equality {
            nonempty_transport(&format!("(Litex.{equality} {object})"), &term)
        } else {
            term
        })
    }

    pub(in crate::compile_to_lean) fn compile_function_space_nonempty_strategy(
        &self,
        kind: FunctionSpaceNonemptyKind,
        goal: &AtomicFact,
        signature: &FnSet,
        proof: &FunctionSpaceNonemptyProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::IsNonemptySetFact(goal) = goal else {
            return Err(LeanCompileError::unsupported("FunctionSpaceNonempty/Goal"));
        };
        if !matches!(
            (&kind, &goal.set),
            (
                FunctionSpaceNonemptyKind::FunctionSet,
                Obj::FunctionSpace(FunctionSpace::FnSet(_))
            ) | (
                FunctionSpaceNonemptyKind::FiniteSequence,
                Obj::SetFormer(SetFormer::FiniteSeqSet(_))
            ) | (
                FunctionSpaceNonemptyKind::Sequence,
                Obj::SetFormer(SetFormer::SeqSet(_))
            )
        ) {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceNonempty/SelectedStrategyCarrier",
            ));
        }
        self.checked_space_signature(&goal.set, signature, position)?;
        let child = self.compile_space_nonempty(&signature.ret_set, proof, position)?;
        self.space_nonempty_from_signature(&goal.set, signature, &child, false, position)
    }

    pub(in crate::compile_to_lean) fn compile_function_space_empty_strategy(
        &self,
        goal: &AtomicFact,
        proof: &FunctionDomainEmptyProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::IsNonemptySetFact(goal) = goal else {
            return Err(LeanCompileError::unsupported("FunctionSpaceNonempty/Goal"));
        };
        self.compile_space_empty(&goal.set, proof, position)
    }

    fn compile_space_nonempty(
        &self,
        carrier: &Obj,
        proof: &FunctionSpaceNonemptyProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            FunctionSpaceNonemptyProof::BaseSet(child) => {
                if !matches!(source_subject(child)?, Fact::AtomicFact(AtomicFact::IsNonemptySetFact(f)) if f.set.ir()==carrier.ir())
                {
                    return Err(LeanCompileError::unsupported(
                        "FunctionSpaceNonempty/BaseSubject",
                    ));
                }
                Ok(self
                    .compile_verify(child, &position.atomic_search_verify_prior(child)?)?
                    .1)
            }
            FunctionSpaceNonemptyProof::CarrierTransport {
                carrier: peer,
                carrier_equal,
                nonempty,
            } => {
                if carrier_equal.path.is_empty() {
                    return Err(LeanCompileError::unsupported(
                        "FunctionSpaceNonempty/EmptyTransport",
                    ));
                }
                let same = self.compile_equality_path(carrier, peer, carrier_equal, position)?;
                let child = self.compile_space_nonempty(peer, nonempty, position)?;
                Ok(nonempty_transport(&same, &child))
            }
            FunctionSpaceNonemptyProof::FiniteCartesianProduct {
                cart,
                factors_nonempty,
            } => {
                if !matches!(carrier,Obj::ProductShape(ProductShape::Cart(actual)) if actual.ir()==cart.ir())
                    || cart.args.len() != factors_nonempty.len()
                {
                    return Err(LeanCompileError::unsupported(
                        "FunctionSpaceNonempty/CartesianSubjects",
                    ));
                }
                let children = cart
                    .args
                    .iter()
                    .zip(factors_nonempty)
                    .map(|(factor, child)| self.compile_space_nonempty(factor, child, position))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(format!(
                    "(Litex.cartNonemptyOfFactors {} {})",
                    self.compile_object_reference(carrier, position)?,
                    finite_vector_proof(&children)
                ))
            }
            FunctionSpaceNonemptyProof::ConstantFunction {
                signature,
                return_nonempty,
            } => {
                self.checked_space_signature(carrier, signature, position)?;
                let child =
                    self.compile_space_nonempty(&signature.ret_set, return_nonempty, position)?;
                self.space_nonempty_from_signature(carrier, signature, &child, false, position)
            }
            FunctionSpaceNonemptyProof::EmptyDomain(proof) => {
                self.compile_space_empty(carrier, proof, position)
            }
        }
    }

    fn compile_space_empty(
        &self,
        carrier: &Obj,
        proof: &FunctionDomainEmptyProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let signature = match proof {
            FunctionDomainEmptyProof::ParameterCarrier(p) => &p.signature,
            FunctionDomainEmptyProof::GuardExclusion(p) => &p.signature,
        };
        let (_, compiled, _) = self.checked_space_signature(carrier, signature, position)?;
        let (base, _, guard) = self.space_domain_components(carrier, signature, position)?;
        let excluded = self.compile_empty_signature_domain(
            proof,
            &compiled,
            &base,
            &guard,
            "_space_domain",
            position,
        )?;
        self.space_nonempty_from_signature(carrier, signature, &excluded, true, position)
    }

    /// Eliminate this signature's packed input using the retained absence proof.
    pub(in crate::compile_to_lean) fn compile_empty_signature_domain(
        &self,
        proof: &FunctionDomainEmptyProof,
        compiled: &str,
        base: &str,
        guard: &str,
        input_membership: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let signature = match proof {
            FunctionDomainEmptyProof::ParameterCarrier(p) => &p.signature,
            FunctionDomainEmptyProof::GuardExclusion(p) => &p.signature,
        };
        let values = self.compile_function_packed_values(signature, "_space_input")?;
        let mut members:Vec<_>=(0..values.len()).map(|i| if values.len()==1 {"_space_members".to_string()} else {
                format!("(Litex.FiniteFunction.coordinate_mem_number (M := M) _space_members ({i} : Fin {}) ({} : ℂ) (by norm_num))",values.len(),i+1)
        }).collect();
        let positive = self.compile_function_positive_inputs(signature, position)?;
        let guard_count = positive.len() + signature.dom_facts.len();
        let parameters: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect();
        for (index, parameter) in parameters.iter().enumerate() {
            if let Some(i) = positive.iter().position(|id| *id == parameter.id) {
                let sign = conjunction_projection("_space_guard", i, guard_count);
                members[index] = format!(
                    "((Litex.positiveReal_members (M := M) {}).mpr ⟨{}, {sign}⟩)",
                    values[index], members[index]
                );
            }
        }
        let mut lines=vec![format!("let _space_signature := {compiled}"),
            "intro _space_input _space_domain".into(),
            format!("obtain ⟨_space_members, _space_guard⟩ := (Litex.SetSemantics.sep_members {base} {guard} _space_input).mp {input_membership}")];
        let guards: Vec<_> = (0..signature.dom_facts.len())
            .map(|i| conjunction_projection("_space_guard", positive.len() + i, guard_count))
            .collect();
        lines.push(format!(
            "exact {}",
            self.compile_empty_function_assignment(proof, &values, &members, &guards, position,)?
        ));
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }

    /// Refute one complete input assignment using its original absence certificate.
    /// Callers supply the already-established input memberships and explicit guards.
    pub(in crate::compile_to_lean) fn compile_empty_function_assignment(
        &self,
        proof: &FunctionDomainEmptyProof,
        values: &[String],
        members: &[String],
        guards: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let signature = match proof {
            FunctionDomainEmptyProof::ParameterCarrier(p) => &p.signature,
            FunctionDomainEmptyProof::GuardExclusion(p) => &p.signature,
        };
        let count = signature
            .set_bound_parameters
            .groups
            .iter()
            .map(|group| group.params.len())
            .sum::<usize>();
        if values.len() != count
            || members.len() != count
            || guards.len() != signature.dom_facts.len()
        {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceEmpty/AssignmentArity",
            ));
        }
        let mut lines = Vec::new();
        match proof {
            FunctionDomainEmptyProof::ParameterCarrier(p) => {
                let group = signature
                    .set_bound_parameters
                    .groups
                    .get(p.parameter_group_index)
                    .filter(|g| !g.params.is_empty())
                    .ok_or_else(|| {
                        LeanCompileError::unsupported("FunctionSpaceEmpty/ParameterGroup")
                    })?;
                let offset = signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .take(p.parameter_group_index)
                    .map(|g| g.params.len())
                    .sum::<usize>();
                let value = &values[offset];
                let member = &members[offset];
                let transported = if p.carrier_equal.path.is_empty() {
                    if group.param_type.ir() != p.empty_carrier.ir() {
                        return Err(LeanCompileError::unsupported(
                            "FunctionSpaceEmpty/CarrierIdentity",
                        ));
                    }
                    member.clone()
                } else {
                    let path = self.compile_equality_path(
                        &group.param_type,
                        &p.empty_carrier,
                        &p.carrier_equal,
                        position,
                    )?;
                    format!("(Eq.mp (congrArg (fun _set => M.mem {value} _set) {path}) {member})")
                };
                match &p.evidence {
                    FunctionDomainEmptyCarrierEvidence::EmptyList => {
                        if !matches!(&p.empty_carrier,Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty())
                        {
                            return Err(LeanCompileError::unsupported(
                                "FunctionSpaceEmpty/EmptyList",
                            ));
                        }
                        lines.push(format!(
                            "exact Litex.SetSemantics.empty_members (M := M) {value} {transported}"
                        ));
                    }
                    FunctionDomainEmptyCarrierEvidence::CheckedEquality(child) => {
                        if !p.carrier_equal.path.is_empty()
                            || !matches!(source_subject(child)?,Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==p.empty_carrier.ir() && matches!(&f.right,Obj::SetFormer(SetFormer::ListSet(s)) if s.list.is_empty()))
                        {
                            return Err(LeanCompileError::unsupported(
                                "FunctionSpaceEmpty/EqualitySubject",
                            ));
                        }
                        let same = self
                            .compile_verify(
                                child,
                                &position.function_domain_empty_verify_prior(child)?,
                            )?
                            .1;
                        lines.push(format!("exact Litex.SetSemantics.empty_members (M := M) {value} (Eq.mp (congrArg (fun _set => M.mem {value} _set) {same}) {transported})"));
                    }
                    FunctionDomainEmptyCarrierEvidence::EmptyIntegerRange => {
                        let (start, end, half) = match &p.empty_carrier {
                            Obj::SetFormer(SetFormer::Range(r)) => (&r.start, &r.end, true),
                            Obj::SetFormer(SetFormer::ClosedRange(r)) => (&r.start, &r.end, false),
                            _ => {
                                return Err(LeanCompileError::unsupported(
                                    "FunctionSpaceEmpty/RangeSubject",
                                ))
                            }
                        };
                        let literal = |x: &Obj| match x {
                            Obj::Literal(Literal::Number(n)) => {
                                n.normalized_value.parse::<i128>().ok()
                            }
                            _ => None,
                        };
                        let (Some(a), Some(b)) = (literal(start), literal(end)) else {
                            return Err(LeanCompileError::unsupported(
                                "FunctionSpaceEmpty/IntegerEndpoints",
                            ));
                        };
                        if if half { a < b } else { a <= b } {
                            return Err(LeanCompileError::unsupported(
                                "FunctionSpaceEmpty/NonemptyRange",
                            ));
                        }
                        let law = if half {
                            "noMemIntegerRange"
                        } else {
                            "noMemClosedIntegerRange"
                        };
                        lines.push(format!("exact Litex.{law} (M := M) ({a} : ℂ) ({b} : ℂ) ({a} : ℤ) ({b} : ℤ) (by norm_num) (by norm_num) (by norm_num) {value} {transported}"));
                    }
                }
            }
            FunctionDomainEmptyProof::GuardExclusion(p) => {
                let Fact::ForallFact(fact) = source_subject(&p.exclusion)? else {
                    return Err(LeanCompileError::unsupported(
                        "FunctionSpaceEmpty/ExclusionFamily",
                    ));
                };
                let original_guard =
                    validate_guard_exclusion(signature, p.excluded_guard_index, &fact)?;
                let prior = position.function_domain_empty_verify_prior(&p.exclusion)?;
                let local = SourcePosition::new(Some(&prior), SourceOwner::Term, 0);
                let checked = self.compile_verify(&p.exclusion, &local)?;
                let mut arguments = Vec::new();
                for (value, member) in values.iter().zip(members) {
                    arguments.push(format!(
                        "(Litex.semanticObject (M := M) {value} (M.member_isSet {member}))"
                    ));
                    arguments.push(member.clone());
                }
                arguments.extend(
                    guards
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != p.excluded_guard_index)
                        .map(|(_, g)| g.clone()),
                );
                let params: Vec<_> = signature
                    .set_bound_parameters
                    .groups
                    .iter()
                    .flat_map(|g| &g.params)
                    .collect();
                let bindings: HashMap<_, _> = params
                    .iter()
                    .zip(values)
                    .map(|(p, v)| (p.id, v.clone()))
                    .collect();
                let raw =
                    self.compile_function_raw_predicate(&original_guard, position, &bindings)?;
                lines.push(format!(
                    "have _space_exclusion_proof : {} := {}",
                    checked.0, checked.1
                ));
                lines.push(format!(
                    "have _space_exclusion := _space_exclusion_proof {}",
                    arguments.join(" ")
                ));
                lines.push(format!(
                    "have _space_excluded : {raw} := {}",
                    guards[p.excluded_guard_index]
                ));
                let Fact::AtomicFact(original_guard) = original_guard else {
                    unreachable!()
                };
                lines.push(if atomic_fact_has_positive_polarity(&original_guard) {
                    "exact _space_exclusion _space_excluded".into()
                } else {
                    "exact _space_excluded _space_exclusion".into()
                });
            }
        }
        Ok(format!(
            "(by\n  {}\n)",
            lines.join("\n").replace('\n', "\n  ")
        ))
    }

    pub(in crate::compile_to_lean) fn space_domain_components(
        &self,
        carrier: &Obj,
        signature: &FnSet,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, String), LeanCompileError> {
        if matches!(carrier, Obj::FunctionSpace(FunctionSpace::FnSet(_))) {
            let (base, sets) = self.compile_function_semantic_base_domain(signature, position)?;
            return Ok((
                base,
                sets,
                self.compile_function_packed_guard_template(signature, position)?,
            ));
        }
        let object = self.compile_object_reference(carrier, position)?;
        let dimensions = match carrier {
            Obj::SetFormer(SetFormer::FiniteSeqSet(_)) => vec![format!("({object}).val.length")],
            Obj::SetFormer(SetFormer::MatrixSet(_)) => vec![
                format!("({object}).val.rows"),
                format!("({object}).val.cols"),
            ],
            Obj::SetFormer(SetFormer::SeqSet(_)) => {
                let base = "(Litex.denote (Litex.NPos (M := M)))".to_string();
                return Ok((
                    base,
                    "(Litex.isSet (Litex.NPos (M := M)))".into(),
                    "(fun _ => True)".into(),
                ));
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FunctionSpaceEmpty/DomainWrapper",
                ))
            }
        };
        let inputs:Vec<_>=dimensions.iter().map(|d|format!("(Litex.SetSemantics.sepValue (M := M) (M.standard .integer) (Litex.ClosedRangeObj.condition ⟨Litex.number 1, {d}⟩))")).collect();
        let sets: Vec<_> = dimensions.iter().map(|d| format!(
            "(Litex.SetSemantics.sep_isSet (M.standard .integer) (Litex.ClosedRangeObj.condition ⟨Litex.number 1, {d}⟩) (M.standard_isSet .integer))"
        )).collect();
        let (base, proof) = if inputs.len() == 1 {
            (inputs[0].clone(), sets[0].clone())
        } else {
            let vector = format!("![{}]", inputs.join(", "));
            (
                format!("(Litex.FiniteFunction.cartValue {vector})"),
                format!(
                    "(Litex.FiniteFunction.cart_isSet {vector} {})",
                    finite_vector_proof(&sets)
                ),
            )
        };
        Ok((base, proof, "(fun _ => True)".into()))
    }
}

fn nonempty_transport(same: &str, child: &str) -> String {
    format!("(Eq.mp (congrArg (fun _set => ∃ _member : M.Value, M.mem _member _set) ({same}).symm) {child})")
}

fn validate_guard_exclusion(
    signature: &FnSet,
    index: usize,
    fact: &ForallFact,
) -> Result<Fact, LeanCompileError> {
    let Some(QuantifierFreeFact::AtomicFact(excluded)) = signature.dom_facts.get(index) else {
        return Err(LeanCompileError::unsupported(
            "FunctionSpaceEmpty/ExcludedGuard",
        ));
    };
    if fact.typed_parameters.groups.len() != signature.set_bound_parameters.groups.len()
        || fact.dom_facts.len() + 1 != signature.dom_facts.len()
        || fact.then_facts.len() != 1
    {
        return Err(LeanCompileError::unsupported(
            "FunctionSpaceEmpty/ExclusionStages",
        ));
    }
    let mut substitution = HashMap::new();
    let mut fresh = HashSet::new();
    for (original, actual) in signature
        .set_bound_parameters
        .groups
        .iter()
        .zip(&fact.typed_parameters.groups)
    {
        if original.params.len() != actual.params.len()
            || !matches!(&actual.param_type,ParamType::Obj(c) if instantiated_object_matches(&original.param_type,c,&substitution))
        {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceEmpty/ExclusionParameters",
            ));
        }
        for (from, to) in original.params.iter().zip(&actual.params) {
            if !fresh.insert(to.id)
                || substitution
                    .insert(from.id, Obj::Identifier(IdentifierObj::from_bound_name(to)))
                    .is_some()
            {
                return Err(LeanCompileError::unsupported(
                    "FunctionSpaceEmpty/ExclusionIdentity",
                ));
            }
        }
    }
    let ExistOrAndChainAtomicFact::AtomicFact(conclusion) = &fact.then_facts[0] else {
        return Err(LeanCompileError::unsupported(
            "FunctionSpaceEmpty/ExclusionConclusion",
        ));
    };
    let negative = negate_atomic_fact(excluded, conclusion.fact_id())
        .ok_or_else(|| LeanCompileError::unsupported("FunctionSpaceEmpty/NegatedGuard"))?;
    if !instantiated_fact_matches(
        &Fact::AtomicFact(negative),
        &Fact::AtomicFact(conclusion.clone()),
        &substitution,
    ) {
        return Err(LeanCompileError::unsupported(
            "FunctionSpaceEmpty/ExclusionConclusion",
        ));
    }
    for (source, actual) in signature
        .dom_facts
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != index)
        .map(|(_, f)| f)
        .zip(&fact.dom_facts)
    {
        if !instantiated_fact_matches(&function_guard_fact(source)?, actual, &substitution) {
            return Err(LeanCompileError::unsupported(
                "FunctionSpaceEmpty/OtherGuards",
            ));
        }
    }
    Ok(Fact::AtomicFact(excluded.clone()))
}
