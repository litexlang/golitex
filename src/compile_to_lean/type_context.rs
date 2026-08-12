use std::collections::HashMap;

use crate::prelude::*;

use super::helper::lean_generic_carrier_name;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct LeanWellDefinednessTargetRequirementKey {
    source_object_key: String,
    role: WellDefinednessRequirementRole,
    proposition: String,
}

#[derive(Clone, Default)]
pub(super) struct LeanWellDefinednessContext {
    proof_names_by_proposition: HashMap<String, String>,
    /// Membership binders may be re-created with alpha-renamed nested
    /// SetBuilder/FnSet parameters during verifier proof search. Retain their
    /// structural objects so exact alpha-equivalent reuse does not depend on a
    /// display string or a preflight FactId.
    membership_proofs: Vec<(Obj, Obj, String)>,
    proof_names_by_certificate_id: HashMap<WellDefinednessCertificateId, String>,
    certificate_ids_by_proposition: HashMap<String, Vec<WellDefinednessCertificateId>>,
    target_requirement_ids:
        HashMap<LeanWellDefinednessTargetRequirementKey, Vec<WellDefinednessCertificateId>>,
}

#[derive(Clone, Default)]
pub(super) struct LeanTypeContext {
    symbol_carriers: HashMap<SymbolId, LitexToLeanCarrierIr>,
    object_expectations: HashMap<String, LitexToLeanCarrierIr>,
    generic_carrier_aliases: HashMap<SymbolId, SymbolId>,
    well_definedness: LeanWellDefinednessContext,
}

impl LeanTypeContext {
    pub(super) fn insert(&mut self, symbol_id: SymbolId, carrier: LitexToLeanCarrierIr) {
        self.symbol_carriers.insert(symbol_id, carrier);
    }

    pub(super) fn insert_param(
        &mut self,
        symbol_id: SymbolId,
        param_type: &LitexToLeanParameterTypeIr,
    ) {
        let carrier = match param_type {
            LitexToLeanParameterTypeIr::Set { element_carrier }
            | LitexToLeanParameterTypeIr::NonemptySet { element_carrier }
            | LitexToLeanParameterTypeIr::FiniteSet { element_carrier } => {
                LitexToLeanCarrierIr::Set {
                    element_carrier: Box::new(element_carrier.clone()),
                }
            }
            LitexToLeanParameterTypeIr::MemberOf {
                element_carrier, ..
            } => element_carrier.clone(),
            LitexToLeanParameterTypeIr::Unsupported(_) => return,
        };
        self.insert(symbol_id, carrier);
    }

    pub(super) fn symbol_carrier(&self, symbol_id: SymbolId) -> Option<&LitexToLeanCarrierIr> {
        self.symbol_carriers.get(&symbol_id)
    }

    pub(super) fn expect_object(&mut self, object: &Obj, carrier: LitexToLeanCarrierIr) {
        self.object_expectations
            .entry(obj_equality_key(object))
            .or_insert(carrier);
    }

    pub(super) fn expected_object(&self, object: &Obj) -> Option<&LitexToLeanCarrierIr> {
        self.object_expectations.get(&obj_equality_key(object))
    }

    pub(super) fn insert_well_definedness_proof(&mut self, proposition: &Fact, name: String) {
        if let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition {
            if let Some(existing) =
                self.well_definedness
                    .membership_proofs
                    .iter_mut()
                    .find(|(element, set, _)| {
                        obj_equality_key(element) == obj_equality_key(&membership.element)
                            && obj_equality_key(set) == obj_equality_key(&membership.set)
                    })
            {
                existing.2 = name.clone();
            } else {
                self.well_definedness.membership_proofs.push((
                    membership.element.clone(),
                    membership.set.clone(),
                    name.clone(),
                ));
            }
        }
        let proposition = proposition.to_string();
        self.well_definedness
            .proof_names_by_proposition
            .insert(proposition.clone(), name.clone());
        if let Some(certificate_ids) = self
            .well_definedness
            .certificate_ids_by_proposition
            .get(&proposition)
        {
            for certificate_id in certificate_ids {
                self.well_definedness
                    .proof_names_by_certificate_id
                    .insert(*certificate_id, name.clone());
            }
        }
    }

    /// Register a source parameter-membership proof together with the
    /// predicate that Lean obtains by reducing a refined standard set.
    ///
    /// For example, a binder proof of `b ∈ Z*` is definitionally also a proof
    /// of `b ≠ 0` in the emitted Lean type. This is not backend proof search:
    /// it is the checked source parameter proof, reused under the exact
    /// definition chosen for that source set.
    pub(super) fn insert_parameter_well_definedness_proof(
        &mut self,
        proposition: &Fact,
        name: String,
    ) {
        self.insert_well_definedness_proof(proposition, name.clone());
        for consequence in refined_parameter_membership_consequences(proposition) {
            self.insert_well_definedness_proof(&consequence, name.clone());
        }
    }

    pub(super) fn well_definedness_proof(&self, proposition: &Fact) -> Option<&str> {
        self.well_definedness
            .proof_names_by_proposition
            .get(&proposition.to_string())
            .map(String::as_str)
    }

    pub(super) fn alpha_equivalent_membership_proof(
        &self,
        element: &Obj,
        set: &Obj,
    ) -> Option<&str> {
        self.well_definedness
            .membership_proofs
            .iter()
            .rev()
            .find(|(candidate_element, candidate_set, _)| {
                objs_equal_with_nested_binder_alpha_equivalence(candidate_element, element)
                    && objs_equal_with_nested_binder_alpha_equivalence(candidate_set, set)
            })
            .map(|(_, _, name)| name.as_str())
    }

    pub(super) fn insert_well_definedness_proof_by_certificate_id(
        &mut self,
        certificate_id: WellDefinednessCertificateId,
        proposition: &Fact,
        name: String,
    ) {
        self.insert_well_definedness_proof(proposition, name.clone());
        self.well_definedness
            .proof_names_by_certificate_id
            .insert(certificate_id, name);
    }

    pub(super) fn install_well_definedness_certificate_metadata(
        &mut self,
        certificate: &LitexToLeanWellDefinednessCertificateIr,
    ) {
        for evidence in certificate.facts.iter() {
            let ids = self
                .well_definedness
                .certificate_ids_by_proposition
                .entry(evidence.expected_proposition.to_string())
                .or_default();
            if !ids.contains(&evidence.certificate_id) {
                ids.push(evidence.certificate_id);
            }
        }
        for requirement in certificate.target_requirements.iter() {
            let key = LeanWellDefinednessTargetRequirementKey {
                source_object_key: obj_equality_key(&requirement.source_object),
                role: requirement.role,
                proposition: requirement.expected_proposition.to_string(),
            };
            let ids = self
                .well_definedness
                .target_requirement_ids
                .entry(key)
                .or_default();
            if !ids.contains(&requirement.certificate_id) {
                ids.push(requirement.certificate_id);
            }
        }
    }

    pub(super) fn function_requirement_proof(
        &self,
        source_application: &Obj,
        role: WellDefinednessRequirementRole,
        proposition: &Fact,
    ) -> Result<(WellDefinednessCertificateId, &str), String> {
        let key = LeanWellDefinednessTargetRequirementKey {
            source_object_key: obj_equality_key(source_application),
            role,
            proposition: proposition.to_string(),
        };
        let Some(certificate_ids) = self.well_definedness.target_requirement_ids.get(&key) else {
            return Err(format!(
                "missing an exact retained WD requirement reference for `{}`",
                proposition
            ));
        };
        let mut replayed = certificate_ids.iter().filter_map(|certificate_id| {
            self.well_definedness
                .proof_names_by_certificate_id
                .get(certificate_id)
                .map(|name| (*certificate_id, name.as_str()))
        });
        let Some(first) = replayed.next() else {
            return Err(format!(
                "retained WD requirement reference for `{}` has not been replayed in this Lean scope",
                proposition
            ));
        };
        for candidate in replayed {
            if candidate.1 != first.1 {
                return Err(format!(
                    "multiple checked occurrences of `{}` retain different WD proof terms for `{}`; exact occurrence identity is required",
                    source_application, proposition
                ));
            }
        }
        Ok(first)
    }

    pub(super) fn replace_well_definedness_context(
        &mut self,
        context: LeanWellDefinednessContext,
    ) -> LeanWellDefinednessContext {
        std::mem::replace(&mut self.well_definedness, context)
    }

    pub(super) fn unify_generic_carriers(
        &mut self,
        left: &LitexToLeanCarrierIr,
        right: &LitexToLeanCarrierIr,
    ) -> Result<(), String> {
        let left = self.resolve_carrier(left)?;
        let right = self.resolve_carrier(right)?;
        match (left, right) {
            (
                LitexToLeanCarrierIr::Generic {
                    anchor: left_anchor,
                },
                LitexToLeanCarrierIr::Generic {
                    anchor: right_anchor,
                },
            ) if left_anchor != right_anchor => {
                let (canonical, alias) = if left_anchor < right_anchor {
                    (left_anchor, right_anchor)
                } else {
                    (right_anchor, left_anchor)
                };
                self.generic_carrier_aliases.insert(alias, canonical);
            }
            (
                LitexToLeanCarrierIr::Set {
                    element_carrier: left,
                },
                LitexToLeanCarrierIr::Set {
                    element_carrier: right,
                },
            ) => self.unify_generic_carriers(&left, &right)?,
            _ => {}
        }
        Ok(())
    }

    pub(super) fn object_carrier(
        &self,
        object: &LitexToLeanObjectIr,
    ) -> Result<Option<LitexToLeanCarrierIr>, String> {
        match object {
            LitexToLeanObjectIr::Symbol { symbol_id, .. } => {
                Ok(self.symbol_carrier(*symbol_id).cloned())
            }
            LitexToLeanObjectIr::Number { .. } => Ok(None),
            LitexToLeanObjectIr::Constant(constant) => Ok(Some(match constant {
                LitexToLeanConstantObjectIr::ImaginaryUnit => LitexToLeanCarrierIr::Complex,
                LitexToLeanConstantObjectIr::EulerNumber | LitexToLeanConstantObjectIr::Pi => {
                    LitexToLeanCarrierIr::Real
                }
            })),
            LitexToLeanObjectIr::StandardSet(set) => Ok(Some(LitexToLeanCarrierIr::Set {
                element_carrier: Box::new(set.element_carrier()),
            })),
            LitexToLeanObjectIr::FunctionSet { function } => Ok(Some(LitexToLeanCarrierIr::Set {
                element_carrier: Box::new(LitexToLeanCarrierIr::Function {
                    function: function.clone(),
                }),
            })),
            LitexToLeanObjectIr::SetBuilder(builder) => Ok(Some(LitexToLeanCarrierIr::Set {
                element_carrier: Box::new(builder.element_carrier.clone()),
            })),
            LitexToLeanObjectIr::AnonymousFunction(function) => {
                Ok(Some(LitexToLeanCarrierIr::Function {
                    function: Box::new(function.function.clone()),
                }))
            }
            LitexToLeanObjectIr::FunctionApplication(application) => {
                self.function_application_result_carrier(application)
            }
            LitexToLeanObjectIr::BuiltinApp {
                operator,
                arguments,
            } => self.builtin_result_carrier(*operator, arguments),
            LitexToLeanObjectIr::Collection {
                constructor: LitexToLeanCollectionObjectIr::ListSet,
                items,
            } => Ok(self.join_object_carriers(items)?.map(|element_carrier| {
                LitexToLeanCarrierIr::Set {
                    element_carrier: Box::new(element_carrier),
                }
            })),
        }
    }

    pub(super) fn membership_element_carrier(
        &self,
        set: &LitexToLeanObjectIr,
    ) -> Result<LitexToLeanCarrierIr, String> {
        if let LitexToLeanObjectIr::StandardSet(standard) = set {
            return Ok(standard.element_carrier());
        }
        match self.object_carrier(set)? {
            Some(LitexToLeanCarrierIr::Set { element_carrier }) => Ok(*element_carrier),
            Some(other) => Err(format!(
                "Litex-to-Lean membership set has non-set target carrier {:?}",
                other
            )),
            None => Ok(LitexToLeanCarrierIr::ElementOfSet {
                set: Box::new(set.clone()),
            }),
        }
    }

    pub(super) fn resolve_carrier(
        &self,
        carrier: &LitexToLeanCarrierIr,
    ) -> Result<LitexToLeanCarrierIr, String> {
        self.resolve_carrier_with_depth(carrier, 0)
    }

    fn resolve_carrier_with_depth(
        &self,
        carrier: &LitexToLeanCarrierIr,
        depth: usize,
    ) -> Result<LitexToLeanCarrierIr, String> {
        if depth > 32 {
            return Err("Litex-to-Lean carrier constraints contain a cycle".to_string());
        }
        match carrier {
            LitexToLeanCarrierIr::ElementOfSet { set } => {
                let element = self.membership_element_carrier(set)?;
                self.resolve_carrier_with_depth(&element, depth + 1)
            }
            LitexToLeanCarrierIr::Set { element_carrier } => Ok(LitexToLeanCarrierIr::Set {
                element_carrier: Box::new(
                    self.resolve_carrier_with_depth(element_carrier, depth + 1)?,
                ),
            }),
            LitexToLeanCarrierIr::Function { function } => {
                let mut resolved = function.as_ref().clone();
                for parameter in resolved.parameters.iter_mut() {
                    parameter.element_carrier =
                        self.resolve_carrier_with_depth(&parameter.element_carrier, depth + 1)?;
                }
                resolved.return_carrier =
                    Box::new(self.resolve_carrier_with_depth(&resolved.return_carrier, depth + 1)?);
                Ok(LitexToLeanCarrierIr::Function {
                    function: Box::new(resolved),
                })
            }
            LitexToLeanCarrierIr::Generic { anchor } => {
                let Some(canonical) = self.generic_carrier_aliases.get(anchor).copied() else {
                    return Ok(carrier.clone());
                };
                self.resolve_carrier_with_depth(
                    &LitexToLeanCarrierIr::Generic { anchor: canonical },
                    depth + 1,
                )
            }
            other => Ok(other.clone()),
        }
    }

    pub(super) fn lean_type(&self, carrier: &LitexToLeanCarrierIr) -> Result<String, String> {
        match self.resolve_carrier(carrier)? {
            LitexToLeanCarrierIr::Natural => Ok("ℕ".to_string()),
            LitexToLeanCarrierIr::Integer => Ok("ℤ".to_string()),
            LitexToLeanCarrierIr::Rational => Ok("ℚ".to_string()),
            LitexToLeanCarrierIr::Real => Ok("ℝ".to_string()),
            LitexToLeanCarrierIr::Complex => Ok("ℂ".to_string()),
            LitexToLeanCarrierIr::Generic { anchor } => {
                Ok(lean_generic_carrier_name(anchor.value()))
            }
            LitexToLeanCarrierIr::Set { element_carrier } => {
                Ok(format!("Set {}", self.lean_type(&element_carrier)?))
            }
            LitexToLeanCarrierIr::Function { function } => {
                super::pipeline::lean_function_type_with_context(&function, self)
                    .map_err(|error| error.trace_message())
            }
            LitexToLeanCarrierIr::ElementOfSet { .. } => {
                Err("Litex-to-Lean could not resolve a set's element carrier".to_string())
            }
        }
    }

    pub(super) fn joined_numeric_carrier(
        &self,
        objects: &[&LitexToLeanObjectIr],
    ) -> Result<Option<LitexToLeanCarrierIr>, String> {
        let mut joined = None;
        for object in objects {
            for carrier in self.fixed_numeric_carriers(object)? {
                joined = Some(match joined {
                    None => carrier,
                    Some(current) => join_numeric_carriers(&current, &carrier)?,
                });
            }
        }
        Ok(joined)
    }

    pub(super) fn needs_numeric_expectation(
        &self,
        object: &LitexToLeanObjectIr,
        expected: &LitexToLeanCarrierIr,
    ) -> Result<bool, String> {
        let expected = self.resolve_carrier(expected)?;
        let Some(expected_rank) = numeric_rank(&expected) else {
            return Ok(false);
        };
        for carrier in self.fixed_numeric_carriers(object)? {
            let carrier = self.resolve_carrier(&carrier)?;
            let Some(rank) = numeric_rank(&carrier) else {
                return Err(format!(
                    "Litex-to-Lean cannot coerce nonnumeric carrier {:?} into {:?}",
                    carrier, expected
                ));
            };
            if rank > expected_rank {
                return Err(format!(
                    "Litex-to-Lean does not insert a numeric downcast from {:?} to {:?}",
                    carrier, expected
                ));
            }
            if carrier != expected {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn fixed_numeric_carriers(
        &self,
        object: &LitexToLeanObjectIr,
    ) -> Result<Vec<LitexToLeanCarrierIr>, String> {
        let mut result = Vec::new();
        self.collect_fixed_numeric_carriers(object, &mut result)?;
        Ok(result)
    }

    fn collect_fixed_numeric_carriers(
        &self,
        object: &LitexToLeanObjectIr,
        result: &mut Vec<LitexToLeanCarrierIr>,
    ) -> Result<(), String> {
        match object {
            LitexToLeanObjectIr::Symbol { symbol_id, .. } => {
                if let Some(carrier) = self.symbol_carrier(*symbol_id) {
                    let carrier = self.resolve_carrier(carrier)?;
                    if numeric_rank(&carrier).is_some() {
                        result.push(carrier);
                    }
                }
            }
            LitexToLeanObjectIr::Constant(constant) => result.push(match constant {
                LitexToLeanConstantObjectIr::ImaginaryUnit => LitexToLeanCarrierIr::Complex,
                LitexToLeanConstantObjectIr::EulerNumber | LitexToLeanConstantObjectIr::Pi => {
                    LitexToLeanCarrierIr::Real
                }
            }),
            LitexToLeanObjectIr::BuiltinApp { arguments, .. } => {
                for argument in arguments {
                    self.collect_fixed_numeric_carriers(argument, result)?;
                }
            }
            LitexToLeanObjectIr::FunctionApplication(application) => {
                self.collect_fixed_numeric_carriers(&application.head, result)?;
                for layer in application.argument_layers.iter() {
                    for argument in layer {
                        self.collect_fixed_numeric_carriers(argument, result)?;
                    }
                }
            }
            LitexToLeanObjectIr::Collection { items, .. } => {
                for item in items {
                    self.collect_fixed_numeric_carriers(item, result)?;
                }
            }
            LitexToLeanObjectIr::Number { .. }
            | LitexToLeanObjectIr::StandardSet(_)
            | LitexToLeanObjectIr::FunctionSet { .. }
            | LitexToLeanObjectIr::SetBuilder(_)
            | LitexToLeanObjectIr::AnonymousFunction(_) => {}
        }
        Ok(())
    }

    fn function_application_result_carrier(
        &self,
        application: &LitexToLeanFunctionApplicationIr,
    ) -> Result<Option<LitexToLeanCarrierIr>, String> {
        let Some(mut carrier) = self.object_carrier(&application.head)? else {
            return Ok(None);
        };
        for (layer_index, arguments) in application.argument_layers.iter().enumerate() {
            let LitexToLeanCarrierIr::Function { function } = self.resolve_carrier(&carrier)?
            else {
                return Err(format!(
                    "Litex-to-Lean function application layer {} has a non-function head carrier",
                    layer_index + 1
                ));
            };
            if arguments.len() != function.parameters.len() {
                return Err(format!(
                    "Litex-to-Lean function application layer {} has {} arguments but its retained signature requires {}",
                    layer_index + 1,
                    arguments.len(),
                    function.parameters.len()
                ));
            }
            carrier = (*function.return_carrier).clone();
        }
        Ok(Some(carrier))
    }

    fn builtin_result_carrier(
        &self,
        operator: LitexToLeanBuiltinObjectOperatorIr,
        arguments: &[LitexToLeanObjectIr],
    ) -> Result<Option<LitexToLeanCarrierIr>, String> {
        if let Some(carrier) = operator.intrinsic_result_carrier() {
            return Ok(Some(carrier));
        }
        match operator {
            LitexToLeanBuiltinObjectOperatorIr::Union
            | LitexToLeanBuiltinObjectOperatorIr::Intersect
            | LitexToLeanBuiltinObjectOperatorIr::SetMinus => {
                let mut joined = None;
                for argument in arguments {
                    let Some(LitexToLeanCarrierIr::Set { element_carrier }) =
                        self.object_carrier(argument)?
                    else {
                        return Ok(None);
                    };
                    joined = Some(match joined {
                        None => *element_carrier,
                        Some(current) if current == *element_carrier => current,
                        Some(current) => {
                            return Err(format!(
                                "Litex-to-Lean set carriers do not unify: {:?} and {:?}",
                                current, element_carrier
                            ));
                        }
                    });
                }
                Ok(joined.map(|element_carrier| LitexToLeanCarrierIr::Set {
                    element_carrier: Box::new(element_carrier),
                }))
            }
            LitexToLeanBuiltinObjectOperatorIr::PowerSet => {
                let Some(argument) = arguments.first() else {
                    return Ok(None);
                };
                Ok(self
                    .object_carrier(argument)?
                    .map(|carrier| LitexToLeanCarrierIr::Set {
                        element_carrier: Box::new(carrier),
                    }))
            }
            LitexToLeanBuiltinObjectOperatorIr::RealPart
            | LitexToLeanBuiltinObjectOperatorIr::ImaginaryPart
            | LitexToLeanBuiltinObjectOperatorIr::ComplexAbs => {
                Ok(Some(LitexToLeanCarrierIr::Real))
            }
            LitexToLeanBuiltinObjectOperatorIr::BigUnion
            | LitexToLeanBuiltinObjectOperatorIr::BigIntersect => Ok(None),
            _ => self.join_object_carriers(arguments),
        }
    }

    fn join_object_carriers(
        &self,
        objects: &[LitexToLeanObjectIr],
    ) -> Result<Option<LitexToLeanCarrierIr>, String> {
        let mut joined = None;
        for object in objects {
            let Some(carrier) = self.object_carrier(object)? else {
                continue;
            };
            joined = Some(match joined {
                None => carrier,
                Some(current) if current == carrier => current,
                Some(current)
                    if numeric_rank(&current).is_some() && numeric_rank(&carrier).is_some() =>
                {
                    join_numeric_carriers(&current, &carrier)?
                }
                Some(current) => {
                    return Err(format!(
                        "Litex-to-Lean carriers do not have a supported common target: {:?} and {:?}",
                        current, carrier
                    ));
                }
            });
        }
        Ok(joined)
    }
}

fn refined_parameter_membership_consequences(proposition: &Fact) -> Vec<Fact> {
    let Fact::AtomicFact(AtomicFact::InFact(membership)) = proposition else {
        return Vec::new();
    };
    let Obj::StandardSet(set) = &membership.set else {
        return Vec::new();
    };
    let element = membership.element.clone();
    let zero: Obj = Number::new("0".to_string()).into();
    let line_file = membership.line_file.clone();
    match set {
        StandardSet::NPos | StandardSet::QPos | StandardSet::RPos => vec![
            LessFact::new(zero.clone(), element.clone(), line_file.clone()).into(),
            // Litex accepts the comparison-dual spelling in function domains;
            // Lean elaborates `element > 0` as the same `<` proposition.
            GreaterFact::new(element, zero, line_file).into(),
        ],
        StandardSet::QNeg | StandardSet::ZNeg | StandardSet::RNeg => vec![
            LessFact::new(element.clone(), zero.clone(), line_file.clone()).into(),
            GreaterFact::new(zero, element, line_file).into(),
        ],
        StandardSet::QStar | StandardSet::ZStar | StandardSet::RStar | StandardSet::CStar => {
            vec![NotEqualFact::new(element, zero, line_file).into()]
        }
        _ => Vec::new(),
    }
}

fn join_numeric_carriers(
    left: &LitexToLeanCarrierIr,
    right: &LitexToLeanCarrierIr,
) -> Result<LitexToLeanCarrierIr, String> {
    let left_rank = numeric_rank(left)
        .ok_or_else(|| format!("Litex-to-Lean carrier {:?} is not numeric", left))?;
    let right_rank = numeric_rank(right)
        .ok_or_else(|| format!("Litex-to-Lean carrier {:?} is not numeric", right))?;
    Ok(if left_rank >= right_rank {
        left.clone()
    } else {
        right.clone()
    })
}

fn numeric_rank(carrier: &LitexToLeanCarrierIr) -> Option<u8> {
    match carrier {
        LitexToLeanCarrierIr::Natural => Some(0),
        LitexToLeanCarrierIr::Integer => Some(1),
        LitexToLeanCarrierIr::Rational => Some(2),
        LitexToLeanCarrierIr::Real => Some(3),
        LitexToLeanCarrierIr::Complex => Some(4),
        LitexToLeanCarrierIr::Generic { .. }
        | LitexToLeanCarrierIr::Set { .. }
        | LitexToLeanCarrierIr::Function { .. }
        | LitexToLeanCarrierIr::ElementOfSet { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structurally_equal_applications_with_different_wd_certificates_are_not_guessed() {
        let source_application: Obj = Number::new("1".to_string()).into();
        let proposition: Fact = NotEqualFact::new(
            source_application.clone(),
            Number::new("0".to_string()).into(),
            default_line_file(),
        )
        .into();
        let role = WellDefinednessRequirementRole::FunctionDomain {
            layer_index: 0,
            domain_index: 0,
        };
        let first_id = WellDefinednessCertificateId::new(1);
        let second_id = WellDefinednessCertificateId::new(2);
        let certificate = LitexToLeanWellDefinednessCertificateIr {
            facts: Vec::new(),
            objects: Vec::new(),
            target_requirements: vec![
                LitexToLeanWellDefinednessTargetRequirementIr {
                    object_occurrence_id: WellDefinednessObjectOccurrenceId::new(1),
                    source_object: source_application.clone(),
                    role,
                    certificate_id: first_id,
                    expected_proposition: proposition.clone(),
                },
                LitexToLeanWellDefinednessTargetRequirementIr {
                    object_occurrence_id: WellDefinednessObjectOccurrenceId::new(2),
                    source_object: source_application.clone(),
                    role,
                    certificate_id: second_id,
                    expected_proposition: proposition.clone(),
                },
            ],
        };

        let mut context = LeanTypeContext::default();
        context.install_well_definedness_certificate_metadata(&certificate);
        context.insert_well_definedness_proof_by_certificate_id(
            first_id,
            &proposition,
            "wd_1".to_string(),
        );
        context.insert_well_definedness_proof_by_certificate_id(
            second_id,
            &proposition,
            "wd_2".to_string(),
        );

        let error = context
            .function_requirement_proof(&source_application, role, &proposition)
            .expect_err("the emitter must not choose between distinct occurrence certificates");
        assert!(error.contains("different WD proof terms"));
    }
}
