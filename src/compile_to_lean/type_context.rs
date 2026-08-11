use std::collections::HashMap;

use crate::prelude::*;

use super::helper::lean_generic_carrier_name;

#[derive(Clone, Default)]
pub(super) struct LeanTypeContext {
    symbol_carriers: HashMap<SymbolId, LitexToLeanCarrierIr>,
    object_expectations: HashMap<String, LitexToLeanCarrierIr>,
    generic_carrier_aliases: HashMap<SymbolId, SymbolId>,
    well_definedness_proof_names: HashMap<String, String>,
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
            .insert(obj_equality_key(object), carrier);
    }

    pub(super) fn expected_object(&self, object: &Obj) -> Option<&LitexToLeanCarrierIr> {
        self.object_expectations.get(&obj_equality_key(object))
    }

    pub(super) fn insert_well_definedness_proof(&mut self, proposition: &Fact, name: String) {
        self.well_definedness_proof_names
            .insert(proposition.to_string(), name);
    }

    pub(super) fn well_definedness_proof(&self, proposition: &Fact) -> Option<&str> {
        self.well_definedness_proof_names
            .get(&proposition.to_string())
            .map(String::as_str)
    }

    pub(super) fn replace_well_definedness_proofs(
        &mut self,
        proofs: HashMap<String, String>,
    ) -> HashMap<String, String> {
        std::mem::replace(&mut self.well_definedness_proof_names, proofs)
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
            | LitexToLeanObjectIr::FunctionSet { .. } => {}
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
