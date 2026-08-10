use std::collections::HashMap;

use crate::prelude::*;

use super::helper::lean_generic_carrier_name;

#[derive(Clone, Default)]
pub(super) struct LeanTypeContext {
    symbol_carriers: HashMap<SymbolId, LeanCarrierToLeanIR>,
    object_expectations: HashMap<String, LeanCarrierToLeanIR>,
    generic_carrier_aliases: HashMap<SymbolId, SymbolId>,
}

impl LeanTypeContext {
    pub(super) fn insert(&mut self, symbol_id: SymbolId, carrier: LeanCarrierToLeanIR) {
        self.symbol_carriers.insert(symbol_id, carrier);
    }

    pub(super) fn insert_param(&mut self, symbol_id: SymbolId, param_type: &ParamTypeToLeanIR) {
        let carrier = match param_type {
            ParamTypeToLeanIR::Set { element_carrier }
            | ParamTypeToLeanIR::NonemptySet { element_carrier }
            | ParamTypeToLeanIR::FiniteSet { element_carrier } => LeanCarrierToLeanIR::Set {
                element_carrier: Box::new(element_carrier.clone()),
            },
            ParamTypeToLeanIR::MemberOf {
                element_carrier, ..
            } => element_carrier.clone(),
            ParamTypeToLeanIR::Unsupported(_) => return,
        };
        self.insert(symbol_id, carrier);
    }

    pub(super) fn symbol_carrier(&self, symbol_id: SymbolId) -> Option<&LeanCarrierToLeanIR> {
        self.symbol_carriers.get(&symbol_id)
    }

    pub(super) fn expect_object(&mut self, object: &Obj, carrier: LeanCarrierToLeanIR) {
        self.object_expectations
            .insert(obj_equality_key(object), carrier);
    }

    pub(super) fn expected_object(&self, object: &Obj) -> Option<&LeanCarrierToLeanIR> {
        self.object_expectations.get(&obj_equality_key(object))
    }

    pub(super) fn unify_generic_carriers(
        &mut self,
        left: &LeanCarrierToLeanIR,
        right: &LeanCarrierToLeanIR,
    ) -> Result<(), String> {
        let left = self.resolve_carrier(left)?;
        let right = self.resolve_carrier(right)?;
        match (left, right) {
            (
                LeanCarrierToLeanIR::Generic {
                    anchor: left_anchor,
                },
                LeanCarrierToLeanIR::Generic {
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
                LeanCarrierToLeanIR::Set {
                    element_carrier: left,
                },
                LeanCarrierToLeanIR::Set {
                    element_carrier: right,
                },
            ) => self.unify_generic_carriers(&left, &right)?,
            _ => {}
        }
        Ok(())
    }

    pub(super) fn object_carrier(
        &self,
        object: &ObjToLeanIR,
    ) -> Result<Option<LeanCarrierToLeanIR>, String> {
        match object {
            ObjToLeanIR::Symbol { symbol_id, .. } => Ok(self.symbol_carrier(*symbol_id).cloned()),
            ObjToLeanIR::Number { .. } => Ok(None),
            ObjToLeanIR::Constant(constant) => Ok(Some(match constant {
                ConstantObjToLeanIR::ImaginaryUnit => LeanCarrierToLeanIR::Complex,
                ConstantObjToLeanIR::EulerNumber | ConstantObjToLeanIR::Pi => {
                    LeanCarrierToLeanIR::Real
                }
            })),
            ObjToLeanIR::StandardSet(set) => Ok(Some(LeanCarrierToLeanIR::Set {
                element_carrier: Box::new(set.element_carrier()),
            })),
            ObjToLeanIR::BuiltinApp {
                operator,
                arguments,
            } => self.builtin_result_carrier(*operator, arguments),
            ObjToLeanIR::Collection {
                constructor: CollectionObjToLeanIR::ListSet,
                items,
            } => Ok(self.join_object_carriers(items)?.map(|element_carrier| {
                LeanCarrierToLeanIR::Set {
                    element_carrier: Box::new(element_carrier),
                }
            })),
        }
    }

    pub(super) fn membership_element_carrier(
        &self,
        set: &ObjToLeanIR,
    ) -> Result<LeanCarrierToLeanIR, String> {
        if let ObjToLeanIR::StandardSet(standard) = set {
            return Ok(standard.element_carrier());
        }
        match self.object_carrier(set)? {
            Some(LeanCarrierToLeanIR::Set { element_carrier }) => Ok(*element_carrier),
            Some(other) => Err(format!(
                "To-Lean membership set has non-set target carrier {:?}",
                other
            )),
            None => Ok(LeanCarrierToLeanIR::ElementOfSet {
                set: Box::new(set.clone()),
            }),
        }
    }

    pub(super) fn resolve_carrier(
        &self,
        carrier: &LeanCarrierToLeanIR,
    ) -> Result<LeanCarrierToLeanIR, String> {
        self.resolve_carrier_with_depth(carrier, 0)
    }

    fn resolve_carrier_with_depth(
        &self,
        carrier: &LeanCarrierToLeanIR,
        depth: usize,
    ) -> Result<LeanCarrierToLeanIR, String> {
        if depth > 32 {
            return Err("To-Lean carrier constraints contain a cycle".to_string());
        }
        match carrier {
            LeanCarrierToLeanIR::ElementOfSet { set } => {
                let element = self.membership_element_carrier(set)?;
                self.resolve_carrier_with_depth(&element, depth + 1)
            }
            LeanCarrierToLeanIR::Set { element_carrier } => Ok(LeanCarrierToLeanIR::Set {
                element_carrier: Box::new(
                    self.resolve_carrier_with_depth(element_carrier, depth + 1)?,
                ),
            }),
            LeanCarrierToLeanIR::Generic { anchor } => {
                let Some(canonical) = self.generic_carrier_aliases.get(anchor).copied() else {
                    return Ok(carrier.clone());
                };
                self.resolve_carrier_with_depth(
                    &LeanCarrierToLeanIR::Generic { anchor: canonical },
                    depth + 1,
                )
            }
            other => Ok(other.clone()),
        }
    }

    pub(super) fn lean_type(&self, carrier: &LeanCarrierToLeanIR) -> Result<String, String> {
        match self.resolve_carrier(carrier)? {
            LeanCarrierToLeanIR::Natural => Ok("ℕ".to_string()),
            LeanCarrierToLeanIR::Integer => Ok("ℤ".to_string()),
            LeanCarrierToLeanIR::Rational => Ok("ℚ".to_string()),
            LeanCarrierToLeanIR::Real => Ok("ℝ".to_string()),
            LeanCarrierToLeanIR::Complex => Ok("ℂ".to_string()),
            LeanCarrierToLeanIR::Generic { anchor } => {
                Ok(lean_generic_carrier_name(anchor.value()))
            }
            LeanCarrierToLeanIR::Set { element_carrier } => {
                Ok(format!("Set {}", self.lean_type(&element_carrier)?))
            }
            LeanCarrierToLeanIR::ElementOfSet { .. } => {
                Err("To-Lean could not resolve a set's element carrier".to_string())
            }
        }
    }

    pub(super) fn joined_numeric_carrier(
        &self,
        objects: &[&ObjToLeanIR],
    ) -> Result<Option<LeanCarrierToLeanIR>, String> {
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
        object: &ObjToLeanIR,
        expected: &LeanCarrierToLeanIR,
    ) -> Result<bool, String> {
        let expected = self.resolve_carrier(expected)?;
        let Some(expected_rank) = numeric_rank(&expected) else {
            return Ok(false);
        };
        for carrier in self.fixed_numeric_carriers(object)? {
            let carrier = self.resolve_carrier(&carrier)?;
            let Some(rank) = numeric_rank(&carrier) else {
                return Err(format!(
                    "To-Lean cannot coerce nonnumeric carrier {:?} into {:?}",
                    carrier, expected
                ));
            };
            if rank > expected_rank {
                return Err(format!(
                    "To-Lean does not insert a numeric downcast from {:?} to {:?}",
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
        object: &ObjToLeanIR,
    ) -> Result<Vec<LeanCarrierToLeanIR>, String> {
        let mut result = Vec::new();
        self.collect_fixed_numeric_carriers(object, &mut result)?;
        Ok(result)
    }

    fn collect_fixed_numeric_carriers(
        &self,
        object: &ObjToLeanIR,
        result: &mut Vec<LeanCarrierToLeanIR>,
    ) -> Result<(), String> {
        match object {
            ObjToLeanIR::Symbol { symbol_id, .. } => {
                if let Some(carrier) = self.symbol_carrier(*symbol_id) {
                    let carrier = self.resolve_carrier(carrier)?;
                    if numeric_rank(&carrier).is_some() {
                        result.push(carrier);
                    }
                }
            }
            ObjToLeanIR::Constant(constant) => result.push(match constant {
                ConstantObjToLeanIR::ImaginaryUnit => LeanCarrierToLeanIR::Complex,
                ConstantObjToLeanIR::EulerNumber | ConstantObjToLeanIR::Pi => {
                    LeanCarrierToLeanIR::Real
                }
            }),
            ObjToLeanIR::BuiltinApp { arguments, .. } => {
                for argument in arguments {
                    self.collect_fixed_numeric_carriers(argument, result)?;
                }
            }
            ObjToLeanIR::Collection { items, .. } => {
                for item in items {
                    self.collect_fixed_numeric_carriers(item, result)?;
                }
            }
            ObjToLeanIR::Number { .. } | ObjToLeanIR::StandardSet(_) => {}
        }
        Ok(())
    }

    fn builtin_result_carrier(
        &self,
        operator: BuiltinObjOperatorToLeanIR,
        arguments: &[ObjToLeanIR],
    ) -> Result<Option<LeanCarrierToLeanIR>, String> {
        match operator {
            BuiltinObjOperatorToLeanIR::Union
            | BuiltinObjOperatorToLeanIR::Intersect
            | BuiltinObjOperatorToLeanIR::SetMinus => {
                let mut joined = None;
                for argument in arguments {
                    let Some(LeanCarrierToLeanIR::Set { element_carrier }) =
                        self.object_carrier(argument)?
                    else {
                        return Ok(None);
                    };
                    joined = Some(match joined {
                        None => *element_carrier,
                        Some(current) if current == *element_carrier => current,
                        Some(current) => {
                            return Err(format!(
                                "To-Lean set carriers do not unify: {:?} and {:?}",
                                current, element_carrier
                            ));
                        }
                    });
                }
                Ok(joined.map(|element_carrier| LeanCarrierToLeanIR::Set {
                    element_carrier: Box::new(element_carrier),
                }))
            }
            BuiltinObjOperatorToLeanIR::PowerSet => {
                let Some(argument) = arguments.first() else {
                    return Ok(None);
                };
                Ok(self
                    .object_carrier(argument)?
                    .map(|carrier| LeanCarrierToLeanIR::Set {
                        element_carrier: Box::new(carrier),
                    }))
            }
            BuiltinObjOperatorToLeanIR::RealPart
            | BuiltinObjOperatorToLeanIR::ImaginaryPart
            | BuiltinObjOperatorToLeanIR::ComplexAbs => Ok(Some(LeanCarrierToLeanIR::Real)),
            BuiltinObjOperatorToLeanIR::BigUnion | BuiltinObjOperatorToLeanIR::BigIntersect => {
                Ok(None)
            }
            _ => self.join_object_carriers(arguments),
        }
    }

    fn join_object_carriers(
        &self,
        objects: &[ObjToLeanIR],
    ) -> Result<Option<LeanCarrierToLeanIR>, String> {
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
                        "To-Lean carriers do not have a supported common target: {:?} and {:?}",
                        current, carrier
                    ));
                }
            });
        }
        Ok(joined)
    }
}

fn join_numeric_carriers(
    left: &LeanCarrierToLeanIR,
    right: &LeanCarrierToLeanIR,
) -> Result<LeanCarrierToLeanIR, String> {
    let left_rank =
        numeric_rank(left).ok_or_else(|| format!("To-Lean carrier {:?} is not numeric", left))?;
    let right_rank =
        numeric_rank(right).ok_or_else(|| format!("To-Lean carrier {:?} is not numeric", right))?;
    Ok(if left_rank >= right_rank {
        left.clone()
    } else {
        right.clone()
    })
}

fn numeric_rank(carrier: &LeanCarrierToLeanIR) -> Option<u8> {
    match carrier {
        LeanCarrierToLeanIR::Natural => Some(0),
        LeanCarrierToLeanIR::Integer => Some(1),
        LeanCarrierToLeanIR::Rational => Some(2),
        LeanCarrierToLeanIR::Real => Some(3),
        LeanCarrierToLeanIR::Complex => Some(4),
        LeanCarrierToLeanIR::Generic { .. }
        | LeanCarrierToLeanIR::Set { .. }
        | LeanCarrierToLeanIR::ElementOfSet { .. } => None,
    }
}
