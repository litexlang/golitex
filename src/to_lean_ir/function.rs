use crate::prelude::*;
use std::fmt;

use super::{LeanCarrierToLeanIR, ObjToLeanIR};

/// One native Lean function type underlying a Litex `fn(...) ...` set.
///
/// Litex application layers remain explicit in `FunctionApplicationToLeanIR`;
/// this type describes exactly one declared source layer.  All value
/// parameters precede the layer's membership/domain proof arguments.
#[derive(Clone, Debug)]
pub struct FunctionTypeToLeanIR {
    /// Display-free source identity used when carrier constraints are compared.
    pub semantic_key: String,
    pub parameters: Vec<FunctionParameterToLeanIR>,
    pub domain_facts: Vec<Fact>,
    pub return_carrier: Box<LeanCarrierToLeanIR>,
}

impl PartialEq for FunctionTypeToLeanIR {
    fn eq(&self, other: &Self) -> bool {
        self.semantic_key == other.semantic_key
    }
}

impl Eq for FunctionTypeToLeanIR {}

#[derive(Clone)]
pub struct FunctionParameterToLeanIR {
    pub symbol_id: SymbolId,
    pub name: String,
    pub substitution_key: String,
    pub source_set: Obj,
    pub set: ObjToLeanIR,
    pub element_carrier: LeanCarrierToLeanIR,
    /// Universal numeric/function sets contribute target typing but do not add
    /// a proof argument. Refined and general source sets retain membership as
    /// an explicit proof parameter.
    pub requires_membership_proof: bool,
}

impl PartialEq for FunctionParameterToLeanIR {
    fn eq(&self, other: &Self) -> bool {
        self.symbol_id == other.symbol_id
            && self.name == other.name
            && self.substitution_key == other.substitution_key
            && obj_equality_key(&self.source_set) == obj_equality_key(&other.source_set)
            && self.set == other.set
            && self.element_carrier == other.element_carrier
            && self.requires_membership_proof == other.requires_membership_proof
    }
}

impl Eq for FunctionParameterToLeanIR {}

impl fmt::Debug for FunctionParameterToLeanIR {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("FunctionParameterToLeanIR")
            .field("symbol_id", &self.symbol_id)
            .field("name", &self.name)
            .field("substitution_key", &self.substitution_key)
            .field("source_set", &self.source_set.to_string())
            .field("set", &self.set)
            .field("element_carrier", &self.element_carrier)
            .field(
                "requires_membership_proof",
                &self.requires_membership_proof,
            )
            .finish()
    }
}

#[derive(Clone)]
pub struct FunctionApplicationToLeanIR {
    pub head: Box<ObjToLeanIR>,
    /// Exact source groups. A one-layer `f(x, y)` never becomes two Litex
    /// layers merely because Lean prints curried application.
    pub argument_layers: Vec<Vec<ObjToLeanIR>>,
    pub source_argument_layers: Vec<Vec<Obj>>,
}

impl PartialEq for FunctionApplicationToLeanIR {
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.argument_layers == other.argument_layers
    }
}

impl Eq for FunctionApplicationToLeanIR {}

impl fmt::Debug for FunctionApplicationToLeanIR {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("FunctionApplicationToLeanIR")
            .field("head", &self.head)
            .field("argument_layers", &self.argument_layers)
            .field(
                "source_argument_layers",
                &self
                    .source_argument_layers
                    .iter()
                    .map(|layer| layer.iter().map(ToString::to_string).collect::<Vec<_>>())
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

impl FunctionTypeToLeanIR {
    pub fn lower(function_set: &FnSet) -> Result<Self, String> {
        Self::lower_body(
            &function_set.body,
            obj_equality_key(&function_set.clone().into()),
        )
    }

    fn lower_body(body: &FnSetBody, semantic_key: String) -> Result<Self, String> {
        let mut parameters = Vec::with_capacity(body.params_def_with_set.number_of_params());
        for group in body.params_def_with_set.groups.iter() {
            let set = ObjToLeanIR::lower(group.set_obj())?;
            let element_carrier = LeanCarrierToLeanIR::for_membership_set(&set);
            let requires_membership_proof = !set.is_universal_native_set();
            for binding in group.params.iter() {
                parameters.push(FunctionParameterToLeanIR {
                    symbol_id: binding.id(),
                    name: binding.name().to_string(),
                    substitution_key: binding.substitution_key(),
                    source_set: group.set_obj().clone(),
                    set: set.clone(),
                    element_carrier: element_carrier.clone(),
                    requires_membership_proof,
                });
            }
        }

        let return_set = ObjToLeanIR::lower(body.ret_set.as_ref())?;
        let return_carrier = LeanCarrierToLeanIR::for_membership_set(&return_set);
        Ok(Self {
            semantic_key,
            parameters,
            domain_facts: body.dom_facts.iter().cloned().map(Fact::from).collect(),
            return_carrier: Box::new(return_carrier),
        })
    }
}

impl ObjToLeanIR {
    pub(crate) fn is_universal_native_set(&self) -> bool {
        matches!(
            self,
            ObjToLeanIR::StandardSet(
                StandardSetToLeanIR::Natural
                    | StandardSetToLeanIR::Integer
                    | StandardSetToLeanIR::Rational
                    | StandardSetToLeanIR::Real
                    | StandardSetToLeanIR::Complex
            ) | ObjToLeanIR::FunctionSet { .. }
        )
    }
}
