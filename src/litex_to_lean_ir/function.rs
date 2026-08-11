use crate::prelude::*;
use std::fmt;

use super::{LitexToLeanCarrierIr, LitexToLeanObjectIr};

/// One native Lean function type underlying a Litex `fn(...) ...` set.
///
/// Litex application layers remain explicit in `LitexToLeanFunctionApplicationIr`;
/// this type describes exactly one declared source layer.  All value
/// parameters precede the layer's membership/domain proof arguments.
#[derive(Clone, Debug)]
pub struct LitexToLeanFunctionTypeIr {
    /// Display-free source identity used when carrier constraints are compared.
    pub semantic_key: String,
    pub parameters: Vec<LitexToLeanFunctionParameterIr>,
    pub domain_facts: Vec<Fact>,
    pub return_carrier: Box<LitexToLeanCarrierIr>,
}

impl PartialEq for LitexToLeanFunctionTypeIr {
    fn eq(&self, other: &Self) -> bool {
        self.semantic_key == other.semantic_key
    }
}

impl Eq for LitexToLeanFunctionTypeIr {}

#[derive(Clone)]
pub struct LitexToLeanFunctionParameterIr {
    pub symbol_id: SymbolId,
    pub name: String,
    pub substitution_key: String,
    pub source_set: Obj,
    pub set: LitexToLeanObjectIr,
    pub element_carrier: LitexToLeanCarrierIr,
    /// Universal numeric/function sets contribute target typing but do not add
    /// a proof argument. Refined and general source sets retain membership as
    /// an explicit proof parameter.
    pub requires_membership_proof: bool,
}

impl PartialEq for LitexToLeanFunctionParameterIr {
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

impl Eq for LitexToLeanFunctionParameterIr {}

impl fmt::Debug for LitexToLeanFunctionParameterIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanFunctionParameterIr")
            .field("symbol_id", &self.symbol_id)
            .field("name", &self.name)
            .field("substitution_key", &self.substitution_key)
            .field("source_set", &self.source_set.to_string())
            .field("set", &self.set)
            .field("element_carrier", &self.element_carrier)
            .field("requires_membership_proof", &self.requires_membership_proof)
            .finish()
    }
}

#[derive(Clone)]
pub struct LitexToLeanFunctionApplicationIr {
    pub head: Box<LitexToLeanObjectIr>,
    /// Exact source groups. A one-layer `f(x, y)` never becomes two Litex
    /// layers merely because Lean prints curried application.
    pub argument_layers: Vec<Vec<LitexToLeanObjectIr>>,
    pub source_argument_layers: Vec<Vec<Obj>>,
}

impl PartialEq for LitexToLeanFunctionApplicationIr {
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.argument_layers == other.argument_layers
    }
}

impl Eq for LitexToLeanFunctionApplicationIr {}

impl fmt::Debug for LitexToLeanFunctionApplicationIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanFunctionApplicationIr")
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

impl LitexToLeanFunctionTypeIr {
    pub fn lower(function_set: &FnSet) -> Result<Self, String> {
        Self::lower_body(
            &function_set.body,
            obj_equality_key(&function_set.clone().into()),
        )
    }

    fn lower_body(body: &FnSetBody, semantic_key: String) -> Result<Self, String> {
        let mut parameters = Vec::with_capacity(body.params_def_with_set.number_of_params());
        for group in body.params_def_with_set.groups.iter() {
            let set = LitexToLeanObjectIr::lower(group.set_obj())?;
            let element_carrier = LitexToLeanCarrierIr::for_membership_set(&set);
            let requires_membership_proof = !set.is_universal_native_set();
            for binding in group.params.iter() {
                parameters.push(LitexToLeanFunctionParameterIr {
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

        let return_set = LitexToLeanObjectIr::lower(body.ret_set.as_ref())?;
        if !return_set.is_universal_native_set() {
            return Err(format!(
                "Litex-to-Lean function sets currently require a universal native numeric or recursively supported function return set; `{}` needs an explicit output-membership representation",
                body.ret_set
            ));
        }
        let return_carrier = LitexToLeanCarrierIr::for_membership_set(&return_set);
        Ok(Self {
            semantic_key,
            parameters,
            domain_facts: body.dom_facts.iter().cloned().map(Fact::from).collect(),
            return_carrier: Box::new(return_carrier),
        })
    }
}

impl LitexToLeanObjectIr {
    pub(crate) fn is_universal_native_set(&self) -> bool {
        matches!(
            self,
            LitexToLeanObjectIr::StandardSet(
                LitexToLeanStandardSetIr::Natural
                    | LitexToLeanStandardSetIr::Integer
                    | LitexToLeanStandardSetIr::Rational
                    | LitexToLeanStandardSetIr::Real
                    | LitexToLeanStandardSetIr::Complex
            ) | LitexToLeanObjectIr::FunctionSet { .. }
        )
    }
}
