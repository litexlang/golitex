use crate::prelude::*;
use std::fmt;

use super::LitexToLeanObjectIr;

/// One source application contract underlying a Litex `fn(...) ...` object.
///
/// Litex application layers remain explicit in `LitexToLeanFunctionApplicationIr`;
/// this type describes exactly one declared source layer. Parameter sets and
/// domain facts remain propositional requirements, so a native-carrier backend
/// can consume them without collapsing the layer into a Lean function type.
#[derive(Clone, Debug)]
pub struct LitexToLeanFunctionTypeIr {
    /// Display-free source identity used when contracts are compared.
    pub semantic_key: String,
    pub parameters: Vec<LitexToLeanFunctionParameterIr>,
    pub domain_facts: Vec<Fact>,
    /// Exact set-valued codomain of this source layer.
    pub return_set: Box<LitexToLeanObjectIr>,
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
}

impl PartialEq for LitexToLeanFunctionParameterIr {
    fn eq(&self, other: &Self) -> bool {
        self.symbol_id == other.symbol_id
            && self.name == other.name
            && self.substitution_key == other.substitution_key
            && obj_equality_key(&self.source_set) == obj_equality_key(&other.source_set)
            && self.set == other.set
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
            .finish()
    }
}

#[derive(Clone)]
pub struct LitexToLeanFunctionApplicationIr {
    pub head: Box<LitexToLeanObjectIr>,
    /// Parser-owned source identity. Repeated textually equal applications
    /// remain different occurrences, while verifier cache reuse preserves the
    /// same identity.
    pub source_occurrence_id: SourceObjectOccurrenceId,
    /// Complete source occurrence used to select exact WD certificate slots.
    pub source_application: Obj,
    /// Exact source groups. A one-layer `f(x, y)` never becomes two Litex
    /// layers merely because Lean prints curried application.
    pub argument_layers: Vec<Vec<LitexToLeanObjectIr>>,
    pub source_argument_layers: Vec<Vec<Obj>>,
}

impl PartialEq for LitexToLeanFunctionApplicationIr {
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head
            && self.source_occurrence_id == other.source_occurrence_id
            && self.argument_layers == other.argument_layers
    }
}

impl Eq for LitexToLeanFunctionApplicationIr {}

impl fmt::Debug for LitexToLeanFunctionApplicationIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanFunctionApplicationIr")
            .field("head", &self.head)
            .field("source_occurrence_id", &self.source_occurrence_id)
            .field("source_application", &self.source_application.to_string())
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

    pub fn lower_anonymous(function: &AnonymousFn) -> Result<Self, String> {
        let signature = FnSet::from_body(function.body.clone()).map_err(|error| {
            format!(
                "Litex-to-Lean could not reconstruct anonymous function signature: {}",
                error.trace_message()
            )
        })?;
        Self::lower_body(&function.body, obj_equality_key(&signature.into()))
    }

    fn lower_body(body: &FnSetBody, semantic_key: String) -> Result<Self, String> {
        let mut parameters = Vec::with_capacity(body.params_def_with_set.number_of_params());
        for group in body.params_def_with_set.groups.iter() {
            let set = LitexToLeanObjectIr::lower(group.set_obj())?;
            for binding in group.params.iter() {
                parameters.push(LitexToLeanFunctionParameterIr {
                    symbol_id: binding.id(),
                    name: binding.name().to_string(),
                    substitution_key: binding.substitution_key(),
                    source_set: group.set_obj().clone(),
                    set: set.clone(),
                });
            }
        }

        let source_return_set = body.ret_set.as_ref().clone();
        let return_set = LitexToLeanObjectIr::lower(&source_return_set)?;
        Ok(Self {
            semantic_key,
            parameters,
            domain_facts: body.dom_facts.iter().cloned().map(Fact::from).collect(),
            return_set: Box::new(return_set),
        })
    }
}
