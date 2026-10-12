use crate::ast::fact::ChainFact;
use crate::ast::line_file::SourceLine;
use crate::ast::names::{AtomicName, BoundName};
use crate::ast::param::TypedParameterList;
use crate::parse::keywords::{EQUAL, GREATER, GREATER_EQUAL, LESS, LESS_EQUAL};
use crate::runtime::CodeSource;

pub(crate) fn chain_line_file(chain_fact: &ChainFact) -> SourceLine {
    chain_fact
        .line_file
        .clone()
        .unwrap_or_else(|| SourceLine::new(0, CodeSource::Eval))
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum OrderEdge {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
}

pub(crate) fn chain_props_all_equal(prop_names: &[AtomicName]) -> bool {
    !prop_names.is_empty()
        && prop_names.iter().all(|p| match p {
            AtomicName::Plain { name } => name == EQUAL,
            _ => false,
        })
}

pub(crate) fn chain_uniform_prop(prop_names: &[AtomicName]) -> Option<AtomicName> {
    let first = prop_names.first()?.clone();
    if prop_names.iter().all(|p| p == &first) {
        Some(first)
    } else {
        None
    }
}

pub(crate) fn chain_order_edges(prop_names: &[AtomicName]) -> Option<Vec<OrderEdge>> {
    let mut edges = Vec::with_capacity(prop_names.len());
    for prop in prop_names {
        let AtomicName::Plain { name } = prop else {
            return None;
        };
        let edge = match name.as_str() {
            EQUAL => OrderEdge::Eq,
            LESS_EQUAL => OrderEdge::Le,
            LESS => OrderEdge::Lt,
            GREATER_EQUAL => OrderEdge::Ge,
            GREATER => OrderEdge::Gt,
            _ => return None,
        };
        edges.push(edge);
    }
    Some(edges)
}

pub(crate) fn flatten_def_prop_params(list: &TypedParameterList) -> Vec<BoundName> {
    let mut out = Vec::new();
    for group in &list.groups {
        for param in &group.params {
            out.push(param.clone());
        }
    }
    out
}

impl crate::runtime::Runtime {
    pub(crate) fn remember_formed_atomic_subjects(&mut self, fact: &crate::ast::fact::Fact) {
        // Formation is established by user-fact verification or the named infer rule.
        // Cache only its direct atomic subjects in this scope, never the bound
        // internals of a quantified fact. Exploratory verify does not record WD.
        if let crate::ast::fact::Fact::AtomicFact(atomic) = fact {
            for obj in crate::ast::fact::atomic_fact_args_ref(atomic) {
                // Named objects have their own definition evidence. Recording
                // a second WD cache entry for each alias adds no certificate.
                if matches!(obj, crate::ast::obj::Obj::Identifier(_)) {
                    continue;
                }
                if self.well_defined_visible_in_stack(obj).is_none() {
                    let id = self.global_ids.allocate_well_definedness_id();
                    self.top_exec_env_mut()
                        .well_defined_objects
                        .record(obj.clone(), id);
                }
            }
        }
    }
}
