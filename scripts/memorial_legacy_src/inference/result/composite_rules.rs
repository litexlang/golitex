/// A stored conjunction exposes one exact ordered component. The component
/// Result owns its own FactId; consumers project it from the conjunction
/// premise instead of looking up an equal proposition by text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConjunctionImpliesComponentInferRule {
    pub component_index: usize,
    pub component_count: usize,
}

/// A stored chain is the conjunction of its ordered adjacent relations. This
/// rule records the exact component selected from that source chain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainImpliesComponentInferRule {
    pub component_index: usize,
    pub component_count: usize,
}
