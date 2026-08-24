/// Identifies the exact conclusion selected from a stored `forall` fact.
///
/// A Litex `forall` may publish several `then` facts. An `and` or chain
/// conclusion is additionally searchable through each of its atomic
/// components. The verifier retains this structural location so later
/// consumers never have to reconstruct a smaller, synthetic `forall` fact.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ForallConclusionLocation {
    DirectThenFact(DirectForallConclusionLocation),
    AndFactComponent(AndFactComponentForallConclusionLocation),
    ChainFactComponent(ChainFactComponentForallConclusionLocation),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DirectForallConclusionLocation {
    pub then_fact_index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AndFactComponentForallConclusionLocation {
    pub then_fact_index: usize,
    pub component_index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ChainFactComponentForallConclusionLocation {
    pub then_fact_index: usize,
    pub component_index: usize,
}

impl ForallConclusionLocation {
    pub fn direct_then_fact(then_fact_index: usize) -> Self {
        Self::DirectThenFact(DirectForallConclusionLocation { then_fact_index })
    }

    pub fn and_fact_component(then_fact_index: usize, component_index: usize) -> Self {
        Self::AndFactComponent(AndFactComponentForallConclusionLocation {
            then_fact_index,
            component_index,
        })
    }

    pub fn chain_fact_component(then_fact_index: usize, component_index: usize) -> Self {
        Self::ChainFactComponent(ChainFactComponentForallConclusionLocation {
            then_fact_index,
            component_index,
        })
    }

    pub fn then_fact_index(self) -> usize {
        match self {
            Self::DirectThenFact(location) => location.then_fact_index,
            Self::AndFactComponent(location) => location.then_fact_index,
            Self::ChainFactComponent(location) => location.then_fact_index,
        }
    }
}
