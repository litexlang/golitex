//! Bounded integer-polynomial normalization for an explicitly selected ring.
//!
//! Atoms are caller-owned identities. In particular, an arbitrary native numeral
//! is not a coefficient in a user-supplied ring. Only its selected zero and one
//! enter this representation as constants. No division or field cancellation
//! is performed. Exhaustion and checked arithmetic overflow are ordinary misses.

use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RingExpression {
    Zero,
    One,
    Atom(usize),
    Add(Box<RingExpression>, Box<RingExpression>),
    Neg(Box<RingExpression>),
    Mul(Box<RingExpression>, Box<RingExpression>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingPolynomial {
    // A monomial is an increasing atom/exponent list. The empty list is one.
    pub terms: BTreeMap<Vec<(usize, u32)>, i128>,
}

#[derive(Clone, Copy, Debug)]
pub struct RingNormalizationLimits {
    pub max_nodes: usize,
    pub max_depth: usize,
    pub max_atoms: usize,
    pub max_monomials: usize,
    pub max_degree: u32,
    pub max_coefficient_bits: u32,
    pub max_work: usize,
}

pub struct RingNormalizationBudget {
    pub limits: RingNormalizationLimits,
    nodes: usize,
    work: usize,
}

// Nodes are topologically ordered. A consumer can validate every recorded
// polynomial operation and match the root to its original reified expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RingNormalizationOperation {
    Zero,
    One,
    Atom(usize),
    Add(usize, usize),
    Neg(usize),
    Mul(usize, usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNormalizationNode {
    pub operation: RingNormalizationOperation,
    pub polynomial: RingPolynomial,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingNormalizationCertificate {
    pub nodes: Vec<RingNormalizationNode>,
    pub root: usize,
}

impl RingNormalizationLimits {
    pub fn new() -> Self {
        Self {
            max_nodes: 2048,
            max_depth: 128,
            max_atoms: 64,
            max_monomials: 256,
            max_degree: 64,
            max_coefficient_bits: 127,
            max_work: 25000,
        }
    }
}

impl RingNormalizationBudget {
    pub fn new(limits: RingNormalizationLimits) -> Self {
        Self {
            limits,
            nodes: 0,
            work: 0,
        }
    }

    fn visit(&mut self, depth: usize) -> Option<()> {
        self.nodes = self.nodes.checked_add(1)?;
        (depth <= self.limits.max_depth && self.nodes <= self.limits.max_nodes).then_some(())
    }

    fn spend(&mut self, amount: usize) -> Option<()> {
        self.work = self.work.checked_add(amount)?;
        (self.work <= self.limits.max_work).then_some(())
    }
}

impl RingPolynomial {
    pub fn new() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    fn insert_coefficient(
        &mut self,
        monomial: Vec<(usize, u32)>,
        coefficient: i128,
        budget: &mut RingNormalizationBudget,
    ) -> Option<()> {
        budget.spend(1)?;
        let coefficient = self
            .terms
            .get(&monomial)
            .copied()
            .unwrap_or(0)
            .checked_add(coefficient)?;
        let bits = 128 - coefficient.unsigned_abs().leading_zeros();
        if bits > budget.limits.max_coefficient_bits {
            return None;
        }
        if coefficient == 0 {
            self.terms.remove(&monomial);
        } else {
            self.terms.insert(monomial, coefficient);
        }
        (self.terms.len() <= budget.limits.max_monomials).then_some(())
    }

    fn add(&self, other: &Self, budget: &mut RingNormalizationBudget) -> Option<Self> {
        let mut result = self.clone();
        for (monomial, coefficient) in &other.terms {
            result.insert_coefficient(monomial.clone(), *coefficient, budget)?;
        }
        Some(result)
    }

    fn neg(&self, budget: &mut RingNormalizationBudget) -> Option<Self> {
        let mut result = Self::new();
        for (monomial, coefficient) in &self.terms {
            result.insert_coefficient(monomial.clone(), coefficient.checked_neg()?, budget)?;
        }
        Some(result)
    }

    fn mul(&self, other: &Self, budget: &mut RingNormalizationBudget) -> Option<Self> {
        let mut result = Self::new();
        for (left, a) in &self.terms {
            for (right, b) in &other.terms {
                budget.spend(left.len().checked_add(right.len())?.checked_add(1)?)?;
                let monomial = multiply_monomials(left, right, budget.limits.max_degree)?;
                result.insert_coefficient(monomial, a.checked_mul(*b)?, budget)?;
            }
        }
        Some(result)
    }
}

impl RingNormalizationCertificate {
    pub fn polynomial(&self) -> Option<&RingPolynomial> {
        self.nodes.get(self.root).map(|node| &node.polynomial)
    }
}

pub fn normalize_ring_expression(
    expression: &RingExpression,
    budget: &mut RingNormalizationBudget,
) -> Option<RingNormalizationCertificate> {
    let mut nodes = Vec::new();
    let root = normalize_node(expression, 0, budget, &mut nodes)?;
    Some(RingNormalizationCertificate { nodes, root })
}

fn normalize_node(
    expression: &RingExpression,
    depth: usize,
    budget: &mut RingNormalizationBudget,
    nodes: &mut Vec<RingNormalizationNode>,
) -> Option<usize> {
    use RingExpression as E;
    use RingNormalizationOperation as O;
    budget.visit(depth)?;
    let mut polynomial = RingPolynomial::new();
    let operation = match expression {
        E::Zero => O::Zero,
        E::One => {
            polynomial.insert_coefficient(Vec::new(), 1, budget)?;
            O::One
        }
        E::Atom(atom) => {
            if *atom >= budget.limits.max_atoms || budget.limits.max_degree == 0 {
                return None;
            }
            polynomial.insert_coefficient(vec![(*atom, 1)], 1, budget)?;
            O::Atom(*atom)
        }
        E::Add(left, right) => {
            let left = normalize_node(left, depth + 1, budget, nodes)?;
            let right = normalize_node(right, depth + 1, budget, nodes)?;
            polynomial = nodes[left]
                .polynomial
                .add(&nodes[right].polynomial, budget)?;
            O::Add(left, right)
        }
        E::Neg(child) => {
            let child = normalize_node(child, depth + 1, budget, nodes)?;
            polynomial = nodes[child].polynomial.neg(budget)?;
            O::Neg(child)
        }
        E::Mul(left, right) => {
            let left = normalize_node(left, depth + 1, budget, nodes)?;
            let right = normalize_node(right, depth + 1, budget, nodes)?;
            polynomial = nodes[left]
                .polynomial
                .mul(&nodes[right].polynomial, budget)?;
            O::Mul(left, right)
        }
    };
    let index = nodes.len();
    nodes.push(RingNormalizationNode {
        operation,
        polynomial,
    });
    Some(index)
}

fn multiply_monomials(
    left: &[(usize, u32)],
    right: &[(usize, u32)],
    max_degree: u32,
) -> Option<Vec<(usize, u32)>> {
    let mut result = Vec::with_capacity(left.len().checked_add(right.len())?);
    let mut i = 0;
    let mut j = 0;
    let mut degree = 0u32;
    while i < left.len() || j < right.len() {
        let next;
        if j == right.len() || (i < left.len() && left[i].0 < right[j].0) {
            next = left[i];
            i += 1;
        } else if i == left.len() || right[j].0 < left[i].0 {
            next = right[j];
            j += 1;
        } else {
            next = (left[i].0, left[i].1.checked_add(right[j].1)?);
            i += 1;
            j += 1;
        }
        degree = degree.checked_add(next.1)?;
        if degree > max_degree {
            return None;
        }
        result.push(next);
    }
    Some(result)
}

// Validate both source shape and every node of a saved certificate. This also
// rejects forged polynomial endpoints, extra nodes and invalid child references.
pub fn check_ring_normalization_certificate(
    expression: &RingExpression,
    certificate: &RingNormalizationCertificate,
    limits: RingNormalizationLimits,
) -> bool {
    let mut budget = RingNormalizationBudget::new(limits);
    let Some(expected) = normalize_ring_expression(expression, &mut budget) else {
        return false;
    };
    expected == *certificate
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/comm_ring/normal_form.rs"]
mod tests;
