//! Fixed elementary identities. Whole-fact WD precedes every matcher.
use super::elementary_identity_helpers::*;
use crate::prelude::*;

// Every variant owns the evidence for exactly one mathematical schema.
pub enum ElementaryIdentitySearchProofByBuiltinRule {
    MinAssociative(MinAssociativeProof),
    MaxAssociative(MaxAssociativeProof),
    MinMaxSum(MinMaxSumProof),
    MinMaxProduct(MinMaxProductProof),
    MinTranslation(MinTranslationProof),
    MaxNegation(MaxNegationProof),
    FloorCharacterization(FloorCharacterizationProof),
    CeilCharacterization(CeilCharacterizationProof),
    GcdAddArgument(GcdAddArgumentProof),
    GcdNegation(GcdNegationProof),
    GcdPositiveScale(GcdPositiveScaleProof),
    RemainderIntegerShift(RemainderIntegerShiftProof),
    CartesianUnion(CartesianUnionProof),
    PowerSetIntersection(PowerSetIntersectionProof),
}

impl Runtime {
    pub(super) fn search_elementary_identity(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<ElementaryIdentitySearchProofByBuiltinRule>> {
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            // Associativity removes only parentheses, preserving all three operands.
            // Example: min(min(x,y),z)=min(x,min(y,z)), x,y,z in R.
            for (parts, constructor) in [
                (min_args as fn(&Obj) -> Option<(&Obj, &Obj)>, true),
                (max_args as fn(&Obj) -> Option<(&Obj, &Obj)>, false),
            ] {
                if let (Some((ab, c)), Some((a, bc))) = (parts(left), parts(right)) {
                    if let (Some((x, y)), Some((u, v))) = (parts(ab), parts(bc)) {
                        if same(x, a) && same(y, u) && same(c, v) {
                            return Ok(Some(if constructor {
                                MinAssociativeProof::new().into()
                            } else {
                                MaxAssociativeProof::new().into()
                            }));
                        }
                    }
                }
            }
            // Sorting a real pair preserves its sum and product.
            // Example: min(x,y)+max(x,y)=x+y.
            for (parts, sum) in [
                (add_args as fn(&Obj) -> Option<(&Obj, &Obj)>, true),
                (mul_args as fn(&Obj) -> Option<(&Obj, &Obj)>, false),
            ] {
                if let (Some((m, n)), Some((x, y))) = (parts(left), parts(right)) {
                    for (m, n) in [(m, n), (n, m)] {
                        if let (Some((a, b)), Some((c, d))) = (min_args(m), max_args(n)) {
                            if same(a, c)
                                && same(b, d)
                                && ((same(a, x) && same(b, y)) || (same(a, y) && same(b, x)))
                            {
                                return Ok(Some(if sum {
                                    MinMaxSumProof::new().into()
                                } else {
                                    MinMaxProductProof::new().into()
                                }));
                            }
                        }
                    }
                }
            }
            // A common translation commutes with minimum.
            // Example: min(x+z,y+z)=min(x,y)+z.
            if let (Some((a, b)), Some((m, z))) = (min_args(left), add_args(right)) {
                if let (Some((x, u)), Some((y, v)), Some((r, s))) =
                    (add_args(a), add_args(b), min_args(m))
                {
                    if same(u, z) && same(v, z) && same(x, r) && same(y, s) {
                        return Ok(Some(MinTranslationProof::new().into()));
                    }
                }
            }
            // Negation reverses order: max(-x,-y)=-min(x,y).
            if let (Some((a, b)), Some(m)) = (max_args(left), neg_arg(right)) {
                if let (Some(x), Some(y), Some((r, s))) = (neg_arg(a), neg_arg(b), min_args(m)) {
                    if same(x, r) && same(y, s) {
                        return Ok(Some(MaxNegationProof::new().into()));
                    }
                }
            }
            // Two integer bounds uniquely characterize floor/ceiling; never guess n.
            // Example: n in Z, n<=x<n+1 => floor(x)=n.
            let rounding = match left {
                Obj::ArithmeticOperator(ArithmeticOperator::Floor(p)) => Some((&*p.arg, true)),
                Obj::ArithmeticOperator(ArithmeticOperator::Ceil(p)) => Some((&*p.arg, false)),
                _ => None,
            };
            if let Some((x, floor)) = rounding {
                let integer_fact: Fact = InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: right.clone(),
                    set: Obj::StandardSet(StandardSet::Z),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let integer = self.verify_builtin_rule_premise(&integer_fact, state)?;
                if !integer.is_failed() {
                    let weak: Fact = LessEqualFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: if floor { right.clone() } else { x.clone() },
                        right: if floor { x.clone() } else { right.clone() },
                        line_file: fact.line_file.clone(),
                    }
                    .into();
                    let strict: Fact = LessFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        left: if floor {
                            x.clone()
                        } else {
                            sub(right, &number("1"))
                        },
                        right: if floor {
                            add(right, &number("1"))
                        } else {
                            x.clone()
                        },
                        line_file: fact.line_file.clone(),
                    }
                    .into();
                    let weak = self.verify_builtin_rule_premise(&weak, state)?;
                    if !weak.is_failed() {
                        let strict = self.verify_builtin_rule_premise(&strict, state)?;
                        if !strict.is_failed() {
                            return Ok(Some(if floor {
                                FloorCharacterizationProof::new(integer, weak, strict).into()
                            } else {
                                CeilCharacterizationProof::new(integer, weak, strict).into()
                            }));
                        }
                    }
                }
            }
            // GCD is unchanged by adding its other argument or changing a sign.
            // Example: gcd(a+b,b)=gcd(a,b); all GCD WD stays mandatory.
            if let (Some((a, b)), Some((c, d))) = (gcd_args(left), gcd_args(right)) {
                if same(b, d) {
                    if let Some((x, y)) = add_args(a) {
                        if (same(x, c) && same(y, b)) || (same(y, c) && same(x, b)) {
                            return Ok(Some(GcdAddArgumentProof::new().into()));
                        }
                    }
                    if let Some(x) = neg_arg(a) {
                        if same(x, c) {
                            return Ok(Some(GcdNegationProof::new().into()));
                        }
                    }
                }
            }
            // A positive integer common factor scales GCD.
            // Example: a,b,k in N+ => gcd(k*a,k*b)=k*gcd(a,b).
            if let (Some((ka, kb)), Some((k, g))) = (gcd_args(left), mul_args(right)) {
                if let (Some((u, a)), Some((v, b)), Some((c, d))) =
                    (mul_args(ka), mul_args(kb), gcd_args(g))
                {
                    if same(k, u) && same(k, v) && same(a, c) && same(b, d) {
                        let mut domains = Vec::new();
                        for obj in [a, b, k] {
                            let goal: Fact = InFact {
                                fact_id: self.global_ids.allocate_fact_id(),
                                element: obj.clone(),
                                set: Obj::StandardSet(StandardSet::NPos),
                                line_file: fact.line_file.clone(),
                            }
                            .into();
                            let proof = self.verify_builtin_rule_premise(&goal, state)?;
                            if proof.is_failed() {
                                break;
                            }
                            domains.push(proof);
                        }
                        if domains.len() == 3 {
                            let mut it = domains.into_iter();
                            return Ok(Some(
                                GcdPositiveScaleProof::new(
                                    it.next().unwrap(),
                                    it.next().unwrap(),
                                    it.next().unwrap(),
                                )
                                .into(),
                            ));
                        }
                    }
                }
            }
            // An explicitly supplied integer multiple does not change the residue.
            // Example: a,k in Z,m in N+ => (a+k*m)%m=a%m.
            if let (
                Obj::IntegerOperator(IntegerOperator::Mod(l)),
                Obj::IntegerOperator(IntegerOperator::Mod(r)),
            ) = (left, right)
            {
                if same(&l.right, &r.right) {
                    if let Some((a, km)) = add_args(&l.left) {
                        if same(a, &r.left) {
                            if let Some((k, m)) = mul_args(km) {
                                if same(m, &r.right) {
                                    let goal: Fact = InFact {
                                        fact_id: self.global_ids.allocate_fact_id(),
                                        element: k.clone(),
                                        set: Obj::StandardSet(StandardSet::Z),
                                        line_file: fact.line_file.clone(),
                                    }
                                    .into();
                                    let integer = self.verify_builtin_rule_premise(&goal, state)?;
                                    if !integer.is_failed() {
                                        return Ok(Some(
                                            RemainderIntegerShiftProof::new(integer).into(),
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // Cartesian product distributes over union, including empty factors.
            // Example: cart(s,union(t,u))=union(cart(s,t),cart(s,u)).
            if let (Some((s, tu)), Some((st, su))) = (cart_args(left), union_args(right)) {
                if let (Some((t, u)), Some((a, b)), Some((c, d))) =
                    (union_args(tu), cart_args(st), cart_args(su))
                {
                    if same(s, a) && same(s, c) && same(t, b) && same(u, d) {
                        return Ok(Some(CartesianUnionProof::new().into()));
                    }
                }
            }
            // A subset of both sets is exactly a subset of their intersection.
            // Example: power_set(intersect(s,t))=intersect(power_set(s),power_set(t)).
            if let (Some(st), Some((ps, pt))) = (power_set_arg(left), intersect_args(right)) {
                if let (Some((s, t)), Some(a), Some(b)) =
                    (intersect_args(st), power_set_arg(ps), power_set_arg(pt))
                {
                    if same(s, a) && same(t, b) {
                        return Ok(Some(PowerSetIntersectionProof::new().into()));
                    }
                }
            }
        }
        Ok(None)
    }
}

pub struct MinAssociativeProof {}
impl MinAssociativeProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct MaxAssociativeProof {}
impl MaxAssociativeProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct MinMaxSumProof {}
impl MinMaxSumProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct MinMaxProductProof {}
impl MinMaxProductProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct MinTranslationProof {}
impl MinTranslationProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct MaxNegationProof {}
impl MaxNegationProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct FloorCharacterizationProof {
    pub integer: VerifyFactResult,
    pub weak_bound: VerifyFactResult,
    pub strict_bound: VerifyFactResult,
}
impl FloorCharacterizationProof {
    pub fn new(
        integer: VerifyFactResult,
        weak_bound: VerifyFactResult,
        strict_bound: VerifyFactResult,
    ) -> Self {
        Self {
            integer,
            weak_bound,
            strict_bound,
        }
    }
}
pub struct CeilCharacterizationProof {
    pub integer: VerifyFactResult,
    pub weak_bound: VerifyFactResult,
    pub strict_bound: VerifyFactResult,
}
impl CeilCharacterizationProof {
    pub fn new(
        integer: VerifyFactResult,
        weak_bound: VerifyFactResult,
        strict_bound: VerifyFactResult,
    ) -> Self {
        Self {
            integer,
            weak_bound,
            strict_bound,
        }
    }
}
pub struct GcdAddArgumentProof {}
impl GcdAddArgumentProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct GcdNegationProof {}
impl GcdNegationProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct GcdPositiveScaleProof {
    pub first_positive: VerifyFactResult,
    pub second_positive: VerifyFactResult,
    pub factor_positive: VerifyFactResult,
}
impl GcdPositiveScaleProof {
    pub fn new(
        first_positive: VerifyFactResult,
        second_positive: VerifyFactResult,
        factor_positive: VerifyFactResult,
    ) -> Self {
        Self {
            first_positive,
            second_positive,
            factor_positive,
        }
    }
}
pub struct RemainderIntegerShiftProof {
    pub multiplier_integer: VerifyFactResult,
}
impl RemainderIntegerShiftProof {
    pub fn new(multiplier_integer: VerifyFactResult) -> Self {
        Self { multiplier_integer }
    }
}
pub struct CartesianUnionProof {}
impl CartesianUnionProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct PowerSetIntersectionProof {}
impl PowerSetIntersectionProof {
    pub fn new() -> Self {
        Self {}
    }
}
impl ElementaryIdentitySearchProofByBuiltinRule {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::MinAssociative(_) => "MinAssociative",
            Self::MaxAssociative(_) => "MaxAssociative",
            Self::MinMaxSum(_) => "MinMaxSum",
            Self::MinMaxProduct(_) => "MinMaxProduct",
            Self::MinTranslation(_) => "MinTranslation",
            Self::MaxNegation(_) => "MaxNegation",
            Self::FloorCharacterization(_) => "FloorCharacterization",
            Self::CeilCharacterization(_) => "CeilCharacterization",
            Self::GcdAddArgument(_) => "GcdAddArgument",
            Self::GcdNegation(_) => "GcdNegation",
            Self::GcdPositiveScale(_) => "GcdPositiveScale",
            Self::RemainderIntegerShift(_) => "RemainderIntegerShift",
            Self::CartesianUnion(_) => "CartesianUnion",
            Self::PowerSetIntersection(_) => "PowerSetIntersection",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::MinAssociative(_) => "min(min(x,y),z)=min(x,min(y,z))",
            Self::MaxAssociative(_) => "max(max(x,y),z)=max(x,max(y,z))",
            Self::MinMaxSum(_) => "min(x,y)+max(x,y)=x+y",
            Self::MinMaxProduct(_) => "min(x,y)*max(x,y)=x*y",
            Self::MinTranslation(_) => "min(x+z,y+z)=min(x,y)+z",
            Self::MaxNegation(_) => "max(-x,-y)=-min(x,y)",
            Self::FloorCharacterization(_) => "n in Z, n<=x, x<n+1 => floor(x)=n",
            Self::CeilCharacterization(_) => "n in Z, n-1<x, x<=n => ceil(x)=n",
            Self::GcdAddArgument(_) => "gcd(a+b,b)=gcd(a,b)",
            Self::GcdNegation(_) => "gcd(-a,b)=gcd(a,b)",
            Self::GcdPositiveScale(_) => "a,b,k in N+ => gcd(k*a,k*b)=k*gcd(a,b)",
            Self::RemainderIntegerShift(_) => "k in Z => (a+k*m)%m=a%m",
            Self::CartesianUnion(_) => "cart(s,union(t,u))=union(cart(s,t),cart(s,u))",
            Self::PowerSetIntersection(_) => {
                "power_set(intersect(s,t))=intersect(power_set(s),power_set(t))"
            }
        }
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/elementary_bt_completion.rs"]
mod tests;

impl From<MinAssociativeProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: MinAssociativeProof) -> Self {
        Self::MinAssociative(proof)
    }
}

impl From<MaxAssociativeProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: MaxAssociativeProof) -> Self {
        Self::MaxAssociative(proof)
    }
}

impl From<MinMaxSumProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: MinMaxSumProof) -> Self {
        Self::MinMaxSum(proof)
    }
}

impl From<MinMaxProductProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: MinMaxProductProof) -> Self {
        Self::MinMaxProduct(proof)
    }
}

impl From<MinTranslationProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: MinTranslationProof) -> Self {
        Self::MinTranslation(proof)
    }
}

impl From<MaxNegationProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: MaxNegationProof) -> Self {
        Self::MaxNegation(proof)
    }
}

impl From<FloorCharacterizationProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: FloorCharacterizationProof) -> Self {
        Self::FloorCharacterization(proof)
    }
}

impl From<CeilCharacterizationProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: CeilCharacterizationProof) -> Self {
        Self::CeilCharacterization(proof)
    }
}

impl From<GcdAddArgumentProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: GcdAddArgumentProof) -> Self {
        Self::GcdAddArgument(proof)
    }
}

impl From<GcdNegationProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: GcdNegationProof) -> Self {
        Self::GcdNegation(proof)
    }
}

impl From<GcdPositiveScaleProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: GcdPositiveScaleProof) -> Self {
        Self::GcdPositiveScale(proof)
    }
}

impl From<RemainderIntegerShiftProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: RemainderIntegerShiftProof) -> Self {
        Self::RemainderIntegerShift(proof)
    }
}

impl From<CartesianUnionProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: CartesianUnionProof) -> Self {
        Self::CartesianUnion(proof)
    }
}

impl From<PowerSetIntersectionProof> for ElementaryIdentitySearchProofByBuiltinRule {
    fn from(proof: PowerSetIntersectionProof) -> Self {
        Self::PowerSetIntersection(proof)
    }
}

impl From<ElementaryIdentitySearchProofByBuiltinRule> for EqualitySearchProofByBuiltinRule {
    fn from(proof: ElementaryIdentitySearchProofByBuiltinRule) -> Self {
        Self::ElementaryIdentity(proof)
    }
}
