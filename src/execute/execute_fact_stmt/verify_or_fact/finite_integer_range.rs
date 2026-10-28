use super::{OrBuiltinClosedIntegerRangeEqualityCover, OrBuiltinHalfOpenIntegerRangeEqualityCover};
use crate::prelude::*;

fn integer_literal(obj: &Obj) -> Option<i128> {
    match obj {
        Obj::Literal(Literal::Number(number)) => number.normalized_value.parse().ok(),
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg)) => {
            let Obj::Literal(Literal::Number(number)) = neg.arg.as_ref() else {
                return None;
            };
            if let Some(positive) = number.normalized_value.strip_prefix('-') {
                positive.parse().ok()
            } else {
                format!("-{}", number.normalized_value).parse().ok()
            }
        }
        _ => None,
    }
}

// The same 1024-value ceiling as literal range expansion. Check before allocating.
pub(crate) fn integer_range_literal_bounds(interval: &Obj) -> Option<(i128, usize)> {
    let (start, end, closed) = match interval {
        Obj::SetFormer(SetFormer::ClosedRange(range)) => (&range.start, &range.end, true),
        Obj::SetFormer(SetFormer::Range(range)) => (&range.start, &range.end, false),
        _ => return None,
    };
    let start = integer_literal(start)?;
    let end = integer_literal(end)?;
    let distance = end.checked_sub(start)?;
    let count = if closed {
        distance.checked_add(1)?
    } else {
        distance
    };
    if count <= 0 || count > 1024 {
        return None;
    }
    Some((start, usize::try_from(count).ok()?))
}

pub(crate) fn integer_range_cover_indices(
    subject: &Obj,
    interval: &Obj,
    branches: &[AndChainAtomicFact],
) -> Option<Vec<usize>> {
    let (start, count) = integer_range_literal_bounds(interval)?;
    let mut indices = vec![None; count];
    for (index, branch) in branches.iter().enumerate() {
        let AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal)) = branch else {
            return None;
        };
        let value = if equal.left.ir() == subject.ir() {
            integer_literal(&equal.right)?
        } else if equal.right.ir() == subject.ir() {
            integer_literal(&equal.left)?
        } else {
            return None;
        };
        if let Some(offset) = value
            .checked_sub(start)
            .and_then(|v| usize::try_from(v).ok())
        {
            if offset < count && indices[offset].is_none() {
                indices[offset] = Some(index);
            }
        }
    }
    indices.into_iter().collect()
}

impl Runtime {
    pub(super) fn search_or_integer_range_equality_cover(
        &mut self,
        fact: &OrFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let Some(AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(first))) = fact.facts.first()
        else {
            return Ok(None);
        };
        for subject in [&first.left, &first.right] {
            for member in self.known_memberships_of(subject) {
                for (interval, path) in self.exact_property_object_values_of_shapes(
                    &member.set,
                    &[EqualToObjShape::ClosedRange, EqualToObjShape::Range],
                ) {
                    let Some(branch_indices) =
                        integer_range_cover_indices(subject, &interval, &fact.facts)
                    else {
                        continue;
                    };
                    let membership =
                        self.verify_fact(&Fact::from(member.clone()), state.clone())?;
                    if membership.is_failed() {
                        continue;
                    }
                    let carrier_equal = KnownEqualityPathProof::new(path);
                    let rule = if matches!(interval, Obj::SetFormer(SetFormer::ClosedRange(_))) {
                        OrFactSearchProofByBuiltinRule::ClosedIntegerRangeEqualityCover(
                            OrBuiltinClosedIntegerRangeEqualityCover {
                                subject: subject.clone(),
                                interval,
                                membership,
                                carrier_equal,
                                branch_indices,
                            },
                        )
                    } else {
                        OrFactSearchProofByBuiltinRule::HalfOpenIntegerRangeEqualityCover(
                            OrBuiltinHalfOpenIntegerRangeEqualityCover {
                                subject: subject.clone(),
                                interval,
                                membership,
                                carrier_equal,
                                branch_indices,
                            },
                        )
                    };
                    return Ok(Some(OrFactSearchedProof::ByBuiltinRule(rule)));
                }
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn number(n: i128) -> Obj {
        Obj::Literal(Literal::Number(Number {
            normalized_value: n.to_string(),
        }))
    }
    fn closed(a: i128, b: i128) -> Obj {
        Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
            start: Box::new(number(a)),
            end: Box::new(number(b)),
        }))
    }
    #[test]
    fn finite_cases_cart_range_count_is_checked_before_allocation() {
        assert_eq!(integer_range_literal_bounds(&closed(-2, 2)), Some((-2, 5)));
        assert_eq!(
            integer_range_literal_bounds(&closed(1, 1024)),
            Some((1, 1024))
        );
        assert_eq!(
            integer_range_literal_bounds(&closed(i128::MAX, i128::MAX)),
            Some((i128::MAX, 1))
        );
        for interval in [closed(1, 1025), closed(1, 0), closed(i128::MIN, i128::MAX)] {
            assert!(integer_range_literal_bounds(&interval).is_none());
        }
    }
}
