use super::aggregate_identity_builtin_rule_proof::*;
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, LessEqualFact, NotInFact};
use crate::ast::obj::{ArithmeticOperator, FiniteSetSize, FiniteSetStat, IdentifierObj,
    Intersect, IteratedOperator, ListSet, Literal, Number, Obj, Pow, SetFormer, SetOperator, StandardSet};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::execute::execute_eval_stmt::evaluate_aggregate::unary_application;
use crate::execute::execute_fact_stmt::{VerifyState, VerifyEqualFactWellDefinedResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::equal_fact_result_from_success;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_equal::AnonFnApplicationBodyProof;
use crate::instantiate::collect_free_plain_ids;
use crate::rational_expression::helper::{add_objs, sub_objs, mul_objs};
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashSet;

impl Runtime {
    pub fn search_equal_fact_by_aggregate_identities(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        for (aggregate_side, other) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Some(aggregate) = aggregate_view(aggregate_side) else {
                continue;
            };
            if let Some(p) = self.aggregate_constant_identity(&aggregate, other, fact, &state)? {
                return Ok(Some(p));
            }
            if let Some(p) = self.aggregate_bridge_identity(&aggregate, other, fact, &state)? {
                return Ok(Some(p));
            }
            if let Some(p) = self.aggregate_partition_identity(&aggregate, other, fact, &state)? {
                return Ok(Some(p));
            }
            if let Some(p) =
                self.aggregate_product_fresh_insertion(&aggregate, other, fact, &state)?
            {
                return Ok(Some(p));
            }
            if let Some(p) =
                self.aggregate_product_member_removal(&aggregate, other, fact, &state)?
            {
                return Ok(Some(p));
            }
            if let Some(p) = self.aggregate_linearity_identity(&aggregate, other, fact, &state)? {
                return Ok(Some(p));
            }
            if let Some(p) = self.aggregate_scalar_identity(&aggregate, other, fact, &state)? {
                return Ok(Some(p));
            }
            if let Some(right) = aggregate_view(other) {
                if aggregate.product != right.product {
                    continue;
                }
                if let Some(p) =
                    self.aggregate_pointwise_identity(&aggregate, &right, fact, &state)?
                {
                    return Ok(Some(p));
                }
                if let Some(p) =
                    self.aggregate_reindex_identity(&aggregate, &right, fact, &state)?
                {
                    return Ok(Some(p));
                }
            }
        }
        Ok(None)
    }

    fn aggregate_constant_identity(
        &mut self,
        aggregate: &AggregationView,
        other: &Obj,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        let binder = self.fresh_internal_param();
        let index = Obj::Identifier(IdentifierObj::from_bound_name(&binder));
        let Some(call) = unary_application(aggregate.func, index) else {
            return Ok(None);
        };
        let Some(expansion) = self.expanded_named_or_literal_anon_fn_application_body(&call)?
        else {
            return Ok(None);
        };
        let mut free = HashSet::new();
        collect_free_plain_ids(&expansion.expanded_body, &HashSet::new(), &mut free);
        if free.contains(&binder.id) {
            return Ok(None);
        }
        let constant = expansion.expanded_body.clone();
        let count = match aggregate.domain {
            AggregationDomain::Range(start, end) => {
                add_objs(sub_objs(end.clone(), start.clone()), number("1"))
            }
            AggregationDomain::FiniteSet(set) => {
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                    set: Box::new(set.clone()),
                }))
            }
        };
        let mut exponent_equal = None;
        let expected = if aggregate.product {
            // Compare exponents as expressions before placing them under Pow;
            // its rational key deliberately treats a symbolic exponent as opaque.
            let exponent = if let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = other {
                let goal = equality(self, power.exponent.as_ref().clone(), count.clone(), fact);
                let proof = self.verify_builtin_rule_premise(&goal, state.clone())?;
                if proof.is_failed() {
                    return Ok(None);
                }
                exponent_equal = Some(proof);
                power.exponent.as_ref().clone()
            } else {
                count
            };
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                base: Box::new(constant.clone()),
                exponent: Box::new(exponent),
            }))
        } else {
            mul_objs(count, constant.clone())
        };
        let residual = equality(self, other.clone(), expected, fact);
        let residual_equal = self.verify_builtin_rule_premise(&residual, state.clone())?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(match (aggregate.domain, aggregate.product) {
            (AggregationDomain::Range(..), false) => {
                AggregateIdentityBuiltinRuleProof::RangeSumConstant(
                    RangeSumConstantBuiltinRuleProof {
                        function_expansion: expansion,
                        constant,
                        residual_equal,
                    },
                )
            }
            (AggregationDomain::Range(..), true) => {
                AggregateIdentityBuiltinRuleProof::RangeProductConstant(
                    RangeProductConstantBuiltinRuleProof {
                        function_expansion: expansion,
                        constant,
                        exponent_equal,
                        residual_equal,
                    },
                )
            }
            (AggregationDomain::FiniteSet(..), false) => {
                AggregateIdentityBuiltinRuleProof::FiniteSetSumConstant(
                    FiniteSetSumConstantBuiltinRuleProof {
                        function_expansion: expansion,
                        constant,
                        residual_equal,
                    },
                )
            }
            (AggregationDomain::FiniteSet(..), true) => {
                AggregateIdentityBuiltinRuleProof::FiniteSetProductConstant(
                    FiniteSetProductConstantBuiltinRuleProof {
                        function_expansion: expansion,
                        constant,
                        exponent_equal,
                        residual_equal,
                    },
                )
            }
        }))
    }

    fn aggregate_bridge_identity(
        &mut self,
        aggregate: &AggregationView,
        other: &Obj,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        let AggregationDomain::FiniteSet(Obj::SetFormer(SetFormer::ClosedRange(range))) =
            aggregate.domain
        else {
            return Ok(None);
        };
        let Some(right) = aggregate_view(other) else {
            return Ok(None);
        };
        if aggregate.product != right.product {
            return Ok(None);
        }
        let AggregationDomain::Range(start, end) = right.domain else {
            return Ok(None);
        };
        let goals = vec![
            equality(self, range.start.as_ref().clone(), start.clone(), fact),
            equality(self, range.end.as_ref().clone(), end.clone(), fact),
            equality(self, aggregate.func.clone(), right.func.clone(), fact),
        ];
        let Some(premises) = self.aggregate_identity_premises(goals, state)? else {
            return Ok(None);
        };
        Ok(Some(if aggregate.product {
            AggregateIdentityBuiltinRuleProof::FiniteSetProductRangeBridge(
                FiniteSetProductRangeBridgeBuiltinRuleProof { premises },
            )
        } else {
            AggregateIdentityBuiltinRuleProof::FiniteSetSumRangeBridge(
                FiniteSetSumRangeBridgeBuiltinRuleProof { premises },
            )
        }))
    }

    fn aggregate_partition_identity(
        &mut self,
        aggregate: &AggregationView,
        other: &Obj,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        let mut parts = Vec::new();
        flatten_fold(other, aggregate.product, &mut parts);
        if parts.len() < 2 || parts.len() > 64 {
            return Ok(None);
        }
        let Some(parts) = parts
            .into_iter()
            .map(aggregate_view)
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        if parts.iter().any(|p| p.product != aggregate.product) {
            return Ok(None);
        }
        let mut goals = Vec::new();
        match aggregate.domain {
            AggregationDomain::Range(start, end) => {
                let Some(ranges) = parts
                    .iter()
                    .map(|p| match p.domain {
                        AggregationDomain::Range(a, b) => Some((a, b)),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()
                else {
                    return Ok(None);
                };
                goals.push(equality(self, start.clone(), ranges[0].0.clone(), fact));
                goals.push(equality(
                    self,
                    end.clone(),
                    ranges.last().unwrap().1.clone(),
                    fact,
                ));
                for pair in ranges.windows(2) {
                    goals.push(equality(
                        self,
                        add_objs(pair[0].1.clone(), number("1")),
                        pair[1].0.clone(),
                        fact,
                    ));
                }
            }
            AggregationDomain::FiniteSet(set) => {
                let Obj::SetOperator(SetOperator::Union(union)) = set else {
                    return Ok(None);
                };
                if parts.len() != 2 {
                    return Ok(None);
                }
                let (AggregationDomain::FiniteSet(a), AggregationDomain::FiniteSet(b)) =
                    (parts[0].domain, parts[1].domain)
                else {
                    return Ok(None);
                };
                goals.push(equality(self, union.left.as_ref().clone(), a.clone(), fact));
                goals.push(equality(
                    self,
                    union.right.as_ref().clone(),
                    b.clone(),
                    fact,
                ));
                let intersection = Obj::SetOperator(SetOperator::Intersect(Intersect {
                    left: Box::new(a.clone()),
                    right: Box::new(b.clone()),
                }));
                goals.push(equality(
                    self,
                    intersection,
                    Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] })),
                    fact,
                ));
            }
        }
        if matches!(aggregate.domain, AggregationDomain::Range(..)) {
            for part in &parts {
                goals.push(equality(
                    self,
                    aggregate.func.clone(),
                    part.func.clone(),
                    fact,
                ));
            }
        }
        let Some(premises) = self.aggregate_identity_premises(goals, state)? else {
            return Ok(None);
        };
        // Restrictions have different function domains. What partitioning needs
        // is agreement on each part, not global equality of the functions.
        let mut callbacks = Vec::new();
        if matches!(aggregate.domain, AggregationDomain::FiniteSet(..)) {
            for part in &parts {
                let AggregationDomain::FiniteSet(domain) = part.domain else {
                    return Ok(None);
                };
                let Some(proof) = self.finite_aggregate_callback_agreement(
                    aggregate.func,
                    part.func,
                    domain,
                    fact,
                    state,
                )?
                else {
                    return Ok(None);
                };
                callbacks.push(proof);
            }
        }
        Ok(Some(match (aggregate.domain, aggregate.product) {
            (AggregationDomain::Range(..), false) => {
                AggregateIdentityBuiltinRuleProof::RangeSumPartition(
                    RangeSumPartitionBuiltinRuleProof { premises },
                )
            }
            (AggregationDomain::Range(..), true) => {
                AggregateIdentityBuiltinRuleProof::RangeProductPartition(
                    RangeProductPartitionBuiltinRuleProof { premises },
                )
            }
            (AggregationDomain::FiniteSet(..), false) => {
                AggregateIdentityBuiltinRuleProof::FiniteSetSumDisjointUnion(
                    FiniteSetSumDisjointUnionBuiltinRuleProof {
                        premises,
                        callbacks,
                    },
                )
            }
            (AggregationDomain::FiniteSet(..), true) => {
                AggregateIdentityBuiltinRuleProof::FiniteSetProductDisjointUnion(
                    FiniteSetProductDisjointUnionBuiltinRuleProof {
                        premises,
                        callbacks,
                    },
                )
            }
        }))
    }

    fn aggregate_product_fresh_insertion(
        &mut self,
        aggregate: &AggregationView,
        other: &Obj,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        // Product over S union {a} factors into the product over S and f(a)
        // when a is fresh. Restricted callbacks must agree on every x in S.
        if !aggregate.product {
            return Ok(None);
        }
        let AggregationDomain::FiniteSet(Obj::SetOperator(SetOperator::Union(union))) =
            aggregate.domain
        else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) = other else {
            return Ok(None);
        };
        for (set, singleton) in [(&*union.left, &*union.right), (&*union.right, &*union.left)] {
            let Obj::SetFormer(SetFormer::ListSet(list)) = singleton else {
                continue;
            };
            if list.list.len() != 1 {
                continue;
            }
            let element = &*list.list[0];
            for (base, factor) in [(&*mul.left, &*mul.right), (&*mul.right, &*mul.left)] {
                let Some(base) = aggregate_view(base) else {
                    continue;
                };
                if !base.product {
                    continue;
                }
                let AggregationDomain::FiniteSet(base_set) = base.domain else {
                    continue;
                };
                let fresh: Fact = NotInFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: element.clone(),
                    set: set.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let same_set = equality(self, set.clone(), base_set.clone(), fact);
                let Some(premises) =
                    self.aggregate_identity_premises(vec![fresh, same_set], state)?
                else {
                    continue;
                };
                let Some(pointwise) = self.finite_aggregate_callback_agreement(
                    aggregate.func,
                    base.func,
                    base_set,
                    fact,
                    state,
                )?
                else {
                    continue;
                };
                let mut factor_expansions = Vec::new();
                let Some(value) =
                    function_at(self, aggregate.func, element, &mut factor_expansions)?
                else {
                    continue;
                };
                let goal = equality(self, value, factor.clone(), fact);
                let factor_equal = self.verify_builtin_rule_premise(&goal, state.clone())?;
                if factor_equal.is_failed() {
                    continue;
                }
                return Ok(Some(
                    AggregateIdentityBuiltinRuleProof::FiniteSetProductFreshInsertion(
                        FiniteSetProductFreshInsertionProof {
                            premises,
                            pointwise,
                            factor_expansions,
                            factor_equal,
                        },
                    ),
                ));
            }
        }
        Ok(None)
    }

    fn aggregate_product_member_removal(
        &mut self,
        aggregate: &AggregationView,
        other: &Obj,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        // For a in S, product(S,f)=product(S\{a},g)*f(a), where g=f on S\{a}.
        // This multiplication identity remains valid when f(a)=0.
        if !aggregate.product {
            return Ok(None);
        }
        let AggregationDomain::FiniteSet(set) = aggregate.domain else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) = other else {
            return Ok(None);
        };
        for (base_obj, factor) in [(&*mul.left, &*mul.right), (&*mul.right, &*mul.left)] {
            let Some(base) = aggregate_view(base_obj) else {
                continue;
            };
            if !base.product {
                continue;
            }
            let AggregationDomain::FiniteSet(base_set) = base.domain else {
                continue;
            };
            let Obj::SetOperator(SetOperator::SetMinus(minus)) = base_set else {
                continue;
            };
            let Obj::SetFormer(SetFormer::ListSet(list)) = &*minus.right else {
                continue;
            };
            if list.list.len() != 1 {
                continue;
            }
            let element = &*list.list[0];
            let member: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: element.clone(),
                set: set.clone(),
                line_file: fact.line_file.clone(),
            }
            .into();
            let same_set = equality(self, set.clone(), *minus.left.clone(), fact);
            let Some(premises) = self.aggregate_identity_premises(vec![member, same_set], state)?
            else {
                continue;
            };
            let Some(pointwise) = self.finite_aggregate_callback_agreement(
                aggregate.func,
                base.func,
                base_set,
                fact,
                state,
            )?
            else {
                continue;
            };
            let mut factor_expansions = Vec::new();
            let Some(value) = function_at(self, aggregate.func, element, &mut factor_expansions)?
            else {
                continue;
            };
            let goal = equality(self, value, factor.clone(), fact);
            let factor_equal = self.verify_builtin_rule_premise(&goal, *state)?;
            if factor_equal.is_failed() {
                continue;
            }
            return Ok(Some(
                AggregateIdentityBuiltinRuleProof::FiniteSetProductMemberRemoval(
                    FiniteSetProductMemberRemovalProof {
                        premises,
                        pointwise,
                        factor_expansions,
                        factor_equal,
                    },
                ),
            ));
        }
        Ok(None)
    }

    // Every finite aggregate consumes its callback only on the aggregate set.
    // Parent equality WD checks the actual domains; a literal restriction is
    // agreement on this set, never a smaller-domain membership of the source.
    fn finite_aggregate_callback_agreement(
        &mut self,
        source: &Obj,
        restricted: &Obj,
        domain: &Obj,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<FinitePartitionCallbackAgreementProof>> {
        if crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal(source, restricted) {
            return Ok(Some(FinitePartitionCallbackAgreementProof::SameFunction(FinitePartitionSameFunctionProof {})));
        }
        if super::helper::finite_restriction_matches(restricted, domain, source) {
            return Ok(Some(
                FinitePartitionCallbackAgreementProof::LiteralRestriction(
                    FinitePartitionLiteralRestrictionProof {},
                ),
            ));
        }
        // Keep the checked whole-function equality route for actual aliases.
        let same_function = equality(self, source.clone(), restricted.clone(), fact);
        let equality = self.verify_builtin_rule_premise(&same_function, *state)?;
        if !equality.is_failed() {
            return Ok(Some(FinitePartitionCallbackAgreementProof::EqualFunctions(
                FinitePartitionEqualFunctionsProof { equality },
            )));
        }
        Ok(self
            .aggregate_pointwise_proof(
                AggregationDomain::FiniteSet(domain),
                fact,
                state,
                |rt, index, expansions| {
                    let Some(left) = function_at(rt, source, index, expansions)? else {
                        return Ok(None);
                    };
                    let Some(right) = function_at(rt, restricted, index, expansions)? else {
                        return Ok(None);
                    };
                    Ok(Some((left, right)))
                },
            )?
            .map(FinitePartitionCallbackAgreementProof::Pointwise))
    }

    fn aggregate_linearity_identity(
        &mut self,
        aggregate: &AggregationView,
        other: &Obj,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        let (left, right, subtract) = match other {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) if !aggregate.product => {
                (a.left.as_ref(), a.right.as_ref(), false)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) if !aggregate.product => {
                (a.left.as_ref(), a.right.as_ref(), true)
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(a))
                if aggregate.product
                    && matches!(aggregate.domain, AggregationDomain::FiniteSet(..)) =>
            {
                (a.left.as_ref(), a.right.as_ref(), false)
            }
            _ => return Ok(None),
        };
        let (Some(left), Some(right)) = (aggregate_view(left), aggregate_view(right)) else {
            return Ok(None);
        };
        if left.product != aggregate.product || right.product != aggregate.product {
            return Ok(None);
        }
        let Some(mut goals) = same_domain_goals(self, aggregate.domain, left.domain, fact) else {
            return Ok(None);
        };
        let Some(other_goals) = same_domain_goals(self, aggregate.domain, right.domain, fact)
        else {
            return Ok(None);
        };
        goals.extend(other_goals);
        let Some(premises) = self.aggregate_identity_premises(goals, state)? else {
            return Ok(None);
        };
        let Some(pointwise) = self.aggregate_pointwise_proof(
            aggregate.domain,
            fact,
            state,
            |rt, index, expansions| {
                let Some(lhs) = function_at(rt, aggregate.func, index, expansions)? else {
                    return Ok(None);
                };
                let Some(a) = function_at(rt, left.func, index, expansions)? else {
                    return Ok(None);
                };
                let Some(b) = function_at(rt, right.func, index, expansions)? else {
                    return Ok(None);
                };
                Ok(Some((
                    lhs,
                    if aggregate.product {
                        mul_objs(a, b)
                    } else if subtract {
                        sub_objs(a, b)
                    } else {
                        add_objs(a, b)
                    },
                )))
            },
        )?
        else {
            return Ok(None);
        };
        Ok(Some(
            match (aggregate.domain, aggregate.product, subtract) {
                (AggregationDomain::Range(..), false, false) => {
                    AggregateIdentityBuiltinRuleProof::RangeSumAdd(RangeSumAddBuiltinRuleProof {
                        premises,
                        pointwise,
                    })
                }
                (AggregationDomain::Range(..), false, true) => {
                    AggregateIdentityBuiltinRuleProof::RangeSumSubtract(
                        RangeSumSubtractBuiltinRuleProof {
                            premises,
                            pointwise,
                        },
                    )
                }
                (AggregationDomain::FiniteSet(..), false, false) => {
                    AggregateIdentityBuiltinRuleProof::FiniteSetSumAdd(
                        FiniteSetSumAddBuiltinRuleProof {
                            premises,
                            pointwise,
                        },
                    )
                }
                (AggregationDomain::FiniteSet(..), false, true) => {
                    AggregateIdentityBuiltinRuleProof::FiniteSetSumSubtract(
                        FiniteSetSumSubtractBuiltinRuleProof {
                            premises,
                            pointwise,
                        },
                    )
                }
                (AggregationDomain::FiniteSet(..), true, _) => {
                    AggregateIdentityBuiltinRuleProof::FiniteSetProductMultiply(
                        FiniteSetProductMultiplyBuiltinRuleProof {
                            premises,
                            pointwise,
                        },
                    )
                }
                (AggregationDomain::Range(..), true, _) => {
                    unreachable!("range products handled by partition")
                }
            },
        ))
    }

    fn aggregate_scalar_identity(
        &mut self,
        aggregate: &AggregationView,
        other: &Obj,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        if aggregate.product {
            return Ok(None);
        }
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = other else {
            return Ok(None);
        };
        for (base, scalar) in [
            (product.left.as_ref(), product.right.as_ref()),
            (product.right.as_ref(), product.left.as_ref()),
        ] {
            let Some(base) = aggregate_view(base) else {
                continue;
            };
            if base.product {
                continue;
            }
            let Some(goals) = same_domain_goals(self, aggregate.domain, base.domain, fact) else {
                continue;
            };
            let Some(premises) = self.aggregate_identity_premises(goals, state)? else {
                continue;
            };
            let Some(pointwise) = self.aggregate_pointwise_proof(
                aggregate.domain,
                fact,
                state,
                |rt, index, expansions| {
                    let Some(lhs) = function_at(rt, aggregate.func, index, expansions)? else {
                        return Ok(None);
                    };
                    let Some(rhs) = function_at(rt, base.func, index, expansions)? else {
                        return Ok(None);
                    };
                    Ok(Some((lhs, mul_objs(scalar.clone(), rhs))))
                },
            )?
            else {
                continue;
            };
            return Ok(Some(match aggregate.domain {
                AggregationDomain::Range(..) => AggregateIdentityBuiltinRuleProof::RangeSumScalar(
                    RangeSumScalarBuiltinRuleProof {
                        premises,
                        pointwise,
                    },
                ),
                AggregationDomain::FiniteSet(..) => {
                    AggregateIdentityBuiltinRuleProof::FiniteSetSumScalar(
                        FiniteSetSumScalarBuiltinRuleProof {
                            premises,
                            pointwise,
                        },
                    )
                }
            }));
        }
        Ok(None)
    }

    fn aggregate_pointwise_identity(
        &mut self,
        left: &AggregationView,
        right: &AggregationView,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        let Some(goals) = same_domain_goals(self, left.domain, right.domain, fact) else {
            return Ok(None);
        };
        let Some(premises) = self.aggregate_identity_premises(goals, state)? else {
            return Ok(None);
        };
        let Some(pointwise) =
            self.aggregate_pointwise_proof(left.domain, fact, state, |rt, index, expansions| {
                let Some(lhs) = function_at(rt, left.func, index, expansions)? else {
                    return Ok(None);
                };
                let Some(rhs) = function_at(rt, right.func, index, expansions)? else {
                    return Ok(None);
                };
                Ok(Some((lhs, rhs)))
            })?
        else {
            return Ok(None);
        };
        Ok(Some(match (left.domain, left.product) {
            (AggregationDomain::Range(..), false) => {
                AggregateIdentityBuiltinRuleProof::RangeSumPointwise(
                    RangeSumPointwiseBuiltinRuleProof {
                        premises,
                        pointwise,
                    },
                )
            }
            (AggregationDomain::Range(..), true) => {
                AggregateIdentityBuiltinRuleProof::RangeProductPointwise(
                    RangeProductPointwiseBuiltinRuleProof {
                        premises,
                        pointwise,
                    },
                )
            }
            (AggregationDomain::FiniteSet(..), false) => {
                AggregateIdentityBuiltinRuleProof::FiniteSetSumPointwise(
                    FiniteSetSumPointwiseBuiltinRuleProof {
                        premises,
                        pointwise,
                    },
                )
            }
            (AggregationDomain::FiniteSet(..), true) => {
                AggregateIdentityBuiltinRuleProof::FiniteSetProductPointwise(
                    FiniteSetProductPointwiseBuiltinRuleProof {
                        premises,
                        pointwise,
                    },
                )
            }
        }))
    }

    fn aggregate_reindex_identity(
        &mut self,
        left: &AggregationView,
        right: &AggregationView,
        fact: &EqualFact,
        state: &VerifyState,
    ) -> RuntimeResult<Option<AggregateIdentityBuiltinRuleProof>> {
        let (AggregationDomain::Range(a, b), AggregationDomain::Range(c, d)) =
            (left.domain, right.domain)
        else {
            return Ok(None);
        };
        let raw_shift = direct_shift(a, c).unwrap_or_else(|| sub_objs(c.clone(), a.clone()));
        let shift = crate::rational_expression::exact_rational::EvalRational::from_obj(&raw_shift)
            .map(|value| value.to_obj())
            .unwrap_or_else(|| raw_shift.clone());
        let end_shift = direct_shift(b, d).unwrap_or_else(|| sub_objs(d.clone(), b.clone()));
        let shift_goal = equality(self, shift.clone(), end_shift, fact);
        let integer_goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: shift.clone(),
            set: Obj::StandardSet(StandardSet::Z),
            line_file: fact.line_file.clone(),
        }));
        let normalization_goal = equality(self, raw_shift, shift.clone(), fact);
        let Some(premises) = self.aggregate_identity_premises(
            vec![normalization_goal, shift_goal, integer_goal],
            state,
        )?
        else {
            return Ok(None);
        };
        let Some(pointwise) =
            self.aggregate_pointwise_proof(left.domain, fact, state, |rt, index, expansions| {
                let Some(lhs) = function_at(rt, left.func, index, expansions)? else {
                    return Ok(None);
                };
                let Some(rhs) =
                    function_at(rt, right.func, &add_objs(index.clone(), shift), expansions)?
                else {
                    return Ok(None);
                };
                Ok(Some((lhs, rhs)))
            })?
        else {
            return Ok(None);
        };
        Ok(Some(if left.product {
            AggregateIdentityBuiltinRuleProof::RangeProductReindex(
                RangeProductReindexBuiltinRuleProof {
                    premises,
                    pointwise,
                },
            )
        } else {
            AggregateIdentityBuiltinRuleProof::RangeSumReindex(RangeSumReindexBuiltinRuleProof {
                premises,
                pointwise,
            })
        }))
    }

    fn aggregate_identity_premises(
        &mut self,
        goals: Vec<Fact>,
        state: &VerifyState,
    ) -> RuntimeResult<Option<Vec<crate::execute::execute_fact_stmt::VerifyFactResult>>> {
        let mut proofs = Vec::with_capacity(goals.len());
        for goal in goals {
            let proof = self.verify_builtin_rule_premise(&goal, state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some(proofs))
    }

    fn aggregate_pointwise_proof<F>(
        &mut self,
        domain: AggregationDomain,
        fact: &EqualFact,
        state: &VerifyState,
        build: F,
    ) -> RuntimeResult<Option<AggregatePointwiseProof>>
    where
        F: FnOnce(
            &mut Runtime,
            &Obj,
            &mut Vec<AnonFnApplicationBodyProof>,
        ) -> RuntimeResult<Option<(Obj, Obj)>>,
    {
        let parameter = self.fresh_internal_param();
        let index = Obj::Identifier(IdentifierObj::from_bound_name(&parameter));
        let (parameter_set, assumptions) = match domain {
            AggregationDomain::FiniteSet(set) => (set.clone(), vec![]),
            AggregationDomain::Range(start, end) => {
                let lo: Fact = LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: start.clone(),
                    right: index.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                let hi: Fact = LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: index.clone(),
                    right: end.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into();
                (Obj::StandardSet(StandardSet::Z), vec![lo, hi])
            }
        };
        let (inner, local_env) = self.run_in_local_env_and_take_env(|rt| {
            let parameters = TypedParameterList {
                groups: vec![TypedParameterGroup {
                    params: vec![parameter.clone()],
                    param_type: ParamType::Obj(parameter_set),
                }],
            };
            rt.define_typed_parameters_in_current_env(&parameters, None, *state)?;
            for assumption in &assumptions {
                rt.store_fact_and_infer(assumption, *state)?;
            }
            let mut expansions = Vec::new();
            let Some((left, right)) = build(rt, &index, &mut expansions)? else {
                return Ok(None);
            };
            let goal = EqualFact {
                fact_id: rt.global_ids.allocate_fact_id(),
                left,
                right,
                line_file: fact.line_file.clone(),
            };
            let proof = rt.verify_builtin_rule_premise(&goal.clone().into(), state.clone())?;
            if !proof.is_failed() {
                return Ok(Some((expansions, proof)));
            }
            // This rule explicitly consumes a known pointwise forall. It does
            // not restart general definition/strategy/rewrite truth search.
            if !state
                .allows(crate::execute::execute_fact_stmt::VerifyStateLevel::DefinitionAndForall)
            {
                return Ok(None);
            }
            let wd = match rt.verify_equal_fact_well_definedness(&goal, *state)? {
                VerifyEqualFactWellDefinedResult::Success(p) => p,
                _ => return Ok(None),
            };
            let Some(searched) = rt.search_equal_fact_proof_by_known_forall_fact(
                &goal,
                state.capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule),
            )?
            else {
                return Ok(None);
            };
            Ok(Some((
                expansions,
                equal_fact_result_from_success(&goal, wd, searched),
            )))
        })?;
        Ok(
            inner.map(|(function_expansions, equality)| AggregatePointwiseProof {
                parameter,
                assumptions,
                function_expansions,
                equality,
                local_env,
            }),
        )
    }
}

#[derive(Clone, Copy)]
enum AggregationDomain<'a> {
    Range(&'a Obj, &'a Obj),
    FiniteSet(&'a Obj),
}
struct AggregationView<'a> {
    domain: AggregationDomain<'a>,
    func: &'a Obj,
    product: bool,
}
fn aggregate_view(obj: &Obj) -> Option<AggregationView<'_>> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::Sum(s)) => Some(AggregationView {
            domain: AggregationDomain::Range(&s.start, &s.end),
            func: &s.func,
            product: false,
        }),
        Obj::IteratedOperator(IteratedOperator::Product(s)) => Some(AggregationView {
            domain: AggregationDomain::Range(&s.start, &s.end),
            func: &s.func,
            product: true,
        }),
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) => Some(AggregationView {
            domain: AggregationDomain::FiniteSet(&s.set),
            func: &s.func,
            product: false,
        }),
        Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(s)) => Some(AggregationView {
            domain: AggregationDomain::FiniteSet(&s.set),
            func: &s.func,
            product: true,
        }),
        _ => None,
    }
}
fn number(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(value.into())))
}
fn equality(rt: &mut Runtime, left: Obj, right: Obj, parent: &EqualFact) -> Fact {
    EqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: parent.line_file.clone(),
    }
    .into()
}
fn same_domain_goals(
    rt: &mut Runtime,
    left: AggregationDomain,
    right: AggregationDomain,
    fact: &EqualFact,
) -> Option<Vec<Fact>> {
    match (left, right) {
        (AggregationDomain::Range(a, b), AggregationDomain::Range(c, d)) => Some(vec![
            equality(rt, a.clone(), c.clone(), fact),
            equality(rt, b.clone(), d.clone(), fact),
        ]),
        (AggregationDomain::FiniteSet(a), AggregationDomain::FiniteSet(b)) => {
            Some(vec![equality(rt, a.clone(), b.clone(), fact)])
        }
        _ => None,
    }
}
fn flatten_fold<'a>(obj: &'a Obj, product: bool, out: &mut Vec<&'a Obj>) {
    let children = match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) if !product => {
            Some((a.left.as_ref(), a.right.as_ref()))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) if product => {
            Some((a.left.as_ref(), a.right.as_ref()))
        }
        _ => None,
    };
    if let Some((a, b)) = children {
        flatten_fold(a, product, out);
        flatten_fold(b, product, out);
    } else {
        out.push(obj);
    }
}
fn function_at(
    rt: &mut Runtime,
    function: &Obj,
    index: &Obj,
    expansions: &mut Vec<AnonFnApplicationBodyProof>,
) -> RuntimeResult<Option<Obj>> {
    let Some(call) = unary_application(function, index.clone()) else {
        return Ok(None);
    };
    if let Some(expansion) = rt.expanded_named_or_literal_anon_fn_application_body(&call)? {
        let body = expansion.expanded_body.clone();
        expansions.push(expansion);
        Ok(Some(body))
    } else {
        Ok(Some(Obj::FnObj(call)))
    }
}

fn direct_shift(before: &Obj, after: &Obj) -> Option<Obj> {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) = after {
        if before.ir() == add.left.ir() {
            return Some(add.right.as_ref().clone());
        }
        if before.ir() == add.right.ir() {
            return Some(add.left.as_ref().clone());
        }
    }
    None
}
