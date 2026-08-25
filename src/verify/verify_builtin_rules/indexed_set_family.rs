use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::{
    factual_equal_success_by_builtin_reason_with_subgoals, objs_match_for_pattern,
};

#[derive(Clone)]
enum IndexedFamilyRef {
    Union(IndexUnion),
    Intersect(IndexIntersect),
}

impl IndexedFamilyRef {
    fn from_obj(obj: &Obj) -> Option<Self> {
        match obj {
            Obj::IndexUnion(value) => Some(Self::Union(value.clone())),
            Obj::IndexIntersect(value) => Some(Self::Intersect(value.clone())),
            _ => None,
        }
    }

    fn index_set(&self) -> &Obj {
        match self {
            Self::Union(value) => value.index_set.as_ref(),
            Self::Intersect(value) => value.index_set.as_ref(),
        }
    }

    fn ambient_set(&self) -> &Obj {
        match self {
            Self::Union(value) => value.ambient_set.as_ref(),
            Self::Intersect(value) => value.ambient_set.as_ref(),
        }
    }

    fn family_fn(&self) -> &Obj {
        match self {
            Self::Union(value) => value.family_fn.as_ref(),
            Self::Intersect(value) => value.family_fn.as_ref(),
        }
    }

    fn same_operator(&self, other: &Self) -> bool {
        matches!(
            (self, other),
            (Self::Union(_), Self::Union(_)) | (Self::Intersect(_), Self::Intersect(_))
        )
    }
}

impl Runtime {
    /// Core indexed-family equalities beyond the definitional membership and
    /// empty-domain rules. Every branch is a single exact matcher and may only
    /// consume the premises displayed by that law.
    pub(super) fn try_verify_indexed_set_family_algebra_equalities(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (indexed_side, other_side) in [
            (&equal_fact.left, &equal_fact.right),
            (&equal_fact.right, &equal_fact.left),
        ] {
            let Some(indexed) = IndexedFamilyRef::from_obj(indexed_side) else {
                continue;
            };

            if self.indexed_singleton_fiber_equality_matches(&indexed, other_side)? {
                return Ok(Some(Self::indexed_family_equality_success(
                    equal_fact,
                    "indexed family over a singleton equals its selected fiber",
                    Vec::new(),
                )));
            }

            if Self::anonymous_indexed_constant_family_matches(&indexed, other_side) {
                if let Some(nonempty_result) = self.verify_index_set_nonempty_premise(
                    indexed.index_set(),
                    &equal_fact.line_file,
                    builtin_state,
                )? {
                    return Ok(Some(Self::indexed_family_equality_success(
                        equal_fact,
                        "nonempty indexed constant family equals its constant value",
                        vec![nonempty_result],
                    )));
                }
            }

            let Some(other_indexed) = IndexedFamilyRef::from_obj(other_side) else {
                continue;
            };
            if indexed.same_operator(&other_indexed)
                && objs_match_for_pattern(indexed.index_set(), other_indexed.index_set())
                && objs_match_for_pattern(indexed.ambient_set(), other_indexed.ambient_set())
            {
                if let Some(pointwise_result) = self.verify_cached_pointwise_family_relation(
                    indexed.index_set(),
                    indexed.family_fn(),
                    other_indexed.family_fn(),
                    PointwiseRelation::Equal,
                    &equal_fact.line_file,
                )? {
                    return Ok(Some(Self::indexed_family_equality_success(
                        equal_fact,
                        "indexed-family extensionality from pointwise equality",
                        vec![pointwise_result],
                    )));
                }
            }
        }

        for (whole_side, decomposition_side) in [
            (&equal_fact.left, &equal_fact.right),
            (&equal_fact.right, &equal_fact.left),
        ] {
            let Some(whole) = IndexedFamilyRef::from_obj(whole_side) else {
                continue;
            };
            if Self::indexed_domain_partition_matches(&whole, decomposition_side) {
                return Ok(Some(Self::indexed_family_equality_success(
                    equal_fact,
                    "indexed family decomposes over a domain partition",
                    Vec::new(),
                )));
            }
            if let Some(selected_index) =
                Self::indexed_singleton_peeling_index(&whole, decomposition_side)
            {
                let membership: AtomicFact = InFact::new(
                    selected_index,
                    whole.index_set().clone(),
                    equal_fact.line_file.clone(),
                )
                .into();
                let result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&membership, builtin_state)?;
                if result.is_success() {
                    return Ok(Some(Self::indexed_family_equality_success(
                        equal_fact,
                        "indexed family peels a selected singleton from its domain",
                        vec![result],
                    )));
                }
            }
        }

        if Self::indexed_domain_difference_equality_matches(&equal_fact.left, &equal_fact.right)
            || Self::indexed_domain_difference_equality_matches(&equal_fact.right, &equal_fact.left)
        {
            return Ok(Some(Self::indexed_family_equality_success(
                equal_fact,
                "indexed-family domain difference retains the result-side set difference",
                Vec::new(),
            )));
        }

        if let Some((reason, premise)) =
            Self::indexed_set_operation_equality_match(&equal_fact.left, &equal_fact.right).or_else(
                || Self::indexed_set_operation_equality_match(&equal_fact.right, &equal_fact.left),
            )
        {
            let mut steps = Vec::new();
            if let Some(premise) = premise {
                match premise {
                    IndexedEqualityPremise::Nonempty(index_set) => {
                        let Some(nonempty_result) = self.verify_index_set_nonempty_premise(
                            &index_set,
                            &equal_fact.line_file,
                            builtin_state,
                        )?
                        else {
                            return Ok(None);
                        };
                        steps.push(nonempty_result);
                    }
                    IndexedEqualityPremise::Subset(left, right) => {
                        let premise: AtomicFact =
                            SubsetFact::new(left, right, equal_fact.line_file.clone()).into();
                        let result = self
                            .verify_atomic_fact_as_builtin_rule_premise(&premise, builtin_state)?;
                        if !result.is_success() {
                            return Ok(None);
                        }
                        steps.push(result);
                    }
                }
            }
            return Ok(Some(Self::indexed_family_equality_success(
                equal_fact, reason, steps,
            )));
        }

        if let Some(reason) = self
            .indexed_set_family_adapter_equality_match(&equal_fact.left, &equal_fact.right)
            .or_else(|| {
                self.indexed_set_family_adapter_equality_match(&equal_fact.right, &equal_fact.left)
            })
        {
            return Ok(Some(Self::indexed_family_equality_success(
                equal_fact,
                reason,
                Vec::new(),
            )));
        }

        Ok(None)
    }

    /// Phase-one subset laws for indexed union/intersection. This is called by
    /// the existing subset owner and does not perform transitive search.
    pub(super) fn try_verify_indexed_set_family_algebra_subset(
        &mut self,
        subset_fact: &SubsetFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Obj::IndexUnion(index_union) = &subset_fact.right {
            if let Some(index) = self.family_application_index_matching(
                index_union.family_fn.as_ref(),
                &subset_fact.left,
            )? {
                let membership: AtomicFact = InFact::new(
                    index,
                    index_union.index_set.as_ref().clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                if let Some(steps) =
                    self.verify_builtin_rule_premises(&[membership], builtin_state)?
                {
                    return Ok(Some(Self::indexed_family_subset_success(
                        subset_fact,
                        "selected fiber is contained in indexed union",
                        steps,
                    )));
                }
            }
        }
        if let Obj::IndexIntersect(index_intersect) = &subset_fact.left {
            if let Some(index) = self.family_application_index_matching(
                index_intersect.family_fn.as_ref(),
                &subset_fact.right,
            )? {
                let membership: AtomicFact = InFact::new(
                    index,
                    index_intersect.index_set.as_ref().clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                if let Some(steps) =
                    self.verify_builtin_rule_premises(&[membership], builtin_state)?
                {
                    return Ok(Some(Self::indexed_family_subset_success(
                        subset_fact,
                        "indexed intersection is contained in a selected fiber",
                        steps,
                    )));
                }
            }
        }

        if let (Some(left), Some(right)) = (
            IndexedFamilyRef::from_obj(&subset_fact.left),
            IndexedFamilyRef::from_obj(&subset_fact.right),
        ) {
            if left.same_operator(&right)
                && objs_match_for_pattern(left.index_set(), right.index_set())
                && objs_match_for_pattern(left.ambient_set(), right.ambient_set())
            {
                if let Some(pointwise_result) = self.verify_cached_pointwise_family_relation(
                    left.index_set(),
                    left.family_fn(),
                    right.family_fn(),
                    PointwiseRelation::Subset,
                    &subset_fact.line_file,
                )? {
                    return Ok(Some(Self::indexed_family_subset_success(
                        subset_fact,
                        "indexed-family monotonicity from pointwise subset",
                        vec![pointwise_result],
                    )));
                }
            }
        }

        if let Obj::IndexUnion(index_union) = &subset_fact.left {
            if let Some(pointwise_result) = self.verify_cached_pointwise_family_relation_to_set(
                index_union.index_set.as_ref(),
                index_union.family_fn.as_ref(),
                &subset_fact.right,
                PointwiseBoundDirection::FamilySubsetSet,
                &subset_fact.line_file,
            )? {
                return Ok(Some(Self::indexed_family_subset_success(
                    subset_fact,
                    "indexed union is contained in a common pointwise upper bound",
                    vec![pointwise_result],
                )));
            }
        }
        if let Obj::IndexIntersect(index_intersect) = &subset_fact.right {
            if let Some(pointwise_result) = self.verify_cached_pointwise_family_relation_to_set(
                index_intersect.index_set.as_ref(),
                index_intersect.family_fn.as_ref(),
                &subset_fact.left,
                PointwiseBoundDirection::SetSubsetFamily,
                &subset_fact.line_file,
            )? {
                let ambient_premise: AtomicFact = SubsetFact::new(
                    subset_fact.left.clone(),
                    index_intersect.ambient_set.as_ref().clone(),
                    subset_fact.line_file.clone(),
                )
                .into();
                let ambient_result = self
                    .verify_atomic_fact_as_builtin_rule_premise(&ambient_premise, builtin_state)?;
                if ambient_result.is_success() {
                    return Ok(Some(Self::indexed_family_subset_success(
                        subset_fact,
                        "common lower bound is contained in indexed intersection",
                        vec![ambient_result, pointwise_result],
                    )));
                }
            }
        }

        if let Some((smaller, larger, is_union)) =
            Self::indexed_domain_monotonicity_parts(&subset_fact.left, &subset_fact.right)
        {
            let domain_premise: AtomicFact = SubsetFact::new(
                smaller.index_set().clone(),
                larger.index_set().clone(),
                subset_fact.line_file.clone(),
            )
            .into();
            if let Some(steps) =
                self.verify_builtin_rule_premises(&[domain_premise], builtin_state)?
            {
                let reason = if is_union {
                    "indexed union is monotone in its index domain"
                } else {
                    "indexed intersection is antitone in its index domain"
                };
                return Ok(Some(Self::indexed_family_subset_success(
                    subset_fact,
                    reason,
                    steps,
                )));
            }
        }

        if Self::indexed_domain_intersection_subset_matches(&subset_fact.left, &subset_fact.right) {
            return Ok(Some(Self::indexed_family_subset_success(
                subset_fact,
                "indexed family domain-intersection inclusion",
                Vec::new(),
            )));
        }

        if let Some(reason) = Self::indexed_pointwise_set_operation_subset_matches(
            &subset_fact.left,
            &subset_fact.right,
        ) {
            return Ok(Some(Self::indexed_family_subset_success(
                subset_fact,
                reason,
                Vec::new(),
            )));
        }

        if let Some(reason) =
            Self::indexed_set_family_adapter_subset_match(&subset_fact.left, &subset_fact.right)
        {
            return Ok(Some(Self::indexed_family_subset_success(
                subset_fact,
                reason,
                Vec::new(),
            )));
        }

        Ok(None)
    }

    fn indexed_family_equality_success(
        equal_fact: &EqualFact,
        reason: &str,
        steps: Vec<StmtResult>,
    ) -> StmtResult {
        factual_equal_success_by_builtin_reason_with_subgoals(equal_fact, reason, steps)
    }

    fn indexed_family_subset_success(
        subset_fact: &SubsetFact,
        reason: &str,
        steps: Vec<StmtResult>,
    ) -> StmtResult {
        SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
            subset_fact.clone().into(),
            reason.to_string(),
            steps,
        )
        .into()
    }

    fn indexed_singleton_fiber_equality_matches(
        &self,
        indexed: &IndexedFamilyRef,
        other_side: &Obj,
    ) -> Result<bool, RuntimeError> {
        let Obj::ListSet(singleton) = indexed.index_set() else {
            return Ok(false);
        };
        if singleton.list.len() != 1 {
            return Ok(false);
        }
        let Some(application) = self
            .apply_indexed_family_once(indexed.family_fn(), singleton.list[0].as_ref().clone())?
        else {
            return Ok(false);
        };
        Ok(objs_match_for_pattern(&application, other_side))
    }

    fn family_application_index_matching(
        &self,
        family: &Obj,
        candidate: &Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        let Obj::FnObj(application) = candidate else {
            return Ok(None);
        };
        if application.body.len() != 1 || application.body[0].len() != 1 {
            return Ok(None);
        }
        let application_head: Obj = application.head.as_ref().clone().into();
        if !objs_match_for_pattern(&application_head, family) {
            return Ok(None);
        }
        let index = application.body[0][0].as_ref().clone();
        let Some(expected) = self.apply_indexed_family_once(family, index.clone())? else {
            return Ok(None);
        };
        Ok(objs_match_for_pattern(&expected, candidate).then_some(index))
    }

    fn apply_indexed_family_once(
        &self,
        family: &Obj,
        index: Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        let Some(head) = FnObjHead::from_callable_obj(family.clone()) else {
            return Ok(None);
        };
        let application: Obj = FnObj::new(head, vec![vec![Box::new(index)]]).into();
        Ok(Some(
            self.beta_reduce_complete_anonymous_application_once(&application)?
                .unwrap_or(application),
        ))
    }

    pub(super) fn verify_index_set_nonempty_premise(
        &mut self,
        index_set: &Obj,
        line_file: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let nonempty: AtomicFact =
            IsNonemptySetFact::new(index_set.clone(), line_file.clone()).into();
        if matches!(index_set, Obj::ListSet(list) if !list.list.is_empty()) {
            return Ok(Some(
                SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
                    nonempty.into(),
                    "nonempty literal index set".to_string(),
                    Vec::new(),
                )
                .into(),
            ));
        }
        let result = self.verify_atomic_fact_as_builtin_rule_premise(&nonempty, builtin_state)?;
        Ok(result.is_success().then_some(result))
    }

    pub(super) fn indexed_family_pointwise_finite_fact(
        &self,
        index_set: &Obj,
        family: &Obj,
        line_file: &LineFile,
    ) -> Result<Option<ForallFact>, RuntimeError> {
        let param_name = self.generate_internal_binder_name();
        let param_group =
            self.fresh_param_group_with_type(vec![param_name], ParamType::Obj(index_set.clone()))?;
        let param = obj_for_bound_param_in_scope(&param_group.params[0]);
        let Some(fiber) = self.apply_indexed_family_once(family, param)? else {
            return Ok(None);
        };
        let finite_fiber: AtomicFact = IsFiniteSetFact::new(fiber, line_file.clone()).into();
        Ok(Some(ForallFact::new_canonical_forall(
            TypedParameterList::new(vec![param_group]),
            Vec::new(),
            vec![finite_fiber.into()],
            line_file.clone(),
        )?))
    }

    pub(super) fn indexed_family_finite_or_nonempty_fiber_exists_fact(
        &self,
        index_set: &Obj,
        family: &Obj,
        finite: bool,
        line_file: &LineFile,
    ) -> Result<Option<ExistFactEnum>, RuntimeError> {
        let param_name = self.generate_internal_binder_name();
        let param_group =
            self.fresh_param_group_with_type(vec![param_name], ParamType::Obj(index_set.clone()))?;
        let param = obj_for_bound_param_in_scope(&param_group.params[0]);
        let Some(fiber) = self.apply_indexed_family_once(family, param)? else {
            return Ok(None);
        };
        let predicate: AtomicFact = if finite {
            IsFiniteSetFact::new(fiber, line_file.clone()).into()
        } else {
            IsNonemptySetFact::new(fiber, line_file.clone()).into()
        };
        Ok(Some(ExistFactEnum::ExistFact(ExistentialSpec::new(
            TypedParameterList::new(vec![param_group]),
            vec![predicate.into()],
            line_file.clone(),
        )?)))
    }

    fn verify_cached_pointwise_family_relation(
        &mut self,
        index_set: &Obj,
        left_family: &Obj,
        right_family: &Obj,
        relation: PointwiseRelation,
        line_file: &LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(forall_fact) = self.pointwise_family_relation_fact(
            index_set,
            left_family,
            right_family,
            relation,
            line_file,
        )?
        else {
            return Ok(None);
        };
        self.verify_forall_fact_from_known_cache_only(&forall_fact)
    }

    fn verify_cached_pointwise_family_relation_to_set(
        &mut self,
        index_set: &Obj,
        family: &Obj,
        bound: &Obj,
        direction: PointwiseBoundDirection,
        line_file: &LineFile,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let param_name = self.generate_internal_binder_name();
        let param_group =
            self.fresh_param_group_with_type(vec![param_name], ParamType::Obj(index_set.clone()))?;
        let param_obj = obj_for_bound_param_in_scope(&param_group.params[0]);
        let Some(fiber) = self.apply_indexed_family_once(family, param_obj)? else {
            return Ok(None);
        };
        let pointwise: AtomicFact = match direction {
            PointwiseBoundDirection::FamilySubsetSet => {
                SubsetFact::new(fiber, bound.clone(), line_file.clone()).into()
            }
            PointwiseBoundDirection::SetSubsetFamily => {
                SubsetFact::new(bound.clone(), fiber, line_file.clone()).into()
            }
        };
        let forall_fact = ForallFact::new_canonical_forall(
            TypedParameterList::new(vec![param_group]),
            vec![],
            vec![pointwise.into()],
            line_file.clone(),
        )?;
        self.verify_forall_fact_from_known_cache_only(&forall_fact)
    }

    fn pointwise_family_relation_fact(
        &self,
        index_set: &Obj,
        left_family: &Obj,
        right_family: &Obj,
        relation: PointwiseRelation,
        line_file: &LineFile,
    ) -> Result<Option<ForallFact>, RuntimeError> {
        let param_name = self.generate_internal_binder_name();
        let param_group =
            self.fresh_param_group_with_type(vec![param_name], ParamType::Obj(index_set.clone()))?;
        let param_obj = obj_for_bound_param_in_scope(&param_group.params[0]);
        let Some(left_fiber) = self.apply_indexed_family_once(left_family, param_obj.clone())?
        else {
            return Ok(None);
        };
        let Some(right_fiber) = self.apply_indexed_family_once(right_family, param_obj)? else {
            return Ok(None);
        };
        let pointwise: AtomicFact = match relation {
            PointwiseRelation::Equal => {
                EqualFact::new(left_fiber, right_fiber, line_file.clone()).into()
            }
            PointwiseRelation::Subset => {
                SubsetFact::new(left_fiber, right_fiber, line_file.clone()).into()
            }
        };
        Ok(Some(ForallFact::new_canonical_forall(
            TypedParameterList::new(vec![param_group]),
            vec![],
            vec![pointwise.into()],
            line_file.clone(),
        )?))
    }

    fn anonymous_indexed_constant_family_matches(
        indexed: &IndexedFamilyRef,
        expected_constant: &Obj,
    ) -> bool {
        let expected_ret: Obj = PowerSet::new(indexed.ambient_set().clone()).into();
        Self::anonymous_family_body_matches(
            indexed.family_fn(),
            indexed.index_set(),
            &expected_ret,
            &mut |_, body| objs_match_for_pattern(body, expected_constant),
        )
    }

    fn anonymous_family_body_matches(
        candidate: &Obj,
        expected_domain: &Obj,
        expected_return_set: &Obj,
        body_matches: &mut dyn FnMut(&Obj, &Obj) -> bool,
    ) -> bool {
        let anonymous = match candidate {
            Obj::AnonymousFn(anonymous) => anonymous,
            Obj::FnObj(function) if function.body.is_empty() => match function.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(anonymous) => anonymous.as_ref(),
                _ => return false,
            },
            _ => return false,
        };
        if !anonymous.body.dom_facts.is_empty()
            || anonymous.body.set_bound_parameters.number_of_params() != 1
            || anonymous.body.set_bound_parameters.len() != 1
        {
            return false;
        }
        let param_group = &anonymous.body.set_bound_parameters.as_slice()[0];
        if !objs_match_for_pattern(param_group.set_obj(), expected_domain)
            || !objs_match_for_pattern(anonymous.body.ret_set.as_ref(), expected_return_set)
        {
            return false;
        }
        let Some(param_binding) = anonymous.body.get_param_bindings().first().cloned() else {
            return false;
        };
        let param_obj = obj_for_bound_param_in_scope(&param_binding);
        body_matches(&param_obj, anonymous.equal_to.as_ref())
    }

    fn indexed_domain_partition_matches(whole: &IndexedFamilyRef, decomposition: &Obj) -> bool {
        let (left_branch, right_branch) = match (whole, decomposition) {
            (IndexedFamilyRef::Union(_), Obj::Union(binary)) => {
                (binary.left.as_ref(), binary.right.as_ref())
            }
            (IndexedFamilyRef::Intersect(_), Obj::Intersect(binary)) => {
                (binary.left.as_ref(), binary.right.as_ref())
            }
            _ => return false,
        };
        Self::indexed_domain_partition_branches_match(whole, left_branch, right_branch)
            || Self::indexed_domain_partition_branches_match(whole, right_branch, left_branch)
    }

    fn indexed_domain_partition_branches_match(
        whole: &IndexedFamilyRef,
        difference_branch_obj: &Obj,
        intersection_branch_obj: &Obj,
    ) -> bool {
        let (Some(difference_branch), Some(intersection_branch)) = (
            IndexedFamilyRef::from_obj(difference_branch_obj),
            IndexedFamilyRef::from_obj(intersection_branch_obj),
        ) else {
            return false;
        };
        if !whole.same_operator(&difference_branch)
            || !whole.same_operator(&intersection_branch)
            || !objs_match_for_pattern(whole.ambient_set(), difference_branch.ambient_set())
            || !objs_match_for_pattern(whole.ambient_set(), intersection_branch.ambient_set())
        {
            return false;
        }
        let Obj::SetMinus(domain_difference) = difference_branch.index_set() else {
            return false;
        };
        let Obj::Intersect(domain_intersection) = intersection_branch.index_set() else {
            return false;
        };
        if !objs_match_for_pattern(domain_difference.left.as_ref(), whole.index_set())
            || !objs_match_for_pattern(domain_intersection.left.as_ref(), whole.index_set())
            || !objs_match_for_pattern(
                domain_difference.right.as_ref(),
                domain_intersection.right.as_ref(),
            )
        {
            return false;
        }
        Self::anonymous_indexed_family_restriction_matches(
            whole.family_fn(),
            difference_branch.index_set(),
            whole.ambient_set(),
            difference_branch.family_fn(),
        ) && Self::anonymous_indexed_family_restriction_matches(
            whole.family_fn(),
            intersection_branch.index_set(),
            whole.ambient_set(),
            intersection_branch.family_fn(),
        )
    }

    fn indexed_singleton_peeling_index(
        whole: &IndexedFamilyRef,
        decomposition: &Obj,
    ) -> Option<Obj> {
        let (left, right) = match (whole, decomposition) {
            (IndexedFamilyRef::Union(_), Obj::Union(binary)) => {
                (binary.left.as_ref(), binary.right.as_ref())
            }
            (IndexedFamilyRef::Intersect(_), Obj::Intersect(binary)) => {
                (binary.left.as_ref(), binary.right.as_ref())
            }
            _ => return None,
        };
        Self::indexed_singleton_peeling_ordered(whole, left, right)
            .or_else(|| Self::indexed_singleton_peeling_ordered(whole, right, left))
    }

    fn indexed_singleton_peeling_ordered(
        whole: &IndexedFamilyRef,
        restricted_obj: &Obj,
        fiber_obj: &Obj,
    ) -> Option<Obj> {
        let restricted = IndexedFamilyRef::from_obj(restricted_obj)?;
        if !whole.same_operator(&restricted)
            || !objs_match_for_pattern(whole.ambient_set(), restricted.ambient_set())
        {
            return None;
        }
        let Obj::SetMinus(domain_difference) = restricted.index_set() else {
            return None;
        };
        if !objs_match_for_pattern(domain_difference.left.as_ref(), whole.index_set()) {
            return None;
        }
        let Obj::ListSet(singleton) = domain_difference.right.as_ref() else {
            return None;
        };
        if singleton.list.len() != 1
            || !Self::anonymous_indexed_family_restriction_matches(
                whole.family_fn(),
                restricted.index_set(),
                whole.ambient_set(),
                restricted.family_fn(),
            )
        {
            return None;
        }
        let index = singleton.list[0].as_ref().clone();
        let Obj::FnObj(application) = fiber_obj else {
            return None;
        };
        if application.body.len() != 1
            || application.body[0].len() != 1
            || !objs_match_for_pattern(application.body[0][0].as_ref(), &index)
        {
            return None;
        }
        let application_head: Obj = application.head.as_ref().clone().into();
        objs_match_for_pattern(&application_head, whole.family_fn()).then_some(index)
    }

    fn indexed_domain_monotonicity_parts(
        left: &Obj,
        right: &Obj,
    ) -> Option<(IndexedFamilyRef, IndexedFamilyRef, bool)> {
        match (left, right) {
            (Obj::IndexUnion(smaller), Obj::IndexUnion(larger))
                if objs_match_for_pattern(
                    smaller.ambient_set.as_ref(),
                    larger.ambient_set.as_ref(),
                ) && Self::anonymous_indexed_family_restriction_matches(
                    larger.family_fn.as_ref(),
                    smaller.index_set.as_ref(),
                    larger.ambient_set.as_ref(),
                    smaller.family_fn.as_ref(),
                ) =>
            {
                Some((
                    IndexedFamilyRef::Union(smaller.clone()),
                    IndexedFamilyRef::Union(larger.clone()),
                    true,
                ))
            }
            (Obj::IndexIntersect(larger), Obj::IndexIntersect(smaller))
                if objs_match_for_pattern(
                    smaller.ambient_set.as_ref(),
                    larger.ambient_set.as_ref(),
                ) && Self::anonymous_indexed_family_restriction_matches(
                    larger.family_fn.as_ref(),
                    smaller.index_set.as_ref(),
                    larger.ambient_set.as_ref(),
                    smaller.family_fn.as_ref(),
                ) =>
            {
                Some((
                    IndexedFamilyRef::Intersect(smaller.clone()),
                    IndexedFamilyRef::Intersect(larger.clone()),
                    false,
                ))
            }
            _ => None,
        }
    }

    fn indexed_domain_intersection_subset_matches(left: &Obj, right: &Obj) -> bool {
        if let (Obj::IndexUnion(overlap), Obj::Intersect(result)) = (left, right) {
            let (Obj::IndexUnion(first), Obj::IndexUnion(second)) =
                (result.left.as_ref(), result.right.as_ref())
            else {
                return false;
            };
            return Self::indexed_overlap_union_branches_match(overlap, first, second)
                || Self::indexed_overlap_union_branches_match(overlap, second, first);
        }
        if let (Obj::Union(source), Obj::IndexIntersect(overlap)) = (left, right) {
            let (Obj::IndexIntersect(first), Obj::IndexIntersect(second)) =
                (source.left.as_ref(), source.right.as_ref())
            else {
                return false;
            };
            return Self::indexed_overlap_intersect_branches_match(overlap, first, second)
                || Self::indexed_overlap_intersect_branches_match(overlap, second, first);
        }
        false
    }

    fn indexed_overlap_union_branches_match(
        overlap: &IndexUnion,
        first: &IndexUnion,
        second: &IndexUnion,
    ) -> bool {
        let Obj::Intersect(domain_overlap) = overlap.index_set.as_ref() else {
            return false;
        };
        Self::indexed_three_restrictions_share_family(
            overlap.index_set.as_ref(),
            overlap.ambient_set.as_ref(),
            overlap.family_fn.as_ref(),
            domain_overlap.left.as_ref(),
            first.ambient_set.as_ref(),
            first.family_fn.as_ref(),
            domain_overlap.right.as_ref(),
            second.ambient_set.as_ref(),
            second.family_fn.as_ref(),
        ) && objs_match_for_pattern(first.index_set.as_ref(), domain_overlap.left.as_ref())
            && objs_match_for_pattern(second.index_set.as_ref(), domain_overlap.right.as_ref())
    }

    fn indexed_overlap_intersect_branches_match(
        overlap: &IndexIntersect,
        first: &IndexIntersect,
        second: &IndexIntersect,
    ) -> bool {
        let Obj::Intersect(domain_overlap) = overlap.index_set.as_ref() else {
            return false;
        };
        Self::indexed_three_restrictions_share_family(
            overlap.index_set.as_ref(),
            overlap.ambient_set.as_ref(),
            overlap.family_fn.as_ref(),
            domain_overlap.left.as_ref(),
            first.ambient_set.as_ref(),
            first.family_fn.as_ref(),
            domain_overlap.right.as_ref(),
            second.ambient_set.as_ref(),
            second.family_fn.as_ref(),
        ) && objs_match_for_pattern(first.index_set.as_ref(), domain_overlap.left.as_ref())
            && objs_match_for_pattern(second.index_set.as_ref(), domain_overlap.right.as_ref())
    }

    #[allow(clippy::too_many_arguments)]
    fn indexed_three_restrictions_share_family(
        first_domain: &Obj,
        ambient: &Obj,
        first_family: &Obj,
        second_domain: &Obj,
        second_ambient: &Obj,
        second_family: &Obj,
        third_domain: &Obj,
        third_ambient: &Obj,
        third_family: &Obj,
    ) -> bool {
        if !objs_match_for_pattern(ambient, second_ambient)
            || !objs_match_for_pattern(ambient, third_ambient)
        {
            return false;
        }
        let Some(original) = Self::restriction_original_family(first_family, first_domain, ambient)
        else {
            return false;
        };
        Self::restriction_original_family(second_family, second_domain, ambient)
            .is_some_and(|candidate| objs_match_for_pattern(&candidate, &original))
            && Self::restriction_original_family(third_family, third_domain, ambient)
                .is_some_and(|candidate| objs_match_for_pattern(&candidate, &original))
    }

    fn indexed_set_family_adapter_equality_match(
        &self,
        adapter_side: &Obj,
        expanded_side: &Obj,
    ) -> Option<&'static str> {
        if Self::indexed_singleton_range_matches(adapter_side, expanded_side) {
            return Some("indexed union of singleton fibers equals function range");
        }
        if self.function_range_domain_union_matches(adapter_side, expanded_side) {
            return Some("function range decomposes over a union domain");
        }
        if Self::power_set_indexed_intersection_matches(adapter_side, expanded_side) {
            return Some("power set commutes with indexed intersection");
        }
        if Self::cart_indexed_family_matches(adapter_side, expanded_side) {
            return Some("fixed-coordinate Cartesian product commutes with indexed family");
        }
        if Self::cart_set_minus_matches(adapter_side, expanded_side) {
            return Some("Cartesian product preserves set difference in one coordinate");
        }
        if Self::general_cart_pointwise_intersection_matches(adapter_side, expanded_side) {
            return Some("general Cartesian product preserves pointwise intersection");
        }
        None
    }

    fn indexed_set_family_adapter_subset_match(left: &Obj, right: &Obj) -> Option<&'static str> {
        // Union of fiber powersets is contained in the powerset of the union.
        if let (Obj::IndexUnion(indexed), Obj::PowerSet(result_power_set)) = (left, right) {
            let Obj::IndexUnion(source) = result_power_set.set.as_ref() else {
                return None;
            };
            if objs_match_for_pattern(indexed.index_set.as_ref(), source.index_set.as_ref()) {
                let expected_ambient: Obj =
                    PowerSet::new(source.ambient_set.as_ref().clone()).into();
                if objs_match_for_pattern(indexed.ambient_set.as_ref(), &expected_ambient)
                    && Self::anonymous_transformed_family_matches(
                        &IndexedFamilyRef::Union(indexed.clone()),
                        &mut |param, body| {
                            let Obj::PowerSet(fiber_power_set) = body else {
                                return false;
                            };
                            Self::family_application_matches(
                                fiber_power_set.set.as_ref(),
                                source.family_fn.as_ref(),
                                param,
                            )
                        },
                    )
                {
                    return Some("indexed union of powersets is contained in powerset of union");
                }
            }
        }

        // general_cart(A) union general_cart(B) is contained in the product
        // of the pointwise unions.
        if let (Obj::Union(binary), Obj::GeneralCart(target)) = (left, right) {
            let (Obj::GeneralCart(first), Obj::GeneralCart(second)) =
                (binary.left.as_ref(), binary.right.as_ref())
            else {
                return None;
            };
            if Self::general_cart_binary_target_matches(target, first, second, SetBinaryKind::Union)
                || Self::general_cart_binary_target_matches(
                    target,
                    second,
                    first,
                    SetBinaryKind::Union,
                )
            {
                return Some("general Cartesian product pointwise-union inclusion");
            }
        }
        None
    }

    fn indexed_singleton_range_matches(indexed_side: &Obj, range_side: &Obj) -> bool {
        let (Obj::IndexUnion(indexed), Obj::FnRange(range)) = (indexed_side, range_side) else {
            return false;
        };
        let mut function = None;
        let matched = Self::anonymous_transformed_family_matches(
            &IndexedFamilyRef::Union(indexed.clone()),
            &mut |param, body| {
                let Obj::ListSet(singleton) = body else {
                    return false;
                };
                if singleton.list.len() != 1 {
                    return false;
                }
                function = Self::family_from_application_at(singleton.list[0].as_ref(), param);
                function.is_some()
            },
        );
        matched
            && function
                .is_some_and(|function| objs_match_for_pattern(&function, range.function.as_ref()))
    }

    fn function_range_domain_union_matches(&self, range_side: &Obj, split_side: &Obj) -> bool {
        let (Obj::FnRange(whole), Obj::Union(split)) = (range_side, split_side) else {
            return false;
        };
        let (Obj::FnRange(first), Obj::FnRange(second)) =
            (split.left.as_ref(), split.right.as_ref())
        else {
            return false;
        };
        self.function_range_domain_union_ordered(whole, first, second)
            || self.function_range_domain_union_ordered(whole, second, first)
    }

    fn function_range_domain_union_ordered(
        &self,
        whole: &FnRange,
        first: &FnRange,
        second: &FnRange,
    ) -> bool {
        let Some((first_original, first_domain, first_ret)) =
            Self::anonymous_function_restriction_parts(first.function.as_ref())
        else {
            return false;
        };
        let Some((second_original, second_domain, second_ret)) =
            Self::anonymous_function_restriction_parts(second.function.as_ref())
        else {
            return false;
        };
        if !objs_match_for_pattern(&first_original, whole.function.as_ref())
            || !objs_match_for_pattern(&second_original, whole.function.as_ref())
            || !objs_match_for_pattern(&first_ret, &second_ret)
        {
            return false;
        }
        let Some(body) = self.get_fn_range_function_body(whole.function.as_ref()) else {
            return false;
        };
        if body.set_bound_parameters.number_of_params() != 1
            || body.set_bound_parameters.len() != 1
            || !objs_match_for_pattern(body.ret_set.as_ref(), &first_ret)
        {
            return false;
        }
        let Obj::Union(whole_domain) = body.set_bound_parameters.as_slice()[0].set_obj() else {
            return false;
        };
        (objs_match_for_pattern(whole_domain.left.as_ref(), &first_domain)
            && objs_match_for_pattern(whole_domain.right.as_ref(), &second_domain))
            || (objs_match_for_pattern(whole_domain.left.as_ref(), &second_domain)
                && objs_match_for_pattern(whole_domain.right.as_ref(), &first_domain))
    }

    fn anonymous_function_restriction_parts(candidate: &Obj) -> Option<(Obj, Obj, Obj)> {
        let anonymous = match candidate {
            Obj::AnonymousFn(anonymous) => anonymous,
            Obj::FnObj(function) if function.body.is_empty() => match function.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(anonymous) => anonymous.as_ref(),
                _ => return None,
            },
            _ => return None,
        };
        if !anonymous.body.dom_facts.is_empty()
            || anonymous.body.set_bound_parameters.number_of_params() != 1
            || anonymous.body.set_bound_parameters.len() != 1
        {
            return None;
        }
        let param_binding = anonymous.body.get_param_bindings().first()?.clone();
        let param = obj_for_bound_param_in_scope(&param_binding);
        let original = Self::family_from_application_at(anonymous.equal_to.as_ref(), &param)?;
        Some((
            original,
            anonymous.body.set_bound_parameters.as_slice()[0]
                .set_obj()
                .clone(),
            anonymous.body.ret_set.as_ref().clone(),
        ))
    }

    fn power_set_indexed_intersection_matches(power_set_side: &Obj, indexed_side: &Obj) -> bool {
        let (Obj::PowerSet(power_set), Obj::IndexIntersect(target)) =
            (power_set_side, indexed_side)
        else {
            return false;
        };
        let Obj::IndexIntersect(source) = power_set.set.as_ref() else {
            return false;
        };
        let expected_ambient: Obj = PowerSet::new(source.ambient_set.as_ref().clone()).into();
        objs_match_for_pattern(source.index_set.as_ref(), target.index_set.as_ref())
            && objs_match_for_pattern(target.ambient_set.as_ref(), &expected_ambient)
            && Self::anonymous_transformed_family_matches(
                &IndexedFamilyRef::Intersect(target.clone()),
                &mut |param, body| {
                    let Obj::PowerSet(fiber_power_set) = body else {
                        return false;
                    };
                    Self::family_application_matches(
                        fiber_power_set.set.as_ref(),
                        source.family_fn.as_ref(),
                        param,
                    )
                },
            )
    }

    fn cart_indexed_family_matches(cart_side: &Obj, indexed_side: &Obj) -> bool {
        let (Obj::Cart(cart), Some(target)) = (cart_side, IndexedFamilyRef::from_obj(indexed_side))
        else {
            return false;
        };
        if cart.args.len() != 2 {
            return false;
        }
        for indexed_position in [0usize, 1usize] {
            let Some(source) = IndexedFamilyRef::from_obj(cart.args[indexed_position].as_ref())
            else {
                continue;
            };
            if !source.same_operator(&target)
                || !objs_match_for_pattern(source.index_set(), target.index_set())
            {
                continue;
            }
            let external_position = 1 - indexed_position;
            let external = cart.args[external_position].as_ref();
            let Obj::Cart(target_ambient) = target.ambient_set() else {
                continue;
            };
            if target_ambient.args.len() != 2
                || !objs_match_for_pattern(
                    target_ambient.args[external_position].as_ref(),
                    external,
                )
                || !objs_match_for_pattern(
                    target_ambient.args[indexed_position].as_ref(),
                    source.ambient_set(),
                )
            {
                continue;
            }
            if Self::anonymous_transformed_family_matches(&target, &mut |param, body| {
                let Obj::Cart(fiber_cart) = body else {
                    return false;
                };
                fiber_cart.args.len() == 2
                    && objs_match_for_pattern(fiber_cart.args[external_position].as_ref(), external)
                    && Self::family_application_matches(
                        fiber_cart.args[indexed_position].as_ref(),
                        source.family_fn(),
                        param,
                    )
            }) {
                return true;
            }
        }
        false
    }

    // A fixed Cartesian coordinate preserves relative complement.
    // Example: `cart(C, set_minus(A, B)) = set_minus(cart(C, A), cart(C, B))`.
    fn cart_set_minus_matches(cart_side: &Obj, difference_side: &Obj) -> bool {
        let (Obj::Cart(source_cart), Obj::SetMinus(result_difference)) =
            (cart_side, difference_side)
        else {
            return false;
        };
        let (Obj::Cart(left_cart), Obj::Cart(right_cart)) = (
            result_difference.left.as_ref(),
            result_difference.right.as_ref(),
        ) else {
            return false;
        };
        if source_cart.args.len() != 2 || left_cart.args.len() != 2 || right_cart.args.len() != 2 {
            return false;
        }

        for difference_position in [0usize, 1usize] {
            let fixed_position = 1 - difference_position;
            let Obj::SetMinus(source_difference) = source_cart.args[difference_position].as_ref()
            else {
                continue;
            };
            if objs_match_for_pattern(
                left_cart.args[fixed_position].as_ref(),
                source_cart.args[fixed_position].as_ref(),
            ) && objs_match_for_pattern(
                right_cart.args[fixed_position].as_ref(),
                source_cart.args[fixed_position].as_ref(),
            ) && objs_match_for_pattern(
                left_cart.args[difference_position].as_ref(),
                source_difference.left.as_ref(),
            ) && objs_match_for_pattern(
                right_cart.args[difference_position].as_ref(),
                source_difference.right.as_ref(),
            ) {
                return true;
            }
        }
        false
    }

    fn general_cart_pointwise_intersection_matches(
        general_cart_side: &Obj,
        intersection_side: &Obj,
    ) -> bool {
        let (Obj::GeneralCart(target), Obj::Intersect(binary)) =
            (general_cart_side, intersection_side)
        else {
            return false;
        };
        let (Obj::GeneralCart(first), Obj::GeneralCart(second)) =
            (binary.left.as_ref(), binary.right.as_ref())
        else {
            return false;
        };
        Self::general_cart_binary_target_matches(target, first, second, SetBinaryKind::Intersect)
            || Self::general_cart_binary_target_matches(
                target,
                second,
                first,
                SetBinaryKind::Intersect,
            )
    }

    fn general_cart_binary_target_matches(
        target: &GeneralCart,
        first: &GeneralCart,
        second: &GeneralCart,
        operation: SetBinaryKind,
    ) -> bool {
        if !objs_match_for_pattern(target.index_set.as_ref(), first.index_set.as_ref())
            || !objs_match_for_pattern(target.index_set.as_ref(), second.index_set.as_ref())
            || !objs_match_for_pattern(target.family_set.as_ref(), first.family_set.as_ref())
            || !objs_match_for_pattern(target.family_set.as_ref(), second.family_set.as_ref())
        {
            return false;
        }
        Self::anonymous_family_body_matches(
            target.family_fn.as_ref(),
            target.index_set.as_ref(),
            target.family_set.as_ref(),
            &mut |param, body| {
                let Some((left, right)) = Self::binary_operands(body, operation) else {
                    return false;
                };
                Self::family_application_matches(left, first.family_fn.as_ref(), param)
                    && Self::family_application_matches(right, second.family_fn.as_ref(), param)
            },
        )
    }

    fn indexed_set_operation_equality_match(
        transformed_side: &Obj,
        expanded_side: &Obj,
    ) -> Option<(&'static str, Option<IndexedEqualityPremise>)> {
        if Self::indexed_demorgan_matches(transformed_side, expanded_side) {
            return Some(("indexed-family De Morgan law", None));
        }
        if let Some(nonempty_index) =
            Self::indexed_external_commutative_operation_matches(transformed_side, expanded_side)
        {
            return Some((
                "external union/intersection distributes over indexed family",
                nonempty_index.map(IndexedEqualityPremise::Nonempty),
            ));
        }
        if let Some(premise) =
            Self::indexed_external_set_minus_match(transformed_side, expanded_side)
        {
            return Some((
                "external set difference distributes over indexed family",
                premise,
            ));
        }
        if Self::indexed_pointwise_binary_equality_matches(transformed_side, expanded_side) {
            return Some(("pointwise set operation over indexed families", None));
        }
        None
    }

    fn indexed_demorgan_matches(set_minus_side: &Obj, indexed_side: &Obj) -> bool {
        let Obj::SetMinus(complement) = set_minus_side else {
            return false;
        };
        let Some(source) = IndexedFamilyRef::from_obj(complement.right.as_ref()) else {
            return false;
        };
        if !objs_match_for_pattern(complement.left.as_ref(), source.ambient_set()) {
            return false;
        }
        let Some(target) = IndexedFamilyRef::from_obj(indexed_side) else {
            return false;
        };
        if source.same_operator(&target)
            || !objs_match_for_pattern(source.index_set(), target.index_set())
            || !objs_match_for_pattern(source.ambient_set(), target.ambient_set())
        {
            return false;
        }
        Self::anonymous_transformed_family_matches(&target, &mut |param, body| {
            let Obj::SetMinus(fiber_complement) = body else {
                return false;
            };
            objs_match_for_pattern(fiber_complement.left.as_ref(), source.ambient_set())
                && Self::family_application_matches(
                    fiber_complement.right.as_ref(),
                    source.family_fn(),
                    param,
                )
        })
    }

    /// The returned index set is present only for `C union U_D(A)`, whose
    /// empty-domain boundary differs from the other external laws.
    fn indexed_external_commutative_operation_matches(
        outer_side: &Obj,
        transformed_side: &Obj,
    ) -> Option<Option<Obj>> {
        for operation in [SetBinaryKind::Intersect, SetBinaryKind::Union] {
            let Some((external, source)) =
                Self::external_operand_and_indexed_family(outer_side, operation)
            else {
                continue;
            };
            let Some(target) = IndexedFamilyRef::from_obj(transformed_side) else {
                continue;
            };
            if !source.same_operator(&target)
                || !objs_match_for_pattern(source.index_set(), target.index_set())
            {
                continue;
            }
            let expected_ambient_matches = match (operation, &source) {
                (SetBinaryKind::Intersect, IndexedFamilyRef::Union(_)) => {
                    objs_match_for_pattern(source.ambient_set(), target.ambient_set())
                }
                (SetBinaryKind::Intersect, IndexedFamilyRef::Intersect(_)) => {
                    Self::commutative_binary_matches(
                        target.ambient_set(),
                        SetBinaryKind::Intersect,
                        external,
                        source.ambient_set(),
                    )
                }
                (SetBinaryKind::Union, _) => Self::commutative_binary_matches(
                    target.ambient_set(),
                    SetBinaryKind::Union,
                    external,
                    source.ambient_set(),
                ),
                (SetBinaryKind::SetMinus, _) => false,
            };
            if !expected_ambient_matches
                || !Self::anonymous_transformed_family_matches(&target, &mut |param, body| {
                    Self::commutative_binary_matches(
                        body,
                        operation,
                        external,
                        &Self::family_application_pattern(source.family_fn(), param),
                    )
                })
            {
                continue;
            }
            return Some(
                matches!(
                    (operation, &source),
                    (SetBinaryKind::Union, IndexedFamilyRef::Union(_))
                )
                .then(|| source.index_set().clone()),
            );
        }
        None
    }

    fn indexed_external_set_minus_match(
        left: &Obj,
        right: &Obj,
    ) -> Option<Option<IndexedEqualityPremise>> {
        let Obj::SetMinus(set_minus) = left else {
            return None;
        };

        // U(A) set_minus C and M(A) set_minus C.
        if let Some(source) = IndexedFamilyRef::from_obj(set_minus.left.as_ref()) {
            if let Some(target) = IndexedFamilyRef::from_obj(right) {
                let expected_ambient: Obj = SetMinus::new(
                    source.ambient_set().clone(),
                    set_minus.right.as_ref().clone(),
                )
                .into();
                if source.same_operator(&target)
                    && objs_match_for_pattern(source.index_set(), target.index_set())
                    && objs_match_for_pattern(&expected_ambient, target.ambient_set())
                    && Self::anonymous_transformed_family_matches(&target, &mut |param, body| {
                        let Obj::SetMinus(fiber_minus) = body else {
                            return false;
                        };
                        Self::family_application_matches(
                            fiber_minus.left.as_ref(),
                            source.family_fn(),
                            param,
                        ) && objs_match_for_pattern(
                            fiber_minus.right.as_ref(),
                            set_minus.right.as_ref(),
                        )
                    })
                {
                    return Some(None);
                }
            }
        }

        let source = IndexedFamilyRef::from_obj(set_minus.right.as_ref())?;
        let external = set_minus.left.as_ref();

        // C set_minus U(A) = M(C set_minus A).
        if matches!(&source, IndexedFamilyRef::Union(_)) {
            if let Some(target @ IndexedFamilyRef::Intersect(_)) = IndexedFamilyRef::from_obj(right)
            {
                if objs_match_for_pattern(source.index_set(), target.index_set())
                    && objs_match_for_pattern(external, target.ambient_set())
                    && Self::anonymous_left_minus_family_matches(&target, external, &source)
                {
                    return Some(None);
                }
            }
        }

        if !matches!(&source, IndexedFamilyRef::Intersect(_)) {
            return None;
        }

        // C set_minus M(A) = (C set_minus X) union U(C set_minus A).
        if let Obj::Union(correction_union) = right {
            for (correction, indexed_term) in [
                (
                    correction_union.left.as_ref(),
                    correction_union.right.as_ref(),
                ),
                (
                    correction_union.right.as_ref(),
                    correction_union.left.as_ref(),
                ),
            ] {
                let expected_correction: Obj =
                    SetMinus::new(external.clone(), source.ambient_set().clone()).into();
                let Some(target @ IndexedFamilyRef::Union(_)) =
                    IndexedFamilyRef::from_obj(indexed_term)
                else {
                    continue;
                };
                if objs_match_for_pattern(correction, &expected_correction)
                    && objs_match_for_pattern(source.index_set(), target.index_set())
                    && objs_match_for_pattern(external, target.ambient_set())
                    && Self::anonymous_left_minus_family_matches(&target, external, &source)
                {
                    return Some(None);
                }
            }
        }

        // If C subset X, the correction term is empty and may be omitted.
        if let Some(target @ IndexedFamilyRef::Union(_)) = IndexedFamilyRef::from_obj(right) {
            if objs_match_for_pattern(source.index_set(), target.index_set())
                && objs_match_for_pattern(external, target.ambient_set())
                && Self::anonymous_left_minus_family_matches(&target, external, &source)
            {
                return Some(Some(IndexedEqualityPremise::Subset(
                    external.clone(),
                    source.ambient_set().clone(),
                )));
            }
        }
        None
    }

    fn anonymous_left_minus_family_matches(
        target: &IndexedFamilyRef,
        external: &Obj,
        source: &IndexedFamilyRef,
    ) -> bool {
        Self::anonymous_transformed_family_matches(target, &mut |param, body| {
            let Obj::SetMinus(fiber_minus) = body else {
                return false;
            };
            objs_match_for_pattern(fiber_minus.left.as_ref(), external)
                && Self::family_application_matches(
                    fiber_minus.right.as_ref(),
                    source.family_fn(),
                    param,
                )
        })
    }

    fn indexed_pointwise_binary_equality_matches(left: &Obj, right: &Obj) -> bool {
        let Some(transformed) = IndexedFamilyRef::from_obj(left) else {
            return false;
        };
        for operation in [
            SetBinaryKind::Union,
            SetBinaryKind::Intersect,
            SetBinaryKind::SetMinus,
        ] {
            let Some((first_family, second_family)) =
                Self::anonymous_pointwise_binary_families(&transformed, operation)
            else {
                continue;
            };
            match (&transformed, operation, right) {
                (IndexedFamilyRef::Union(_), SetBinaryKind::Union, Obj::Union(binary)) => {
                    if Self::binary_indexed_family_operands_match(
                        binary.left.as_ref(),
                        binary.right.as_ref(),
                        &transformed,
                        &first_family,
                        &second_family,
                        true,
                    ) {
                        return true;
                    }
                }
                (
                    IndexedFamilyRef::Intersect(_),
                    SetBinaryKind::Intersect,
                    Obj::Intersect(binary),
                ) => {
                    if Self::binary_indexed_family_operands_match(
                        binary.left.as_ref(),
                        binary.right.as_ref(),
                        &transformed,
                        &first_family,
                        &second_family,
                        true,
                    ) {
                        return true;
                    }
                }
                (
                    IndexedFamilyRef::Intersect(_),
                    SetBinaryKind::SetMinus,
                    Obj::SetMinus(binary),
                ) => {
                    if Self::mixed_indexed_family_operands_match(
                        binary.left.as_ref(),
                        binary.right.as_ref(),
                        &transformed,
                        &first_family,
                        &second_family,
                    ) {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn indexed_pointwise_set_operation_subset_matches(
        left: &Obj,
        right: &Obj,
    ) -> Option<&'static str> {
        // U(A intersect B) subset U(A) intersect U(B).
        if let (Some(transformed @ IndexedFamilyRef::Union(_)), Obj::Intersect(binary)) =
            (IndexedFamilyRef::from_obj(left), right)
        {
            if let Some((first, second)) =
                Self::anonymous_pointwise_binary_families(&transformed, SetBinaryKind::Intersect)
            {
                if Self::binary_indexed_family_operands_match(
                    binary.left.as_ref(),
                    binary.right.as_ref(),
                    &transformed,
                    &first,
                    &second,
                    true,
                ) {
                    return Some("pointwise intersection indexed-union inclusion");
                }
            }
        }

        // M(A) union M(B) subset M(A union B).
        if let (Obj::Union(binary), Some(transformed @ IndexedFamilyRef::Intersect(_))) =
            (left, IndexedFamilyRef::from_obj(right))
        {
            if let Some((first, second)) =
                Self::anonymous_pointwise_binary_families(&transformed, SetBinaryKind::Union)
            {
                if Self::binary_indexed_family_operands_match(
                    binary.left.as_ref(),
                    binary.right.as_ref(),
                    &transformed,
                    &first,
                    &second,
                    true,
                ) {
                    return Some("pointwise union indexed-intersection inclusion");
                }
            }
        }

        // U(A) set_minus U(B) subset U(A set_minus B).
        if let (Obj::SetMinus(binary), Some(transformed @ IndexedFamilyRef::Union(_))) =
            (left, IndexedFamilyRef::from_obj(right))
        {
            if let Some((first, second)) =
                Self::anonymous_pointwise_binary_families(&transformed, SetBinaryKind::SetMinus)
            {
                if Self::binary_indexed_family_operands_match(
                    binary.left.as_ref(),
                    binary.right.as_ref(),
                    &transformed,
                    &first,
                    &second,
                    false,
                ) {
                    return Some("lower mixed set-difference indexed-union inclusion");
                }
            }
        }

        // U(A set_minus B) subset U(A) set_minus M(B).
        if let (Some(transformed @ IndexedFamilyRef::Union(_)), Obj::SetMinus(binary)) =
            (IndexedFamilyRef::from_obj(left), right)
        {
            if let Some((first, second)) =
                Self::anonymous_pointwise_binary_families(&transformed, SetBinaryKind::SetMinus)
            {
                if Self::mixed_union_intersect_operands_match(
                    binary.left.as_ref(),
                    binary.right.as_ref(),
                    &transformed,
                    &first,
                    &second,
                ) {
                    return Some("upper mixed set-difference indexed-union inclusion");
                }
            }
        }
        None
    }

    fn anonymous_transformed_family_matches(
        target: &IndexedFamilyRef,
        body_matches: &mut dyn FnMut(&Obj, &Obj) -> bool,
    ) -> bool {
        let expected_ret: Obj = PowerSet::new(target.ambient_set().clone()).into();
        Self::anonymous_family_body_matches(
            target.family_fn(),
            target.index_set(),
            &expected_ret,
            body_matches,
        )
    }

    fn anonymous_pointwise_binary_families(
        target: &IndexedFamilyRef,
        operation: SetBinaryKind,
    ) -> Option<(Obj, Obj)> {
        let mut families = None;
        let matched = Self::anonymous_transformed_family_matches(target, &mut |param, body| {
            let Some((left, right)) = Self::binary_operands(body, operation) else {
                return false;
            };
            let (Some(first), Some(second)) = (
                Self::family_from_application_at(left, param),
                Self::family_from_application_at(right, param),
            ) else {
                return false;
            };
            families = Some((first, second));
            true
        });
        matched.then_some(families).flatten()
    }

    fn binary_indexed_family_operands_match(
        left: &Obj,
        right: &Obj,
        template: &IndexedFamilyRef,
        first_family: &Obj,
        second_family: &Obj,
        commutative: bool,
    ) -> bool {
        Self::ordered_indexed_family_operands_match(
            left,
            right,
            template,
            first_family,
            second_family,
        ) || (commutative
            && Self::ordered_indexed_family_operands_match(
                left,
                right,
                template,
                second_family,
                first_family,
            ))
    }

    fn ordered_indexed_family_operands_match(
        left: &Obj,
        right: &Obj,
        template: &IndexedFamilyRef,
        first_family: &Obj,
        second_family: &Obj,
    ) -> bool {
        let (Some(first), Some(second)) = (
            IndexedFamilyRef::from_obj(left),
            IndexedFamilyRef::from_obj(right),
        ) else {
            return false;
        };
        template.same_operator(&first)
            && template.same_operator(&second)
            && Self::indexed_ref_matches_family(&first, template, first_family)
            && Self::indexed_ref_matches_family(&second, template, second_family)
    }

    fn mixed_indexed_family_operands_match(
        left: &Obj,
        right: &Obj,
        template: &IndexedFamilyRef,
        first_family: &Obj,
        second_family: &Obj,
    ) -> bool {
        let (
            Some(first @ IndexedFamilyRef::Intersect(_)),
            Some(second @ IndexedFamilyRef::Union(_)),
        ) = (
            IndexedFamilyRef::from_obj(left),
            IndexedFamilyRef::from_obj(right),
        )
        else {
            return false;
        };
        Self::indexed_ref_matches_family(&first, template, first_family)
            && Self::indexed_ref_matches_family(&second, template, second_family)
    }

    fn mixed_union_intersect_operands_match(
        left: &Obj,
        right: &Obj,
        template: &IndexedFamilyRef,
        first_family: &Obj,
        second_family: &Obj,
    ) -> bool {
        let (
            Some(first @ IndexedFamilyRef::Union(_)),
            Some(second @ IndexedFamilyRef::Intersect(_)),
        ) = (
            IndexedFamilyRef::from_obj(left),
            IndexedFamilyRef::from_obj(right),
        )
        else {
            return false;
        };
        Self::indexed_ref_matches_family(&first, template, first_family)
            && Self::indexed_ref_matches_family(&second, template, second_family)
    }

    fn indexed_ref_matches_family(
        indexed: &IndexedFamilyRef,
        template: &IndexedFamilyRef,
        family: &Obj,
    ) -> bool {
        objs_match_for_pattern(indexed.index_set(), template.index_set())
            && objs_match_for_pattern(indexed.ambient_set(), template.ambient_set())
            && objs_match_for_pattern(indexed.family_fn(), family)
    }

    fn external_operand_and_indexed_family(
        obj: &Obj,
        operation: SetBinaryKind,
    ) -> Option<(&Obj, IndexedFamilyRef)> {
        let (left, right) = Self::binary_operands(obj, operation)?;
        if let Some(indexed) = IndexedFamilyRef::from_obj(left) {
            return Some((right, indexed));
        }
        IndexedFamilyRef::from_obj(right).map(|indexed| (left, indexed))
    }

    fn binary_operands(obj: &Obj, operation: SetBinaryKind) -> Option<(&Obj, &Obj)> {
        match (operation, obj) {
            (SetBinaryKind::Union, Obj::Union(binary)) => {
                Some((binary.left.as_ref(), binary.right.as_ref()))
            }
            (SetBinaryKind::Intersect, Obj::Intersect(binary)) => {
                Some((binary.left.as_ref(), binary.right.as_ref()))
            }
            (SetBinaryKind::SetMinus, Obj::SetMinus(binary)) => {
                Some((binary.left.as_ref(), binary.right.as_ref()))
            }
            _ => None,
        }
    }

    fn commutative_binary_matches(
        candidate: &Obj,
        operation: SetBinaryKind,
        first: &Obj,
        second: &Obj,
    ) -> bool {
        let Some((left, right)) = Self::binary_operands(candidate, operation) else {
            return false;
        };
        (objs_match_for_pattern(left, first) && objs_match_for_pattern(right, second))
            || (objs_match_for_pattern(left, second) && objs_match_for_pattern(right, first))
    }

    fn family_application_pattern(family: &Obj, param: &Obj) -> Obj {
        let head = FnObjHead::from_callable_obj(family.clone())
            .expect("well-defined indexed family is callable");
        FnObj::new(head, vec![vec![Box::new(param.clone())]]).into()
    }

    fn family_application_matches(candidate: &Obj, family: &Obj, param: &Obj) -> bool {
        objs_match_for_pattern(candidate, &Self::family_application_pattern(family, param))
    }

    fn family_from_application_at(candidate: &Obj, param: &Obj) -> Option<Obj> {
        let Obj::FnObj(application) = candidate else {
            return None;
        };
        if application.body.len() != 1
            || application.body[0].len() != 1
            || !objs_match_for_pattern(application.body[0][0].as_ref(), param)
        {
            return None;
        }
        Some(application.head.as_ref().clone().into())
    }

    fn indexed_domain_difference_equality_matches(left: &Obj, right: &Obj) -> bool {
        match (left, right) {
            (Obj::SetMinus(lhs), Obj::SetMinus(rhs)) => {
                match (
                    lhs.left.as_ref(),
                    lhs.right.as_ref(),
                    rhs.left.as_ref(),
                    rhs.right.as_ref(),
                ) {
                    (
                        Obj::IndexUnion(d_left),
                        Obj::IndexUnion(e_left),
                        Obj::IndexUnion(d_minus_e),
                        Obj::IndexUnion(e_right),
                    ) => Self::indexed_union_domain_difference_parts_match(
                        d_left, e_left, d_minus_e, e_right,
                    ),
                    (
                        Obj::IndexIntersect(d_left),
                        Obj::IndexIntersect(e_left),
                        Obj::IndexIntersect(d_right),
                        Obj::IndexIntersect(e_minus_d),
                    ) => Self::indexed_intersect_domain_difference_parts_match(
                        d_left, e_left, d_right, e_minus_d,
                    ),
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn indexed_union_domain_difference_parts_match(
        d_left: &IndexUnion,
        e_left: &IndexUnion,
        d_minus_e: &IndexUnion,
        e_right: &IndexUnion,
    ) -> bool {
        let Obj::SetMinus(domain_difference) = d_minus_e.index_set.as_ref() else {
            return false;
        };
        if !objs_match_for_pattern(domain_difference.left.as_ref(), d_left.index_set.as_ref())
            || !objs_match_for_pattern(domain_difference.right.as_ref(), e_left.index_set.as_ref())
            || !Self::indexed_family_objects_match(e_left, e_right)
        {
            return false;
        }
        Self::indexed_three_restrictions_share_family(
            d_left.index_set.as_ref(),
            d_left.ambient_set.as_ref(),
            d_left.family_fn.as_ref(),
            e_left.index_set.as_ref(),
            e_left.ambient_set.as_ref(),
            e_left.family_fn.as_ref(),
            d_minus_e.index_set.as_ref(),
            d_minus_e.ambient_set.as_ref(),
            d_minus_e.family_fn.as_ref(),
        )
    }

    fn indexed_intersect_domain_difference_parts_match(
        d_left: &IndexIntersect,
        e_left: &IndexIntersect,
        d_right: &IndexIntersect,
        e_minus_d: &IndexIntersect,
    ) -> bool {
        let Obj::SetMinus(domain_difference) = e_minus_d.index_set.as_ref() else {
            return false;
        };
        if !objs_match_for_pattern(domain_difference.left.as_ref(), e_left.index_set.as_ref())
            || !objs_match_for_pattern(domain_difference.right.as_ref(), d_left.index_set.as_ref())
            || !Self::indexed_intersect_objects_match(d_left, d_right)
        {
            return false;
        }
        Self::indexed_three_restrictions_share_family(
            d_left.index_set.as_ref(),
            d_left.ambient_set.as_ref(),
            d_left.family_fn.as_ref(),
            e_left.index_set.as_ref(),
            e_left.ambient_set.as_ref(),
            e_left.family_fn.as_ref(),
            e_minus_d.index_set.as_ref(),
            e_minus_d.ambient_set.as_ref(),
            e_minus_d.family_fn.as_ref(),
        )
    }

    fn indexed_family_objects_match(left: &IndexUnion, right: &IndexUnion) -> bool {
        objs_match_for_pattern(left.index_set.as_ref(), right.index_set.as_ref())
            && objs_match_for_pattern(left.ambient_set.as_ref(), right.ambient_set.as_ref())
            && objs_match_for_pattern(left.family_fn.as_ref(), right.family_fn.as_ref())
    }

    fn indexed_intersect_objects_match(left: &IndexIntersect, right: &IndexIntersect) -> bool {
        objs_match_for_pattern(left.index_set.as_ref(), right.index_set.as_ref())
            && objs_match_for_pattern(left.ambient_set.as_ref(), right.ambient_set.as_ref())
            && objs_match_for_pattern(left.family_fn.as_ref(), right.family_fn.as_ref())
    }

    fn restriction_original_family(
        restriction: &Obj,
        expected_domain: &Obj,
        expected_ambient: &Obj,
    ) -> Option<Obj> {
        let expected_ret: Obj = PowerSet::new(expected_ambient.clone()).into();
        let mut original = None;
        let matched = Self::anonymous_family_body_matches(
            restriction,
            expected_domain,
            &expected_ret,
            &mut |param, body| {
                let Obj::FnObj(application) = body else {
                    return false;
                };
                if application.body.len() != 1
                    || application.body[0].len() != 1
                    || !objs_match_for_pattern(application.body[0][0].as_ref(), param)
                {
                    return false;
                }
                original = Some(application.head.as_ref().clone().into());
                true
            },
        );
        matched.then_some(original).flatten()
    }
}

#[derive(Clone, Copy)]
enum PointwiseRelation {
    Equal,
    Subset,
}

#[derive(Clone, Copy)]
enum PointwiseBoundDirection {
    FamilySubsetSet,
    SetSubsetFamily,
}

#[derive(Clone, Copy)]
enum SetBinaryKind {
    Union,
    Intersect,
    SetMinus,
}

enum IndexedEqualityPremise {
    Nonempty(Obj),
    Subset(Obj, Obj),
}
