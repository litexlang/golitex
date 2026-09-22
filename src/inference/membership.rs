use crate::prelude::*;
use std::collections::HashMap;

/// Objects whose equality key may own reusable function-set knowledge.
pub fn object_eligible_for_function_set_knowledge(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Atom(AtomObj::Identifier(_))
            | Obj::Atom(AtomObj::IdentifierWithMod(_))
            | Obj::Atom(AtomObj::Bound(_))
            | Obj::ObjAtIndex(_)
            | Obj::ObjAsStructInstanceWithFieldAccess(_)
    )
}

/// Extra map keys so `FnObj` well-defined lookup (`Identifier` head) finds entries
/// registered under exact bound-symbol identity rather than display spelling.
fn extra_known_fn_set_keys_for_bare_name_lookup(element: &Obj) -> Vec<String> {
    match element {
        Obj::Atom(AtomObj::Identifier(p)) => vec![p.name.clone()],
        Obj::Atom(AtomObj::IdentifierWithMod(p)) => vec![
            p.name.clone(),
            format!("{}{}{}", p.mod_name, MOD_SIGN, p.name),
        ],
        Obj::Atom(AtomObj::Bound(p)) => vec![p.name().to_string()],
        _ => vec![],
    }
}

impl Runtime {
    fn upsert_known_fn_info_for_key(
        object_knowledge: &mut ObjectPropertyMemory,
        key: ObjString,
        body: Option<(FnSetBody, LineFile, Option<FactId>)>,
        equal_to: Option<(Obj, LineFile)>,
    ) {
        if body.is_none() && equal_to.is_none() {
            return;
        }
        let info = object_knowledge.function_set_mut(key);
        if let Some((body, line_file, membership_fact_id)) = body {
            // Once a defining RHS is paired with a signature, later
            // registrations must not replace only that signature: its
            // parameter bindings are the substitution keys used by the RHS.
            if info.equal_to.is_none() || info.fn_set.is_none() {
                info.fn_set = Some((body, line_file));
                info.fn_set_membership_fact_id = membership_fact_id;
            }
        }
        if let Some((equal_to, line_file)) = equal_to {
            // A checked `have fn` stores the canonical RHS together with the
            // signature.  Later equalities such as
            // `qh = fn(x S) Z {q(h(x))}` are ordinary consequences, not a
            // redefinition.  Replacing the stored RHS here can detach its
            // parameter SymbolIds from the stored FnSetBody, so unfolding
            // `qh(a)` leaves the original binder instead of substituting `a`.
            // Keep the first checked defining RHS and only fill this slot
            // when the callable had a signature but no definition yet.
            if info.equal_to.is_none() {
                info.equal_to = Some((equal_to, line_file));
            }
        }
    }

    /// Record `element` as having function signature `body` (same lookup keys as `element $in fn ...` infer).
    /// When `equal_to` is `Some`, stores the defining expression (e.g. from `a = '…{…}` or `have fn`).
    pub fn register_function_set_knowledge_for_element(
        &mut self,
        element: &Obj,
        body: FnSetBody,
        membership_fact_id: Option<FactId>,
        equal_to: Option<Obj>,
        fn_signature_line_file: LineFile,
        defining_expr_line_file: LineFile,
    ) {
        if !object_eligible_for_function_set_knowledge(element) {
            return;
        }
        let key = element.to_string();
        let env = self.top_level_env();
        let body_opt = Some((
            body.clone(),
            fn_signature_line_file.clone(),
            membership_fact_id,
        ));
        let equal_opt = equal_to
            .clone()
            .map(|eq| (eq, defining_expr_line_file.clone()));
        Self::upsert_known_fn_info_for_key(
            &mut env.object_properties,
            key.clone(),
            body_opt,
            equal_opt.clone(),
        );
        for alternate_key in extra_known_fn_set_keys_for_bare_name_lookup(element) {
            if alternate_key != key {
                Self::upsert_known_fn_info_for_key(
                    &mut env.object_properties,
                    alternate_key,
                    Some((
                        body.clone(),
                        fn_signature_line_file.clone(),
                        membership_fact_id,
                    )),
                    equal_opt.clone(),
                );
            }
        }
    }

    // RHS is a function space `FnSet`: record it in the element's object-knowledge profile.
    pub fn infer_membership_in_fn_set_from_in_fact(
        &mut self,
        in_fact: &InFact,
        fn_set_with_dom: &FnSet,
    ) -> Result<SuccessInferResult, RuntimeError> {
        if !object_eligible_for_function_set_knowledge(&in_fact.element) {
            return Ok(SuccessInferResult::new());
        }

        let lf = in_fact.line_file.clone();
        let membership_fact_id = self.known_fact_id_for_fact(&in_fact.clone().into())?;
        self.register_function_set_knowledge_for_element(
            &in_fact.element,
            fn_set_with_dom.body.clone(),
            membership_fact_id,
            None,
            lf.clone(),
            lf,
        );

        let mut result = SuccessInferResult::new();
        result.new_fact(&in_fact.clone().into());
        Ok(result)
    }

    // Equal-function-space inference: if `S = fn(...) T`, then `x $in S` also gives
    // `x $in fn(...) T`, which registers `x` as callable with that function signature.
    // Example: `A $in \tensor3<R, 3>` and `\tensor3<R, 3> = fn(i, j, k closed_range(1, 3)) R`.
    fn infer_membership_in_equal_fn_set_from_in_fact(
        &mut self,
        in_fact: &InFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        for equal_set in self
            .get_all_obj_representatives_equal_to_given(&in_fact.set)
            .into_iter()
        {
            let Obj::FnSet(fn_set) = equal_set else {
                continue;
            };
            let expanded_atomic: AtomicFact = self
                .new_in_fact(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                )
                .into();
            result.new_infer_result_inside(
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                    expanded_atomic,
                    InferReason::StoredFact.store_reason(),
                    inference_state,
                )?,
            );
        }
        Ok(result)
    }

    fn infer_membership_in_equal_set_representatives_from_in_fact(
        &mut self,
        in_fact: &InFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        // A local proof binder may be tested against the same ambient carrier
        // many times while that carrier is equal to an arbitrarily deep user
        // template result. Eagerly replaying every opaque representative here
        // unfolds the whole template for every fresh binder. Explicit goals can
        // already transport membership through known equality and unfold the
        // one-layer definition on demand, so keep eager inference for concrete
        // set constructors but defer opaque function/template applications.
        let element_is_local_proof_binder =
            matches!(&in_fact.element, Obj::Atom(AtomObj::Bound(_)));
        let mut result = SuccessInferResult::new();
        for equal_set in self
            .get_all_obj_representatives_equal_to_given(&in_fact.set)
            .into_iter()
        {
            if element_is_local_proof_binder
                && matches!(equal_set, Obj::FnObj(_) | Obj::InstantiatedTemplateObj(_))
            {
                continue;
            }
            let expanded_fact: AtomicFact = self
                .new_in_fact(
                    in_fact.element.clone(),
                    equal_set.clone(),
                    in_fact.line_file.clone(),
                )
                .into();
            if self
                .cache_known_facts_contains(&expanded_fact.to_string())
                .0
            {
                continue;
            }
            let source_on_left: Fact = self
                .new_equal_fact(
                    in_fact.set.clone(),
                    equal_set.clone(),
                    in_fact.line_file.clone(),
                )
                .into();
            let source_on_right: Fact = self
                .new_equal_fact(
                    equal_set.clone(),
                    in_fact.set.clone(),
                    in_fact.line_file.clone(),
                )
                .into();
            let (equality, equality_orientation) = if self
                .known_fact_id_for_fact(&source_on_left)?
                .is_some()
            {
                (source_on_left, KnownSetEqualityOrientation::SourceSetOnLeft)
            } else if self.known_fact_id_for_fact(&source_on_right)?.is_some() {
                (
                    source_on_right,
                    KnownSetEqualityOrientation::SourceSetOnRight,
                )
            } else {
                result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        expanded_fact,
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?,
                );
                continue;
            };
            let conclusion_fact: Fact = expanded_fact.clone().into();
            let conclusion_infers = self
                .store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                    expanded_fact,
                    InferReason::StoredFact.store_reason(),
                    inference_state,
                )?;
            result.add_rule_application_preserving_conclusion_result_structure(
                InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(
                    MembershipInSetWithKnownEqualityImpliesMembershipInEqualSetInferRule {
                        equality_orientation,
                    },
                ),
                vec![in_fact.clone().into(), equality],
                vec![SuccessStoreFactResult::new(
                    conclusion_fact,
                    conclusion_infers,
                )],
            );
        }
        Ok(result)
    }

    // RHS is set-builder `{ x $in S | ... }`: emit `element $in S` and each defining fact with `x := element`.
    pub(in crate::inference) fn infer_membership_in_set_builder_from_in_fact(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let unfolded_membership: Fact = self
            .new_in_fact(
                in_fact.element.clone(),
                set_builder.clone().into(),
                in_fact.line_file.clone(),
            )
            .into();
        let firing_key = format!(
            "set builder membership:{}",
            nested_obj_binder_normalized_fact_key(&unfolded_membership)
        );
        // Membership in one fixed set builder has one substitution result.
        // Example: `x $in {y S: P(y)}` infers `x $in S` and `P(x)` once.
        if self.infer_rule_firing_cached(&firing_key) {
            return Ok(SuccessInferResult::new());
        }
        self.store_infer_rule_firing(firing_key);
        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        insert_symbol_substitution(
            &mut param_to_arg_map,
            &set_builder.param_binding,
            in_fact.element.clone(),
        );

        let element_in_param_set_fact = self
            .new_in_fact(
                in_fact.element.clone(),
                *set_builder.param_set.clone(),
                in_fact.line_file.clone(),
            )
            .into();

        let mut result = SuccessInferResult::new();
        result.new_fact(&element_in_param_set_fact);
        let element_in_param_set_infers = self.store_typed_inference_conclusion_and_infer(
            element_in_param_set_fact.clone(),
            inference_state,
        )?;
        result.add_rule_application(
            InferRule::SetBuilderBaseMembershipProjection,
            unfolded_membership.clone(),
            vec![SuccessStoreFactResult::new(
                element_in_param_set_fact,
                element_in_param_set_infers,
            )],
        );

        for (clause_index, fact_in_set_builder) in set_builder.facts.iter().enumerate() {
            let instantiated_fact_in_set_builder = self
                .inst_quantifier_free_fact(
                    fact_in_set_builder,
                    &param_to_arg_map,
                    SubstitutionMode::Exact,
                    Some(&in_fact.line_file),
                )
                .map_err(|e| {
                    RuntimeError::from(InferRuntimeError(RuntimeErrorStruct::new(
                        None,
                        format!(
                            "failed to instantiate set builder fact while inferring `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(e),
                        vec![],
                    )))
                })?;
            let fact_to_store = instantiated_fact_in_set_builder.to_fact();

            result.new_fact(&fact_to_store);
            let conclusion_infers = self.store_typed_inference_conclusion_and_infer(
                fact_to_store.clone(),
                inference_state,
            )?;
            result.add_rule_application(
                InferRule::SetBuilderPredicateProjection { clause_index },
                unfolded_membership.clone(),
                vec![SuccessStoreFactResult::new(
                    fact_to_store,
                    conclusion_infers,
                )],
            );
        }
        Ok(result)
    }

    pub(in crate::inference) fn infer_membership_in_index_cart_from_in_fact(
        &mut self,
        in_fact: &InFact,
        index_cart: &IndexCart,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let fn_set_fact: Fact = self
            .new_in_fact(
                in_fact.element.clone(),
                index_cart_member_fn_set(self, index_cart)?,
                in_fact.line_file.clone(),
            )
            .into();

        let mut result = SuccessInferResult::new();
        result.new_fact(&fn_set_fact);
        self.store_typed_inference_conclusion_and_infer(fn_set_fact, inference_state)?;

        let choice_fact: Fact = crate::verification::index_cart_member_choice_fact(
            self,
            index_cart,
            in_fact.element.clone(),
            in_fact.line_file.clone(),
        )
        .into();
        result.new_fact(&choice_fact);
        self.store_typed_inference_conclusion_and_infer(choice_fact, inference_state)?;

        Ok(result)
    }

    // A member of a symbolic cart is a tuple whose coordinates lie in the
    // corresponding symbolic projections. Example: `p $in C`, `$is_cart(C)`
    // infer `tuple_dim(p) = cart_dim(C)` and `p[i] $in proj(C, i)`.
    fn infer_membership_in_symbolic_cart_from_in_fact(
        &mut self,
        in_fact: &InFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        // Literal carts are handled by the dedicated `Obj::Cart` branch.  The
        // symbolic fallback requires either an exact stored `$is_cart(C)` fact
        // (symbolic cart coordinate representation) or concrete Cartesian
        // metadata.  Restricting this lookup to known non-forall facts prevents
        // an unrelated dependent set parameter from being misclassified by a
        // theorem/forall search while preserving generic symbolic carts.
        let is_cart_fact: AtomicFact = self
            .new_is_cart_fact(in_fact.set.clone(), in_fact.line_file.clone())
            .into();
        let is_known_symbolic_cart = self
            .verify_atomic_except_equality_with_known_atomic_facts(&is_cart_fact)?
            .is_success();
        if !is_known_symbolic_cart && self.get_object_equal_to_cart(&in_fact.set).is_none() {
            return Ok(SuccessInferResult::new());
        }

        let mut result = SuccessInferResult::new();
        let is_tuple_fact: AtomicFact = self
            .new_is_tuple_fact(in_fact.element.clone(), in_fact.line_file.clone())
            .into();
        result.push_atomic_fact(&is_tuple_fact);
        result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                is_tuple_fact,
                InferReason::StoredFact.store_reason(),
                inference_state,
            )?,
        );

        let tuple_dim_fact: AtomicFact = self
            .new_equal_fact(
                TupleDim::new(in_fact.element.clone()).into(),
                CartDim::new(in_fact.set.clone()).into(),
                in_fact.line_file.clone(),
            )
            .into();
        result.push_atomic_fact(&tuple_dim_fact);
        result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                tuple_dim_fact,
                InferReason::StoredFact.store_reason(),
                inference_state,
            )?,
        );

        let index_name = self.generate_random_unused_name();
        let index_set: Obj = ClosedRange::new(
            Number::new("1".to_string()).into(),
            CartDim::new(in_fact.set.clone()).into(),
        )
        .into();
        let index_group =
            self.fresh_param_group_with_type(vec![index_name], ParamType::Obj(index_set))?;
        let index_obj = obj_for_bound_param_in_scope(&index_group.params[0]);
        let coordinate_fact: AtomicFact = self
            .new_in_fact(
                ObjAtIndex::new(in_fact.element.clone(), index_obj.clone()).into(),
                Proj::new(in_fact.set.clone(), index_obj).into(),
                in_fact.line_file.clone(),
            )
            .into();
        let coordinate_forall_fact: Fact = self
            .new_forall_fact(
                TypedParameterList::new(vec![index_group]),
                vec![],
                vec![coordinate_fact.into()],
                in_fact.line_file.clone(),
            )?
            .into();
        result.new_fact(&coordinate_forall_fact);
        result.new_infer_result_inside(
            self.store_typed_inference_conclusion_and_infer(
                coordinate_forall_fact,
                inference_state,
            )?,
        );

        Ok(result)
    }

    // Membership `x $in S`: unfold `S` into stored facts (disjunction, bounds, predicate instances, …).
    pub(in crate::inference) fn membership(
        &mut self,
        in_fact: &InFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        match &in_fact.set {
            // Function-space knowledge is retained for later typing and satisfaction checks.
            Obj::FnSet(fn_set_with_dom) => {
                self.infer_membership_in_fn_set_from_in_fact(in_fact, fn_set_with_dom)
            }
            // Function range: `z $in fn_range(f)` implies `z` is in the codomain of `f`
            // and has a preimage in the function domain.
            // Example: if `f fn(x S) T`, storing `z $in fn_range(f)` infers
            // `z $in T` and `exist x S st {z = f(x)}`.
            Obj::FnRange(fn_range) => {
                self.infer_membership_in_fn_range(in_fact, fn_range, inference_state)
            }
            // Replacement elimination: `y $in replacement(P, A)` infers a preimage witness exists.
            // Example: `y $in replacement(P, A)` infers `exist x A st {$P(x, y)}`.
            Obj::Replacement(replacement) => {
                self.infer_membership_in_replacement(in_fact, replacement, inference_state)
            }
            // Finite enum set: `a $in {1,2}` => fact `(a = 1) or (a = 2)`.
            Obj::ListSet(list_set) => {
                if list_set.list.is_empty() {
                    return Ok(SuccessInferResult::new());
                }

                // Singleton membership has one definite value, so expose it as
                // an atomic equality rather than a one-branch disjunction.
                // Example: `x $in {2}` infers `x = 2`, which makes a restricted
                // function body usable when its ambient domain contains `2`.
                if let [singleton] = list_set.list.as_slice() {
                    let equal_fact = self.new_equal_fact(
                        in_fact.element.clone(),
                        singleton.as_ref().clone(),
                        in_fact.line_file.clone(),
                    );
                    let equal_atomic_fact: AtomicFact = equal_fact.clone().into();
                    let mut result = SuccessInferResult::new();
                    let equal_fact_for_result: Fact = equal_atomic_fact.clone().into();
                    result.push_atomic_fact(&equal_atomic_fact);
                    self.top_level_env()
                        .store_atomic_fact(equal_atomic_fact.clone())?;
                    self.store_fact_cache_keys_with_nested_obj_binders(&equal_atomic_fact.into())?;
                    let conclusion_infers = self.infer_equal_fact(&equal_fact, inference_state)?;
                    result.add_rule_application_preserving_conclusion_result_structure(
                        InferRule::ListSetMembershipImpliesEqualityAlternatives(
                            ListSetMembershipImpliesEqualityAlternativesInferRule {
                                element_count: 1,
                            },
                        ),
                        vec![in_fact.clone().into()],
                        vec![SuccessStoreFactResult::new(
                            equal_fact_for_result,
                            conclusion_infers,
                        )],
                    );
                    return Ok(result);
                }

                let mut or_case_facts: Vec<AndChainAtomicFact> =
                    Vec::with_capacity(list_set.list.len());
                for obj_in_list_set in list_set.list.iter() {
                    let equal_fact = self
                        .new_equal_fact(
                            in_fact.element.clone(),
                            *obj_in_list_set.clone(),
                            in_fact.line_file.clone(),
                        )
                        .into();
                    or_case_facts.push(AndChainAtomicFact::AtomicFact(equal_fact));
                }

                let or_fact = self
                    .new_or_fact(or_case_facts, in_fact.line_file.clone())
                    .into();
                let mut result = SuccessInferResult::new();
                result.new_fact(&or_fact);
                let conclusion_infers = self
                    .store_typed_inference_conclusion_and_infer(or_fact.clone(), inference_state)?;
                result.add_rule_application_preserving_conclusion_result_structure(
                    InferRule::ListSetMembershipImpliesEqualityAlternatives(
                        ListSetMembershipImpliesEqualityAlternativesInferRule {
                            element_count: list_set.list.len(),
                        },
                    ),
                    vec![in_fact.clone().into()],
                    vec![SuccessStoreFactResult::new(or_fact, conclusion_infers)],
                );
                Ok(result)
            }
            // Set comprehension: membership in parameter domain plus instantiated filter facts.
            Obj::SetBuilder(set_builder) => self.infer_membership_in_set_builder_from_in_fact(
                in_fact,
                set_builder,
                inference_state,
            ),
            // General Cartesian product: membership gives the choice function type and the
            // pointwise factor-membership forall.
            // Example: `c $in index_cart(I, s, g)` infers
            // `c $in fn(t I)family_union(s)` and `forall t I: c(t) $in g(t)`.
            Obj::IndexCart(index_cart) => self.infer_membership_in_index_cart_from_in_fact(
                in_fact,
                index_cart,
                inference_state,
            ),
            // Power set membership: `A $in power_set(B)` means `A $subset B`.
            // Example: from `A $in power_set(Z)`, infer `A $subset Z`.
            Obj::PowerSet(power_set) => {
                let subset_fact = self
                    .new_subset_fact(
                        in_fact.element.clone(),
                        (*power_set.set).clone(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                let mut result = SuccessInferResult::new();
                result.push_atomic_fact(&subset_fact);
                result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        subset_fact,
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?,
                );
                Ok(result)
            }
            // Cartesian product: element is an n-tuple with matching dimension; bind tuple/cart metadata.
            Obj::Cart(cart) => {
                if cart.args.len() < 2 {
                    return Ok(SuccessInferResult::new());
                }
                let mut result = SuccessInferResult::new();

                let is_cart_fact = self
                    .new_is_tuple_fact(in_fact.element.clone(), in_fact.line_file.clone())
                    .into();

                result.new_fact(&is_cart_fact);
                let tuple_shape_infers = self.store_typed_inference_conclusion_and_infer(
                    is_cart_fact.clone(),
                    inference_state,
                )?;
                result.add_rule_application(
                    InferRule::CartesianMembershipProjection(
                        CartesianMembershipProjectionInferRule {
                            coordinate_count: cart.args.len(),
                            projection: CartesianMembershipProjectionKind::TupleShape,
                        },
                    ),
                    in_fact.clone().into(),
                    vec![SuccessStoreFactResult::new(
                        is_cart_fact,
                        tuple_shape_infers,
                    )],
                );

                let cart_args_count = cart.args.len();
                let tuple_dim_obj = TupleDim::new(in_fact.element.clone()).into();
                let cart_args_count_obj = Number::new(cart_args_count.to_string()).into();
                let tuple_dim_fact = self
                    .new_equal_fact(
                        tuple_dim_obj,
                        cart_args_count_obj,
                        in_fact.line_file.clone(),
                    )
                    .into();

                result.new_fact(&tuple_dim_fact);
                let tuple_dimension_infers = self.store_typed_inference_conclusion_and_infer(
                    tuple_dim_fact.clone(),
                    inference_state,
                )?;
                result.add_rule_application(
                    InferRule::CartesianMembershipProjection(
                        CartesianMembershipProjectionInferRule {
                            coordinate_count: cart.args.len(),
                            projection: CartesianMembershipProjectionKind::TupleDimension,
                        },
                    ),
                    in_fact.clone().into(),
                    vec![SuccessStoreFactResult::new(
                        tuple_dim_fact,
                        tuple_dimension_infers,
                    )],
                );

                self.store_tuple_obj_and_cart(
                    &in_fact.element.to_string(),
                    None,
                    Some(cart.clone()),
                    in_fact.line_file.clone(),
                );

                // From `x $in cart(A_1, ..., A_n)`, infer `x[i] $in A_i` (or tuple components when the
                // element is a literal n-tuple matching the product arity). Matches Cartesian product semantics.
                // Example: `u $in cart(R, Q)` => `u[1] $in R`, `u[2] $in Q`.
                for (index, factor) in cart.args.iter().enumerate() {
                    let projected = match &in_fact.element {
                        Obj::Tuple(tuple) if tuple.args.len() == cart.args.len() => {
                            (*tuple.args[index]).clone()
                        }
                        _ => ObjAtIndex::new(
                            in_fact.element.clone(),
                            Number::new((index + 1).to_string()).into(),
                        )
                        .into(),
                    };
                    let projected_in_factor: Fact = self
                        .new_in_fact(projected, (**factor).clone(), in_fact.line_file.clone())
                        .into();
                    result.new_fact(&projected_in_factor);
                    let coordinate_infers = self.store_typed_inference_conclusion_and_infer(
                        projected_in_factor.clone(),
                        inference_state,
                    )?;
                    result.add_rule_application(
                        InferRule::CartesianMembershipProjection(
                            CartesianMembershipProjectionInferRule {
                                coordinate_count: cart.args.len(),
                                projection: CartesianMembershipProjectionKind::Coordinate { index },
                            },
                        ),
                        in_fact.clone().into(),
                        vec![SuccessStoreFactResult::new(
                            projected_in_factor,
                            coordinate_infers,
                        )],
                    );
                }

                Ok(result)
            }
            // Half-open integer interval: `i $in range(a,b)` => `i $in Z`, `a <= i`, `i < b`.
            Obj::Range(r) => {
                let start = (*r.start).clone();
                let end = (*r.end).clone();
                self.infer_in_fact_element_in_integer_interval(
                    in_fact,
                    start,
                    end,
                    false,
                    inference_state,
                )
            }
            // Closed integer interval: `i $in closed_range(a,b)` => `i $in Z`, `a <= i`, `i <= b`.
            Obj::ClosedRange(c) => {
                let start = (*c.start).clone();
                let end = (*c.end).clone();
                self.infer_in_fact_element_in_integer_interval(
                    in_fact,
                    start,
                    end,
                    true,
                    inference_state,
                )
            }
            // Real interval membership: `x $in '(a, b]` => `x $in R`, `a < x`, `x <= b`.
            Obj::IntervalObj(interval) => {
                self.infer_in_fact_element_in_real_interval(in_fact, interval, inference_state)
            }
            // Half-infinite real interval membership: `x $in '[a,)` => `x $in R`, `a <= x`.
            Obj::OneSideInfinityIntervalObj(interval) => self
                .infer_in_fact_element_in_one_side_infinity_interval(
                    in_fact,
                    interval,
                    inference_state,
                ),
            // Strictly positive number sets: `x $in R+` (etc.) => `0 < x`.
            Obj::StandardSet(
                source_set @ (StandardSet::QPos | StandardSet::RPos | StandardSet::NPos),
            ) => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let inferred_atomic_fact: AtomicFact = self
                    .new_less_fact(zero_obj, in_fact.element.clone(), in_fact.line_file.clone())
                    .into();
                let inferred_fact: Fact = inferred_atomic_fact.clone().into();
                let mut result = SuccessInferResult::new();
                result.push_atomic_fact(&inferred_atomic_fact);
                let conclusion_infers = self
                    .store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        inferred_atomic_fact.clone(),
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?;
                result.add_rule_application(
                    InferRule::PositiveStandardSetMembershipImpliesPositive(
                        PositiveStandardSetMembershipImpliesPositiveInferRule {
                            source_set: *source_set,
                        },
                    ),
                    in_fact.clone().into(),
                    vec![SuccessStoreFactResult::new(
                        inferred_fact,
                        conclusion_infers,
                    )],
                );
                Ok(result)
            }
            // Strictly negative rays: `x $in R-` (etc.) => `x < 0`.
            Obj::StandardSet(
                source_set @ (StandardSet::QNeg | StandardSet::ZNeg | StandardSet::RNeg),
            ) => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let inferred_atomic_fact: AtomicFact = self
                    .new_less_fact(in_fact.element.clone(), zero_obj, in_fact.line_file.clone())
                    .into();
                let inferred_fact: Fact = inferred_atomic_fact.clone().into();
                let mut result = SuccessInferResult::new();
                result.push_atomic_fact(&inferred_atomic_fact);
                let conclusion_infers = self
                    .store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        inferred_atomic_fact.clone(),
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?;
                result.add_rule_application(
                    InferRule::NegativeStandardSetMembershipImpliesNegative(
                        NegativeStandardSetMembershipImpliesNegativeInferRule {
                            source_set: *source_set,
                        },
                    ),
                    in_fact.clone().into(),
                    vec![SuccessStoreFactResult::new(
                        inferred_fact,
                        conclusion_infers,
                    )],
                );
                Ok(result)
            }
            // Nonzero: `x $in R*` or `x $in C*` (etc.) => `x != 0`.
            Obj::StandardSet(
                source_set @ (StandardSet::QStar
                | StandardSet::ZStar
                | StandardSet::RStar
                | StandardSet::CStar),
            ) => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let inferred_atomic_fact: AtomicFact = self
                    .new_not_equal_fact(
                        in_fact.element.clone(),
                        zero_obj,
                        in_fact.line_file.clone(),
                    )
                    .into();
                let inferred_fact: Fact = inferred_atomic_fact.clone().into();
                let mut result = SuccessInferResult::new();
                result.push_atomic_fact(&inferred_atomic_fact);
                let conclusion_infers = self
                    .store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        inferred_atomic_fact.clone(),
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?;
                result.add_rule_application(
                    InferRule::NonzeroStandardSetMembershipImpliesNonzero(
                        NonzeroStandardSetMembershipImpliesNonzeroInferRule {
                            source_set: *source_set,
                        },
                    ),
                    in_fact.clone().into(),
                    vec![SuccessStoreFactResult::new(
                        inferred_fact,
                        conclusion_infers,
                    )],
                );
                Ok(result)
            }
            // `N` = {0,1,2,…}: store `n >= 0` so numeric resolution and order checks match `forall n N:`.
            // Example: after `k $in N`, infer stores `k >= 0` (same as an explicit second line).
            Obj::StandardSet(StandardSet::N) => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let inferred_atomic_fact: AtomicFact = self
                    .new_greater_equal_fact(
                        in_fact.element.clone(),
                        zero_obj,
                        in_fact.line_file.clone(),
                    )
                    .into();
                let inferred_fact: Fact = inferred_atomic_fact.clone().into();
                let mut result = SuccessInferResult::new();
                result.push_atomic_fact(&inferred_atomic_fact);
                let conclusion_infers = self
                    .store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        inferred_atomic_fact.clone(),
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?;
                result.add_rule_application(
                    InferRule::NaturalMembershipImpliesNonnegative,
                    in_fact.clone().into(),
                    vec![SuccessStoreFactResult::new(
                        inferred_fact,
                        conclusion_infers,
                    )],
                );
                Ok(result)
            }
            // Full `Z`, `Q`, `R`: no extra atomic facts inferred here.
            Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::R)
            | Obj::StandardSet(StandardSet::C) => Ok(SuccessInferResult::new()),
            // Struct membership is intentionally opaque. It proves only the
            // membership itself; tuple shape, named-field bridges, and struct
            // laws are released by a direct `x &Struct` binding or an explicit
            // `release struct def x` statement.
            Obj::StructObj(_) => Ok(SuccessInferResult::new()),
            // Finite sequence space: desugar to `FnSet`, then same as function-space membership.
            Obj::FiniteSeqSet(fs) => {
                let fn_set = self.finite_seq_set_to_fn_set(fs, in_fact.line_file.clone());
                let mut result = self.infer_membership_in_fn_set_from_in_fact(in_fact, &fn_set)?;
                let expanded_atomic: AtomicFact = self
                    .new_in_fact(
                        in_fact.element.clone(),
                        fn_set.into(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        expanded_atomic,
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?,
                );
                Ok(result)
            }
            // General sequence set: desugar to `FnSet` + store expanded `InFact`.
            Obj::SeqSet(ss) => {
                let fn_set = self.seq_set_to_fn_set(ss, in_fact.line_file.clone());
                let mut result = self.infer_membership_in_fn_set_from_in_fact(in_fact, &fn_set)?;
                let expanded_atomic: AtomicFact = self
                    .new_in_fact(
                        in_fact.element.clone(),
                        fn_set.into(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        expanded_atomic,
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?,
                );
                Ok(result)
            }
            // Matrix set: desugar to `FnSet` + store expanded `InFact`.
            Obj::MatrixSet(ms) => {
                self.store_obj_in_matrix_set(
                    &in_fact.element,
                    ms.clone(),
                    in_fact.line_file.clone(),
                );
                let fn_set = self.matrix_set_to_fn_set(ms, in_fact.line_file.clone());
                let mut result = self.infer_membership_in_fn_set_from_in_fact(in_fact, &fn_set)?;
                let expanded_atomic: AtomicFact = self
                    .new_in_fact(
                        in_fact.element.clone(),
                        fn_set.into(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                        expanded_atomic,
                        InferReason::StoredFact.store_reason(),
                        inference_state,
                    )?,
                );
                Ok(result)
            }
            // Binary union: storing `x $in union(A, B)` infers the disjunction
            // `x $in A or x $in B`. Example: `x $in union(A, B)` can split into
            // the two membership cases.
            Obj::Union(union) => {
                let lf = in_fact.line_file.clone();
                let element_in_left: AtomicFact = self
                    .new_in_fact(in_fact.element.clone(), (*union.left).clone(), lf.clone())
                    .into();
                let element_in_right: AtomicFact = self
                    .new_in_fact(in_fact.element.clone(), (*union.right).clone(), lf.clone())
                    .into();
                let union_membership_cases: Fact = self
                    .new_or_fact(
                        vec![
                            AndChainAtomicFact::AtomicFact(element_in_left),
                            AndChainAtomicFact::AtomicFact(element_in_right),
                        ],
                        lf,
                    )
                    .into();
                let mut result = SuccessInferResult::new();
                result.new_fact(&union_membership_cases);
                result.new_infer_result_inside(self.store_typed_inference_conclusion_and_infer(
                    union_membership_cases,
                    inference_state,
                )?);
                Ok(result)
            }
            // Binary intersection: storing `x $in intersect(A, B)` yields `x $in A` and `x $in B`.
            // Example: from `t $in intersect({-2, 3}, {y Q : y^2 = 9})`, infer both memberships for case splits.
            Obj::Intersect(intersect) => {
                let lf = in_fact.line_file.clone();
                let element_in_left: Fact = self
                    .new_in_fact(
                        in_fact.element.clone(),
                        (*intersect.left).clone(),
                        lf.clone(),
                    )
                    .into();
                let element_in_right: Fact = self
                    .new_in_fact(
                        in_fact.element.clone(),
                        (*intersect.right).clone(),
                        lf.clone(),
                    )
                    .into();
                let mut result = SuccessInferResult::new();
                result.new_fact(&element_in_left);
                result.new_infer_result_inside(self.store_typed_inference_conclusion_and_infer(
                    element_in_left,
                    inference_state,
                )?);
                result.new_fact(&element_in_right);
                result.new_infer_result_inside(self.store_typed_inference_conclusion_and_infer(
                    element_in_right,
                    inference_state,
                )?);
                Ok(result)
            }
            // Set difference: storing `x $in set_minus(A, B)` yields `x $in A` and `not x $in B`.
            // Example: from `t $in set_minus({1,2}, {2})`, infer membership in `{1,2}` and non-membership in `{2}`.
            Obj::SetMinus(sm) => {
                let lf = in_fact.line_file.clone();
                let element_in_left: Fact = self
                    .new_in_fact(in_fact.element.clone(), (*sm.left).clone(), lf.clone())
                    .into();
                let element_not_in_right: Fact = self
                    .new_not_in_fact(in_fact.element.clone(), (*sm.right).clone(), lf.clone())
                    .into();
                let mut result = SuccessInferResult::new();
                result.new_fact(&element_in_left);
                result.new_infer_result_inside(self.store_typed_inference_conclusion_and_infer(
                    element_in_left,
                    inference_state,
                )?);
                result.new_fact(&element_not_in_right);
                result.new_infer_result_inside(self.store_typed_inference_conclusion_and_infer(
                    element_not_in_right,
                    inference_state,
                )?);
                // Singleton exclusion: `x $in set_minus(A, {a})` implies `x != a`.
                // Example: a quotient over `set_minus(X, {x0})` may use `x - x0` as a divisor.
                if let Obj::ListSet(list_set) = sm.right.as_ref() {
                    if let [excluded] = list_set.list.as_slice() {
                        let element_not_equal: Fact = self
                            .new_not_equal_fact(
                                in_fact.element.clone(),
                                excluded.as_ref().clone(),
                                lf,
                            )
                            .into();
                        result.new_fact(&element_not_equal);
                        result.new_infer_result_inside(
                            self.store_typed_inference_conclusion_and_infer(
                                element_not_equal,
                                inference_state,
                            )?,
                        );
                    }
                }
                Ok(result)
            }
            // Family union elimination: `x $in family_union(F)` means `x` lies in some member set of `F`.
            // Example: from `x $in family_union(F)`, infer `exist item F st {x $in item}`.
            Obj::FamilyUnion(family_union) => {
                self.infer_membership_in_family_union(in_fact, family_union, inference_state)
            }
            Obj::IndexUnion(index_union) => {
                self.infer_membership_in_index_union(in_fact, index_union, inference_state)
            }
            Obj::IndexIntersect(index_intersect) => {
                self.infer_membership_in_index_intersect(in_fact, index_intersect, inference_state)
            }
            set_obj => {
                let symbolic_cart_infer =
                    self.infer_membership_in_symbolic_cart_from_in_fact(in_fact, inference_state)?;
                if !symbolic_cart_infer.is_empty() {
                    return Ok(symbolic_cart_infer);
                }
                let equal_set_infer = self
                    .infer_membership_in_equal_set_representatives_from_in_fact(
                        in_fact,
                        inference_state,
                    )?;
                if !equal_set_infer.is_empty() {
                    return Ok(equal_set_infer);
                }
                let equal_fn_set_infer =
                    self.infer_membership_in_equal_fn_set_from_in_fact(in_fact, inference_state)?;
                if !equal_fn_set_infer.is_empty() {
                    return Ok(equal_fn_set_infer);
                }
                // Follow checked set-valued definitions to their set builder for
                // inference too. Besides `circle(5)`, this covers a defined
                // family such as `rows(n)(K) = row(K)`.
                if let Some(set_builder) = self
                    .unfold_known_fn_application_to_set_builder(set_obj, &VerifyState::initial())?
                {
                    return self.infer_membership_in_set_builder_from_in_fact(
                        in_fact,
                        &set_builder,
                        inference_state,
                    );
                }
                if let Some(set_builder) = self.get_obj_equal_to_set_builder(set_obj) {
                    self.infer_membership_in_set_builder_from_in_fact(
                        in_fact,
                        &set_builder,
                        inference_state,
                    )
                } else {
                    Ok(SuccessInferResult::new())
                }
            }
        }
    }

    fn infer_membership_in_fn_range(
        &mut self,
        in_fact: &InFact,
        fn_range: &FnRange,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
            return Ok(SuccessInferResult::new());
        };
        let codomain_atomic: AtomicFact = self
            .new_in_fact(
                in_fact.element.clone(),
                body.ret_set.as_ref().clone(),
                in_fact.line_file.clone(),
            )
            .into();
        let codomain_fact: Fact = codomain_atomic.clone().into();
        let mut result = SuccessInferResult::new();
        result.new_fact(&codomain_fact);
        let codomain_infers = self
            .store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                codomain_atomic,
                InferReason::StoredFact.store_reason(),
                inference_state,
            )?;
        result.add_rule_application(
            InferRule::FunctionRangeMembershipImpliesCodomainMembership,
            in_fact.clone().into(),
            vec![SuccessStoreFactResult::new(codomain_fact, codomain_infers)],
        );

        // For a displayed application `f(args) in fn_range(f)`, the source
        // arguments are already the explicit preimage and `have by preimage`
        // can extract them directly from this membership. Avoid publishing a
        // redundant existential here. General range members still receive the
        // ordinary existential elimination fact.
        let application_is_its_own_displayed_preimage = matches!(
            &in_fact.element,
            Obj::FnObj(application)
                if objs_equal_with_nested_binder_alpha_equivalence(
                    &Obj::from(application.head.as_ref().clone()),
                    fn_range.function.as_ref(),
                )
        );
        if !application_is_its_own_displayed_preimage {
            if let Some(exist_fact) =
                self.preimage_exist_fact_from_fn_body(in_fact, fn_range.function.as_ref(), &body)?
            {
                result.new_fact(&exist_fact);
                result.new_infer_result_inside(
                    self.store_typed_inference_conclusion_and_infer(exist_fact, inference_state)?,
                );
            }
        }
        Ok(result)
    }

    fn preimage_exist_fact_from_fn_body(
        &self,
        in_fact: &InFact,
        function: &Obj,
        body: &FnSetBody,
    ) -> Result<Option<Fact>, RuntimeError> {
        let param_names = body.set_bound_parameters.collect_param_names();
        if param_names.is_empty() {
            return Ok(None);
        }

        let generated_names = param_names
            .iter()
            .map(|_| self.generate_internal_binder_name())
            .collect::<Vec<_>>();
        let preimage_bindings = self.allocate_local_symbol_bindings(&generated_names)?;
        let preimage_objs: Vec<Obj> = preimage_bindings
            .iter()
            .map(|binding| obj_for_bound_param_in_scope(binding))
            .collect();
        let instantiated_param_sets = self.inst_param_def_with_set_one_by_one(
            &body.set_bound_parameters,
            &preimage_objs,
            SubstitutionMode::Exact,
        )?;

        let mut param_groups = Vec::with_capacity(body.set_bound_parameters.len());
        let mut binding_offset = 0;
        for (param_def, param_set) in body
            .set_bound_parameters
            .iter()
            .zip(instantiated_param_sets.iter())
        {
            let next_offset = binding_offset + param_def.params.len();
            param_groups.push(TypedParameterGroup::new(
                preimage_bindings[binding_offset..next_offset].to_vec(),
                ParamType::Obj(param_set.clone()),
            ));
            binding_offset = next_offset;
        }

        let param_to_obj_map = body
            .set_bound_parameters
            .param_defs_and_args_to_param_to_arg_map(&preimage_objs);
        let mut facts = Vec::with_capacity(body.dom_facts.len() + 1);
        for dom_fact in body.dom_facts.iter() {
            let instantiated_dom_fact = self.inst_quantifier_free_fact(
                dom_fact,
                &param_to_obj_map,
                SubstitutionMode::Exact,
                Some(&in_fact.line_file),
            )?;
            facts.push(instantiated_dom_fact.into());
        }

        let Some(application) = preimage_application_obj_for_range_infer(function, &preimage_objs)
        else {
            return Ok(None);
        };
        facts.push(
            self.new_equal_fact(
                in_fact.element.clone(),
                application,
                in_fact.line_file.clone(),
            )
            .into(),
        );

        let exist_body = self.new_plain_exist_fact(
            TypedParameterList::new(param_groups),
            facts,
            in_fact.line_file.clone(),
        )?;
        Ok(Some(ExistFact::PlainExistFact(exist_body).into()))
    }

    fn infer_membership_in_family_union(
        &mut self,
        in_fact: &InFact,
        family_union: &FamilyUnion,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let member_name = self.generate_internal_binder_name();
        let member_group = self.fresh_param_group_with_type(
            vec![member_name],
            ParamType::Obj(family_union.left.as_ref().clone()),
        )?;
        let member_obj = obj_for_bound_param_in_scope(&member_group.params[0]);
        let element_in_member: AtomicFact = self
            .new_in_fact(
                in_fact.element.clone(),
                member_obj,
                in_fact.line_file.clone(),
            )
            .into();
        let exist_body = self.new_plain_exist_fact(
            TypedParameterList::new(vec![member_group]),
            vec![element_in_member.into()],
            in_fact.line_file.clone(),
        )?;
        let exist_fact: Fact = ExistFact::PlainExistFact(exist_body).into();
        let mut result = SuccessInferResult::new();
        result.new_fact(&exist_fact);
        result.new_infer_result_inside(
            self.store_typed_inference_conclusion_and_infer(exist_fact, inference_state)?,
        );
        Ok(result)
    }

    fn indexed_family_application_for_infer(
        &self,
        family_fn: &Obj,
        index: Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        let Some(head) = FnObjHead::from_callable_obj(family_fn.clone()) else {
            return Ok(None);
        };
        let application: Obj = FnObj::new(head, vec![vec![Box::new(index)]]).into();
        Ok(Some(
            self.beta_reduce_complete_anonymous_application_once(&application)?
                .unwrap_or(application),
        ))
    }

    fn infer_membership_in_index_union(
        &mut self,
        in_fact: &InFact,
        index_union: &IndexUnion,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        let ambient_membership: Fact = self
            .new_in_fact(
                in_fact.element.clone(),
                index_union.ambient_set.as_ref().clone(),
                in_fact.line_file.clone(),
            )
            .into();
        result.new_fact(&ambient_membership);
        result.new_infer_result_inside(
            self.store_typed_inference_conclusion_and_infer(ambient_membership, inference_state)?,
        );

        let index_name = self.generate_internal_binder_name();
        let index_group = self.fresh_param_group_with_type(
            vec![index_name],
            ParamType::Obj(index_union.index_set.as_ref().clone()),
        )?;
        let index_obj = obj_for_bound_param_in_scope(&index_group.params[0]);
        let Some(fiber) =
            self.indexed_family_application_for_infer(index_union.family_fn.as_ref(), index_obj)?
        else {
            return Ok(result);
        };
        let element_in_fiber: AtomicFact = self
            .new_in_fact(in_fact.element.clone(), fiber, in_fact.line_file.clone())
            .into();
        let exist_fact: Fact = ExistFact::PlainExistFact(self.new_plain_exist_fact(
            TypedParameterList::new(vec![index_group]),
            vec![element_in_fiber.into()],
            in_fact.line_file.clone(),
        )?)
        .into();
        result.new_fact(&exist_fact);
        result.new_infer_result_inside(
            self.store_typed_inference_conclusion_and_infer(exist_fact, inference_state)?,
        );
        Ok(result)
    }

    fn infer_membership_in_index_intersect(
        &mut self,
        in_fact: &InFact,
        index_intersect: &IndexIntersect,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut result = SuccessInferResult::new();
        let ambient_membership: Fact = self
            .new_in_fact(
                in_fact.element.clone(),
                index_intersect.ambient_set.as_ref().clone(),
                in_fact.line_file.clone(),
            )
            .into();
        result.new_fact(&ambient_membership);
        result.new_infer_result_inside(
            self.store_typed_inference_conclusion_and_infer(ambient_membership, inference_state)?,
        );

        let index_name = self.generate_internal_binder_name();
        let index_group = self.fresh_param_group_with_type(
            vec![index_name],
            ParamType::Obj(index_intersect.index_set.as_ref().clone()),
        )?;
        let index_obj = obj_for_bound_param_in_scope(&index_group.params[0]);
        let Some(fiber) = self
            .indexed_family_application_for_infer(index_intersect.family_fn.as_ref(), index_obj)?
        else {
            return Ok(result);
        };
        let element_in_fiber: AtomicFact = self
            .new_in_fact(in_fact.element.clone(), fiber, in_fact.line_file.clone())
            .into();
        let forall_fact: Fact = self
            .new_forall_fact(
                TypedParameterList::new(vec![index_group]),
                vec![],
                vec![element_in_fiber.into()],
                in_fact.line_file.clone(),
            )?
            .into();
        result.new_fact(&forall_fact);
        result.new_infer_result_inside(
            self.store_typed_inference_conclusion_and_infer(forall_fact, inference_state)?,
        );
        Ok(result)
    }

    fn infer_membership_in_replacement(
        &mut self,
        in_fact: &InFact,
        replacement: &Replacement,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let preimage_name = self.generate_internal_binder_name();
        let preimage_group = self.fresh_param_group_with_type(
            vec![preimage_name],
            ParamType::Obj(replacement.source_set.as_ref().clone()),
        )?;
        let preimage_obj = obj_for_bound_param_in_scope(&preimage_group.params[0]);
        let relation_fact: AtomicFact = self
            .new_normal_atomic_fact(
                replacement.prop_name.clone(),
                vec![preimage_obj, in_fact.element.clone()],
                in_fact.line_file.clone(),
            )
            .into();
        let exist_body = self.new_plain_exist_fact(
            TypedParameterList::new(vec![preimage_group]),
            vec![relation_fact.into()],
            in_fact.line_file.clone(),
        )?;
        let exist_fact: Fact = ExistFact::PlainExistFact(exist_body).into();
        let mut result = SuccessInferResult::new();
        result.new_fact(&exist_fact);
        result.new_infer_result_inside(
            self.store_typed_inference_conclusion_and_infer(exist_fact, inference_state)?,
        );
        Ok(result)
    }

    // Shared integer interval body: always `element $in Z`, lower `start <= element`, upper strict or closed.
    fn infer_in_fact_element_in_integer_interval(
        &mut self,
        in_fact: &InFact,
        start: Obj,
        end: Obj,
        end_inclusive: bool,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();

        let inferred_in_z_fact = self
            .new_in_fact(element.clone(), StandardSet::Z.into(), lf.clone())
            .into();
        let mut result = SuccessInferResult::new();
        result.push_atomic_fact(&inferred_in_z_fact);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            inferred_in_z_fact.clone(),
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;

        let lower_bound = self
            .new_less_equal_fact(start.clone(), element.clone(), lf.clone())
            .into();
        result.push_atomic_fact(&lower_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            lower_bound.clone(),
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;

        let upper_bound = if end_inclusive {
            self.new_less_equal_fact(element.clone(), end.clone(), lf.clone())
                .into()
        } else {
            self.new_less_fact(element.clone(), end.clone(), lf.clone())
                .into()
        };
        result.push_atomic_fact(&upper_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            upper_bound.clone(),
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;

        if let Some(singleton) =
            self.singleton_value_for_integer_interval(&start, &end, end_inclusive)
        {
            let equal_fact = self.new_equal_fact(element, singleton, lf).into();
            result.push_atomic_fact(&equal_fact);
            self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                equal_fact,
                InferReason::StoredFact.store_reason(),
                inference_state,
            )?;
        }

        Ok(result)
    }

    // Shared real interval body: always `element $in R`; endpoint bounds follow the interval closure flags.
    fn infer_in_fact_element_in_real_interval(
        &mut self,
        in_fact: &InFact,
        interval: &IntervalObj,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();

        let inferred_in_r_fact = self
            .new_in_fact(element.clone(), StandardSet::R.into(), lf.clone())
            .into();
        let mut result = SuccessInferResult::new();
        result.push_atomic_fact(&inferred_in_r_fact);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            inferred_in_r_fact.clone(),
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;

        let lower_bound = if interval.left_closed() {
            self.new_less_equal_fact(interval.start().clone(), element.clone(), lf.clone())
                .into()
        } else {
            self.new_less_fact(interval.start().clone(), element.clone(), lf.clone())
                .into()
        };
        result.push_atomic_fact(&lower_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            lower_bound.clone(),
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;

        let upper_bound = if interval.right_closed() {
            self.new_less_equal_fact(element.clone(), interval.end().clone(), lf.clone())
                .into()
        } else {
            self.new_less_fact(element.clone(), interval.end().clone(), lf.clone())
                .into()
        };
        result.push_atomic_fact(&upper_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            upper_bound.clone(),
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;

        Ok(result)
    }

    fn infer_in_fact_element_in_one_side_infinity_interval(
        &mut self,
        in_fact: &InFact,
        interval: &OneSideInfinityIntervalObj,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();

        let inferred_in_r_fact = self
            .new_in_fact(element.clone(), StandardSet::R.into(), lf.clone())
            .into();
        let mut result = SuccessInferResult::new();
        result.push_atomic_fact(&inferred_in_r_fact);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            inferred_in_r_fact.clone(),
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;

        let bound = match interval {
            OneSideInfinityIntervalObj::LeftOpen(_) => self
                .new_less_fact(interval.start().clone(), element.clone(), lf.clone())
                .into(),
            OneSideInfinityIntervalObj::LeftClosed(_) => self
                .new_less_equal_fact(interval.start().clone(), element.clone(), lf.clone())
                .into(),
            OneSideInfinityIntervalObj::RightOpen(_) => self
                .new_less_fact(element.clone(), interval.start().clone(), lf.clone())
                .into(),
            OneSideInfinityIntervalObj::RightClosed(_) => self
                .new_less_equal_fact(element.clone(), interval.start().clone(), lf.clone())
                .into(),
        };
        result.push_atomic_fact(&bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            bound.clone(),
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;

        Ok(result)
    }

    // Singleton integer intervals force the element's value.
    // Example: `x $in range(1, 2)` or `x $in closed_range(1, 1)` infers `x = 1`.
    fn singleton_value_for_integer_interval(
        &self,
        start: &Obj,
        end: &Obj,
        end_inclusive: bool,
    ) -> Option<Obj> {
        let start_number = self.resolve_obj_to_number(start)?;
        let end_number = self.resolve_obj_to_number(end)?;
        let start_i = start_number.normalized_value.parse::<i128>().ok()?;
        let end_i = end_number.normalized_value.parse::<i128>().ok()?;
        if end_inclusive {
            if start_i == end_i {
                return Some(Number::new(start_i.to_string()).into());
            }
        } else if start_i.checked_add(1) == Some(end_i) {
            return Some(Number::new(start_i.to_string()).into());
        }
        None
    }

    // Every Litex cartesian product has at least two coordinate factors.
    // Example: `$is_cart(C)` infers `cart_dim(C) >= 2`, which permits a
    // symbolic tuple coordinate construction via indexed functions / projections.
    pub(in crate::inference) fn infer_is_cart_dimension_lower_bound(
        &mut self,
        is_cart_fact: &IsCartFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let lower_bound: AtomicFact = self
            .new_greater_equal_fact(
                CartDim::new(is_cart_fact.set.clone()).into(),
                Number::new("2".to_string()).into(),
                is_cart_fact.line_file.clone(),
            )
            .into();
        let mut result = SuccessInferResult::new();
        result.push_atomic_fact(&lower_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
            lower_bound,
            InferReason::StoredFact.store_reason(),
            inference_state,
        )?;
        Ok(result)
    }
}

fn preimage_application_obj_for_range_infer(function: &Obj, args: &Vec<Obj>) -> Option<Obj> {
    let head = match function {
        Obj::AnonymousFn(anonymous_fn) => {
            FnObjHead::AnonymousFnLiteral(Box::new(anonymous_fn.clone()))
        }
        Obj::FiniteSeqListObj(list) => FnObjHead::FiniteSeqListObj(list.clone()),
        Obj::InstantiatedTemplateObj(template_obj) => {
            FnObjHead::InstantiatedTemplateObj(template_obj.clone())
        }
        _ => FnObjHead::given_an_atom_return_a_fn_obj_head(function.clone())?,
    };
    let group = args.iter().cloned().map(Box::new).collect();
    Some(FnObj::new(head, vec![group]).into())
}
