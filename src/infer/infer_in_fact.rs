use crate::prelude::*;
use std::collections::hash_map::Entry;
use std::collections::HashMap;

/// Objects whose `to_string()` is used as the key in `Environment::known_objs_in_fn_sets`.
pub(crate) fn obj_eligible_for_known_objs_in_fn_sets(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Atom(AtomObj::Identifier(_))
            | Obj::Atom(AtomObj::IdentifierWithMod(_))
            | Obj::Atom(AtomObj::Forall(_))
            | Obj::Atom(AtomObj::Exist(_))
            | Obj::Atom(AtomObj::Def(_))
            | Obj::Atom(AtomObj::SetBuilder(_))
            | Obj::Atom(AtomObj::FnSet(_))
            | Obj::Atom(AtomObj::Induc(_))
            | Obj::Atom(AtomObj::DefAlgo(_))
            | Obj::ObjAtIndex(_)
            | Obj::ObjAsStructInstanceWithFieldAccess(_)
    )
}

/// Extra map keys so `FnObj` well-defined lookup (`Identifier` head) finds entries
/// registered under tagged free-param display (e.g. `~1a` vs `a`).
fn extra_known_fn_set_keys_for_bare_name_lookup(element: &Obj) -> Vec<String> {
    match element {
        Obj::Atom(AtomObj::Forall(p)) => vec![p.name.clone()],
        Obj::Atom(AtomObj::Exist(p)) => vec![p.name.clone()],
        Obj::Atom(AtomObj::Def(p)) => vec![p.name.clone()],
        Obj::Atom(AtomObj::SetBuilder(p)) => vec![p.name.clone()],
        Obj::Atom(AtomObj::FnSet(p)) => vec![p.name.clone()],
        Obj::Atom(AtomObj::Induc(p)) => vec![p.name.clone()],
        Obj::Atom(AtomObj::DefAlgo(p)) => vec![p.name.clone()],
        _ => vec![],
    }
}

impl Runtime {
    fn upsert_known_fn_info_for_key(
        map: &mut HashMap<ObjString, KnownFnInfo>,
        key: ObjString,
        body: Option<(FnSetBody, LineFile)>,
        equal_to: Option<(Obj, LineFile)>,
    ) {
        match map.entry(key) {
            Entry::Occupied(mut o) => {
                let info = o.get_mut();
                if let Some((b, lf)) = body {
                    // A later type-only membership must not detach an existing definition body
                    // from the signature whose parameters it cites.
                    if equal_to.is_some() || info.equal_to.is_none() || info.fn_set.is_none() {
                        info.fn_set = Some((b, lf));
                    }
                }
                if let Some((eq, lf)) = equal_to {
                    info.equal_to = Some((eq, lf));
                }
            }
            Entry::Vacant(v) => {
                if body.is_none() && equal_to.is_none() {
                    return;
                }
                v.insert(KnownFnInfo::merge_fn_set_equal_to(body, equal_to));
            }
        }
    }

    fn upsert_known_fn_restrict_to_for_key(
        map: &mut HashMap<ObjString, KnownFnInfo>,
        key: ObjString,
        restrict_body: FnSetBody,
        line_file: LineFile,
    ) {
        match map.entry(key) {
            Entry::Occupied(mut o) => {
                o.get_mut()
                    .update_restrict_to(restrict_body, line_file.clone());
            }
            Entry::Vacant(v) => {
                let mut info = KnownFnInfo::default();
                info.update_restrict_to(restrict_body, line_file);
                v.insert(info);
            }
        }
    }

    /// Record `$restricts_to(f, fn …)` RHS body for `f` (overwrites prior `restrict_to` for that key).
    pub(crate) fn register_known_fn_restrict_to_for_element(
        &mut self,
        element: &Obj,
        restrict_body: FnSetBody,
        line_file: LineFile,
    ) {
        if !obj_eligible_for_known_objs_in_fn_sets(element) {
            return;
        }
        let key = element.to_string();
        let env = self.top_level_env();
        Self::upsert_known_fn_restrict_to_for_key(
            &mut env.known_objs_in_fn_sets,
            key.clone(),
            restrict_body.clone(),
            line_file.clone(),
        );
        for alias in extra_known_fn_set_keys_for_bare_name_lookup(element) {
            if alias != key {
                Self::upsert_known_fn_restrict_to_for_key(
                    &mut env.known_objs_in_fn_sets,
                    alias,
                    restrict_body.clone(),
                    line_file.clone(),
                );
            }
        }
    }

    /// `$restricts_to(f, narrower_fn_set)` after the fact is stored: remember the narrowed `FnSetBody`.
    /// If the RHS is a set, treat it as a unary real-valued restriction on that domain.
    pub fn infer_restrict_fact(&mut self, rf: &RestrictFact) -> Result<InferResult, RuntimeError> {
        let restrict_body = match &rf.obj_can_restrict_to_fn_set {
            Obj::FnSet(fs) => fs.body.clone(),
            domain => FnSetBody::new(
                vec![ParamGroupWithSet::new(
                    vec!["x".to_string()],
                    domain.clone(),
                )],
                vec![],
                StandardSet::R.into(),
            ),
        };
        self.register_known_fn_restrict_to_for_element(
            &rf.obj,
            restrict_body,
            rf.line_file.clone(),
        );
        Ok(InferResult::new())
    }

    /// Record `element` as having function signature `body` (same keys/aliases as `element $in fn ...` infer).
    /// When `equal_to` is `Some`, stores the defining expression (e.g. from `a = '…{…}` or `have fn`).
    pub(crate) fn register_known_objs_in_fn_sets_for_element_body(
        &mut self,
        element: &Obj,
        body: FnSetBody,
        equal_to: Option<Obj>,
        fn_signature_line_file: LineFile,
        defining_expr_line_file: LineFile,
    ) {
        if !obj_eligible_for_known_objs_in_fn_sets(element) {
            return;
        }
        let key = element.to_string();
        let env = self.top_level_env();
        let body_opt = Some((body.clone(), fn_signature_line_file.clone()));
        let equal_opt = equal_to
            .clone()
            .map(|eq| (eq, defining_expr_line_file.clone()));
        Self::upsert_known_fn_info_for_key(
            &mut env.known_objs_in_fn_sets,
            key.clone(),
            body_opt,
            equal_opt.clone(),
        );
        for alias in extra_known_fn_set_keys_for_bare_name_lookup(element) {
            if alias != key {
                Self::upsert_known_fn_info_for_key(
                    &mut env.known_objs_in_fn_sets,
                    alias,
                    Some((body.clone(), fn_signature_line_file.clone())),
                    equal_opt.clone(),
                );
            }
        }
    }

    // RHS is a function space `FnSet`: record the element in `known_objs_in_fn_sets`.
    pub fn infer_membership_in_fn_set_from_in_fact(
        &mut self,
        in_fact: &InFact,
        fn_set_with_dom: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
        if !obj_eligible_for_known_objs_in_fn_sets(&in_fact.element) {
            return Ok(InferResult::new());
        }

        let lf = in_fact.line_file.clone();
        self.register_known_objs_in_fn_sets_for_element_body(
            &in_fact.element,
            fn_set_with_dom.body.clone(),
            None,
            lf.clone(),
            lf,
        );

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&in_fact.clone().into());
        Ok(infer_result)
    }

    // Alias-to-function-space inference: if `S = fn(...) T`, then `x $in S` also gives
    // `x $in fn(...) T`, which registers `x` as callable with that function signature.
    // Example: `A $in \tensor3<R, 3>` and `\tensor3<R, 3> = fn(i, j, k closed_range(1, 3)) R`.
    fn infer_membership_in_equal_fn_set_from_in_fact(
        &mut self,
        in_fact: &InFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for equal_set in self
            .get_all_obj_representatives_equal_to_given(&in_fact.set)
            .into_iter()
        {
            let Obj::FnSet(fn_set) = equal_set else {
                continue;
            };
            let expanded_atomic: AtomicFact = InFact::new(
                in_fact.element.clone(),
                fn_set.into(),
                in_fact.line_file.clone(),
            )
            .into();
            infer_result.new_infer_result_inside(
                self.store_atomic_fact_without_well_defined_verified_and_infer(expanded_atomic)?,
            );
        }
        Ok(infer_result)
    }

    fn infer_membership_in_equal_set_representatives_from_in_fact(
        &mut self,
        in_fact: &InFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for equal_set in self
            .get_all_obj_representatives_equal_to_given(&in_fact.set)
            .into_iter()
        {
            let expanded_fact: AtomicFact = InFact::new(
                in_fact.element.clone(),
                equal_set,
                in_fact.line_file.clone(),
            )
            .into();
            if self
                .cache_known_facts_contains(&expanded_fact.to_string())
                .0
            {
                continue;
            }
            infer_result.new_infer_result_inside(
                self.store_atomic_fact_without_well_defined_verified_and_infer(expanded_fact)?,
            );
        }
        Ok(infer_result)
    }

    // RHS is set-builder `{ x $in S | ... }`: emit `element $in S` and each defining fact with `x := element`.
    pub fn infer_membership_in_set_builder_from_in_fact(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
    ) -> Result<InferResult, RuntimeError> {
        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        param_to_arg_map.insert(set_builder.param.clone(), in_fact.element.clone());

        let element_in_param_set_fact = InFact::new(
            in_fact.element.clone(),
            *set_builder.param_set.clone(),
            in_fact.line_file.clone(),
        )
        .into();

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&element_in_param_set_fact);
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(
            element_in_param_set_fact,
        )?;

        for fact_in_set_builder in set_builder.facts.iter() {
            let instantiated_fact_in_set_builder = self
                .inst_exist_body_fact(
                    fact_in_set_builder,
                    &param_to_arg_map,
                    ParamObjType::SetBuilder,
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

            infer_result.new_fact(&fact_to_store);
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(fact_to_store)?;
        }

        Ok(infer_result)
    }

    pub fn infer_membership_in_general_cart_from_in_fact(
        &mut self,
        in_fact: &InFact,
        general_cart: &GeneralCart,
    ) -> Result<InferResult, RuntimeError> {
        let fn_set_fact: Fact = InFact::new(
            in_fact.element.clone(),
            general_cart_member_fn_set(general_cart)?,
            in_fact.line_file.clone(),
        )
        .into();

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&fn_set_fact);
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(fn_set_fact)?;

        if let Some(pointwise_fact) =
            general_cart_member_pointwise_fact(general_cart, &in_fact.element, &in_fact.line_file)?
        {
            infer_result.new_fact(&pointwise_fact);
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(pointwise_fact)?;
        }

        Ok(infer_result)
    }

    // Membership `x $in S`: unfold `S` into stored facts (disjunction, bounds, predicate instances, …).
    pub(in crate::infer) fn infer_in_fact(
        &mut self,
        in_fact: &InFact,
    ) -> Result<InferResult, RuntimeError> {
        match &in_fact.set {
            // Function space: side table `known_objs_in_fn_sets` for typing/satisfaction later.
            Obj::FnSet(fn_set_with_dom) => {
                self.infer_membership_in_fn_set_from_in_fact(in_fact, fn_set_with_dom)
            }
            // Function range: `z $in fn_range(f)` implies `z` is in the codomain of `f`
            // and has a preimage in the function domain.
            // Example: if `f fn(x S) T`, storing `z $in fn_range(f)` infers
            // `z $in T` and `exist x S st {z = f(x)}`.
            Obj::FnRange(fn_range) => self.infer_membership_in_fn_range(in_fact, fn_range),
            // Restricted function range: `z $in fn_range_on(f, S)` implies `z` is in
            // the codomain of `f` and has a preimage in the restricted domain `S`.
            // Example: if `a seq(R)`, storing `z $in fn_range_on(a, 1...3)` infers
            // `z $in R` and `exist k 1...3 st {z = a(k)}`.
            Obj::FnRangeOn(fn_range_on) => {
                self.infer_membership_in_fn_range_on(in_fact, fn_range_on)
            }
            // Replacement elimination: `y $in replacement(P, A)` infers a preimage witness exists.
            // Example: `y $in replacement(P, A)` infers `exist x A st {$P(x, y)}`.
            Obj::Replacement(replacement) => {
                self.infer_membership_in_replacement(in_fact, replacement)
            }
            // Finite enum set: `a $in {1,2}` => fact `(a = 1) or (a = 2)`.
            Obj::ListSet(list_set) => {
                if list_set.list.is_empty() {
                    return Ok(InferResult::new());
                }

                let mut or_case_facts: Vec<AndChainAtomicFact> =
                    Vec::with_capacity(list_set.list.len());
                for obj_in_list_set in list_set.list.iter() {
                    let equal_fact = EqualFact::new(
                        in_fact.element.clone(),
                        *obj_in_list_set.clone(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                    or_case_facts.push(AndChainAtomicFact::AtomicFact(equal_fact));
                }

                let or_fact = OrFact::new(or_case_facts, in_fact.line_file.clone()).into();
                let mut infer_result = InferResult::new();
                infer_result.new_fact(&or_fact);
                self.verify_well_defined_and_store_and_infer_with_default_verify_state(or_fact)?;
                Ok(infer_result)
            }
            // Set comprehension: membership in parameter domain plus instantiated filter facts.
            Obj::SetBuilder(set_builder) => {
                self.infer_membership_in_set_builder_from_in_fact(in_fact, set_builder)
            }
            // General Cartesian product: membership gives the choice function type and the
            // pointwise factor-membership forall.
            // Example: `c $in general_cart(I, s, g)` infers
            // `c $in fn(t I)cup(s)` and `forall t I: c(t) $in g(t)`.
            Obj::GeneralCart(general_cart) => {
                self.infer_membership_in_general_cart_from_in_fact(in_fact, general_cart)
            }
            // Power set membership: `A $in power_set(B)` means `A $subset B`.
            // Example: from `A $in power_set(Z)`, infer `A $subset Z`.
            Obj::PowerSet(power_set) => {
                let subset_fact = SubsetFact::new(
                    in_fact.element.clone(),
                    (*power_set.set).clone(),
                    in_fact.line_file.clone(),
                )
                .into();
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&subset_fact);
                infer_result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer(subset_fact)?,
                );
                Ok(infer_result)
            }
            // Cartesian product: element is an n-tuple with matching dimension; bind tuple/cart metadata.
            Obj::Cart(cart) => {
                if cart.args.len() < 2 {
                    return Ok(InferResult::new());
                }
                let mut infer_result = InferResult::new();

                let is_cart_fact =
                    IsTupleFact::new(in_fact.element.clone(), in_fact.line_file.clone()).into();

                infer_result.new_fact(&is_cart_fact);
                self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                    is_cart_fact,
                )?;

                let cart_args_count = cart.args.len();
                let tuple_dim_obj = TupleDim::new(in_fact.element.clone()).into();
                let cart_args_count_obj = Number::new(cart_args_count.to_string()).into();
                let tuple_dim_fact = EqualFact::new(
                    tuple_dim_obj,
                    cart_args_count_obj,
                    in_fact.line_file.clone(),
                )
                .into();

                infer_result.new_fact(&tuple_dim_fact);
                self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                    tuple_dim_fact,
                )?;

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
                    let projected_in_factor: Fact =
                        InFact::new(projected, (**factor).clone(), in_fact.line_file.clone())
                            .into();
                    infer_result.new_fact(&projected_in_factor);
                    infer_result.new_infer_result_inside(
                        self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                            projected_in_factor,
                        )?,
                    );
                }

                Ok(infer_result)
            }
            // Half-open integer interval: `i $in range(a,b)` => `i $in Z`, `a <= i`, `i < b`.
            Obj::Range(r) => {
                let start = (*r.start).clone();
                let end = (*r.end).clone();
                self.infer_in_fact_element_in_integer_interval(in_fact, start, end, false)
            }
            // Closed integer interval: `i $in closed_range(a,b)` => `i $in Z`, `a <= i`, `i <= b`.
            Obj::ClosedRange(c) => {
                let start = (*c.start).clone();
                let end = (*c.end).clone();
                self.infer_in_fact_element_in_integer_interval(in_fact, start, end, true)
            }
            // Real interval membership: `x $in '(a, b]` => `x $in R`, `a < x`, `x <= b`.
            Obj::IntervalObj(interval) => {
                self.infer_in_fact_element_in_real_interval(in_fact, interval)
            }
            // Half-infinite real interval membership: `x $in '[a,)` => `x $in R`, `a <= x`.
            Obj::OneSideInfinityIntervalObj(interval) => {
                self.infer_in_fact_element_in_one_side_infinity_interval(in_fact, interval)
            }
            // Strictly positive number sets: `x $in R_pos` (etc.) => `0 < x`.
            Obj::StandardSet(StandardSet::QPos)
            | Obj::StandardSet(StandardSet::RPos)
            | Obj::StandardSet(StandardSet::NPos) => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let inferred_atomic_fact =
                    LessFact::new(zero_obj, in_fact.element.clone(), in_fact.line_file.clone())
                        .into();
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    inferred_atomic_fact.clone(),
                )?;
                Ok(infer_result)
            }
            // Strictly negative rays: `x $in R_neg` (etc.) => `x < 0`.
            Obj::StandardSet(StandardSet::QNeg)
            | Obj::StandardSet(StandardSet::ZNeg)
            | Obj::StandardSet(StandardSet::RNeg) => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let inferred_atomic_fact =
                    LessFact::new(in_fact.element.clone(), zero_obj, in_fact.line_file.clone())
                        .into();
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    inferred_atomic_fact.clone(),
                )?;
                Ok(infer_result)
            }
            // Nonzero: `x $in R_nz` (etc.) => `x != 0`.
            Obj::StandardSet(StandardSet::QNz)
            | Obj::StandardSet(StandardSet::ZNz)
            | Obj::StandardSet(StandardSet::RNz) => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let inferred_atomic_fact =
                    NotEqualFact::new(in_fact.element.clone(), zero_obj, in_fact.line_file.clone())
                        .into();
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    inferred_atomic_fact.clone(),
                )?;
                Ok(infer_result)
            }
            // `N` = {0,1,2,…}: store `n >= 0` so numeric resolution and order checks match `forall n N:`.
            // Example: after `k $in N`, infer stores `k >= 0` (same as an explicit second line).
            Obj::StandardSet(StandardSet::N) => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let inferred_atomic_fact = GreaterEqualFact::new(
                    in_fact.element.clone(),
                    zero_obj,
                    in_fact.line_file.clone(),
                )
                .into();
                let mut infer_result = InferResult::new();
                infer_result.push_atomic_fact(&inferred_atomic_fact);
                self.store_atomic_fact_without_well_defined_verified_and_infer(
                    inferred_atomic_fact.clone(),
                )?;
                Ok(infer_result)
            }
            // Full `Z`, `Q`, `R`: no extra atomic facts inferred here.
            Obj::StandardSet(StandardSet::Q)
            | Obj::StandardSet(StandardSet::Z)
            | Obj::StandardSet(StandardSet::R) => Ok(InferResult::new()),
            // Struct membership releases its named tuple-view facts.
            // Example: from `p $in &Point`, infer `&Point{p}.x $in R`
            // and `p[1] $in R`. Equivalent facts are instantiated with the
            // explicit field-access objects and tuple projections.
            Obj::StructObj(struct_obj) => {
                let (def, header_map) =
                    self.struct_header_param_to_arg_map(struct_obj, &VerifyState::new(0, false))?;
                let field_types =
                    self.instantiated_struct_field_types(struct_obj, &VerifyState::new(0, false))?;

                let mut infer_result = InferResult::new();
                let cart_membership: Fact = InFact::new(
                    in_fact.element.clone(),
                    Cart::new(field_types.clone()).into(),
                    in_fact.line_file.clone(),
                )
                .into();
                infer_result.new_fact(&cart_membership);
                infer_result.new_infer_result_inside(
                    self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                        cart_membership,
                    )?,
                );

                let mut field_map: HashMap<String, Obj> = HashMap::new();
                let mut projection_field_map: HashMap<String, Obj> = HashMap::new();
                for (index, (field_name, _)) in def.fields.iter().enumerate() {
                    let field_access: Obj = ObjAsStructInstanceWithFieldAccess::new(
                        struct_obj.clone(),
                        in_fact.element.clone(),
                        field_name.clone(),
                    )
                    .into();
                    field_map.insert(field_name.clone(), field_access.clone());

                    let field_in_type: Fact = InFact::new(
                        field_access,
                        field_types[index].clone(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                    infer_result.new_fact(&field_in_type);
                    infer_result.new_infer_result_inside(
                        self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                            field_in_type,
                        )?,
                    );

                    let projected_field: Obj = match &in_fact.element {
                        Obj::Tuple(tuple) => (*tuple.args[index]).clone(),
                        _ => ObjAtIndex::new(
                            in_fact.element.clone(),
                            Number::new((index + 1).to_string()).into(),
                        )
                        .into(),
                    };
                    projection_field_map.insert(field_name.clone(), projected_field.clone());
                    let projected_field_in_type: Fact = InFact::new(
                        projected_field,
                        field_types[index].clone(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                    infer_result.new_fact(&projected_field_in_type);
                    infer_result.new_infer_result_inside(
                        self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                            projected_field_in_type,
                        )?,
                    );
                }

                for fact in def.equivalent_facts.iter() {
                    let after_header = self.inst_fact(
                        fact,
                        &header_map,
                        ParamObjType::DefHeader,
                        Some(in_fact.line_file.clone()),
                    )?;
                    let instantiated_fact = self.inst_fact(
                        &after_header,
                        &field_map,
                        ParamObjType::DefStructField,
                        Some(in_fact.line_file.clone()),
                    )?;
                    infer_result.new_fact(&instantiated_fact);
                    let instantiated_fact_line_file = instantiated_fact.line_file();
                    let instantiated_fact_string = instantiated_fact.to_string();
                    self.top_level_env().store_fact(instantiated_fact)?;
                    self.top_level_env().store_fact_to_cache_known_fact(
                        instantiated_fact_string,
                        instantiated_fact_line_file,
                    )?;

                    let projected_fact = self.inst_fact(
                        &after_header,
                        &projection_field_map,
                        ParamObjType::DefStructField,
                        Some(in_fact.line_file.clone()),
                    )?;
                    infer_result.new_fact(&projected_fact);
                    infer_result.new_infer_result_inside(
                        self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                            projected_fact,
                        )?,
                    );
                }

                Ok(infer_result)
            }
            // Finite sequence space: desugar to `FnSet`, then same as function-space membership.
            Obj::FiniteSeqSet(fs) => {
                let fn_set = self.finite_seq_set_to_fn_set(fs, in_fact.line_file.clone());
                let mut infer_result =
                    self.infer_membership_in_fn_set_from_in_fact(in_fact, &fn_set)?;
                let expanded_atomic: AtomicFact = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                )
                .into();
                infer_result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer(
                        expanded_atomic,
                    )?,
                );
                Ok(infer_result)
            }
            // General sequence set: desugar to `FnSet` + store expanded `InFact`.
            Obj::SeqSet(ss) => {
                let fn_set = self.seq_set_to_fn_set(ss, in_fact.line_file.clone());
                let mut infer_result =
                    self.infer_membership_in_fn_set_from_in_fact(in_fact, &fn_set)?;
                let expanded_atomic: AtomicFact = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                )
                .into();
                infer_result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer(
                        expanded_atomic,
                    )?,
                );
                Ok(infer_result)
            }
            // Matrix set: desugar to `FnSet` + store expanded `InFact`.
            Obj::MatrixSet(ms) => {
                let fn_set = self.matrix_set_to_fn_set(ms, in_fact.line_file.clone());
                let mut infer_result =
                    self.infer_membership_in_fn_set_from_in_fact(in_fact, &fn_set)?;
                let expanded_atomic: AtomicFact = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                )
                .into();
                infer_result.new_infer_result_inside(
                    self.store_atomic_fact_without_well_defined_verified_and_infer(
                        expanded_atomic,
                    )?,
                );
                Ok(infer_result)
            }
            // Binary intersection: storing `x $in intersect(A, B)` yields `x $in A` and `x $in B`.
            // Example: from `t $in intersect({-2, 3}, {y Q : y^2 = 9})`, infer both memberships for case splits.
            Obj::Intersect(intersect) => {
                let lf = in_fact.line_file.clone();
                let element_in_left: Fact = InFact::new(
                    in_fact.element.clone(),
                    (*intersect.left).clone(),
                    lf.clone(),
                )
                .into();
                let element_in_right: Fact = InFact::new(
                    in_fact.element.clone(),
                    (*intersect.right).clone(),
                    lf.clone(),
                )
                .into();
                let mut infer_result = InferResult::new();
                infer_result.new_fact(&element_in_left);
                infer_result.new_infer_result_inside(
                    self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                        element_in_left,
                    )?,
                );
                infer_result.new_fact(&element_in_right);
                infer_result.new_infer_result_inside(
                    self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                        element_in_right,
                    )?,
                );
                Ok(infer_result)
            }
            // Set difference: storing `x $in set_minus(A, B)` yields `x $in A` and `not x $in B`.
            // Example: from `t $in set_minus({1,2}, {2})`, infer membership in `{1,2}` and non-membership in `{2}`.
            Obj::SetMinus(sm) => {
                let lf = in_fact.line_file.clone();
                let element_in_left: Fact =
                    InFact::new(in_fact.element.clone(), (*sm.left).clone(), lf.clone()).into();
                let element_not_in_right: Fact =
                    NotInFact::new(in_fact.element.clone(), (*sm.right).clone(), lf.clone()).into();
                let mut infer_result = InferResult::new();
                infer_result.new_fact(&element_in_left);
                infer_result.new_infer_result_inside(
                    self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                        element_in_left,
                    )?,
                );
                infer_result.new_fact(&element_not_in_right);
                infer_result.new_infer_result_inside(
                    self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                        element_not_in_right,
                    )?,
                );
                Ok(infer_result)
            }
            // Family union elimination: `x $in cup(F)` means `x` lies in some member set of `F`.
            // Example: from `x $in cup(F)`, infer `exist item F st {x $in item}`.
            Obj::Cup(cup) => self.infer_membership_in_cup(in_fact, cup),
            set_obj => {
                let equal_set_infer =
                    self.infer_membership_in_equal_set_representatives_from_in_fact(in_fact)?;
                if !equal_set_infer.is_empty() {
                    return Ok(equal_set_infer);
                }
                let alias_infer = self.infer_membership_in_equal_fn_set_from_in_fact(in_fact)?;
                if !alias_infer.is_empty() {
                    return Ok(alias_infer);
                }
                // If the set side is a one-layer user-defined set builder, unfold it
                // for inference too. Example: `(3,4) $in circle(5)` infers
                // `(3,4) $in cart(R,R)` and the instantiated circle equation.
                if let Some(Obj::SetBuilder(set_builder)) =
                    self.unfold_known_fn_application_once(set_obj, &VerifyState::new(0, false))?
                {
                    return self
                        .infer_membership_in_set_builder_from_in_fact(in_fact, &set_builder);
                }
                if let Some(set_builder) = self.get_obj_equal_to_set_builder(&set_obj.to_string()) {
                    self.infer_membership_in_set_builder_from_in_fact(in_fact, &set_builder)
                } else {
                    Ok(InferResult::new())
                }
            }
        }
    }

    fn infer_membership_in_fn_range(
        &mut self,
        in_fact: &InFact,
        fn_range: &FnRange,
    ) -> Result<InferResult, RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
            return Ok(InferResult::new());
        };
        let codomain_fact: AtomicFact = InFact::new(
            in_fact.element.clone(),
            body.ret_set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let mut infer_result = InferResult::new();
        infer_result.push_atomic_fact(&codomain_fact);
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(codomain_fact)?,
        );
        if let Some(exist_fact) =
            self.preimage_exist_fact_from_fn_body(in_fact, fn_range.function.as_ref(), &body)?
        {
            infer_result.new_fact(&exist_fact);
            infer_result.new_infer_result_inside(
                self.verify_well_defined_and_store_and_infer_with_default_verify_state(exist_fact)?,
            );
        }
        Ok(infer_result)
    }

    fn infer_membership_in_fn_range_on(
        &mut self,
        in_fact: &InFact,
        fn_range_on: &FnRangeOn,
    ) -> Result<InferResult, RuntimeError> {
        let Some(body) = self.get_fn_range_on_function_body(&fn_range_on.function) else {
            return Ok(InferResult::new());
        };
        let Some(restricted_body) = self.fn_range_on_restricted_body(fn_range_on, &body) else {
            return Ok(InferResult::new());
        };
        let codomain_fact: AtomicFact = InFact::new(
            in_fact.element.clone(),
            restricted_body.ret_set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let mut infer_result = InferResult::new();
        infer_result.push_atomic_fact(&codomain_fact);
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(codomain_fact)?,
        );
        if let Some(exist_fact) = self.preimage_exist_fact_from_fn_body(
            in_fact,
            fn_range_on.function.as_ref(),
            &restricted_body,
        )? {
            infer_result.new_fact(&exist_fact);
            infer_result.new_infer_result_inside(
                self.verify_well_defined_and_store_and_infer_with_default_verify_state(exist_fact)?,
            );
        }
        Ok(infer_result)
    }

    fn fn_range_on_restricted_body(
        &self,
        fn_range_on: &FnRangeOn,
        body: &FnSetBody,
    ) -> Option<FnSetBody> {
        if body.params_def_with_set.number_of_params() != 1 {
            return None;
        }
        let param_name = body
            .params_def_with_set
            .collect_param_names()
            .first()?
            .clone();
        Some(FnSetBody::new(
            vec![ParamGroupWithSet::new(
                vec![param_name],
                fn_range_on.set.as_ref().clone(),
            )],
            vec![],
            body.ret_set.as_ref().clone(),
        ))
    }

    fn preimage_exist_fact_from_fn_body(
        &self,
        in_fact: &InFact,
        function: &Obj,
        body: &FnSetBody,
    ) -> Result<Option<Fact>, RuntimeError> {
        let param_names = body.params_def_with_set.collect_param_names();
        if param_names.is_empty() {
            return Ok(None);
        }

        let preimage_objs: Vec<Obj> = param_names
            .iter()
            .map(|name| obj_for_bound_param_in_scope(name.clone(), ParamObjType::Exist))
            .collect();
        let instantiated_param_sets = self.inst_param_def_with_set_one_by_one(
            &body.params_def_with_set,
            &preimage_objs,
            ParamObjType::FnSet,
        )?;

        let mut param_groups = Vec::with_capacity(body.params_def_with_set.len());
        for (param_def, param_set) in body
            .params_def_with_set
            .iter()
            .zip(instantiated_param_sets.iter())
        {
            param_groups.push(ParamGroupWithParamType::new(
                param_def.params.clone(),
                ParamType::Obj(param_set.clone()),
            ));
        }

        let param_to_obj_map = body
            .params_def_with_set
            .param_defs_and_args_to_param_to_arg_map(&preimage_objs);
        let mut facts = Vec::with_capacity(body.dom_facts.len() + 1);
        for dom_fact in body.dom_facts.iter() {
            let instantiated_dom_fact = self.inst_or_and_chain_atomic_fact(
                dom_fact,
                &param_to_obj_map,
                ParamObjType::FnSet,
                Some(&in_fact.line_file),
            )?;
            facts.push(instantiated_dom_fact.into());
        }

        let Some(application) = preimage_application_obj_for_range_infer(function, &preimage_objs)
        else {
            return Ok(None);
        };
        facts.push(
            EqualFact::new(
                in_fact.element.clone(),
                application,
                in_fact.line_file.clone(),
            )
            .into(),
        );

        let exist_body = ExistFactBody::new(
            ParamDefWithType::new(param_groups),
            facts,
            in_fact.line_file.clone(),
        )?;
        Ok(Some(ExistFactEnum::ExistFact(exist_body).into()))
    }

    fn infer_membership_in_cup(
        &mut self,
        in_fact: &InFact,
        cup: &Cup,
    ) -> Result<InferResult, RuntimeError> {
        let member_name = "item".to_string();
        let member_obj = obj_for_bound_param_in_scope(member_name.clone(), ParamObjType::Exist);
        let element_in_member: AtomicFact = InFact::new(
            in_fact.element.clone(),
            member_obj,
            in_fact.line_file.clone(),
        )
        .into();
        let exist_body = ExistFactBody::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![member_name],
                ParamType::Obj(cup.left.as_ref().clone()),
            )]),
            vec![element_in_member.into()],
            in_fact.line_file.clone(),
        )?;
        let exist_fact: Fact = ExistFactEnum::ExistFact(exist_body).into();
        let mut infer_result = InferResult::new();
        infer_result.new_fact(&exist_fact);
        infer_result.new_infer_result_inside(
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(exist_fact)?,
        );
        Ok(infer_result)
    }

    fn infer_membership_in_replacement(
        &mut self,
        in_fact: &InFact,
        replacement: &Replacement,
    ) -> Result<InferResult, RuntimeError> {
        let preimage_name = "x".to_string();
        let preimage_obj = obj_for_bound_param_in_scope(preimage_name.clone(), ParamObjType::Exist);
        let relation_fact: AtomicFact = NormalAtomicFact::new(
            replacement.prop_name.clone(),
            vec![preimage_obj, in_fact.element.clone()],
            in_fact.line_file.clone(),
        )
        .into();
        let exist_body = ExistFactBody::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![preimage_name],
                ParamType::Obj(replacement.source_set.as_ref().clone()),
            )]),
            vec![relation_fact.into()],
            in_fact.line_file.clone(),
        )?;
        let exist_fact: Fact = ExistFactEnum::ExistFact(exist_body).into();
        let mut infer_result = InferResult::new();
        infer_result.new_fact(&exist_fact);
        infer_result.new_infer_result_inside(
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(exist_fact)?,
        );
        Ok(infer_result)
    }

    // Shared integer interval body: always `element $in Z`, lower `start <= element`, upper strict or closed.
    fn infer_in_fact_element_in_integer_interval(
        &mut self,
        in_fact: &InFact,
        start: Obj,
        end: Obj,
        end_inclusive: bool,
    ) -> Result<InferResult, RuntimeError> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();

        let inferred_in_z_fact =
            InFact::new(element.clone(), StandardSet::Z.into(), lf.clone()).into();
        let mut infer_result = InferResult::new();
        infer_result.push_atomic_fact(&inferred_in_z_fact);
        self.store_atomic_fact_without_well_defined_verified_and_infer(inferred_in_z_fact.clone())?;

        let lower_bound = LessEqualFact::new(start.clone(), element.clone(), lf.clone()).into();
        infer_result.push_atomic_fact(&lower_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer(lower_bound.clone())?;

        let upper_bound = if end_inclusive {
            LessEqualFact::new(element.clone(), end.clone(), lf.clone()).into()
        } else {
            LessFact::new(element.clone(), end.clone(), lf.clone()).into()
        };
        infer_result.push_atomic_fact(&upper_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer(upper_bound.clone())?;

        if let Some(singleton) =
            self.singleton_value_for_integer_interval(&start, &end, end_inclusive)
        {
            let equal_fact = EqualFact::new(element, singleton, lf).into();
            infer_result.push_atomic_fact(&equal_fact);
            self.store_atomic_fact_without_well_defined_verified_and_infer(equal_fact)?;
        }

        Ok(infer_result)
    }

    // Shared real interval body: always `element $in R`; endpoint bounds follow the interval closure flags.
    fn infer_in_fact_element_in_real_interval(
        &mut self,
        in_fact: &InFact,
        interval: &IntervalObj,
    ) -> Result<InferResult, RuntimeError> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();

        let inferred_in_r_fact =
            InFact::new(element.clone(), StandardSet::R.into(), lf.clone()).into();
        let mut infer_result = InferResult::new();
        infer_result.push_atomic_fact(&inferred_in_r_fact);
        self.store_atomic_fact_without_well_defined_verified_and_infer(inferred_in_r_fact.clone())?;

        let lower_bound = if interval.left_closed() {
            LessEqualFact::new(interval.start().clone(), element.clone(), lf.clone()).into()
        } else {
            LessFact::new(interval.start().clone(), element.clone(), lf.clone()).into()
        };
        infer_result.push_atomic_fact(&lower_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer(lower_bound.clone())?;

        let upper_bound = if interval.right_closed() {
            LessEqualFact::new(element.clone(), interval.end().clone(), lf.clone()).into()
        } else {
            LessFact::new(element.clone(), interval.end().clone(), lf.clone()).into()
        };
        infer_result.push_atomic_fact(&upper_bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer(upper_bound.clone())?;

        Ok(infer_result)
    }

    fn infer_in_fact_element_in_one_side_infinity_interval(
        &mut self,
        in_fact: &InFact,
        interval: &OneSideInfinityIntervalObj,
    ) -> Result<InferResult, RuntimeError> {
        let element = in_fact.element.clone();
        let lf = in_fact.line_file.clone();

        let inferred_in_r_fact =
            InFact::new(element.clone(), StandardSet::R.into(), lf.clone()).into();
        let mut infer_result = InferResult::new();
        infer_result.push_atomic_fact(&inferred_in_r_fact);
        self.store_atomic_fact_without_well_defined_verified_and_infer(inferred_in_r_fact.clone())?;

        let bound = match interval {
            OneSideInfinityIntervalObj::LeftOpen(_) => {
                LessFact::new(interval.start().clone(), element.clone(), lf.clone()).into()
            }
            OneSideInfinityIntervalObj::LeftClosed(_) => {
                LessEqualFact::new(interval.start().clone(), element.clone(), lf.clone()).into()
            }
            OneSideInfinityIntervalObj::RightOpen(_) => {
                LessFact::new(element.clone(), interval.start().clone(), lf.clone()).into()
            }
            OneSideInfinityIntervalObj::RightClosed(_) => {
                LessEqualFact::new(element.clone(), interval.start().clone(), lf.clone()).into()
            }
        };
        infer_result.push_atomic_fact(&bound);
        self.store_atomic_fact_without_well_defined_verified_and_infer(bound.clone())?;

        Ok(infer_result)
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
