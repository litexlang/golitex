use super::*;

impl Runtime {
    /// `sum(s,e,f) = sum(s,e,g) + sum(s,e,h)` when for all integer `x` with `s <= x <= e`,
    /// `f(x) = g(x) + h(x)` (summands are unary anonymous `fn` bodies, instantiated at `x`).
    pub(crate) fn try_verify_sum_additivity(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }

        let (sum_m, sum_a, sum_b) = match (left, right) {
            (Obj::Sum(m), Obj::Add(a)) => match (a.left.as_ref(), a.right.as_ref()) {
                (Obj::Sum(a1), Obj::Sum(a2)) => (m, a1, a2),
                _ => return Ok(None),
            },
            (Obj::Add(a), Obj::Sum(m)) => match (a.left.as_ref(), a.right.as_ref()) {
                (Obj::Sum(a1), Obj::Sum(a2)) => (m, a1, a2),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };

        let mut require_eq = |a: &Obj, b: &Obj| -> Result<bool, RuntimeError> {
            Ok(self
                .verify_objs_are_equal_in_equality_builtin(a, b, line_file.clone(), verify_state)?
                .is_true())
        };
        if !require_eq(sum_m.start.as_ref(), sum_a.start.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.start.as_ref(), sum_b.start.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.end.as_ref(), sum_a.end.as_ref())? {
            return Ok(None);
        }
        if !require_eq(sum_m.end.as_ref(), sum_b.end.as_ref())? {
            return Ok(None);
        }

        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);

        let Some(l_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_m.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(a_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_a.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(b_inst) =
            self.instantiate_unary_anonymous_summand_at(sum_b.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };

        let then_fact: AtomicFact =
            EqualFact::new(l_inst, Add::new(a_inst, b_inst).into(), line_file.clone()).into();

        let dom_lo: Fact =
            LessEqualFact::new((*sum_m.start).clone(), x_obj.clone(), line_file.clone()).into();
        let dom_hi: Fact =
            LessEqualFact::new(x_obj.clone(), (*sum_m.end).clone(), line_file.clone()).into();

        let r = self.verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
            x_name,
            vec![dom_lo, dom_hi],
            &then_fact,
            verify_state,
        )?;
        if r.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: sum additivity from pointwise equality on the integer index range",
            )));
        }
        Ok(None)
    }

    pub(crate) fn instantiate_unary_anonymous_summand_at(
        &mut self,
        func: &Obj,
        x: &Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        let af: &AnonymousFn = match func {
            Obj::AnonymousFn(af) => af,
            Obj::FnObj(fo) => {
                if !fo.body.is_empty() {
                    return Ok(None);
                }
                match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        };
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let param_defs = &af.body.params_def_with_set;
        let args = vec![x.clone()];
        let param_to_arg_map =
            ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(param_defs, &args);
        Ok(Some(self.inst_obj(
            af.equal_to.as_ref(),
            &param_to_arg_map,
            ParamObjType::FnSet,
        )?))
    }

    pub(crate) fn verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
        &mut self,
        param_name: String,
        dom_facts: Vec<Fact>,
        then_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![param_name],
                ParamType::Obj(StandardSet::Z.into()),
            )]);
            rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
            for dom_fact in dom_facts {
                rt.store_fact_without_forall_coverage_check_and_infer(dom_fact)?;
            }
            rt.verify_atomic_fact_by_known_atomic_or_builtin_only(then_fact, verify_state)
        })
    }

    /// `sum(a..b) + sum((b+1)..c) = sum(a..c)` with the same unary anonymous summand on each side.
    pub(crate) fn try_verify_sum_merge_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let (add, s3) = match (left, right) {
            (Obj::Add(a), Obj::Sum(s)) => (a, s),
            (Obj::Sum(s), Obj::Add(a)) => (a, s),
            _ => return Ok(None),
        };
        let (s1, s2) = match (add.left.as_ref(), add.right.as_ref()) {
            (Obj::Sum(x), Obj::Sum(y)) => (x, y),
            _ => return Ok(None),
        };
        for (a, b) in [(s1, s2), (s2, s1)] {
            if let Some(done) = self.try_verify_sum_merge_ordered_pair(
                a,
                b,
                s3,
                left,
                right,
                line_file.clone(),
                verify_state,
            )? {
                return Ok(Some(done));
            }
        }
        Ok(None)
    }

    pub(super) fn try_verify_sum_merge_ordered_pair(
        &mut self,
        s1: &Sum,
        s2: &Sum,
        s3: &Sum,
        stmt_left: &Obj,
        stmt_right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let one: Obj = Number::new("1".to_string()).into();
        let gap = Add::new((*s1.end).clone(), one).into();
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &gap,
                s2.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.start.as_ref(),
                s3.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s2.end.as_ref(),
                s3.end.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.func.as_ref(),
                s2.func.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                s1.func.as_ref(),
                s3.func.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            stmt_left,
            stmt_right,
            line_file,
            "equality: merge adjacent sum ranges with the same summand",
        )))
    }

    // A finite sum over one index is the summand at that index.
    // Example: `sum(1, 1, fn(x N_pos) N_pos {x}) = 1`.
    pub(crate) fn try_verify_sum_single_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (sum_obj, other) in [(left, right), (right, left)] {
            let Obj::Sum(sum) = sum_obj else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    sum.start.as_ref(),
                    sum.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let Some(expected) =
                self.instantiate_unary_anonymous_summand_at(sum.func.as_ref(), sum.start.as_ref())?
            else {
                continue;
            };
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    &expected,
                    other,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: single-term sum equals the summand",
                )));
            }
        }
        Ok(None)
    }

    // A finite product over one index is the factor at that index.
    // Example: `product(1, 1, fn(x N_pos) N_pos {x}) = 1`.
    pub(crate) fn try_verify_product_single_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (product_obj, other) in [(left, right), (right, left)] {
            let Obj::Product(product) = product_obj else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    product.start.as_ref(),
                    product.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let Some(expected) = self.instantiate_unary_anonymous_summand_at(
                product.func.as_ref(),
                product.start.as_ref(),
            )?
            else {
                continue;
            };
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    &expected,
                    other,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: single-term product equals the factor",
                )));
            }
        }
        Ok(None)
    }

    // sum(s,e,f) = sum(s,e-1,f) + f(e): same unary summand, shared start, e = (e-1)+1 on the shorter range.
    pub(crate) fn try_verify_sum_split_last_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let one: Obj = Number::new("1".to_string()).into();
        for (full_obj, add_obj) in [(left, right), (right, left)] {
            let Obj::Sum(s_full) = full_obj else {
                continue;
            };
            let Obj::Add(a) = add_obj else {
                continue;
            };
            for (sum_part, tail) in [
                (a.left.as_ref(), a.right.as_ref()),
                (a.right.as_ref(), a.left.as_ref()),
            ] {
                let Obj::Sum(s_pre) = sum_part else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.start.as_ref(),
                        s_pre.start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let end_pre_plus_one: Obj = Add::new((*s_pre.end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.end.as_ref(),
                        &end_pre_plus_one,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.func.as_ref(),
                        s_pre.func.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let Some(expected_tail) = self.instantiate_unary_anonymous_summand_at(
                    s_full.func.as_ref(),
                    s_full.end.as_ref(),
                )?
                else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &expected_tail,
                        tail,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum through e equals sum through e-1 plus last summand f(e)",
                )));
            }
        }
        Ok(None)
    }

    // product(s,e,f) = product(s,e-1,f) * f(e): same unary factor, shared start, e = (e-1)+1.
    pub(crate) fn try_verify_product_split_last_term(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let one: Obj = Number::new("1".to_string()).into();
        for (full_obj, mul_obj) in [(left, right), (right, left)] {
            let Obj::Product(p_full) = full_obj else {
                continue;
            };
            let Obj::Mul(m) = mul_obj else {
                continue;
            };
            for (prod_part, tail) in [
                (m.left.as_ref(), m.right.as_ref()),
                (m.right.as_ref(), m.left.as_ref()),
            ] {
                let Obj::Product(p_pre) = prod_part else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.start.as_ref(),
                        p_pre.start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let end_pre_plus_one: Obj = Add::new((*p_pre.end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.end.as_ref(),
                        &end_pre_plus_one,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.func.as_ref(),
                        p_pre.func.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let Some(expected_tail) = self.instantiate_unary_anonymous_summand_at(
                    p_full.func.as_ref(),
                    p_full.end.as_ref(),
                )?
                else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &expected_tail,
                        tail,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: product through e equals product through e-1 times last factor f(e)",
                )));
            }
        }
        Ok(None)
    }

    pub(super) fn flatten_left_assoc_add_chain(obj: &Obj) -> Vec<&Obj> {
        match obj {
            Obj::Add(a) => {
                let mut v = Self::flatten_left_assoc_add_chain(a.left.as_ref());
                v.push(a.right.as_ref());
                v
            }
            _ => vec![obj],
        }
    }

    pub(super) fn flatten_left_assoc_mul_chain(obj: &Obj) -> Vec<&Obj> {
        match obj {
            Obj::Mul(m) => {
                let mut v = Self::flatten_left_assoc_mul_chain(m.left.as_ref());
                v.push(m.right.as_ref());
                v
            }
            _ => vec![obj],
        }
    }

    // sum(s,e,f) = sum(s1,e1,f) + sum(s2,e2,f) + ... with contiguous [si,ei] tiling [s,e], same unary f.
    pub(crate) fn try_verify_sum_partition_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let one: Obj = Number::new("1".to_string()).into();
        for (full_side, add_side) in [(left, right), (right, left)] {
            let Obj::Sum(s_full) = full_side else {
                continue;
            };
            let Obj::Add(_) = add_side else {
                continue;
            };
            let parts = Self::flatten_left_assoc_add_chain(add_side);
            if parts.len() < 2 {
                continue;
            }
            let mut sums: Vec<&Sum> = Vec::with_capacity(parts.len());
            let mut all_sum = true;
            for p in &parts {
                if let Obj::Sum(s) = p {
                    sums.push(s);
                } else {
                    all_sum = false;
                    break;
                }
            }
            if !all_sum {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    s_full.start.as_ref(),
                    sums[0].start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    s_full.end.as_ref(),
                    sums[sums.len() - 1].end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let mut gaps_ok = true;
            for i in 0..sums.len().saturating_sub(1) {
                let gap = Add::new((*sums[i].end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &gap,
                        sums[i + 1].start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    gaps_ok = false;
                    break;
                }
            }
            if !gaps_ok {
                continue;
            }
            let mut func_ok = true;
            for s in &sums {
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        s_full.func.as_ref(),
                        s.func.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    func_ok = false;
                    break;
                }
            }
            if !func_ok {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: sum partitions closed range into adjacent sub-sums with the same summand",
            )));
        }
        Ok(None)
    }

    // product(s,e,f) = product(s1,e1,f) * product(s2,e2,f) * ... contiguous tiling, same unary f.
    pub(crate) fn try_verify_product_partition_adjacent_ranges(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let one: Obj = Number::new("1".to_string()).into();
        for (full_side, mul_side) in [(left, right), (right, left)] {
            let Obj::Product(p_full) = full_side else {
                continue;
            };
            let Obj::Mul(_) = mul_side else {
                continue;
            };
            let parts = Self::flatten_left_assoc_mul_chain(mul_side);
            if parts.len() < 2 {
                continue;
            }
            let mut products: Vec<&Product> = Vec::with_capacity(parts.len());
            let mut all_prod = true;
            for p in &parts {
                if let Obj::Product(pr) = p {
                    products.push(pr);
                } else {
                    all_prod = false;
                    break;
                }
            }
            if !all_prod {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    p_full.start.as_ref(),
                    products[0].start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    p_full.end.as_ref(),
                    products[products.len() - 1].end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let mut gaps_ok = true;
            for i in 0..products.len().saturating_sub(1) {
                let gap = Add::new((*products[i].end).clone(), one.clone()).into();
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        &gap,
                        products[i + 1].start.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    gaps_ok = false;
                    break;
                }
            }
            if !gaps_ok {
                continue;
            }
            let mut func_ok = true;
            for p in &products {
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        p_full.func.as_ref(),
                        p.func.as_ref(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    func_ok = false;
                    break;
                }
            }
            if !func_ok {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: product partitions closed range into adjacent sub-products with the same factor",
            )));
        }
        Ok(None)
    }

    /// `sum(L) = sum(R)` with `R` a translate of `L` by `k` on both bounds, reduced to pointwise
    /// equality on the right-hand index range.
    pub(crate) fn try_verify_sum_reindex_shift(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (l_obj, r_obj) in [(left, right), (right, left)] {
            let (Obj::Sum(l_sum), Obj::Sum(r_sum)) = (l_obj, r_obj) else {
                continue;
            };
            let k: Obj = Sub::new((*r_sum.start).clone(), (*l_sum.start).clone()).into();
            let k_end = Sub::new((*r_sum.end).clone(), (*l_sum.end).clone()).into();
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    &k,
                    &k_end,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let y_name = self.generate_random_unused_name();
            let y_obj = obj_for_bound_param_in_scope(y_name.clone(), ParamObjType::Forall);
            let index_for_left = Sub::new(y_obj.clone(), k.clone()).into();
            let Some(at_l) =
                self.instantiate_unary_anonymous_summand_at(l_sum.func.as_ref(), &index_for_left)?
            else {
                continue;
            };
            let Some(at_r) =
                self.instantiate_unary_anonymous_summand_at(r_sum.func.as_ref(), &y_obj)?
            else {
                continue;
            };
            let then_fact: AtomicFact = EqualFact::new(at_l, at_r, line_file.clone()).into();
            let dom_lo: Fact =
                LessEqualFact::new((*r_sum.start).clone(), y_obj.clone(), line_file.clone()).into();
            let dom_hi: Fact =
                LessEqualFact::new(y_obj.clone(), (*r_sum.end).clone(), line_file.clone()).into();
            let r = self.verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                y_name,
                vec![dom_lo, dom_hi],
                &then_fact,
                verify_state,
            )?;
            if r.is_true() {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum reindexing (integer shift) from pointwise equality on the range",
                )));
            }
        }
        Ok(None)
    }

    /// `sum(s,e, \lambda x.c) = (e - s + 1) * c` when `c` does not mention the index parameter.
    pub(crate) fn try_verify_sum_constant_summand(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (sum_side, other) in [(left, right), (right, left)] {
            let Obj::Sum(s) = sum_side else {
                continue;
            };
            let af = match s.func.as_ref() {
                Obj::AnonymousFn(af) => af,
                Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => continue,
                },
                _ => continue,
            };
            if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
                continue;
            }
            let names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
            let pname = match names.first() {
                Some(n) => n.as_str(),
                None => continue,
            };
            if obj_expr_mentions_bare_id(af.equal_to.as_ref(), pname) {
                continue;
            }
            let c = (*af.equal_to).clone();
            let one: Obj = Number::new("1".to_string()).into();
            let count: Obj =
                Add::new(Sub::new((*s.end).clone(), (*s.start).clone()).into(), one).into();
            let m1: Obj = Mul::new(count.clone(), c.clone()).into();
            let m2: Obj = Mul::new(c, count).into();
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &m1,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
                || self
                    .verify_objs_are_equal_in_equality_builtin(
                        other,
                        &m2,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: sum of a constant summand over a closed integer range",
                )));
            }
        }
        Ok(None)
    }

    // Scalars factor out of finite sums over the same integer index range.
    // Example: `sum(m, n, fn(i Z) R {c * a(i)}) = c * sum(m, n, fn(i Z) R {a(i)})`.
    pub(crate) fn try_verify_sum_scalar_mul(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }

        for (sum_side, product_side) in [(left, right), (right, left)] {
            let Obj::Sum(sum) = sum_side else {
                continue;
            };
            let Obj::Mul(product) = product_side else {
                continue;
            };
            for (base_side, scalar) in [
                (product.left.as_ref(), product.right.as_ref()),
                (product.right.as_ref(), product.left.as_ref()),
            ] {
                let Obj::Sum(base_sum) = base_side else {
                    continue;
                };
                let start_result = self.verify_objs_are_equal_in_equality_builtin(
                    sum.start.as_ref(),
                    base_sum.start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !start_result.is_true() {
                    continue;
                }
                let end_result = self.verify_objs_are_equal_in_equality_builtin(
                    sum.end.as_ref(),
                    base_sum.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !end_result.is_true() {
                    continue;
                }

                let x_name = self.generate_random_unused_name();
                let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
                let Some(sum_inst) =
                    self.instantiate_unary_anonymous_summand_at(sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let Some(base_inst) =
                    self.instantiate_unary_anonymous_summand_at(base_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let expected: Obj = Mul::new(scalar.clone(), base_inst).into();
                let pointwise_fact: AtomicFact =
                    EqualFact::new(sum_inst, expected, line_file.clone()).into();
                let dom_lo: Fact =
                    LessEqualFact::new((*sum.start).clone(), x_obj.clone(), line_file.clone())
                        .into();
                let dom_hi: Fact =
                    LessEqualFact::new(x_obj.clone(), (*sum.end).clone(), line_file.clone()).into();
                let pointwise_result = self
                    .verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                        x_name,
                        vec![dom_lo, dom_hi],
                        &pointwise_fact,
                        verify_state,
                    )?;
                if !pointwise_result.is_true() {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite sum scalar multiplication",
                )));
            }
        }
        Ok(None)
    }
}
