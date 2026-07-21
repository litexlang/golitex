use crate::common::count_range_integer::{
    count_closed_range_integer_endpoints, count_half_open_range_integer_endpoints,
};
use crate::prelude::*;
use crate::verify::{compare_normalized_number_str_to_zero, NumberCompareResult};

impl Runtime {
    fn cached_less_equal_fact_holds(&self, left: Obj, right: Obj) -> bool {
        let fact: Fact = LessEqualFact::new(left, right, default_line_file()).into();
        let (cache_ok, _) = self.cache_known_facts_contains(&fact.to_string());
        cache_ok
    }

    fn obj_is_known_nonnegative(&self, obj: &Obj) -> bool {
        self.cached_less_equal_fact_holds(Number::new("0".to_string()).into(), obj.clone())
    }

    fn obj_is_known_nonpositive(&self, obj: &Obj) -> bool {
        self.cached_less_equal_fact_holds(obj.clone(), Number::new("0".to_string()).into())
    }

    pub fn resolve_obj_to_number(&self, obj: &Obj) -> Option<Number> {
        if let Some(number) = obj.evaluate_to_normalized_decimal_number() {
            return Some(number);
        }
        let obj_key = obj.to_string();
        if let Some(number) = self.get_object_equal_to_normalized_decimal_number(&obj_key) {
            return Some(number);
        }
        None
    }

    pub fn resolve_obj_to_number_resolved(&self, obj: &Obj) -> Option<Number> {
        self.resolve_obj_to_number(&self.resolve_obj(obj))
    }

    // After resolving children, fold literals; if still not a number, use
    // `known_obj_values` so e.g. `a - b` becomes `100` when that
    // binding exists, then outer `(... - 10)` can evaluate (used by equality `calculation`).
    fn resolve_obj_try_fold_arithmetic(&self, result: Obj) -> Obj {
        if let Some(calculated) = result.evaluate_to_normalized_decimal_number() {
            return calculated.into();
        }
        if let Some(n) = self.resolve_obj_to_number(&result) {
            return n.into();
        }
        if let Some(known_value) = self.get_known_obj_value_as_obj(&result.to_string()) {
            return known_value;
        }
        result
    }

    pub fn resolve_obj(&self, obj: &Obj) -> Obj {
        if let Some(number) = self.resolve_obj_to_number(obj) {
            return number.into();
        }
        if let Some(known_value) = self.get_known_obj_value_as_obj(&obj.to_string()) {
            return known_value;
        }
        match obj {
            Obj::Number(number) => number.clone().into(),
            Obj::Atom(AtomObj::IdentifierWithMod(identifier))
                if self.is_current_parse_module(&identifier.mod_name) =>
            {
                let local_obj: Obj = Identifier::new(identifier.name.clone()).into();
                self.resolve_obj(&local_obj)
            }
            Obj::Add(add) => {
                let result: Obj =
                    Add::new(self.resolve_obj(&add.left), self.resolve_obj(&add.right)).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Sub(sub) => {
                let result: Obj =
                    Sub::new(self.resolve_obj(&sub.left), self.resolve_obj(&sub.right)).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Mul(mul) => {
                let result: Obj =
                    Mul::new(self.resolve_obj(&mul.left), self.resolve_obj(&mul.right)).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Mod(mod_obj) => {
                let result: Obj = Mod::new(
                    self.resolve_obj(&mod_obj.left),
                    self.resolve_obj(&mod_obj.right),
                )
                .into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::IntegerQuotient(quotient) => {
                let result: Obj = IntegerQuotient::new(
                    self.resolve_obj(&quotient.dividend),
                    self.resolve_obj(&quotient.divisor),
                )
                .into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Pow(pow) => {
                let result = self.resolve_pow_after_children(
                    self.resolve_obj(&pow.base),
                    self.resolve_obj(&pow.exponent),
                );
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Div(div) => {
                let resolved_left = self.resolve_obj(&div.left);
                let resolved_right = self.resolve_obj(&div.right);
                if let Some(cancelled) = self
                    .try_resolve_division_by_matching_mul_factor(&resolved_left, &resolved_right)
                {
                    return cancelled;
                }
                let result: Obj = Div::new(resolved_left, resolved_right).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Abs(a) => {
                let resolved_arg = self.resolve_obj(&a.arg);
                if self.obj_is_known_nonnegative(&resolved_arg) {
                    return resolved_arg;
                }
                if self.obj_is_known_nonpositive(&resolved_arg) {
                    let result: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), resolved_arg).into();
                    return self.resolve_obj_try_fold_arithmetic(result);
                }
                let result: Obj = Abs::new(resolved_arg).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Log(l) => {
                let result: Obj =
                    Log::new(self.resolve_obj(&l.base), self.resolve_obj(&l.arg)).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::FiniteSeqSet(fs) => {
                FiniteSeqSet::new(self.resolve_obj(&fs.set), self.resolve_obj(&fs.n)).into()
            }
            Obj::SeqSet(ss) => SeqSet::new(self.resolve_obj(&ss.set)).into(),
            Obj::MatrixSet(ms) => MatrixSet::new(
                self.resolve_obj(&ms.set),
                self.resolve_obj(&ms.row_len),
                self.resolve_obj(&ms.col_len),
            )
            .into(),
            Obj::FiniteSeqListObj(list) => {
                let objs: Vec<Obj> = list.objs.iter().map(|o| self.resolve_obj(o)).collect();
                FiniteSeqListObj::new(objs).into()
            }
            Obj::MatrixListObj(matrix) => {
                let rows: Vec<Vec<Obj>> = matrix
                    .rows
                    .iter()
                    .map(|row| row.iter().map(|o| self.resolve_obj(o)).collect())
                    .collect();
                MatrixListObj::new(rows).into()
            }
            Obj::IntervalObj(interval) => {
                let start = self.resolve_obj(interval.start());
                let end = self.resolve_obj(interval.end());
                match interval {
                    IntervalObj::LeftOpenRightOpen(_) => {
                        IntervalObj::new_left_open_right_open(start, end).into()
                    }
                    IntervalObj::LeftOpenRightClosed(_) => {
                        IntervalObj::new_left_open_right_closed(start, end).into()
                    }
                    IntervalObj::LeftClosedRightOpen(_) => {
                        IntervalObj::new_left_closed_right_open(start, end).into()
                    }
                    IntervalObj::LeftClosedRightClosed(_) => {
                        IntervalObj::new_left_closed_right_closed(start, end).into()
                    }
                }
            }
            Obj::OneSideInfinityIntervalObj(interval) => {
                let start = self.resolve_obj(interval.start());
                match interval {
                    OneSideInfinityIntervalObj::LeftOpen(_) => {
                        OneSideInfinityIntervalObj::new_left_open(start).into()
                    }
                    OneSideInfinityIntervalObj::LeftClosed(_) => {
                        OneSideInfinityIntervalObj::new_left_closed(start).into()
                    }
                    OneSideInfinityIntervalObj::RightOpen(_) => {
                        OneSideInfinityIntervalObj::new_right_open(start).into()
                    }
                    OneSideInfinityIntervalObj::RightClosed(_) => {
                        OneSideInfinityIntervalObj::new_right_closed(start).into()
                    }
                }
            }
            Obj::FnObj(fn_obj) => {
                if let FnObjHead::MatrixOperator(matrix) = fn_obj.head.as_ref() {
                    let args: Vec<Obj> = fn_obj
                        .body
                        .iter()
                        .flat_map(|group| group.iter().map(|arg| (**arg).clone()))
                        .collect();
                    if args.len() == 2 {
                        if let Some(entry) =
                            self.matrix_operator_entry(matrix, args[0].clone(), args[1].clone())
                        {
                            return self.resolve_obj(&entry);
                        }
                    }
                }
                if let FnObjHead::AnonymousFnLiteral(anonymous_fn) = fn_obj.head.as_ref() {
                    if !fn_obj.body.is_empty() {
                        let mut args: Vec<Obj> = Vec::new();
                        for group in fn_obj.body.iter() {
                            for arg in group.iter() {
                                args.push((**arg).clone());
                            }
                        }
                        let param_defs = &anonymous_fn.body.params_def_with_set;
                        if args.len() == ParamGroupWithSet::number_of_params(param_defs) {
                            let param_to_arg_map =
                                ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(
                                    param_defs, &args,
                                );
                            if let Ok(reduced) = self.inst_obj(
                                anonymous_fn.equal_to.as_ref(),
                                &param_to_arg_map,
                                ParamObjType::FnSet,
                            ) {
                                return self.resolve_obj(&reduced);
                            }
                        }
                    }
                }
                if fn_obj.body.len() == 1 && fn_obj.body[0].len() == 1 {
                    if let FnObjHead::FiniteSeqListObj(list) = fn_obj.head.as_ref() {
                        let arg = self.resolve_obj(fn_obj.body[0][0].as_ref());
                        if let Some(ix) = self.resolve_obj_to_number(&arg) {
                            if let Ok(one_based) = ix.normalized_value.parse::<usize>() {
                                if one_based >= 1 && one_based <= list.objs.len() {
                                    return (*list.objs[one_based - 1]).clone();
                                }
                            }
                        }
                    }
                    let head_key = fn_obj.head.to_string();
                    if let Some(list) = self.get_obj_equal_to_finite_seq_list(&head_key) {
                        let arg = self.resolve_obj(fn_obj.body[0][0].as_ref());
                        if let Some(ix) = self.resolve_obj_to_number(&arg) {
                            if let Ok(one_based) = ix.normalized_value.parse::<usize>() {
                                if one_based >= 1 && one_based <= list.objs.len() {
                                    return (*list.objs[one_based - 1]).clone();
                                }
                            }
                        }
                    }
                }
                if fn_obj.body.len() == 2 && fn_obj.body[0].len() == 1 && fn_obj.body[1].len() == 1
                {
                    let head_key = fn_obj.head.to_string();
                    if let Some(mat) = self.get_obj_equal_to_matrix_list(&head_key) {
                        let r_arg = self.resolve_obj(fn_obj.body[0][0].as_ref());
                        let c_arg = self.resolve_obj(fn_obj.body[1][0].as_ref());
                        if let (Some(rn), Some(cn)) = (
                            self.resolve_obj_to_number(&r_arg),
                            self.resolve_obj_to_number(&c_arg),
                        ) {
                            if let (Ok(r1), Ok(c1)) = (
                                rn.normalized_value.parse::<usize>(),
                                cn.normalized_value.parse::<usize>(),
                            ) {
                                if r1 >= 1
                                    && r1 <= mat.rows.len()
                                    && c1 >= 1
                                    && c1 <= mat.rows[r1 - 1].len()
                                {
                                    return (*mat.rows[r1 - 1][c1 - 1]).clone();
                                }
                            }
                        }
                    }
                }
                if fn_obj.body.len() == 1 && fn_obj.body[0].len() == 2 {
                    let head_key = fn_obj.head.to_string();
                    if let Some(mat) = self.get_obj_equal_to_matrix_list(&head_key) {
                        let r_arg = self.resolve_obj(fn_obj.body[0][0].as_ref());
                        let c_arg = self.resolve_obj(fn_obj.body[0][1].as_ref());
                        if let (Some(rn), Some(cn)) = (
                            self.resolve_obj_to_number(&r_arg),
                            self.resolve_obj_to_number(&c_arg),
                        ) {
                            if let (Ok(r1), Ok(c1)) = (
                                rn.normalized_value.parse::<usize>(),
                                cn.normalized_value.parse::<usize>(),
                            ) {
                                if r1 >= 1
                                    && r1 <= mat.rows.len()
                                    && c1 >= 1
                                    && c1 <= mat.rows[r1 - 1].len()
                                {
                                    return (*mat.rows[r1 - 1][c1 - 1]).clone();
                                }
                            }
                        }
                    }
                }
                if let Some(number) = self.resolve_obj_to_number(obj) {
                    number.into()
                } else {
                    let resolved_body: Vec<Vec<Box<Obj>>> = fn_obj
                        .body
                        .iter()
                        .map(|group| {
                            group
                                .iter()
                                .map(|arg| Box::new(self.resolve_obj(arg.as_ref())))
                                .collect()
                        })
                        .collect();
                    FnObj::new(*fn_obj.head.clone(), resolved_body).into()
                }
            }
            Obj::Atom(AtomObj::Identifier(_))
            | Obj::Atom(AtomObj::IdentifierWithMod(_))
            | Obj::Atom(AtomObj::Forall(_))
            | Obj::Atom(AtomObj::Def(_))
            | Obj::Atom(AtomObj::Exist(_))
            | Obj::Atom(AtomObj::SetBuilder(_))
            | Obj::Atom(AtomObj::FnSet(_))
            | Obj::Atom(AtomObj::Induc(_))
            | Obj::Atom(AtomObj::DefAlgo(_))
            | Obj::Atom(AtomObj::DefStructField(_))
            | Obj::Atom(AtomObj::TupleIndex(_))
            | Obj::Atom(AtomObj::CartIndex(_)) => {
                if let Some(number) = self.resolve_obj_to_number(obj) {
                    number.into()
                } else {
                    obj.clone()
                }
            }
            Obj::FiniteSetSize(finite_set_size) => match &*finite_set_size.set {
                Obj::ListSet(list_set) => Number::new(list_set.list.len().to_string()).into(),
                Obj::ClosedRange(cr) => {
                    if let (Some(a_num), Some(b_num)) = (
                        self.resolve_obj_to_number_resolved(cr.start.as_ref()),
                        self.resolve_obj_to_number_resolved(cr.end.as_ref()),
                    ) {
                        if let Some(n) = count_closed_range_integer_endpoints(&a_num, &b_num) {
                            return n.into();
                        }
                    }
                    obj.clone()
                }
                Obj::Range(r) => {
                    if let (Some(a_num), Some(b_num)) = (
                        self.resolve_obj_to_number_resolved(r.start.as_ref()),
                        self.resolve_obj_to_number_resolved(r.end.as_ref()),
                    ) {
                        if let Some(n) = count_half_open_range_integer_endpoints(&a_num, &b_num) {
                            return n.into();
                        }
                    }
                    obj.clone()
                }
                Obj::Cart(cart) => {
                    let mut acc = "1".to_string();
                    for arg in &cart.args {
                        let resolved_arg = self.resolve_obj(arg.as_ref());
                        let finite_set_size_obj =
                            Obj::FiniteSetSize(FiniteSetSize::new(resolved_arg));
                        let n = match self.resolve_obj_to_number(&finite_set_size_obj) {
                            Some(n) => n,
                            None => return obj.clone(),
                        };
                        acc = mul_signed_decimal_str(acc.trim(), n.normalized_value.trim());
                    }
                    Number::new(acc).into()
                }
                _ => obj.clone(),
            },
            Obj::FiniteSetMax(extremum) => {
                let result: Obj = FiniteSetMax::new(self.resolve_obj(&extremum.set)).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::FiniteSetMin(extremum) => {
                let result: Obj = FiniteSetMin::new(self.resolve_obj(&extremum.set)).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::FnRange(fn_range) => FnRange::new(self.resolve_obj(&fn_range.function)).into(),
            Obj::Replacement(replacement) => Replacement::new(
                replacement.prop_name.clone(),
                self.resolve_obj(&replacement.source_set),
            )
            .into(),
            Obj::TupleDim(dim) => match &*dim.arg {
                Obj::Tuple(tuple) => Number::new(tuple.args.len().to_string()).into(),
                _ => obj.clone(),
            },
            Obj::CartDim(cart_dim) => match &*cart_dim.set {
                Obj::Cart(cart) => Number::new(cart.args.len().to_string()).into(),
                _ => obj.clone(),
            },
            Obj::Proj(proj) => match &*proj.set {
                Obj::Cart(cart) => {
                    let projection_index_number = self.resolve_obj_to_number(&proj.dim);
                    if let Some(projection_index_number) = projection_index_number {
                        let projection_index_parsed_result =
                            projection_index_number.normalized_value.parse::<usize>();
                        if let Ok(projection_index_one_based) = projection_index_parsed_result {
                            if projection_index_one_based >= 1
                                && projection_index_one_based <= cart.args.len()
                            {
                                return (*cart.args[projection_index_one_based - 1]).clone();
                            }
                        }
                    }
                    obj.clone()
                }
                _ => {
                    let known_cart_obj = self.get_object_equal_to_cart(&proj.set.to_string());
                    if let Some(known_cart_obj) = known_cart_obj {
                        let projection_index_number = self.resolve_obj_to_number(&proj.dim);
                        if let Some(projection_index_number) = projection_index_number {
                            let projection_index_parsed_result =
                                projection_index_number.normalized_value.parse::<usize>();
                            if let Ok(projection_index_one_based) = projection_index_parsed_result {
                                if projection_index_one_based >= 1
                                    && projection_index_one_based <= known_cart_obj.args.len()
                                {
                                    return (*known_cart_obj.args[projection_index_one_based - 1])
                                        .clone();
                                }
                            }
                        }
                    }
                    obj.clone()
                }
            },
            Obj::ObjAtIndex(obj_at_index) => match &*obj_at_index.obj {
                Obj::Tuple(tuple) => {
                    let tuple_index_number = self.resolve_obj_to_number(&obj_at_index.index);
                    if let Some(tuple_index_number) = tuple_index_number {
                        let tuple_index_parsed_result =
                            tuple_index_number.normalized_value.parse::<usize>();
                        if let Ok(tuple_index_one_based) = tuple_index_parsed_result {
                            if tuple_index_one_based >= 1
                                && tuple_index_one_based <= tuple.args.len()
                            {
                                return (*tuple.args[tuple_index_one_based - 1]).clone();
                            }
                        }
                    }
                    obj.clone()
                }
                Obj::FiniteSeqListObj(list) => {
                    let ix = self.resolve_obj_to_number(&obj_at_index.index);
                    if let Some(ix) = ix {
                        if let Ok(one_based) = ix.normalized_value.parse::<usize>() {
                            if one_based >= 1 && one_based <= list.objs.len() {
                                return (*list.objs[one_based - 1]).clone();
                            }
                        }
                    }
                    obj.clone()
                }
                _ => {
                    let known_tuple_obj =
                        self.get_obj_equal_to_tuple(&obj_at_index.obj.to_string());
                    if let Some(known_tuple_obj) = known_tuple_obj {
                        let tuple_index_number = self.resolve_obj_to_number(&obj_at_index.index);
                        if let Some(tuple_index_number) = tuple_index_number {
                            let tuple_index_parsed_result =
                                tuple_index_number.normalized_value.parse::<usize>();
                            if let Ok(tuple_index_one_based) = tuple_index_parsed_result {
                                if tuple_index_one_based >= 1
                                    && tuple_index_one_based <= known_tuple_obj.args.len()
                                {
                                    return (*known_tuple_obj.args[tuple_index_one_based - 1])
                                        .clone();
                                }
                            }
                        }
                    }
                    if let Some(known_list) =
                        self.get_obj_equal_to_finite_seq_list(&obj_at_index.obj.to_string())
                    {
                        let ix = self.resolve_obj_to_number(&obj_at_index.index);
                        if let Some(ix) = ix {
                            if let Ok(one_based) = ix.normalized_value.parse::<usize>() {
                                if one_based >= 1 && one_based <= known_list.objs.len() {
                                    return (*known_list.objs[one_based - 1]).clone();
                                }
                            }
                        }
                    }
                    obj.clone()
                }
            },
            _ => obj.clone(),
        }
    }

    pub(crate) fn obj_is_resolved_zero(&self, obj: &Obj) -> bool {
        self.resolve_obj_to_number(obj)
            .map(|n| {
                matches!(
                    compare_normalized_number_str_to_zero(&n.normalized_value),
                    NumberCompareResult::Equal
                )
            })
            .unwrap_or(false)
    }

    /// If `obj` is `(-1) * u` or `u * (-1)` with literal `-1`, returns `u`.
    pub(crate) fn peel_mul_by_literal_neg_one(&self, obj: &Obj) -> Option<Obj> {
        let Obj::Mul(m) = obj else {
            return None;
        };
        if let Some(ln) = self.resolve_obj_to_number(m.left.as_ref()) {
            if ln.normalized_value == "-1" {
                return Some(m.right.as_ref().clone());
            }
        }
        if let Some(rn) = self.resolve_obj_to_number(m.right.as_ref()) {
            if rn.normalized_value == "-1" {
                return Some(m.left.as_ref().clone());
            }
        }
        None
    }

    /// Cancel a matching multiplicative factor when the divisor is known nonzero.
    /// Example: from `a != 0`, both `a * b / a` and `b * a / a` resolve to `b`.
    fn try_resolve_division_by_matching_mul_factor(
        &self,
        numerator: &Obj,
        denominator: &Obj,
    ) -> Option<Obj> {
        let Obj::Mul(mul) = numerator else {
            return None;
        };

        let denominator_key = denominator.to_string();
        let cancelled = if mul.left.to_string() == denominator_key {
            mul.right.as_ref().clone()
        } else if mul.right.to_string() == denominator_key {
            mul.left.as_ref().clone()
        } else {
            return None;
        };

        let denominator_known_nonzero = if let Some(number) =
            self.resolve_obj_to_number(denominator)
        {
            !matches!(
                compare_normalized_number_str_to_zero(&number.normalized_value),
                NumberCompareResult::Equal
            )
        } else {
            let zero: Obj = Number::new("0".to_string()).into();
            let forward: Fact =
                NotEqualFact::new(denominator.clone(), zero.clone(), default_line_file()).into();
            let backward: Fact =
                NotEqualFact::new(zero, denominator.clone(), default_line_file()).into();
            self.cache_known_facts_contains(&forward.to_string()).0
                || self.cache_known_facts_contains(&backward.to_string()).0
        };

        if denominator_known_nonzero {
            Some(cancelled)
        } else {
            None
        }
    }

    fn resolve_pow_after_children(&self, base: Obj, exponent: Obj) -> Obj {
        if let Some(signless_base) = try_remove_even_power_negative_sign(&base, &exponent) {
            let signless_power: Obj = Pow::new(signless_base, exponent.clone()).into();
            return self.resolve_obj(&signless_power);
        }

        if let Some(resolved_sqrt_power) = self.try_resolve_sqrt_even_power(&base, &exponent) {
            return resolved_sqrt_power;
        }

        if let Some(resolved_product_power) =
            self.try_resolve_product_power_to_number(&base, &exponent)
        {
            return resolved_product_power;
        }

        Pow::new(base, exponent).into()
    }

    fn try_resolve_sqrt_even_power(&self, base: &Obj, exponent: &Obj) -> Option<Obj> {
        let exponent_value = nonnegative_integer_value(exponent)?;
        if exponent_value % 2 != 0 {
            return None;
        }
        let Obj::Sqrt(sqrt) = base else {
            return None;
        };

        let half_exponent = exponent_value / 2;
        if half_exponent == 0 {
            return Some(Number::new("1".to_string()).into());
        }
        if half_exponent == 1 {
            return Some(self.resolve_obj(sqrt.arg.as_ref()));
        }

        let half_exponent_obj: Obj = Number::new(half_exponent.to_string()).into();
        let result: Obj = Pow::new(sqrt.arg.as_ref().clone(), half_exponent_obj).into();
        Some(self.resolve_obj(&result))
    }

    fn try_resolve_product_power_to_number(&self, base: &Obj, exponent: &Obj) -> Option<Obj> {
        nonnegative_integer_value(exponent)?;

        let mut factors = Vec::new();
        collect_mul_factors(base, &mut factors);
        if factors.len() <= 1 {
            return None;
        }

        let mut product = "1".to_string();
        for factor in factors {
            let factor_power: Obj = Pow::new(factor, exponent.clone()).into();
            let resolved_factor_power = self.resolve_obj(&factor_power);
            let number = self.resolve_obj_to_number(&resolved_factor_power)?;
            product = mul_signed_decimal_str(product.as_str(), number.normalized_value.as_str());
        }

        Some(Number::new(product).into())
    }

    pub(crate) fn known_obj_value_from_obj(&self, obj: &Obj) -> Option<KnownObjValue> {
        if let Some(number) = self.resolve_obj_to_number(obj) {
            return Some(KnownObjValue::SimplifiedNumber(number));
        }
        let (numerator, denominator) = self.simplified_rational_pair_from_obj(obj)?;
        if denominator == 1 {
            return Some(KnownObjValue::SimplifiedNumber(Number::new(
                numerator.to_string(),
            )));
        }

        let div = Div::new(
            Number::new(numerator.to_string()).into(),
            Number::new(denominator.to_string()).into(),
        );
        let div_obj: Obj = div.clone().into();
        if let Some(number) = div_obj.evaluate_to_normalized_decimal_number() {
            return Some(KnownObjValue::SimplifiedNumber(number));
        }
        Some(KnownObjValue::SimplifiedFraction(div))
    }

    fn simplified_rational_pair_from_obj(&self, obj: &Obj) -> Option<(i128, i128)> {
        if self.resolve_obj_to_number(obj).is_some() {
            return None;
        }

        let resolved = self.resolve_obj(obj);
        rational_pair_from_obj(&resolved)
    }

    fn matrix_operator_entry(&self, matrix: &Obj, row: Obj, col: Obj) -> Option<Obj> {
        match matrix {
            Obj::MatrixAdd(value) => Some(
                Add::new(
                    matrix_entry_application((*value.left).clone(), row.clone(), col.clone())?,
                    matrix_entry_application((*value.right).clone(), row, col)?,
                )
                .into(),
            ),
            Obj::MatrixSub(value) => Some(
                Sub::new(
                    matrix_entry_application((*value.left).clone(), row.clone(), col.clone())?,
                    matrix_entry_application((*value.right).clone(), row, col)?,
                )
                .into(),
            ),
            Obj::MatrixScalarMul(value) => Some(
                Mul::new(
                    (*value.scalar).clone(),
                    matrix_entry_application((*value.matrix).clone(), row, col)?,
                )
                .into(),
            ),
            Obj::MatrixMul(value) => {
                let end = self.matrix_column_dimension(&value.left)?;
                let index_name = self.generate_random_unused_name();
                let index = obj_for_bound_param_in_scope(index_name.clone(), ParamObjType::FnSet);
                let term: Obj = Mul::new(
                    matrix_entry_application((*value.left).clone(), row, index.clone())?,
                    matrix_entry_application((*value.right).clone(), index.clone(), col)?,
                )
                .into();
                let function = AnonymousFn::new(
                    vec![ParamGroupWithSet::new(
                        vec![index_name],
                        StandardSet::NPos.into(),
                    )],
                    vec![AtomicFact::from(LessEqualFact::new(
                        index,
                        end.clone(),
                        default_line_file(),
                    ))
                    .into()],
                    StandardSet::R.into(),
                    term,
                )
                .ok()?;
                Some(Sum::new(Number::new("1".to_string()).into(), end, function.into()).into())
            }
            Obj::MatrixPow(value) => {
                let exponent = self.resolve_obj(&value.exponent);
                let one: Obj = Number::new("1".to_string()).into();
                if exponent.to_string() == one.to_string() {
                    return matrix_entry_application((*value.base).clone(), row, col);
                }
                let predecessor = match &exponent {
                    Obj::Number(number) => {
                        let value = number.normalized_value.parse::<usize>().ok()?;
                        if value <= 1 {
                            return None;
                        }
                        Number::new((value - 1).to_string()).into()
                    }
                    Obj::Add(add)
                        if self.resolve_obj(&add.right).to_string() == one.to_string() =>
                    {
                        (*add.left).clone()
                    }
                    Obj::Add(add) if self.resolve_obj(&add.left).to_string() == one.to_string() => {
                        (*add.right).clone()
                    }
                    _ => return None,
                };
                let product: Obj = MatrixMul::new(
                    MatrixPow::new((*value.base).clone(), predecessor).into(),
                    (*value.base).clone(),
                )
                .into();
                self.matrix_operator_entry(&product, row, col)
            }
            _ => None,
        }
    }

    fn matrix_column_dimension(&self, matrix: &Obj) -> Option<Obj> {
        if let Some(matrix_set) = self.get_matrix_set_for_obj(matrix) {
            return Some((*matrix_set.col_len).clone());
        }
        match matrix {
            Obj::MatrixListObj(value) if !value.rows.is_empty() && !value.rows[0].is_empty() => {
                Some(Number::new(value.rows[0].len().to_string()).into())
            }
            Obj::MatrixAdd(value) => self.matrix_column_dimension(&value.left),
            Obj::MatrixSub(value) => self.matrix_column_dimension(&value.left),
            Obj::MatrixMul(value) => self.matrix_column_dimension(&value.right),
            Obj::MatrixScalarMul(value) => self.matrix_column_dimension(&value.matrix),
            Obj::MatrixPow(value) => self.matrix_column_dimension(&value.base),
            _ => None,
        }
    }
}

fn matrix_entry_application(matrix: Obj, row: Obj, col: Obj) -> Option<Obj> {
    let head = FnObjHead::from_callable_obj(matrix)?;
    Some(FnObj::new(head, vec![vec![Box::new(row), Box::new(col)]]).into())
}

fn normalize_rational_pair(numerator: i128, denominator: i128) -> Option<(i128, i128)> {
    if denominator == 0 {
        return None;
    }
    if numerator == 0 {
        return Some((0, 1));
    }

    let mut n = numerator;
    let mut d = denominator;
    if d < 0 {
        n = n.checked_neg()?;
        d = d.checked_neg()?;
    }
    let g = gcd_i128(n, d);
    Some((n / g, d / g))
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn rational_pair_from_number(number: &Number) -> Option<(i128, i128)> {
    let value = number.normalized_value.as_str();
    let (is_negative, unsigned) = match value.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, value),
    };

    let (digits, denominator) = if let Some(dot_index) = unsigned.find('.') {
        let integer_part = &unsigned[..dot_index];
        let fractional_part = &unsigned[dot_index + 1..];
        let integer_digits = if integer_part.is_empty() {
            "0"
        } else {
            integer_part
        };
        let digits = format!("{}{}", integer_digits, fractional_part);
        let denominator = 10_i128.checked_pow(fractional_part.len() as u32)?;
        (digits, denominator)
    } else {
        (unsigned.to_string(), 1)
    };

    let mut numerator = digits.parse::<i128>().ok()?;
    if is_negative {
        numerator = numerator.checked_neg()?;
    }
    normalize_rational_pair(numerator, denominator)
}

fn rational_pair_from_obj(obj: &Obj) -> Option<(i128, i128)> {
    if let Some(number) = obj.evaluate_to_normalized_decimal_number() {
        return rational_pair_from_number(&number);
    }

    match obj {
        Obj::Number(number) => rational_pair_from_number(number),
        Obj::Add(add) => {
            let (ln, ld) = rational_pair_from_obj(add.left.as_ref())?;
            let (rn, rd) = rational_pair_from_obj(add.right.as_ref())?;
            let left_scaled = ln.checked_mul(rd)?;
            let right_scaled = rn.checked_mul(ld)?;
            normalize_rational_pair(left_scaled.checked_add(right_scaled)?, ld.checked_mul(rd)?)
        }
        Obj::Sub(sub) => {
            let (ln, ld) = rational_pair_from_obj(sub.left.as_ref())?;
            let (rn, rd) = rational_pair_from_obj(sub.right.as_ref())?;
            let left_scaled = ln.checked_mul(rd)?;
            let right_scaled = rn.checked_mul(ld)?;
            normalize_rational_pair(left_scaled.checked_sub(right_scaled)?, ld.checked_mul(rd)?)
        }
        Obj::Mul(mul) => {
            let (ln, ld) = rational_pair_from_obj(mul.left.as_ref())?;
            let (rn, rd) = rational_pair_from_obj(mul.right.as_ref())?;
            normalize_rational_pair(ln.checked_mul(rn)?, ld.checked_mul(rd)?)
        }
        Obj::Div(div) => {
            let (ln, ld) = rational_pair_from_obj(div.left.as_ref())?;
            let (rn, rd) = rational_pair_from_obj(div.right.as_ref())?;
            normalize_rational_pair(ln.checked_mul(rd)?, ld.checked_mul(rn)?)
        }
        _ => None,
    }
}

fn nonnegative_integer_value(obj: &Obj) -> Option<usize> {
    let Obj::Number(number) = obj else {
        return None;
    };
    if number.normalized_value.starts_with('-') {
        return None;
    }
    if !is_number_string_literally_integer_without_dot(number.normalized_value.clone()) {
        return None;
    }
    number.normalized_value.parse::<usize>().ok()
}

fn try_remove_even_power_negative_sign(base: &Obj, exponent: &Obj) -> Option<Obj> {
    let exponent_value = nonnegative_integer_value(exponent)?;
    if exponent_value % 2 != 0 {
        return None;
    }

    let mut factors = Vec::new();
    collect_mul_factors(base, &mut factors);
    let mut sign_removed = false;
    let mut signless_factors = Vec::with_capacity(factors.len());
    for factor in factors {
        if !sign_removed {
            if let Obj::Number(number) = &factor {
                if let Some(positive_value) = number.normalized_value.strip_prefix('-') {
                    sign_removed = true;
                    if positive_value != "1" {
                        signless_factors.push(Number::new(positive_value.to_string()).into());
                    }
                    continue;
                }
            }
        }
        signless_factors.push(factor);
    }

    if !sign_removed {
        return None;
    }
    Some(obj_from_mul_factors(signless_factors))
}

fn collect_mul_factors(obj: &Obj, factors: &mut Vec<Obj>) {
    if let Obj::Mul(mul) = obj {
        collect_mul_factors(mul.left.as_ref(), factors);
        collect_mul_factors(mul.right.as_ref(), factors);
    } else {
        factors.push(obj.clone());
    }
}

fn obj_from_mul_factors(factors: Vec<Obj>) -> Obj {
    let mut iter = factors.into_iter();
    let Some(first) = iter.next() else {
        return Number::new("1".to_string()).into();
    };
    let mut result = first;
    for factor in iter {
        result = Mul::new(result, factor).into();
    }
    result
}
