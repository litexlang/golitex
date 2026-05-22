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
    // `known_objs_equal_to_normalized_decimal_number` so e.g. `a - b` becomes `100` when that
    // binding exists, then outer `(... - 10)` can evaluate (used by equality `calculation`).
    fn resolve_obj_try_fold_arithmetic(&self, result: Obj) -> Obj {
        if let Some(calculated) = result.evaluate_to_normalized_decimal_number() {
            return calculated.into();
        }
        if let Some(n) = self.resolve_obj_to_number(&result) {
            return n.into();
        }
        result
    }

    pub fn resolve_obj(&self, obj: &Obj) -> Obj {
        if let Some(number) = self.resolve_obj_to_number(obj) {
            return number.into();
        }
        match obj {
            Obj::Number(number) => number.clone().into(),
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
            Obj::Pow(pow) => {
                let result: Obj =
                    Pow::new(self.resolve_obj(&pow.base), self.resolve_obj(&pow.exponent)).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Div(div) => {
                let result: Obj =
                    Div::new(self.resolve_obj(&div.left), self.resolve_obj(&div.right)).into();
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
            Obj::Max(m) => {
                let result: Obj =
                    Max::new(self.resolve_obj(&m.left), self.resolve_obj(&m.right)).into();
                self.resolve_obj_try_fold_arithmetic(result)
            }
            Obj::Min(m) => {
                let result: Obj =
                    Min::new(self.resolve_obj(&m.left), self.resolve_obj(&m.right)).into();
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
            Obj::FnObj(fn_obj) => {
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
            Obj::Atom(AtomObj::Identifier(_)) | Obj::Atom(AtomObj::IdentifierWithMod(_)) => {
                if let Some(number) = self.resolve_obj_to_number(obj) {
                    number.into()
                } else {
                    obj.clone()
                }
            }
            Obj::Count(count) => match &*count.set {
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
                        let count_obj = Obj::Count(Count::new(resolved_arg));
                        let n = match self.resolve_obj_to_number(&count_obj) {
                            Some(n) => n,
                            None => return obj.clone(),
                        };
                        acc = mul_signed_decimal_str(acc.trim(), n.normalized_value.trim());
                    }
                    Number::new(acc).into()
                }
                _ => obj.clone(),
            },
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
}
