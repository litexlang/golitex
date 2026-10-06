use crate::ast::names::AtomicName;
use crate::ast::obj::{
    Abs, AnonymousFn, Arccos, Arccot, Arcsin, Arctan, ArithmeticOperator, Cart, Ceil,
    ClosedRange, ComplexAbs, ComplexOperator, Cos, Cot, EulerNumber, Exp, ExpLogOperator,
    Factorial, FamilyIntersect, FamilyUnion, FiniteSeqSet, FiniteSetMax, FiniteSetMin,
    FiniteSetReduce, FiniteSetSize, FiniteSetStat, Floor, FnObjHead, FnRange, FnSet, FunctionSpace,
    Gcd, IdentifierObj, ImaginaryPart, ImaginaryUnit, IndexCart, IndexIntersect, IndexUnion,
    InstantiatedTemplateObj, IntegerOperator, Intersect, IntervalObj, IntervalObjStruct,
    IteratedOperator, Lcm, ListSet, Literal, Ln, Log, Max, Min, Number, Obj,
    OneSideInfinityIntervalObj, OneSideInfinityIntervalObjStruct, Pi, PowerSet, Product,
    ProductOfFiniteSet, ProductShape, Quot, Range, RealPart, Reduce, SeqSet, SetBuilder,
    SetFormer, SetMinus, SetOperator, Sign, Sin, Sqrt, StandardSet, StructAndFieldAccessObj,
    StructObj, Sum, SumOfFiniteSet, Tan, TrigOperator, Tuple, Union,
};
use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::parse::keywords::{
    ABS, ARCCOS, ARCCOT, ARCSIN, ARCTAN, C, CART, CART_DIM, CEIL, CLOSED_RANGE, COLON, COMMA, COS,
    COT, C_ABS, C_STAR, DOT, EXP, FACTORIAL, FAMILY_INTERSECT, FAMILY_UNION, FINITE_SEQ,
    FINITE_SET_MAX, FINITE_SET_MIN, FINITE_SET_PRODUCT, FINITE_SET_REDUCE, FINITE_SET_SIZE,
    FINITE_SET_SUM, FLOOR, FN, FN_RANGE, GCD, GREATER, IMG, INDEX_CART, INDEX_INTERSECT, INDEX_UNION,
    INTERSECT, INTERVAL_LITERAL_PREFIX, LCM, LEFT_BRACKET, LEFT_CURLY, LEFT_PAREN, LESS, LN, LOG,
    MAX, MIN, MOD_FLAT_SIGN, MOD_SIGN, N, N_POS, POWER_SET, PRODUCT, PROJ, Q, QUOT, Q_NEG, Q_POS,
    Q_STAR, R, RANGE, RE, REDUCE, RIGHT_BRACKET, RIGHT_CURLY, RIGHT_PAREN, R_NEG, R_POS, R_STAR,
    SEQ, SET_MINUS, SIGN, SIN, SQRT, STRUCT_VIEW_PREFIX, SUM, TAN, TEMPLATE_INSTANCE_PREFIX, TUPLE,
    TUPLE_DIM, UNION, Z, Z_NEG, Z_POS, Z_STAR,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

use super::expression::parse_obj;

/// Parse `(a, b, …)` into a vector of objects. Used by keyword primaries and `$prop(...)`.
#[allow(dead_code)]
pub fn parse_obj_list_paren(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Vec<Obj>> {
    tb.expect(LEFT_PAREN)?;
    if tb.peek() == Some(RIGHT_PAREN) {
        tb.advance()?;
        return Ok(vec![]);
    }
    let mut objs = vec![parse_obj(rt, tb)?];
    while tb.peek() == Some(COMMA) {
        tb.advance()?;
        objs.push(parse_obj(rt, tb)?);
    }
    tb.expect(RIGHT_PAREN)?;
    Ok(objs)
}

/// Alias for paren-list args (legacy `parse_braced_objs` meant `(...)`).
#[allow(dead_code)]
pub fn parse_braced_objs(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Vec<Obj>> {
    parse_obj_list_paren(rt, tb)
}

pub fn parse_primary(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let Some(token) = tb.peek().map(str::to_string) else {
        return Err(tb.parse_error("expected object"));
    };

    if token == LEFT_PAREN {
        return parse_paren_or_tuple(rt, tb);
    }
    if token == LEFT_CURLY {
        return parse_list_set(rt, tb);
    }
    if token == LEFT_BRACKET {
        return Err(tb.parse_error(
            "`[...]` finite-sequence list literals are not supported; use tuple literals and ordinary calls `t(i)`",
        ));
    }
    if token == FN {
        return rt.parse_fn_set_or_anonymous_fn(tb);
    }
    if token == STRUCT_VIEW_PREFIX {
        return parse_struct_view(rt, tb);
    }
    if token == TEMPLATE_INSTANCE_PREFIX {
        return parse_instantiated_template(rt, tb);
    }
    if token == INTERVAL_LITERAL_PREFIX {
        return parse_interval_literal(rt, tb);
    }

    if let Some(obj) = try_parse_keyword_primary(rt, tb, &token)? {
        return Ok(obj);
    }

    if starts_with_digit(&token) {
        return parse_number(tb);
    }

    if is_atom_name(&token) || is_simple_name(&token) {
        return parse_identifier_or_mod_or_standard_set(rt, tb);
    }

    Err(tb.parse_error(format!("expected object, got `{token}`")))
}

pub(super) fn fn_obj_head_from_obj(obj: Obj) -> Option<FnObjHead> {
    Some(FnObjHead::from_obj(obj))
}

pub fn is_simple_name(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

pub fn is_atom_name(s: &str) -> bool {
    if is_simple_name(s) {
        return true;
    }
    matches!(
        s,
        "N+" | "Z+" | "Q+" | "R+" | "Z-" | "Q-" | "R-" | "Z*" | "Q*" | "R*" | "C*"
    )
}

// `&Name` / `&Module::export::Name<...>` → StructObj.
// No `&Struct{obj}` / `&Name(...)` form.
fn parse_struct_view(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    tb.expect(STRUCT_VIEW_PREFIX)?;
    let name_tok = tb
        .peek()
        .ok_or_else(|| tb.parse_error("`&` expects a struct name"))?;
    if !is_simple_name(&name_tok) {
        return Err(tb.parse_error(format!("invalid struct name `{name_tok}` after `&`")));
    }
    // Reuse the canonical owner/export resolver already used by templates.
    let name = rt.parse_prop_name(tb).map_err(|err| match err {
        crate::runtime::RuntimeError::InternalBug(message) => tb.parse_error(message),
        other => other,
    })?;

    if tb.peek() == Some(LEFT_CURLY) {
        return Err(tb.parse_error(
            "explicit struct selection `&Struct{object}.field` has been removed; define the object or function return directly with `&Struct` and write `object.field`",
        ));
    }
    if tb.peek() == Some(LEFT_PAREN) {
        return Err(
            tb.parse_error("struct view parameters use `<...>` (e.g. `&Pair<R>`), not `(...)`")
        );
    }

    let params = if tb.peek() == Some(LESS) {
        parse_obj_list_angle(rt, tb)?
    } else {
        Vec::new()
    };

    Ok(Obj::StructAndFieldAccessObj(
        StructAndFieldAccessObj::StructObj(StructObj { name, params }),
    ))
}

// `\Name<args>` → InstantiatedTemplateObj. Angle args are required.
fn parse_instantiated_template(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    tb.expect(TEMPLATE_INSTANCE_PREFIX)?;
    let name_tok = tb
        .peek()
        .ok_or_else(|| tb.parse_error("`\\` expects a template name"))?;
    if !is_simple_name(name_tok) {
        return Err(tb.parse_error(format!("invalid template name `{name_tok}` after `\\`")));
    }
    // Templates already carry AtomicName. Resolve the same canonical export /
    // import forms as predicates, e.g. `\prefix::copied<R>`.
    let template_name = rt.parse_prop_name(tb).map_err(|err| match err {
        crate::runtime::RuntimeError::InternalBug(message) => tb.parse_error(message),
        other => other,
    })?;
    if tb.peek() != Some(LESS) {
        return Err(tb.parse_error("template instance expects `<...>` arguments (e.g. `\\T<a>`)"));
    }
    let args = parse_obj_list_angle(rt, tb)?;
    Ok(Obj::InstantiatedTemplateObj(InstantiatedTemplateObj {
        template_name,
        args,
    }))
}

fn parse_obj_list_angle(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Vec<Obj>> {
    tb.expect(LESS)?;
    if tb.peek() == Some(GREATER) {
        tb.advance()?;
        return Ok(vec![]);
    }
    let mut objs = vec![parse_obj(rt, tb)?];
    while tb.peek() == Some(COMMA) {
        tb.advance()?;
        objs.push(parse_obj(rt, tb)?);
    }
    tb.expect(GREATER)?;
    Ok(objs)
}

fn parse_paren_or_tuple(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    tb.expect(LEFT_PAREN)?;
    if tb.peek() == Some(RIGHT_PAREN) {
        tb.advance()?;
        return Ok(Obj::ProductShape(ProductShape::Tuple(Tuple {
            args: vec![],
        })));
    }
    let first = parse_obj(rt, tb)?;
    if tb.peek() == Some(COMMA) {
        let mut args = vec![Box::new(first)];
        while tb.peek() == Some(COMMA) {
            tb.advance()?;
            args.push(Box::new(parse_obj(rt, tb)?));
        }
        tb.expect(RIGHT_PAREN)?;
        return Ok(Obj::ProductShape(ProductShape::Tuple(Tuple { args })));
    }
    tb.expect(RIGHT_PAREN)?;
    Ok(first)
}

fn parse_list_set(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    tb.expect(LEFT_CURLY)?;
    if tb.peek() == Some(RIGHT_CURLY) {
        tb.advance()?;
        return Ok(Obj::SetFormer(SetFormer::ListSet(ListSet { list: vec![] })));
    }
    if braced_content_has_top_level_colon(tb) {
        return rt.parse_set_builder(tb);
    }
    let mut list = vec![Box::new(parse_obj(rt, tb)?)];
    while tb.peek() == Some(COMMA) {
        tb.advance()?;
        list.push(Box::new(parse_obj(rt, tb)?));
    }
    tb.expect(RIGHT_CURLY)?;
    Ok(Obj::SetFormer(SetFormer::ListSet(ListSet { list })))
}

impl Runtime {
    // `{` already consumed. Form: `{ x S : facts }`.
    fn parse_set_builder(&mut self, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
        self.push_parse_scope();
        let result = (|| {
            let name = tb.advance()?;
            if !is_atom_name(&name) && !is_simple_name(&name) {
                return Err(
                    tb.parse_error(format!("set-builder expects a binder name, got `{name}`"))
                );
            }
            let binding = self.define_plain_atom_as_parse(tb, name)?;
            let param_set = parse_obj(self, tb)?;
            tb.expect(COLON)?;
            let mut facts = Vec::new();
            loop {
                facts.push(self.parse_quantifier_free_fact_inline(tb)?);
                if tb.peek() == Some(RIGHT_CURLY) {
                    break;
                }
                tb.expect(COMMA)?;
            }
            tb.expect(RIGHT_CURLY)?;
            Ok(Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
                param_binding: binding,
                param_set: Box::new(param_set),
                facts,
            })))
        })();
        self.pop_parse_scope();
        result
    }

    fn parse_fn_set_or_anonymous_fn(&mut self, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
        tb.expect(FN)?;
        self.push_parse_scope();
        let result = (|| {
            let (params, dom_facts, ret_set) = self.parse_fn_set_signature(tb)?;
            let body = FnSet {
                set_bound_parameters: params,
                dom_facts,
                ret_set: Box::new(ret_set),
            };
            if tb.peek() == Some(LEFT_CURLY) {
                tb.advance()?;
                self.occupy_set_bound_parameters_as_parse(tb, &body.set_bound_parameters)?;
                let equal_to = parse_obj(self, tb)?;
                tb.expect(RIGHT_CURLY)?;
                Ok(Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                    AnonymousFn {
                        body,
                        equal_to: Box::new(equal_to),
                    },
                )))
            } else {
                Ok(Obj::FunctionSpace(FunctionSpace::FnSet(body)))
            }
        })();
        self.pop_parse_scope();
        result
    }

    // Function carriers are parsed before any of this signature's parameters
    // are visible. Only domain conditions and the later body use those binders.
    pub(in crate::parse) fn parse_fn_set_signature(
        &mut self,
        tb: &mut TokenBlock,
    ) -> RuntimeResult<(
        SetBoundParameterList,
        Vec<crate::ast::fact::QuantifierFreeFact>,
        Obj,
    )> {
        tb.expect(LEFT_PAREN)?;
        let mut unbound_groups = Vec::new();
        while !tb.exceed_end_of_head() && tb.peek() != Some(COLON) && tb.peek() != Some(RIGHT_PAREN)
        {
            let mut names = Vec::new();
            loop {
                let name = tb.advance()?;
                if !is_atom_name(&name) {
                    return Err(tb.parse_error(format!("invalid function parameter name `{name}`")));
                }
                names.push(name);
                if tb.peek() != Some(COMMA) {
                    break;
                }
                tb.advance()?;
            }
            if matches!(tb.peek(), Some(crate::parse::keywords::SET | crate::parse::keywords::NONEMPTY_SET | crate::parse::keywords::FINITE_SET)) {
                return Err(tb.parse_error(
                    "fn parameters must be set-bound objects (e.g. `x R`), not `set` / `nonempty_set` / `finite_set`",
                ));
            }
            let param_type = parse_obj(self, tb)?;
            unbound_groups.push((names, param_type));
            if tb.peek() == Some(COMMA) {
                tb.advance()?;
            }
        }
        if unbound_groups.is_empty() {
            return Err(tb.parse_error("fn expects at least one parameter"));
        }

        self.push_parse_scope();
        let header: RuntimeResult<_> = (|| {
            let mut groups = Vec::new();
            for (names, param_type) in unbound_groups {
                let mut params = Vec::new();
                for name in names {
                    params.push(self.define_plain_atom_as_parse(tb, name)?);
                }
                groups.push(SetBoundParameterGroup { params, param_type: Box::new(param_type) });
            }
            let mut dom_facts = Vec::new();
            if tb.peek() == Some(COLON) {
                tb.advance()?;
                loop {
                    dom_facts.push(self.parse_quantifier_free_fact_inline(tb)?);
                    if tb.peek() != Some(COMMA) {
                        break;
                    }
                    tb.advance()?;
                }
            }
            tb.expect(RIGHT_PAREN)?;
            Ok((SetBoundParameterList { groups }, dom_facts))
        })();
        self.pop_parse_scope();
        let (params, dom_facts) = header?;
        let ret_set = parse_obj(self, tb)?;
        Ok((params, dom_facts, ret_set))
    }
}

fn braced_content_has_top_level_colon(tb: &TokenBlock) -> bool {
    let mut depth: i32 = 0;
    for tok in tb.header.iter().skip(tb.parse_index) {
        let t = tok.as_str();
        if depth == 0 && t == RIGHT_CURLY {
            return false;
        }
        if depth == 0 && t == COLON {
            return true;
        }
        if t == LEFT_CURLY || t == LEFT_PAREN || t == LEFT_BRACKET {
            depth += 1;
        } else if t == RIGHT_CURLY || t == RIGHT_PAREN || t == RIGHT_BRACKET {
            depth -= 1;
        }
    }
    false
}

fn try_parse_keyword_primary(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    token: &str,
) -> RuntimeResult<Option<Obj>> {
    match token {
        ABS => Ok(Some(parse_unary_keyword(rt, tb, ABS, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: Box::new(arg) }))
        })?)),
        "i" => {
            tb.advance()?;
            Ok(Some(Obj::Literal(Literal::ImaginaryUnit(ImaginaryUnit))))
        }
        "e" => {
            tb.advance()?;
            Ok(Some(Obj::Literal(Literal::EulerNumber(EulerNumber))))
        }
        "pi" => {
            tb.advance()?;
            Ok(Some(Obj::Literal(Literal::Pi(Pi))))
        }
        SIN => Ok(Some(parse_unary_keyword(rt, tb, SIN, |arg| {
            Obj::TrigOperator(TrigOperator::Sin(Sin { arg: Box::new(arg) }))
        })?)),
        ARCSIN => Ok(Some(parse_unary_keyword(rt, tb, ARCSIN, |arg| {
            Obj::TrigOperator(TrigOperator::Arcsin(Arcsin { arg: Box::new(arg) }))
        })?)),
        ARCCOS => Ok(Some(parse_unary_keyword(rt, tb, ARCCOS, |arg| {
            Obj::TrigOperator(TrigOperator::Arccos(Arccos { arg: Box::new(arg) }))
        })?)),
        ARCTAN => Ok(Some(parse_unary_keyword(rt, tb, ARCTAN, |arg| {
            Obj::TrigOperator(TrigOperator::Arctan(Arctan { arg: Box::new(arg) }))
        })?)),
        ARCCOT => Ok(Some(parse_unary_keyword(rt, tb, ARCCOT, |arg| {
            Obj::TrigOperator(TrigOperator::Arccot(Arccot { arg: Box::new(arg) }))
        })?)),
        COS => Ok(Some(parse_unary_keyword(rt, tb, COS, |arg| {
            Obj::TrigOperator(TrigOperator::Cos(Cos { arg: Box::new(arg) }))
        })?)),
        TAN => Ok(Some(parse_unary_keyword(rt, tb, TAN, |arg| {
            Obj::TrigOperator(TrigOperator::Tan(Tan { arg: Box::new(arg) }))
        })?)),
        COT => Ok(Some(parse_unary_keyword(rt, tb, COT, |arg| {
            Obj::TrigOperator(TrigOperator::Cot(Cot { arg: Box::new(arg) }))
        })?)),
        SQRT => Ok(Some(parse_unary_keyword(rt, tb, SQRT, |arg| {
            Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg: Box::new(arg) }))
        })?)),
        FLOOR => Ok(Some(parse_unary_keyword(rt, tb, FLOOR, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor { arg: Box::new(arg) }))
        })?)),
        CEIL => Ok(Some(parse_unary_keyword(rt, tb, CEIL, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Ceil(Ceil { arg: Box::new(arg) }))
        })?)),
        SIGN => Ok(Some(parse_unary_keyword(rt, tb, SIGN, |arg| {
            Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign { arg: Box::new(arg) }))
        })?)),
        EXP => Ok(Some(parse_unary_keyword(rt, tb, EXP, |arg| {
            Obj::ExpLogOperator(ExpLogOperator::Exp(Exp { arg: Box::new(arg) }))
        })?)),
        LN => Ok(Some(parse_unary_keyword(rt, tb, LN, |arg| {
            Obj::ExpLogOperator(ExpLogOperator::Ln(Ln { arg: Box::new(arg) }))
        })?)),
        RE => Ok(Some(parse_unary_keyword(rt, tb, RE, |arg| {
            Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg: Box::new(arg) }))
        })?)),
        IMG => Ok(Some(parse_unary_keyword(rt, tb, IMG, |arg| {
            Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart { arg: Box::new(arg) }))
        })?)),
        C_ABS => Ok(Some(parse_unary_keyword(rt, tb, C_ABS, |arg| {
            Obj::ComplexOperator(ComplexOperator::ComplexAbs(ComplexAbs { arg: Box::new(arg) }))
        })?)),

        FACTORIAL => Ok(Some(parse_unary_keyword(rt, tb, FACTORIAL, |arg| {
            Obj::IntegerOperator(IntegerOperator::Factorial(Factorial {
                arg: Box::new(arg),
            }))
        })?)),
        LOG => Ok(Some(parse_binary_keyword(rt, tb, LOG, |base, arg| {
            Obj::ExpLogOperator(ExpLogOperator::Log(Log {
                base: Box::new(base),
                arg: Box::new(arg),
            }))
        })?)),
        UNION => Ok(Some(parse_binary_keyword(rt, tb, UNION, |left, right| {
            Obj::SetOperator(SetOperator::Union(Union {
                left: Box::new(left),
                right: Box::new(right),
            }))
        })?)),
        INTERSECT => Ok(Some(parse_binary_keyword(
            rt,
            tb,
            INTERSECT,
            |left, right| {
                Obj::SetOperator(SetOperator::Intersect(Intersect {
                    left: Box::new(left),
                    right: Box::new(right),
                }))
            },
        )?)),
        SET_MINUS => Ok(Some(parse_binary_keyword(
            rt,
            tb,
            SET_MINUS,
            |left, right| {
                Obj::SetOperator(SetOperator::SetMinus(SetMinus {
                    left: Box::new(left),
                    right: Box::new(right),
                }))
            },
        )?)),
        FAMILY_UNION => Ok(Some(parse_unary_keyword(rt, tb, FAMILY_UNION, |left| {
            Obj::SetOperator(SetOperator::FamilyUnion(FamilyUnion {
                left: Box::new(left),
            }))
        })?)),
        FAMILY_INTERSECT => Ok(Some(parse_unary_keyword(
            rt,
            tb,
            FAMILY_INTERSECT,
            |left| {
                Obj::SetOperator(SetOperator::FamilyIntersect(FamilyIntersect {
                    left: Box::new(left),
                }))
            },
        )?)),
        MIN => Ok(Some(parse_binary_keyword(rt, tb, MIN, |left, right| {
            Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
                left: Box::new(left),
                right: Box::new(right),
            }))
        })?)),
        MAX => Ok(Some(parse_binary_keyword(rt, tb, MAX, |left, right| {
            Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                left: Box::new(left),
                right: Box::new(right),
            }))
        })?)),
        GCD => Ok(Some(parse_binary_keyword(rt, tb, GCD, |left, right| {
            Obj::IntegerOperator(IntegerOperator::Gcd(Gcd {
                left: Box::new(left),
                right: Box::new(right),
            }))
        })?)),
        LCM => Ok(Some(parse_binary_keyword(rt, tb, LCM, |left, right| {
            Obj::IntegerOperator(IntegerOperator::Lcm(Lcm {
                left: Box::new(left),
                right: Box::new(right),
            }))
        })?)),
        QUOT => Ok(Some(parse_binary_keyword(rt, tb, QUOT, |left, right| {
            Obj::IntegerOperator(IntegerOperator::Quot(Quot {
                left: Box::new(left),
                right: Box::new(right),
            }))
        })?)),
        FINITE_SET_PRODUCT => Ok(Some(parse_binary_keyword(
            rt,
            tb,
            FINITE_SET_PRODUCT,
            |set, func| {
                Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(ProductOfFiniteSet {
                    set: Box::new(set),
                    func: Box::new(func),
                }))
            },
        )?)),
        FINITE_SET_SUM => Ok(Some(parse_binary_keyword(
            rt,
            tb,
            FINITE_SET_SUM,
            |set, func| {
                Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(SumOfFiniteSet {
                    set: Box::new(set),
                    func: Box::new(func),
                }))
            },
        )?)),
        SUM => Ok(Some(parse_ternary_keyword(rt, tb, SUM, |start, end, func| {
            Obj::IteratedOperator(IteratedOperator::Sum(Sum {
                start: Box::new(start),
                end: Box::new(end),
                func: Box::new(func),
            }))
        })?)),
        PRODUCT => Ok(Some(parse_ternary_keyword(
            rt,
            tb,
            PRODUCT,
            |start, end, func| {
                Obj::IteratedOperator(IteratedOperator::Product(Product {
                    start: Box::new(start),
                    end: Box::new(end),
                    func: Box::new(func),
                }))
            },
        )?)),
        FINITE_SET_REDUCE => Ok(Some(parse_quaternary_keyword(
            rt,
            tb,
            FINITE_SET_REDUCE,
            |set, func, op, seed| {
                Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(FiniteSetReduce {
                    set: Box::new(set),
                    func: Box::new(func),
                    op: Box::new(op),
                    seed: Box::new(seed),
                }))
            },
        )?)),
        REDUCE => Ok(Some(parse_quinary_keyword(
            rt,
            tb,
            REDUCE,
            |start, end, func, op, seed| {
                Obj::IteratedOperator(IteratedOperator::Reduce(Reduce {
                    start: Box::new(start),
                    end: Box::new(end),
                    func: Box::new(func),
                    op: Box::new(op),
                    seed: Box::new(seed),
                }))
            },
        )?)),
        CART => {
            tb.advance()?;
            let args = parse_obj_list_paren(rt, tb)?;
            Ok(Some(Obj::ProductShape(ProductShape::Cart(Cart {
                args: args.into_iter().map(Box::new).collect(),
            }))))
        }
        TUPLE => {
            tb.advance()?;
            let args = parse_obj_list_paren(rt, tb)?;
            Ok(Some(Obj::ProductShape(ProductShape::Tuple(Tuple {
                args: args.into_iter().map(Box::new).collect(),
            }))))
        }
        CART_DIM => Err(tb.parse_error("cart_dim is removed: a Cartesian set has no unique construction dimension")),
        TUPLE_DIM => Err(tb.parse_error("tuple_dim is removed: use exact finite_seq membership and complete-domain evidence")),
        PROJ => Err(tb.parse_error("proj is removed: Cartesian sets do not retain construction projections")),
        // Half-open integer interval [start, end).
        // Example: `range(1, 3)` is {1, 2}.
        RANGE => Ok(Some(parse_binary_keyword(rt, tb, RANGE, |start, end| {
            Obj::SetFormer(SetFormer::Range(Range {
                start: Box::new(start),
                end: Box::new(end),
            }))
        })?)),
        // Closed integer interval [start, end]. Same as `start...end`.
        // Example: `closed_range(1, 2)` is {1, 2}.
        CLOSED_RANGE => Ok(Some(parse_binary_keyword(
            rt,
            tb,
            CLOSED_RANGE,
            |start, end| {
                Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
                    start: Box::new(start),
                    end: Box::new(end),
                }))
            },
        )?)),
        POWER_SET => Ok(Some(parse_unary_keyword(rt, tb, POWER_SET, |set| {
            Obj::SetOperator(SetOperator::PowerSet(PowerSet { set: Box::new(set) }))
        })?)),
        FINITE_SET_SIZE => Ok(Some(parse_unary_keyword(rt, tb, FINITE_SET_SIZE, |set| {
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                set: Box::new(set),
            }))
        })?)),
        FINITE_SET_MAX => Ok(Some(parse_unary_keyword(rt, tb, FINITE_SET_MAX, |set| {
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(FiniteSetMax {
                set: Box::new(set),
            }))
        })?)),
        FINITE_SET_MIN => Ok(Some(parse_unary_keyword(rt, tb, FINITE_SET_MIN, |set| {
            Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(FiniteSetMin {
                set: Box::new(set),
            }))
        })?)),
        FN_RANGE => Ok(Some(parse_unary_keyword(rt, tb, FN_RANGE, |function| {
            Obj::FunctionSpace(FunctionSpace::FnRange(FnRange {
                function: Box::new(function),
            }))
        })?)),
        // Finite sequences of length n in S. Example: `finite_seq(R, 3)`.
        FINITE_SEQ => Ok(Some(parse_binary_keyword(rt, tb, FINITE_SEQ, |set, n| {
            Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                set: Box::new(set),
                n: Box::new(n),
            }))
        })?)),
        // Infinite sequences in S. Example: `seq(R)`.
        SEQ => Ok(Some(parse_unary_keyword(rt, tb, SEQ, |set| {
            Obj::SetFormer(SetFormer::SeqSet(SeqSet {
                set: Box::new(set),
            }))
        })?)),
        INDEX_UNION => Ok(Some(parse_ternary_keyword(
            rt,
            tb,
            INDEX_UNION,
            |index_set, ambient_set, family_fn| {
                Obj::SetOperator(SetOperator::IndexUnion(IndexUnion {
                    index_set: Box::new(index_set),
                    ambient_set: Box::new(ambient_set),
                    family_fn: Box::new(family_fn),
                }))
            },
        )?)),
        INDEX_INTERSECT => Ok(Some(parse_ternary_keyword(
            rt,
            tb,
            INDEX_INTERSECT,
            |index_set, ambient_set, family_fn| {
                Obj::SetOperator(SetOperator::IndexIntersect(IndexIntersect {
                    index_set: Box::new(index_set),
                    ambient_set: Box::new(ambient_set),
                    family_fn: Box::new(family_fn),
                }))
            },
        )?)),
        INDEX_CART => Ok(Some(parse_ternary_keyword(
            rt,
            tb,
            INDEX_CART,
            |index_set, family_set, family_fn| {
                Obj::SetOperator(SetOperator::IndexCart(IndexCart {
                    index_set: Box::new(index_set),
                    family_set: Box::new(family_set),
                    family_fn: Box::new(family_fn),
                }))
            },
        )?)),
        _ => Ok(None),
    }
}

fn parse_unary_keyword(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    name: &str,
    build: impl FnOnce(Obj) -> Obj,
) -> RuntimeResult<Obj> {
    tb.advance()?;
    let mut args = parse_obj_list_paren(rt, tb)?;
    if args.len() != 1 {
        return Err(tb.parse_error(format!("`{name}` expects 1 argument")));
    }
    Ok(build(args.remove(0)))
}

fn parse_binary_keyword(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    name: &str,
    build: impl FnOnce(Obj, Obj) -> Obj,
) -> RuntimeResult<Obj> {
    tb.advance()?;
    let mut args = parse_obj_list_paren(rt, tb)?;
    if args.len() != 2 {
        return Err(tb.parse_error(format!("`{name}` expects 2 arguments")));
    }
    let right = args.pop().expect("arity checked");
    let left = args.pop().expect("arity checked");
    Ok(build(left, right))
}

fn parse_ternary_keyword(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    name: &str,
    build: impl FnOnce(Obj, Obj, Obj) -> Obj,
) -> RuntimeResult<Obj> {
    tb.advance()?;
    let mut args = parse_obj_list_paren(rt, tb)?;
    if args.len() != 3 {
        return Err(tb.parse_error(format!("`{name}` expects 3 arguments")));
    }
    let third = args.pop().expect("arity checked");
    let second = args.pop().expect("arity checked");
    let first = args.pop().expect("arity checked");
    Ok(build(first, second, third))
}

fn parse_quaternary_keyword(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    name: &str,
    build: impl FnOnce(Obj, Obj, Obj, Obj) -> Obj,
) -> RuntimeResult<Obj> {
    tb.advance()?;
    let mut args = parse_obj_list_paren(rt, tb)?;
    if args.len() != 4 {
        return Err(tb.parse_error(format!("`{name}` expects 4 arguments")));
    }
    let fourth = args.pop().expect("arity checked");
    let third = args.pop().expect("arity checked");
    let second = args.pop().expect("arity checked");
    let first = args.pop().expect("arity checked");
    Ok(build(first, second, third, fourth))
}

fn parse_quinary_keyword(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    name: &str,
    build: impl FnOnce(Obj, Obj, Obj, Obj, Obj) -> Obj,
) -> RuntimeResult<Obj> {
    tb.advance()?;
    let mut args = parse_obj_list_paren(rt, tb)?;
    if args.len() != 5 {
        return Err(tb.parse_error(format!("`{name}` expects 5 arguments")));
    }
    let fifth = args.pop().expect("arity checked");
    let fourth = args.pop().expect("arity checked");
    let third = args.pop().expect("arity checked");
    let second = args.pop().expect("arity checked");
    let first = args.pop().expect("arity checked");
    Ok(build(first, second, third, fourth, fifth))
}

fn parse_number(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let number = tb.advance()?;
    let normalized = if tb.peek() == Some(DOT) {
        // `1 . 5` as decimal: only when the next token is a digit fraction.
        let frac = tb.peek_at(1).map(str::to_string);
        if let Some(frac) = frac {
            if frac.chars().all(|c| c.is_ascii_digit()) && !frac.is_empty() {
                tb.advance()?; // `.`
                let frac = tb.advance()?;
                format!("{number}.{frac}")
            } else {
                number
            }
        } else {
            number
        }
    } else {
        number
    };
    if !is_number_literal(&normalized) {
        return Err(tb.parse_error(format!("invalid number `{normalized}`")));
    }
    Ok(Obj::Literal(Literal::Number(Number::new(normalized))))
}

fn parse_identifier_or_mod_or_standard_set(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
) -> RuntimeResult<Obj> {
    let name = tb.advance()?;
    if tb.peek() == Some(MOD_FLAT_SIGN) {
        tb.advance()?;
        let next = tb.advance()?;
        if !is_simple_name(&next) {
            return Err(tb.parse_error(format!("expected identifier after `:::`, got `{next}`")));
        }
        let key = rt
            .elaborate_flat_import(&name, next)
            .map_err(|err| match err {
                crate::runtime::RuntimeError::InternalBug(message) => {
                    tb.parse_error(message)
                }
                other => other,
            })?;
        return Ok(Obj::Identifier(identifier_obj_from_qualified_atomic(
            tb, key,
        )?));
    }
    if tb.peek() == Some(MOD_SIGN) {
        let mut parts = vec![name];
        while tb.peek() == Some(MOD_SIGN) {
            tb.advance()?;
            let next = tb.advance()?;
            if !is_simple_name(&next) {
                return Err(tb.parse_error(format!("expected identifier after `::`, got `{next}`")));
            }
            parts.push(next);
        }
        if parts.len() != 2 && parts.len() != 3 {
            return Err(tb.parse_error("qualified name must be `a::b`, `a:::b`, or `a::b::c`"));
        }
        let key = rt.elaborate_name_parts(&parts).map_err(|err| match err {
            crate::runtime::RuntimeError::InternalBug(message) => {
                tb.parse_error(message)
            }
            other => other,
        })?;

        return Ok(Obj::Identifier(identifier_obj_from_qualified_atomic(
            tb, key,
        )?));
    }

    if let Some(set) = standard_set_from_name(&name) {
        return Ok(Obj::StandardSet(set));
    }

    if !is_atom_name(&name) {
        return Err(tb.parse_error(format!("expected name, got `{name}`")));
    }

    // File-root free refs become WithExportFileId / WithModAndExportFileId;
    // inner-scope binders stay Plain { id, name }.
    let identifier = rt
        .identifier_obj_for_plain_free_ref(name)
        .map_err(|err| match err {
            crate::runtime::RuntimeError::InternalBug(message) => {
                tb.parse_error(message)
            }
            other => other,
        })?;
    Ok(Obj::Identifier(identifier))
}

fn standard_set_from_name(name: &str) -> Option<StandardSet> {
    match name {
        N_POS | Z_POS => Some(StandardSet::NPos),
        N => Some(StandardSet::N),
        Q => Some(StandardSet::Q),
        Z => Some(StandardSet::Z),
        R => Some(StandardSet::R),
        C => Some(StandardSet::C),
        Q_POS => Some(StandardSet::QPos),
        R_POS => Some(StandardSet::RPos),
        Q_NEG => Some(StandardSet::QNeg),
        Z_NEG => Some(StandardSet::ZNeg),
        R_NEG => Some(StandardSet::RNeg),
        Q_STAR => Some(StandardSet::QStar),
        Z_STAR => Some(StandardSet::ZStar),
        R_STAR => Some(StandardSet::RStar),
        C_STAR => Some(StandardSet::CStar),
        _ => None,
    }
}

fn starts_with_digit(s: &str) -> bool {
    s.chars()
        .next()
        .map(|c| c.is_ascii_digit())
        .unwrap_or(false)
}

fn is_number_literal(s: &str) -> bool {
    if s.is_empty() || s == "." {
        return false;
    }
    let mut dot_count = 0;
    for c in s.chars() {
        if c == '.' {
            dot_count += 1;
            if dot_count > 1 {
                return false;
            }
        } else if !c.is_ascii_digit() {
            return false;
        }
    }
    true
}

fn identifier_obj_from_qualified_atomic(
    tb: &TokenBlock,
    key: AtomicName,
) -> RuntimeResult<IdentifierObj> {
    match key {
        AtomicName::WithExportFileId {
            export_file_id,
            name,
        } => Ok(IdentifierObj::with_export_file_id(export_file_id, name)),
        AtomicName::WithModAndExportFileId {
            global_mod_id,
            export_file_id,
            name,
        } => Ok(IdentifierObj::with_mod_and_export_file_id(
            global_mod_id,
            export_file_id,
            name,
        )),
        AtomicName::Plain { name } => Err(tb.parse_error(format!(
            "internal: expected qualified atom, got plain `{name}`"
        ))),
    }
}

// Parse `'[a,b]`, `'(a,b)`, `'[a,)`, `'(,b]` and the other endpoint/openness shapes.
// Example: `'[0, 1)` → LeftClosedRightOpen with start=0, end=1.
fn parse_interval_literal(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    tb.expect(INTERVAL_LITERAL_PREFIX)?;
    let left_closed = match tb.current()? {
        LEFT_PAREN => false,
        LEFT_BRACKET => true,
        _ => {
            return Err(tb.parse_error(
                "interval literal after `'` expects `(` or `[`",
            ));
        }
    };
    tb.advance()?;

    // `'(,a)` / `'(,a]`: left-unbounded ray (must open with `(`).
    if tb.peek() == Some(COMMA) {
        if left_closed {
            return Err(tb.parse_error(
                "left-unbounded interval must start with `(`; use `'(,a)` or `'(,a]`",
            ));
        }
        tb.expect(COMMA)?;
        if tb.peek() == Some(RIGHT_PAREN) {
            return Err(tb.parse_error(
                "interval literal cannot omit both endpoints; use `R`",
            ));
        }
        let right = parse_obj(rt, tb)?;
        if tb.peek() == Some(COMMA) {
            return Err(tb.parse_error(
                "interval literal expects exactly two endpoints",
            ));
        }
        let right_closed = match tb.current()? {
            RIGHT_PAREN => false,
            RIGHT_BRACKET => true,
            _ => {
                return Err(tb.parse_error(
                    "interval literal expects `)` or `]` after its right endpoint",
                ));
            }
        };
        tb.advance()?;
        let body = OneSideInfinityIntervalObjStruct {
            start: Box::new(right),
        };
        let interval = if right_closed {
            OneSideInfinityIntervalObj::UpperClosed(body)
        } else {
            OneSideInfinityIntervalObj::UpperOpen(body)
        };
        return Ok(Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(
            interval,
        )));
    }

    let left = parse_obj(rt, tb)?;
    tb.expect(COMMA)?;

    // `'(a,)` / `'[a,)`: right-unbounded ray (must end with `)`).
    if tb.peek() == Some(RIGHT_PAREN) {
        tb.advance()?;
        let body = OneSideInfinityIntervalObjStruct {
            start: Box::new(left),
        };
        let interval = if left_closed {
            OneSideInfinityIntervalObj::LowerClosed(body)
        } else {
            OneSideInfinityIntervalObj::LowerOpen(body)
        };
        return Ok(Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(
            interval,
        )));
    }
    if tb.peek() == Some(RIGHT_BRACKET) {
        return Err(tb.parse_error(
            "right-unbounded interval must end with `)`; use `'(a,)` or `'[a,)`",
        ));
    }

    let right = parse_obj(rt, tb)?;
    if tb.peek() == Some(COMMA) {
        return Err(tb.parse_error(
            "interval literal expects exactly two endpoints",
        ));
    }
    let right_closed = match tb.current()? {
        RIGHT_PAREN => false,
        RIGHT_BRACKET => true,
        _ => {
            return Err(tb.parse_error(
                "interval literal expects `)` or `]` after its right endpoint",
            ));
        }
    };
    tb.advance()?;

    let body = IntervalObjStruct {
        start: Box::new(left),
        end: Box::new(right),
    };
    let interval = match (left_closed, right_closed) {
        (false, false) => IntervalObj::LeftOpenRightOpen(body),
        (false, true) => IntervalObj::LeftOpenRightClosed(body),
        (true, false) => IntervalObj::LeftClosedRightOpen(body),
        (true, true) => IntervalObj::LeftClosedRightClosed(body),
    };
    Ok(Obj::SetFormer(SetFormer::IntervalObj(interval)))
}
