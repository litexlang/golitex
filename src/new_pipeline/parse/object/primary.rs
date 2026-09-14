use crate::new_pipeline::ast::obj::{
    Abs, AtomObj, Cart, Ceil, Cos, Exp, Floor, FnObjHead, Gcd, Identifier, IdentifierWithMod,
    Intersect, Lcm, ListSet, Ln, Max, Min, Number, Obj, Quot, SetMinus, Sin, Sqrt, StandardSet,
    Tan, Tuple, Union,
};
use crate::new_pipeline::parse::keywords::{
    ABS, C, CART, CEIL, COLON, COMMA, COS, C_STAR, DOT, EXP, FLOOR, FN, GCD, INTERSECT, LCM,
    LEFT_BRACKET, LEFT_CURLY, LEFT_PAREN, LN, MATRIX, MAX, MIN, MOD_SIGN, N, N_POS, Q, Q_NEG, Q_POS,
    Q_STAR, QUOT, R, RIGHT_BRACKET, RIGHT_CURLY, RIGHT_PAREN, R_NEG, R_POS, R_STAR, SET_MINUS, SIN,
    SQRT, STRUCT_VIEW_PREFIX, TAN, TUPLE, UNION, Z, Z_NEG, Z_POS, Z_STAR,
};
use crate::new_pipeline::runtime::{OccupiedName, Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

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
            "matrix / finite_seq list literal `[...]` is not wired in phase 1 object parse",
        ));
    }
    if token == FN {
        return Err(tb.parse_error("`fn` object forms are not wired in phase 1 object parse"));
    }
    if token == STRUCT_VIEW_PREFIX {
        return Err(tb.parse_error("struct view `&` is not wired in phase 1 object parse"));
    }
    if token == MATRIX {
        return Err(tb.parse_error("`matrix(...)` is not wired in phase 1 object parse"));
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
    match obj {
        Obj::Atom(AtomObj::Identifier(id)) => Some(FnObjHead::Identifier(id)),
        Obj::Atom(AtomObj::IdentifierWithMod(m)) => Some(FnObjHead::IdentifierWithMod(m)),
        Obj::ObjAtIndex(v) => Some(FnObjHead::ObjAtIndex(v)),
        Obj::ObjAsStructInstanceWithFieldAccess(v) => {
            Some(FnObjHead::ObjAsStructInstanceWithFieldAccess(v))
        }
        _ => None,
    }
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

fn parse_paren_or_tuple(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    tb.expect(LEFT_PAREN)?;
    if tb.peek() == Some(RIGHT_PAREN) {
        tb.advance()?;
        return Ok(Obj::Tuple(Tuple { args: vec![] }));
    }
    let first = parse_obj(rt, tb)?;
    if tb.peek() == Some(COMMA) {
        let mut args = vec![Box::new(first)];
        while tb.peek() == Some(COMMA) {
            tb.advance()?;
            args.push(Box::new(parse_obj(rt, tb)?));
        }
        tb.expect(RIGHT_PAREN)?;
        return Ok(Obj::Tuple(Tuple { args }));
    }
    tb.expect(RIGHT_PAREN)?;
    Ok(first)
}

fn parse_list_set(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    tb.expect(LEFT_CURLY)?;
    if tb.peek() == Some(RIGHT_CURLY) {
        tb.advance()?;
        return Ok(Obj::ListSet(ListSet { list: vec![] }));
    }
    if braced_content_has_top_level_colon(tb) {
        return Err(tb.parse_error("set-builder not wired"));
    }
    let mut list = vec![Box::new(parse_obj(rt, tb)?)];
    while tb.peek() == Some(COMMA) {
        tb.advance()?;
        list.push(Box::new(parse_obj(rt, tb)?));
    }
    tb.expect(RIGHT_CURLY)?;
    Ok(Obj::ListSet(ListSet { list }))
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

fn try_parse_keyword_primary(rt: &mut Runtime, tb: &mut TokenBlock, token: &str) -> RuntimeResult<Option<Obj>> {
    match token {
        ABS => Ok(Some(parse_unary_keyword(rt, tb, ABS, |arg| {
            Obj::Abs(Abs { arg: Box::new(arg) })
        })?)),
        SIN => Ok(Some(parse_unary_keyword(rt, tb, SIN, |arg| {
            Obj::Sin(Sin { arg: Box::new(arg) })
        })?)),
        COS => Ok(Some(parse_unary_keyword(rt, tb, COS, |arg| {
            Obj::Cos(Cos { arg: Box::new(arg) })
        })?)),
        TAN => Ok(Some(parse_unary_keyword(rt, tb, TAN, |arg| {
            Obj::Tan(Tan { arg: Box::new(arg) })
        })?)),
        SQRT => Ok(Some(parse_unary_keyword(rt, tb, SQRT, |arg| {
            Obj::Sqrt(Sqrt { arg: Box::new(arg) })
        })?)),
        FLOOR => Ok(Some(parse_unary_keyword(rt, tb, FLOOR, |arg| {
            Obj::Floor(Floor { arg: Box::new(arg) })
        })?)),
        CEIL => Ok(Some(parse_unary_keyword(rt, tb, CEIL, |arg| {
            Obj::Ceil(Ceil { arg: Box::new(arg) })
        })?)),
        EXP => Ok(Some(parse_unary_keyword(rt, tb, EXP, |arg| {
            Obj::Exp(Exp { arg: Box::new(arg) })
        })?)),
        LN => Ok(Some(parse_unary_keyword(rt, tb, LN, |arg| {
            Obj::Ln(Ln { arg: Box::new(arg) })
        })?)),
        UNION => Ok(Some(parse_binary_keyword(rt, tb, UNION, |left, right| {
            Obj::Union(Union {
                left: Box::new(left),
                right: Box::new(right),
            })
        })?)),
        INTERSECT => Ok(Some(parse_binary_keyword(rt, tb, INTERSECT, |left, right| {
            Obj::Intersect(Intersect {
                left: Box::new(left),
                right: Box::new(right),
            })
        })?)),
        SET_MINUS => Ok(Some(parse_binary_keyword(rt, tb, SET_MINUS, |left, right| {
            Obj::SetMinus(SetMinus {
                left: Box::new(left),
                right: Box::new(right),
            })
        })?)),
        MIN => Ok(Some(parse_binary_keyword(rt, tb, MIN, |left, right| {
            Obj::Min(Min {
                left: Box::new(left),
                right: Box::new(right),
            })
        })?)),
        MAX => Ok(Some(parse_binary_keyword(rt, tb, MAX, |left, right| {
            Obj::Max(Max {
                left: Box::new(left),
                right: Box::new(right),
            })
        })?)),
        GCD => Ok(Some(parse_binary_keyword(rt, tb, GCD, |left, right| {
            Obj::Gcd(Gcd {
                left: Box::new(left),
                right: Box::new(right),
            })
        })?)),
        LCM => Ok(Some(parse_binary_keyword(rt, tb, LCM, |left, right| {
            Obj::Lcm(Lcm {
                left: Box::new(left),
                right: Box::new(right),
            })
        })?)),
        QUOT => Ok(Some(parse_binary_keyword(rt, tb, QUOT, |left, right| {
            Obj::Quot(Quot {
                left: Box::new(left),
                right: Box::new(right),
            })
        })?)),
        CART => {
            tb.advance()?;
            let args = parse_obj_list_paren(rt, tb)?;
            if args.len() < 2 {
                return Err(tb.parse_error("cart expects at least 2 arguments"));
            }
            Ok(Some(Obj::Cart(Cart {
                args: args.into_iter().map(Box::new).collect(),
            })))
        }
        TUPLE => {
            tb.advance()?;
            let args = parse_obj_list_paren(rt, tb)?;
            Ok(Some(Obj::Tuple(Tuple {
                args: args.into_iter().map(Box::new).collect(),
            })))
        }
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
    Ok(Obj::Number(Number {
        normalized_value: normalized,
    }))
}

fn parse_identifier_or_mod_or_standard_set(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let name = tb.advance()?;
    if tb.peek() == Some(MOD_SIGN) {
        let mut parts = vec![name];
        while tb.peek() == Some(MOD_SIGN) {
            tb.advance()?;
            let next = tb.advance()?;
            if !is_simple_name(&next) {
                return Err(tb.parse_error(format!(
                    "expected identifier after `::`, got `{next}`"
                )));
            }
            parts.push(next);
        }
        let local = parts.pop().expect("qualified name has a local part");
        let mod_name = parts.join(MOD_SIGN);
        let key = OccupiedName::WithMod {
            mod_name: mod_name.clone(),
            name: local.clone(),
        };
        let identifier_id = match rt.lookup_identifier_id(&key) {
            Some(identifier_id) => identifier_id,
            None => rt.define_atom(key).map_err(|err| match err {
                crate::new_pipeline::runtime::RuntimeError::Invariant(message) => {
                    tb.parse_error(message)
                }
                other => other,
            })?,
        };
        return Ok(Obj::Atom(AtomObj::IdentifierWithMod(IdentifierWithMod {
            mod_name,
            name: local,
            identifier_id,
        })));
    }

    if let Some(set) = standard_set_from_name(&name) {
        return Ok(Obj::StandardSet(set));
    }

    if !is_atom_name(&name) {
        return Err(tb.parse_error(format!("expected name, got `{name}`")));
    }

    let Some(identifier_id) = rt.lookup_plain_identifier_id(&name) else {
        return Err(tb.parse_error(format!("undefined name `{name}`")));
    };
    Ok(Obj::Atom(AtomObj::Identifier(Identifier { name, identifier_id })))
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
