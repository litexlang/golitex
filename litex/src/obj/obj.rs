use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StandardSet {
    NPos,
    N,
    Q,
    Z,
    R,
    QPos,
    RPos,
    QNeg,
    ZNeg,
    RNeg,
    QNz,
    ZNz,
    RNz,
}

#[derive(Clone)]
pub enum Obj {
    Identifier(Identifier),
    IdentifierWithMod(IdentifierWithMod),
    FieldAccess(FieldAccess),
    FieldAccessWithMod(FieldAccessWithMod),
    FnObj(FnObj),
    Number(Number),
    Add(Add),
    Sub(Sub),
    Mul(Mul),
    Div(Div),
    Mod(Mod),
    Pow(Pow),
    Union(Union),
    Intersect(Intersect),
    SetMinus(SetMinus),
    SetDiff(SetDiff),
    Cup(Cup),
    Cap(Cap),
    ListSet(ListSet),
    SetBuilder(SetBuilder),
    FnSetWithoutParams(FnSetWithoutParams),
    FnSetWithParams(FnSetWithParams),
    InstSetStructObj(InstStructObj),
    Cart(Cart),
    CartDim(CartDim),
    Proj(Proj),
    TupleDim(TupleDim),
    Tuple(Tuple),
    Count(Count),
    Range(Range),
    ClosedRange(ClosedRange),
    Val(Val),
    PowerSet(PowerSet),
    Choose(Choose),
    ObjAtIndex(ObjAtIndex),
    StandardSet {
        standard_set: StandardSet,
    },
}

#[derive(Clone)]
pub enum FnSetObj {
    FnSetWithoutParams(FnSetWithoutParams),
    FnSetWithDom(FnSetWithParams),
}

#[derive(Clone)]
pub struct ObjAtIndex {
    pub obj: Box<Obj>,
    pub index: Box<Obj>,
}

#[derive(Clone)]
pub struct Choose {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct PowerSet {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct Val {
    pub value: Box<Obj>,
}

#[derive(Clone)]
pub struct Range {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

#[derive(Clone)]
pub struct ClosedRange {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
}

#[derive(Clone)]
pub struct Count {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct Tuple {
    pub args: Vec<Box<Obj>>,
}

#[derive(Clone)]
pub struct TupleDim {
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct CartDim {
    pub set: Box<Obj>,
}

#[derive(Clone)]
pub struct Proj {
    pub set: Box<Obj>,
    pub dim: Box<Obj>,
}

#[derive(Clone)]
pub struct FnObj {
    pub head: Box<Atom>,
    pub body: Vec<Vec<Box<Obj>>>,
}

#[derive(Clone)]
pub struct Number {
    pub normalized_value: String,
}

#[derive(Clone)]
pub struct Add {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Sub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Mul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Div {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Mod {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Pow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

#[derive(Clone)]
pub struct Union {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Intersect {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct SetMinus {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct SetDiff {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Cup {
    pub left: Box<Obj>,
}

#[derive(Clone)]
pub struct Cap {
    pub left: Box<Obj>,
}

#[derive(Clone)]
pub struct ListSet {
    pub list: Vec<Box<Obj>>,
}

#[derive(Clone)]
pub struct SetBuilder {
    pub param: String,
    pub param_set: Box<Obj>,
    pub facts: Vec<OrAndChainAtomicFact>,
}

#[derive(Clone)]
pub struct FnSetWithoutParams {
    pub param_sets: Vec<Box<Obj>>,
    pub ret_set: Box<Obj>,
}

impl FnSetWithParams {
    pub fn params(&self) -> Vec<String> {
        let mut ret = Vec::with_capacity(ParamDefWithParamSet::number_of_params(
            &self.params_def_with_set,
        ));
        for param_def_with_set in &self.params_def_with_set {
            ret.extend(param_def_with_set.0.iter().cloned());
        }
        ret
    }
}

#[derive(Clone)]
pub struct FnSetWithParams {
    pub params_def_with_set: Vec<ParamDefWithParamSet>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub ret_set: Box<Obj>,
}

#[derive(Clone)]
pub struct InstStructObj {
    pub struct_name: IdentifierOrIdentifierWithMod,
    pub args: Vec<Box<Obj>>,
}

#[derive(Clone)]
pub struct Cart {
    pub args: Vec<Box<Obj>>,
}

impl ObjAtIndex {
    pub fn new(obj: Obj, index: Obj) -> Self {
        ObjAtIndex {
            obj: Box::new(obj),
            index: Box::new(index),
        }
    }
}

impl FnObj {
    pub fn new(head: Atom, body: Vec<Vec<Box<Obj>>>) -> Self {
        FnObj {
            head: Box::new(head),
            body,
        }
    }
}

impl Number {
    pub fn new(value: String) -> Self {
        Number {
            normalized_value: normalize_decimal_number_string(&value),
        }
    }
}

impl Add {
    pub fn new(left: Obj, right: Obj) -> Self {
        Add {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Sub {
    pub fn new(left: Obj, right: Obj) -> Self {
        Sub {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Mul {
    pub fn new(left: Obj, right: Obj) -> Self {
        Mul {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Div {
    pub fn new(left: Obj, right: Obj) -> Self {
        Div {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Mod {
    pub fn new(left: Obj, right: Obj) -> Self {
        Mod {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Pow {
    pub fn new(base: Obj, exponent: Obj) -> Self {
        Pow {
            base: Box::new(base),
            exponent: Box::new(exponent),
        }
    }
}

impl Union {
    pub fn new(left: Obj, right: Obj) -> Self {
        Union {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Intersect {
    pub fn new(left: Obj, right: Obj) -> Self {
        Intersect {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl SetMinus {
    pub fn new(left: Obj, right: Obj) -> Self {
        SetMinus {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl SetDiff {
    pub fn new(left: Obj, right: Obj) -> Self {
        SetDiff {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Cup {
    pub fn new(left: Obj) -> Self {
        Cup {
            left: Box::new(left),
        }
    }
}

impl Cap {
    pub fn new(left: Obj) -> Self {
        Cap {
            left: Box::new(left),
        }
    }
}

impl ListSet {
    pub fn new(list: Vec<Obj>) -> Self {
        ListSet {
            list: list.into_iter().map(Box::new).collect(),
        }
    }
}

impl SetBuilder {
    pub fn new(param: String, param_set: Obj, facts: Vec<OrAndChainAtomicFact>) -> Self {
        SetBuilder {
            param: param,
            param_set: Box::new(param_set),
            facts,
        }
    }
}

impl FnSetWithoutParams {
    pub fn new(param_sets: Vec<Obj>, ret_set: Obj) -> Self {
        FnSetWithoutParams {
            param_sets: param_sets.into_iter().map(Box::new).collect(),
            ret_set: Box::new(ret_set),
        }
    }
}

impl FnSetWithParams {
    pub fn new(
        params_and_their_sets: Vec<ParamDefWithParamSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Self {
        FnSetWithParams {
            params_def_with_set: params_and_their_sets,
            dom_facts,
            ret_set: Box::new(ret_set),
        }
    }
}

impl InstStructObj {
    pub fn new(struct_name: IdentifierOrIdentifierWithMod, param_sets: Vec<Obj>) -> Self {
        InstStructObj {
            struct_name,
            args: param_sets.into_iter().map(Box::new).collect(),
        }
    }
}

impl PowerSet {
    pub fn new(set: Obj) -> Self {
        PowerSet { set: Box::new(set) }
    }
}

impl Choose {
    pub fn new(set: Obj) -> Self {
        Choose { set: Box::new(set) }
    }
}

impl CartDim {
    pub fn new(set: Obj) -> Self {
        CartDim { set: Box::new(set) }
    }
}

impl Proj {
    pub fn new(set: Obj, dim: Obj) -> Self {
        Proj {
            set: Box::new(set),
            dim: Box::new(dim),
        }
    }
}

impl TupleDim {
    pub fn new(dim: Obj) -> Self {
        TupleDim { arg: Box::new(dim) }
    }
}

impl Cart {
    pub fn new(args: Vec<Obj>) -> Self {
        Cart {
            args: args.into_iter().map(Box::new).collect(),
        }
    }
}

impl Tuple {
    pub fn new(elements: Vec<Obj>) -> Self {
        Tuple {
            args: elements.into_iter().map(Box::new).collect(),
        }
    }
}

impl Count {
    pub fn new(set: Obj) -> Self {
        Count { set: Box::new(set) }
    }
}

impl Range {
    pub fn new(start: Obj, end: Obj) -> Self {
        Range {
            start: Box::new(start),
            end: Box::new(end),
        }
    }
}

impl ClosedRange {
    pub fn new(start: Obj, end: Obj) -> Self {
        ClosedRange {
            start: Box::new(start),
            end: Box::new(end),
        }
    }
}

impl Val {
    pub fn new(value: Obj) -> Self {
        Val {
            value: Box::new(value),
        }
    }
}

/// 算术运算符优先级：数值越小绑定越紧。^=1, * / %=2, + -=3；非算术=0 不参与括号。
fn precedence(o: &Obj) -> u8 {
    match o {
        Obj::Add(_) | Obj::Sub(_) => 3,
        Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) => 2,
        Obj::Pow(_) => 1,
        _ => 0,
    }
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_precedence(f, 0)
    }
}

impl Obj {
    /// 按优先级输出：当子表达式优先级低于父节点时自动加括号，例如 ^ 下出现 + 则写成 (a + b)。
    pub fn fmt_with_precedence(
        &self,
        f: &mut fmt::Formatter<'_>,
        parent_precedent: u8,
    ) -> fmt::Result {
        let precedent = precedence(self);
        let need_parens = parent_precedent != 0 && precedent != 0 && precedent > parent_precedent;
        if need_parens {
            write!(f, "{}", LEFT_BRACE)?;
        }
        match self {
            Obj::Add(a) => {
                a.left.fmt_with_precedence(f, 3)?;
                write!(f, " {} ", ADD)?;
                a.right.fmt_with_precedence(f, 3)?;
            }
            Obj::Sub(s) => {
                s.left.fmt_with_precedence(f, 3)?;
                write!(f, " {} ", SUB)?;
                s.right.fmt_with_precedence(f, 3)?;
            }
            Obj::Mul(m) => {
                m.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", MUL)?;
                m.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Div(d) => {
                d.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", DIV)?;
                d.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Mod(m) => {
                m.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", MOD)?;
                m.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Pow(p) => {
                p.base.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", POW)?;
                p.exponent.fmt_with_precedence(f, 1)?;
            }
            Obj::Union(x) => write!(f, "{}", x)?,
            Obj::Intersect(x) => write!(f, "{}", x)?,
            Obj::SetMinus(x) => write!(f, "{}", x)?,
            Obj::SetDiff(x) => write!(f, "{}", x)?,
            Obj::Cup(x) => write!(f, "{}", x)?,
            Obj::Cap(x) => write!(f, "{}", x)?,
            Obj::Identifier(x) => write!(f, "{}", x)?,
            Obj::IdentifierWithMod(x) => write!(f, "{}", x)?,
            Obj::FieldAccess(x) => write!(f, "{}", x)?,
            Obj::FieldAccessWithMod(x) => write!(f, "{}", x)?,
            Obj::FnObj(x) => write!(f, "{}", x)?,
            Obj::Number(x) => write!(f, "{}", x)?,
            Obj::ListSet(x) => write!(f, "{}", x)?,
            Obj::SetBuilder(x) => write!(f, "{}", x)?,
            Obj::FnSetWithoutParams(x) => write!(f, "{}", x)?,
            Obj::FnSetWithParams(x) => write!(f, "{}", x)?,
            Obj::StandardSet { standard_set } => write!(f, "{}", standard_set)?,
            Obj::InstSetStructObj(x) => write!(f, "{}", x)?,
            Obj::Cart(x) => write!(f, "{}", x)?,
            Obj::CartDim(x) => write!(f, "{}", x)?,
            Obj::Proj(x) => write!(f, "{}", x)?,
            Obj::TupleDim(x) => write!(f, "{}", x)?,
            Obj::Tuple(x) => write!(f, "{}", x)?,
            Obj::Count(x) => write!(f, "{}", x)?,
            Obj::Range(x) => write!(f, "{}", x)?,
            Obj::ClosedRange(x) => write!(f, "{}", x)?,
            Obj::Val(x) => write!(f, "{}", x)?,
            Obj::PowerSet(x) => write!(f, "{}", x)?,
            Obj::Choose(x) => write!(f, "{}", x)?,
            Obj::ObjAtIndex(x) => write!(f, "{}", x)?,
        }
        if need_parens {
            write!(f, "{}", RIGHT_BRACE)?;
        }
        Ok(())
    }
}

impl fmt::Display for ObjAtIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}{}",
            self.obj, LEFT_BRACKET, self.index, RIGHT_BRACKET
        )
    }
}

impl fmt::Display for Choose {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            CHOOSE,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            RANGE,
            braced_vec_to_string(&vec![self.start.as_ref(), self.end.as_ref()])
        )
    }
}

impl fmt::Display for ClosedRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            CLOSED_RANGE,
            braced_vec_to_string(&vec![self.start.as_ref(), self.end.as_ref()])
        )
    }
}

impl fmt::Display for Count {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            COUNT,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for CartDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            CART_DIM,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for Proj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            PROJ,
            braced_vec_to_string(&vec![self.set.as_ref(), self.dim.as_ref()])
        )
    }
}

impl fmt::Display for TupleDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            TUPLE_DIM,
            braced_vec_to_string(&vec![self.arg.as_ref()])
        )
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for FnObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", fn_obj_to_string(self.head.as_ref(), &self.body))
    }
}

pub fn fn_obj_to_string(head: &Atom, body: &Vec<Vec<Box<Obj>>>) -> String {
    let mut fn_obj_string = head.to_string();
    for group in body.iter() {
        fn_obj_string = format!("{}{}", fn_obj_string, braced_vec_to_string(group));
    }
    fn_obj_string
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.normalized_value)
    }
}

impl fmt::Display for Add {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, ADD, self.right)
    }
}

impl fmt::Display for Sub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, SUB, self.right)
    }
}

impl fmt::Display for Mul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, MUL, self.right)
    }
}

impl fmt::Display for Div {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, DIV, self.right)
    }
}

impl fmt::Display for Mod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, MOD, self.right)
    }
}

impl fmt::Display for Pow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.base, POW, self.exponent)
    }
}

impl fmt::Display for Union {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            UNION,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for Intersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            INTERSECT,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for SetMinus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            SET_MINUS,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for SetDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            SET_DIFF,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for Cup {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            CUP,
            braced_vec_to_string(&vec![self.left.as_ref()])
        )
    }
}

impl fmt::Display for Cap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            CAP,
            braced_vec_to_string(&vec![self.left.as_ref()])
        )
    }
}

impl fmt::Display for IdentifierWithMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.mod_name, MOD_SIGN, self.name)
    }
}

impl fmt::Display for ListSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", curly_braced_vec_to_string(&self.list))
    }
}

impl fmt::Display for SetBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{} {}{} {}{}",
            LEFT_CURLY_BRACE,
            self.param,
            self.param_set,
            COLON,
            vec_to_string_join_by_comma(&self.facts),
            RIGHT_CURLY_BRACE
        )
    }
}

impl fmt::Display for FnSetWithoutParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}",
            FN_FOR_FN_WITHOUT_PARAMS,
            braced_vec_to_string(&self.param_sets),
            self.ret_set
        )
    }
}

impl fmt::Display for FnSetWithParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}",
            FN_FOR_FN_WITH_PARAMS,
            brace_vec_colon_vec_to_string(&self.params_def_with_set, &self.dom_facts),
            self.ret_set
        )
    }
}

impl fmt::Display for StandardSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StandardSet::NPos => write!(f, "{}", N_POS),
            StandardSet::N => write!(f, "{}", N),
            StandardSet::Q => write!(f, "{}", Q),
            StandardSet::Z => write!(f, "{}", Z),
            StandardSet::R => write!(f, "{}", R),
            StandardSet::QPos => write!(f, "{}", Q_POS),
            StandardSet::RPos => write!(f, "{}", R_POS),
            StandardSet::QNeg => write!(f, "{}", Q_NEG),
            StandardSet::ZNeg => write!(f, "{}", Z_NEG),
            StandardSet::RNeg => write!(f, "{}", R_NEG),
            StandardSet::QNz => write!(f, "{}", Q_NZ),
            StandardSet::ZNz => write!(f, "{}", Z_NZ),
            StandardSet::RNz => write!(f, "{}", R_NZ),
        }
    }
}

impl fmt::Display for InstStructObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", INST_STRUCT_OBJ_SIGN)?;
        match &self.struct_name {
            IdentifierOrIdentifierWithMod::Identifier(identifier) => write!(f, "{}", identifier)?,
            IdentifierOrIdentifierWithMod::IdentifierWithMod(identifier_with_mod) => {
                write!(f, "{}", identifier_with_mod)?
            }
        };
        write!(f, "{}", braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for Cart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CART, braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            VAL,
            braced_vec_to_string(&vec![self.value.as_ref()])
        )
    }
}

impl fmt::Display for PowerSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            POWER_SET,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl From<Atom> for Obj {
    fn from(atom: Atom) -> Self {
        match atom {
            Atom::Identifier(a) => Obj::Identifier(a),
            Atom::IdentifierWithMod(a) => Obj::IdentifierWithMod(a),
            Atom::FieldAccess(a) => Obj::FieldAccess(a),
            Atom::FieldAccessWithMod(a) => Obj::FieldAccessWithMod(a),
        }
    }
}

impl Identifier {
    /// Build an Obj::Identifier from a name. Parameter is String (not &str).
    pub fn mk(name: String) -> Obj {
        Obj::Identifier(Identifier { name })
    }
}

impl fmt::Display for FnSetObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FnSetObj::FnSetWithoutParams(fn_set_without_dom) => write!(f, "{}", fn_set_without_dom),
            FnSetObj::FnSetWithDom(fn_set_with_dom) => write!(f, "{}", fn_set_with_dom),
        }
    }
}

impl Obj {
    pub fn instantiate(&self, param_to_arg_map: &HashMap<String, Obj>) -> Obj {
        match self {
            Obj::Identifier(inner) => inner.instantiate(param_to_arg_map),
            Obj::IdentifierWithMod(inner) => inner.instantiate(param_to_arg_map),
            Obj::FieldAccess(inner) => inner.instantiate(param_to_arg_map),
            Obj::FieldAccessWithMod(inner) => inner.instantiate(param_to_arg_map),
            Obj::FnObj(inner) => inner.instantiate(param_to_arg_map),
            Obj::Number(inner) => inner.instantiate(param_to_arg_map),
            Obj::Add(inner) => inner.instantiate(param_to_arg_map),
            Obj::Sub(inner) => inner.instantiate(param_to_arg_map),
            Obj::Mul(inner) => inner.instantiate(param_to_arg_map),
            Obj::Div(inner) => inner.instantiate(param_to_arg_map),
            Obj::Mod(inner) => inner.instantiate(param_to_arg_map),
            Obj::Pow(inner) => inner.instantiate(param_to_arg_map),
            Obj::Union(inner) => inner.instantiate(param_to_arg_map),
            Obj::Intersect(inner) => inner.instantiate(param_to_arg_map),
            Obj::SetMinus(inner) => inner.instantiate(param_to_arg_map),
            Obj::SetDiff(inner) => inner.instantiate(param_to_arg_map),
            Obj::Cup(inner) => inner.instantiate(param_to_arg_map),
            Obj::Cap(inner) => inner.instantiate(param_to_arg_map),
            Obj::ListSet(inner) => inner.instantiate(param_to_arg_map),
            Obj::SetBuilder(inner) => inner.instantiate(param_to_arg_map),
            Obj::FnSetWithoutParams(inner) => inner.instantiate(param_to_arg_map),
            Obj::FnSetWithParams(inner) => inner.instantiate(param_to_arg_map),
            Obj::StandardSet { standard_set } => Obj::StandardSet {
                standard_set: *standard_set,
            },
            Obj::InstSetStructObj(inner) => inner.instantiate(param_to_arg_map),
            Obj::Cart(inner) => inner.instantiate(param_to_arg_map),
            Obj::CartDim(inner) => inner.instantiate(param_to_arg_map),
            Obj::Proj(inner) => inner.instantiate(param_to_arg_map),
            Obj::TupleDim(inner) => inner.instantiate(param_to_arg_map),
            Obj::Tuple(inner) => inner.instantiate(param_to_arg_map),
            Obj::Count(inner) => inner.instantiate(param_to_arg_map),
            Obj::Range(inner) => inner.instantiate(param_to_arg_map),
            Obj::ClosedRange(inner) => inner.instantiate(param_to_arg_map),
            Obj::Val(inner) => inner.instantiate(param_to_arg_map),
            Obj::PowerSet(inner) => inner.instantiate(param_to_arg_map),
            Obj::Choose(inner) => inner.instantiate(param_to_arg_map),
            Obj::ObjAtIndex(inner) => inner.instantiate(param_to_arg_map),
        }
    }
}

impl FnSetObj {
    pub fn ret_set(&self) -> Box<Obj> {
        match self {
            FnSetObj::FnSetWithDom(e) => e.ret_set.clone(),
            FnSetObj::FnSetWithoutParams(e) => e.ret_set.clone(),
        }
    }
}
