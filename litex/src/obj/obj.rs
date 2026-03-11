use crate::stmt::parameter_type_and_property::ParamDefWithParamSet;
use crate::fact::OrAndChainAtomicFact;
use crate::common::keywords::{
    ADD, CAP, CART, CART_DIM, CHOOSE, CLOSED_RANGE, COLON, COUNT, CUP, SET_DIFF, DIV, FN, INST_STRUCT_OBJ_SIGN, INTERSECT, LEFT_BRACE, LEFT_BRACKET, LEFT_CURLY_BRACE, MOD, MOD_SING, MUL, N, N_POS, POW, POWER_SET, PROJ, Q, Q_NEG, Q_NZ, Q_POS, R, R_NEG, R_NZ, R_POS, RANGE, RIGHT_BRACE, RIGHT_BRACKET, RIGHT_CURLY_BRACE, SET_MINUS, SUB, UNION, VAL, Z, Z_NEG, Z_NZ, Z_POS
};
use std::fmt;
use crate::common::helper::{braced_vec_to_string, curly_braced_vec_to_string, vec_to_string_join_by_comma, brace_vec_colon_vec_to_string};
use super::atom::{Atom, Identifier, IdentifierWithMod, IdentifierOrIdentifierWithMod, FieldAccess, FieldAccessWithMod};

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
    FnSetWithoutDom(FnSetWithoutDom),
    FnSetWithDom(FnSetWithDom),
    NPosObj(NPosObj),
    NObj(NObj),
    QObj(QObj),
    ZObj(ZObj),
    RObj(RObj),
    InstSetStructObj(InstStructObj),
    Cart(Cart),
    CartDim(CartDim),
    Proj(Proj),
    Dim(Dim),
    Tuple(Tuple),
    Count(Count),
    Range(Range),
    ClosedRange(ClosedRange),
    Val(Val),
    PowerSet(PowerSet),
    Choose(Choose),
    ObjAtIndex(ObjAtIndex),
    QPos(QPos),
    ZPos(ZPos),
    RPos(RPos),
    QNeg(QNeg),
    ZNeg(ZNeg),
    RNeg(RNeg),
    QNz(QNz),
    ZNz(ZNz),
    RNz(RNz),
}

#[derive(Clone)]
pub enum FnSetObj {
    FnSetWithoutDom(FnSetWithoutDom),
    FnSetWithDom(FnSetWithDom),
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
    pub elements: Vec<Box<Obj>>,
}

#[derive(Clone)]
pub struct Dim {
    pub dim: Box<Obj>,
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
    pub head: Box<Obj>,
    pub body: Vec<Box<Obj>>,
}


#[derive(Clone)]
pub struct Number {
    pub value: String,
}


#[derive(Clone)]
pub struct Add {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub can_be_calculated: bool,
}

#[derive(Clone)]
pub struct Sub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub can_be_calculated: bool,
}

#[derive(Clone)]
pub struct Mul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub can_be_calculated: bool,
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
    pub can_be_calculated: bool,
}

#[derive(Clone)]
pub struct Pow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
    pub can_be_calculated: bool,
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
pub struct FnSetWithoutDom {
    pub param_sets: Vec<Box<Obj>>,
    pub ret_set: Box<Obj>,
}

impl FnSetWithDom {
    pub fn params(&self) -> Vec<String> {
        let mut ret = vec![];
        for param_def_with_set in &self.params_def_with_set {
            ret.extend(param_def_with_set.0.iter().cloned());
        }
        ret
    }
}

#[derive(Clone)]
pub struct FnSetWithDom {
    pub params_def_with_set: Vec<ParamDefWithParamSet>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub ret_set: Box<Obj>,
}

#[derive(Clone)]
pub struct NPosObj {
}

#[derive(Clone)]
pub struct NObj {
}

#[derive(Clone)]
pub struct QObj {
}

#[derive(Clone)]
pub struct ZObj {
}

#[derive(Clone)]
pub struct RObj {
}

#[derive(Clone)]
pub struct QPos {}

#[derive(Clone)]
pub struct ZPos {}

#[derive(Clone)]
pub struct RPos {}

#[derive(Clone)]
pub struct QNeg {}

#[derive(Clone)]
pub struct ZNeg {}

#[derive(Clone)]
pub struct RNeg {}

#[derive(Clone)]
pub struct QNz {}

#[derive(Clone)]
pub struct ZNz {}

#[derive(Clone)]
pub struct RNz {}

#[derive(Clone)]
pub struct InstStructObj {
    pub struct_name: IdentifierOrIdentifierWithMod,
    pub param_sets: Vec<Box<Obj>>,
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

impl FnObj 
{
    pub fn new(head: Obj, body: Vec<Obj>) -> Self {
        FnObj {
            head: Box::new(head),
            body: body.into_iter().map(Box::new).collect(),
        }
    }
}

impl Number {
    pub fn new(value: &str) -> Self {
        Number { value: value.to_string() }
    }
}

impl Add {
    pub fn new(left: Obj, right: Obj, is_arithmetic_expr: bool) -> Self {
        Add {
            left: Box::new(left),
            right: Box::new(right),
            can_be_calculated: is_arithmetic_expr,
        }
    }
}

impl Sub {
    pub fn new(left: Obj, right: Obj, is_arithmetic_expr: bool) -> Self {
        Sub {
            left: Box::new(left),
            right: Box::new(right),
            can_be_calculated: is_arithmetic_expr,
        }
    }
}

impl Mul {
    pub fn new(left: Obj, right: Obj, is_arithmetic_expr: bool) -> Self {
        Mul {
            left: Box::new(left),
            right: Box::new(right),
            can_be_calculated: is_arithmetic_expr,
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
    pub fn new(left: Obj, right: Obj, is_arithmetic_expr: bool) -> Self {
        Mod {
            left: Box::new(left),
            right: Box::new(right),
            can_be_calculated: is_arithmetic_expr,
        }
    }
}

impl Pow {
    pub fn new(base: Obj, exponent: Obj, is_arithmetic_expr: bool) -> Self {
        Pow {
            base: Box::new(base),
            exponent: Box::new(exponent),
            can_be_calculated: is_arithmetic_expr,
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
        Cup { left: Box::new(left) }
    }
}

impl Cap {
    pub fn new(left: Obj) -> Self {
        Cap { left: Box::new(left) }
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

impl FnSetWithoutDom {
    pub fn new(param_sets: Vec<Obj>, ret_set: Obj) -> Self {
        FnSetWithoutDom {
            param_sets: param_sets.into_iter().map(Box::new).collect(),
            ret_set: Box::new(ret_set),
        }
    }
}

impl FnSetWithDom {
    pub fn new(params_and_their_sets: Vec<ParamDefWithParamSet>, dom_facts: Vec<OrAndChainAtomicFact>, ret_set: Obj) -> Self {
        FnSetWithDom {
            params_def_with_set: params_and_their_sets,
            dom_facts,
            ret_set: Box::new(ret_set),
        }
    }
}

impl NPosObj {
    pub fn new() -> Self {
        NPosObj { }
    }
}

impl NObj {
    pub fn new() -> Self {
        NObj { }
    }
}

impl QObj {
    pub fn new() -> Self {
        QObj { }
    }
}

impl ZObj {
    pub fn new() -> Self {
        ZObj { }
    }
}

impl RObj {
    pub fn new() -> Self {
        RObj { }
    }
}

impl QPos {
    pub fn new() -> Self { QPos {} }
}

impl ZPos {
    pub fn new() -> Self { ZPos {} }
}

impl RPos {
    pub fn new() -> Self { RPos {} }
}

impl QNeg {
    pub fn new() -> Self { QNeg {} }
}

impl ZNeg {
    pub fn new() -> Self { ZNeg {} }
}

impl RNeg {
    pub fn new() -> Self { RNeg {} }
}

impl QNz {
    pub fn new() -> Self { QNz {} }
}

impl ZNz {
    pub fn new() -> Self { ZNz {} }
}

impl RNz {
    pub fn new() -> Self { RNz {} }
}

impl InstStructObj {
    pub fn new(struct_name: IdentifierOrIdentifierWithMod, param_sets: Vec<Obj>) -> Self {
        InstStructObj {
            struct_name,
            param_sets: param_sets.into_iter().map(Box::new).collect(),
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
        Choose {
            set: Box::new(set),
        }
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

impl Dim {
    pub fn new(dim: Obj) -> Self {
        Dim { dim: Box::new(dim) }
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
            elements: elements.into_iter().map(Box::new).collect(),
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
    pub fn fmt_with_precedence(&self, f: &mut fmt::Formatter<'_>, parent_precedent: u8) -> fmt::Result {
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
            Obj::FnSetWithoutDom(x) => write!(f, "{}", x)?,
            Obj::FnSetWithDom(x) => write!(f, "{}", x)?,
            Obj::NPosObj(x) => write!(f, "{}", x)?,
            Obj::NObj(x) => write!(f, "{}", x)?,
            Obj::QObj(x) => write!(f, "{}", x)?,
            Obj::ZObj(x) => write!(f, "{}", x)?,
            Obj::RObj(x) => write!(f, "{}", x)?,
            Obj::InstSetStructObj(x) => write!(f, "{}", x)?,
            Obj::Cart(x) => write!(f, "{}", x)?,
            Obj::CartDim(x) => write!(f, "{}", x)?,
            Obj::Proj(x) => write!(f, "{}", x)?,
            Obj::Dim(x) => write!(f, "{}", x)?,
            Obj::Tuple(x) => write!(f, "{}", x)?,
            Obj::Count(x) => write!(f, "{}", x)?,
            Obj::Range(x) => write!(f, "{}", x)?,
            Obj::ClosedRange(x) => write!(f, "{}", x)?,
            Obj::Val(x) => write!(f, "{}", x)?,
            Obj::PowerSet(x) => write!(f, "{}", x)?,
            Obj::Choose(x) => write!(f, "{}", x)?,
            Obj::ObjAtIndex(x) => write!(f, "{}", x)?,
            Obj::QPos(x) => write!(f, "{}", x)?,
            Obj::ZPos(x) => write!(f, "{}", x)?,
            Obj::RPos(x) => write!(f, "{}", x)?,
            Obj::QNeg(x) => write!(f, "{}", x)?,
            Obj::ZNeg(x) => write!(f, "{}", x)?,
            Obj::RNeg(x) => write!(f, "{}", x)?,
            Obj::QNz(x) => write!(f, "{}", x)?,
            Obj::ZNz(x) => write!(f, "{}", x)?,
            Obj::RNz(x) => write!(f, "{}", x)?,
        }
        if need_parens {
            write!(f, "{}", RIGHT_BRACE)?;
        }
        Ok(())
    }
}

impl fmt::Display for ObjAtIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}", self.obj, LEFT_BRACKET, self.index, RIGHT_BRACKET)
    }
}

impl fmt::Display for Choose {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CHOOSE, braced_vec_to_string(&vec![self.set.as_ref()]))
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", RANGE, braced_vec_to_string(&vec![self.start.as_ref(), self.end.as_ref()]))
    }
}

impl fmt::Display for ClosedRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CLOSED_RANGE, braced_vec_to_string(&vec![self.start.as_ref(), self.end.as_ref()]))
    }
}

impl fmt::Display for Count {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", COUNT, braced_vec_to_string(&vec![self.set.as_ref()]))
    }
}

impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", braced_vec_to_string(&self.elements))
    }
}

impl fmt::Display for CartDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CART_DIM, braced_vec_to_string(&vec![self.set.as_ref()]))
    }
}

impl fmt::Display for Proj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", PROJ, braced_vec_to_string(&vec![self.set.as_ref(), self.dim.as_ref()]))
    }
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CART_DIM, braced_vec_to_string(&vec![self.dim.as_ref()]))
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for FnObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.head, braced_vec_to_string(&self.body))
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
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
        write!(f, "{}{}", UNION, braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()]))
    }
}

impl fmt::Display for Intersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", INTERSECT, braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()]))
    }
}

impl fmt::Display for SetMinus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", SET_MINUS, braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()]))
    }
}

impl fmt::Display for SetDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", SET_DIFF, braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()]))
    }
}

impl fmt::Display for Cup {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CUP, braced_vec_to_string(&vec![self.left.as_ref()]))
    }
}

impl fmt::Display for Cap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CAP, braced_vec_to_string(&vec![self.left.as_ref()]))
    }
}

impl fmt::Display for IdentifierWithMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.mod_name, MOD_SING, self.name)
    }
}

impl fmt::Display for ListSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", curly_braced_vec_to_string(&self.list))
    }
}

impl fmt::Display for SetBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{} {}{} {}{}", LEFT_CURLY_BRACE, self.param, self.param_set, COLON, vec_to_string_join_by_comma(&self.facts), RIGHT_CURLY_BRACE)
    }
}

impl fmt::Display for FnSetWithoutDom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FN, braced_vec_to_string(&self.param_sets), self.ret_set)
    }
}

impl fmt::Display for FnSetWithDom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}",
            FN,
            brace_vec_colon_vec_to_string(&self.params_def_with_set, &self.dom_facts),
            self.ret_set
        )
    }
}

impl fmt::Display for NPosObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", N_POS)
    }
}

impl fmt::Display for NObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", N)
    }
}

impl fmt::Display for QObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Q)
    }
}

impl fmt::Display for ZObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Z)
    }
}

impl fmt::Display for RObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", R)
    }
}

impl fmt::Display for QPos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Q_POS)
    }
}

impl fmt::Display for ZPos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Z_POS)
    }
}

impl fmt::Display for RPos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", R_POS)
    }
}

impl fmt::Display for QNeg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Q_NEG)
    }
}

impl fmt::Display for ZNeg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Z_NEG)
    }
}

impl fmt::Display for RNeg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", R_NEG)
    }
}


impl fmt::Display for QNz {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Q_NZ)
    }
}

impl fmt::Display for ZNz {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Z_NZ)
    }
}

impl fmt::Display for RNz {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", R_NZ)
    }
}

impl fmt::Display for InstStructObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", INST_STRUCT_OBJ_SIGN)?;
        match &self.struct_name {
            IdentifierOrIdentifierWithMod::Identifier(identifier) => write!(f, "{}", identifier)?,
            IdentifierOrIdentifierWithMod::IdentifierWithMod(identifier_with_mod) => write!(f, "{}", identifier_with_mod)?,
        };
        write!(f, "{}", braced_vec_to_string(&self.param_sets))
    }
}

impl fmt::Display for Cart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CART,  braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", VAL, braced_vec_to_string(&vec![self.value.as_ref()]))
    }
}

impl fmt::Display for PowerSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", POWER_SET, braced_vec_to_string(&vec![self.set.as_ref()]))
    }
}


impl From<Atom> for Obj {
    fn from(atom: Atom) -> Self {
        match atom {
            Atom::IdentifierAtom(a) => Obj::Identifier(a),
            Atom::IdentifierWithMod(a) => Obj::IdentifierWithMod(a),
            Atom::FieldAccess(a) => Obj::FieldAccess(a),
            Atom::FieldAccessWithMod(a) => Obj::FieldAccessWithMod(a),
        }
    }
}

impl Obj {
    pub fn mk(s: &str) -> Obj {
        Obj::Identifier(Identifier::new(s))
    }
}

impl fmt::Display for FnSetObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FnSetObj::FnSetWithoutDom(fn_set_without_dom) => write!(f, "{}", fn_set_without_dom),
            FnSetObj::FnSetWithDom(fn_set_with_dom) => write!(f, "{}", fn_set_with_dom),
        }
    }
}

impl Obj {
    pub fn is_add_sub_mul_div_mod_pow(&self) -> bool {
        match self {
            Obj::Add(_) => true,
            Obj::Sub(_) => true,
            Obj::Mul(_) => true,
            Obj::Div(_) => true,
            Obj::Mod(_) => true,
            Obj::Pow(_) => true,
            _ => false,
        }
    }
}    
