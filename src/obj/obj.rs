use super::standard_set::StandardSet;
use crate::prelude::*;
use std::fmt;

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
    PowerSet(PowerSet),
    ListSet(ListSet),
    SetBuilder(SetBuilder),
    FnSet(FnSet),
    Cart(Cart),
    CartDim(CartDim),
    Proj(Proj),
    TupleDim(TupleDim),
    Tuple(Tuple),
    Count(Count),
    Range(Range),
    ClosedRange(ClosedRange),
    Choose(Choose),
    ObjAtIndex(ObjAtIndex),
    StandardSet(StandardSet),
    FamilyObj(FamilyObj),
    StructObj(StructObj),
}

/// Instantiated family type: `family` name followed by argument objects (often sets).
#[derive(Clone)]
pub struct FamilyObj {
    pub name: IdentifierOrIdentifierWithMod,
    pub params: Vec<Obj>,
}

/// Instantiated struct type: `struct` name followed by argument objects (field types / indices).
#[derive(Clone)]
pub struct StructObj {
    pub name: IdentifierOrIdentifierWithMod,
    pub args: Vec<Obj>,
}

impl StructObj {
    pub fn new(name: IdentifierOrIdentifierWithMod, args: Vec<Obj>) -> Self {
        StructObj { name, args }
    }
}

impl fmt::Display for FamilyObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}({})",
            FAMILY,
            self.name,
            vec_to_string_join_by_comma(&self.params)
        )
    }
}

impl fmt::Display for StructObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}({})",
            STRUCT,
            self.name,
            vec_to_string_join_by_comma(&self.args)
        )
    }
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
pub struct FnSet {
    pub params_def_with_set: Vec<ParamGroupWithSet>,
    pub dom_facts: Vec<OrAndChainAtomicFact>,
    pub ret_set: Box<Obj>,
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

impl FnSet {
    pub fn new(
        params_and_their_sets: Vec<ParamGroupWithSet>,
        dom_facts: Vec<OrAndChainAtomicFact>,
        ret_set: Obj,
    ) -> Self {
        FnSet {
            params_def_with_set: params_and_their_sets,
            dom_facts,
            ret_set: Box::new(ret_set),
        }
    }

    pub fn get_params(&self) -> Vec<String> {
        let mut ret = Vec::with_capacity(ParamGroupWithSet::number_of_params(
            &self.params_def_with_set,
        ));
        for param_def_with_set in &self.params_def_with_set {
            ret.extend(param_def_with_set.params.iter().cloned());
        }
        ret
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
        let n = args.len();
        if n < 2 {
            panic!("Cart::new: expected at least 2 factors, got {n}");
        }
        Cart {
            args: args.into_iter().map(Box::new).collect(),
        }
    }
}

impl Tuple {
    pub fn new(elements: Vec<Obj>) -> Self {
        let n = elements.len();
        if n < 2 {
            panic!("Tuple::new: expected at least 2 elements, got {n}");
        }
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
            Obj::FnSet(x) => write!(f, "{}", x)?,
            Obj::StandardSet(standard_set) => write!(f, "{}", standard_set)?,
            Obj::Cart(x) => write!(f, "{}", x)?,
            Obj::CartDim(x) => write!(f, "{}", x)?,
            Obj::Proj(x) => write!(f, "{}", x)?,
            Obj::TupleDim(x) => write!(f, "{}", x)?,
            Obj::Tuple(x) => write!(f, "{}", x)?,
            Obj::Count(x) => write!(f, "{}", x)?,
            Obj::Range(x) => write!(f, "{}", x)?,
            Obj::ClosedRange(x) => write!(f, "{}", x)?,
            Obj::PowerSet(x) => write!(f, "{}", x)?,
            Obj::Choose(x) => write!(f, "{}", x)?,
            Obj::ObjAtIndex(x) => write!(f, "{}", x)?,
            Obj::FamilyObj(x) => write!(f, "{}", x)?,
            Obj::StructObj(x) => write!(f, "{}", x)?,
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

impl fmt::Display for FnSet {
    /// 与 AST 一致：形参表、dom 均使用**存储名**（`fn` 形参为 `__` + 用户符面）。  
    /// 区别于单独 [`ParamGroupWithSet`] 的 `Display`（会隐去 `__` 以便其它上下文）。
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let params_with_sets_display: Vec<String> = self
            .params_def_with_set
            .iter()
            .map(|g| format!("{} {}", vec_to_string_join_by_comma(&g.params), g.set))
            .collect();
        write!(
            f,
            "{} {} {}",
            FN_LOWER_CASE,
            brace_vec_colon_vec_to_string(&params_with_sets_display, &self.dom_facts),
            self.ret_set
        )
    }
}

impl fmt::Display for Cart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CART, braced_vec_to_string(&self.args))
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
