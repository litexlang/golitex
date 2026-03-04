use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::parameter_type_and_property::ParamDefWithParamSet;
use crate::keywords::{
    ADD, CAP, CART, CHOICE, CLOSED_RANGE, COLON, COUNT, CUP, DISJOINT_UNION, DIV, FN, INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL, INTERSECT, LEFT_CURLY_BRACE, LEFT_BRACKET, MOD, MUL, N,  N_POS, MOD_SEPARATOR, POW, POWER_SET, PROJ, Q, Q_NEG, Q_NZ, Q_POS, R, R_NEG, R_NZ, R_POS, RANGE, RIGHT_CURLY_BRACE, RIGHT_BRACKET, SET_DIM, SET_MINUS, SUB, UNION, VAL, Z, Z_NEG, Z_NZ, Z_POS
};
use std::fmt;
use crate::helper::{braced_string, braced_two_strings, braced_vec_to_string, curly_braced_vec_to_string,  vec_to_string_join_by_comma};
use crate::atom::{AtomWithoutModName, AtomWithModName};
use crate::atom::Atom;

#[derive(Clone)]
pub enum Obj {
    AtomWithoutModName(AtomWithoutModName),
    AtomWithModName(AtomWithModName),
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
    DisjointUnion(DisjointUnion),
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
    InstSetTemplateObj(InstSetTemplateObj),
    Cart(Cart),
    SetDim(SetDim),
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
    pub element: Box<Obj>,
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
pub struct SetDim {
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
    pub is_arithmetic_expr: bool,
}

#[derive(Clone)]
pub struct Sub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub is_arithmetic_expr: bool,
}

#[derive(Clone)]
pub struct Mul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub is_arithmetic_expr: bool,
}

#[derive(Clone)]
pub struct Div {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub is_arithmetic_expr: bool,
}

#[derive(Clone)]
pub struct Mod {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
    pub is_arithmetic_expr: bool,
}

#[derive(Clone)]
pub struct Pow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
    pub is_arithmetic_expr: bool,
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
pub struct DisjointUnion {
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
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct ListSet {
    pub list: Vec<Box<Obj>>,
}

#[derive(Clone)]
pub struct SetBuilder {
    pub param: String,
    pub param_set: Box<Obj>,
    pub facts: Vec<OrFactOrAndFactOrSpecFact>,
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
            match param_def_with_set {
                ParamDefWithParamSet::ParamAndItsSetPair(param_name, _) => {
                    ret.push(param_name.clone());
                }
                ParamDefWithParamSet::ParamsAndTheirSetsPair(param_names, _) => {
                    ret.extend(param_names.iter().map(|param_name| param_name.clone()));
                }
            }
        }
        ret
    }
}

#[derive(Clone)]
pub struct FnSetWithDom {
    pub params_def_with_set: Vec<ParamDefWithParamSet>,
    pub dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
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
pub struct InstSetTemplateObj {
    pub set_template: Atom,
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

impl FnObj {
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
            is_arithmetic_expr,
        }
    }
}

impl Sub {
    pub fn new(left: Obj, right: Obj, is_arithmetic_expr: bool) -> Self {
        Sub {
            left: Box::new(left),
            right: Box::new(right),
            is_arithmetic_expr,
        }
    }
}

impl Mul {
    pub fn new(left: Obj, right: Obj, is_arithmetic_expr: bool) -> Self {
        Mul {
            left: Box::new(left),
            right: Box::new(right),
            is_arithmetic_expr,
        }
    }
}

impl Div {
    pub fn new(left: Obj, right: Obj, is_arithmetic_expr: bool) -> Self {
        Div {
            left: Box::new(left),
            right: Box::new(right),
            is_arithmetic_expr,
        }
    }
}

impl Mod {
    pub fn new(left: Obj, right: Obj, is_arithmetic_expr: bool) -> Self {
        Mod {
            left: Box::new(left),
            right: Box::new(right),
            is_arithmetic_expr,
        }
    }
}

impl Pow {
    pub fn new(base: Obj, exponent: Obj, is_arithmetic_expr: bool) -> Self {
        Pow {
            base: Box::new(base),
            exponent: Box::new(exponent),
            is_arithmetic_expr,
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

impl DisjointUnion {
    pub fn new(left: Obj, right: Obj) -> Self {
        DisjointUnion {
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
    pub fn new(left: Obj, right: Obj) -> Self {
        Cap {
            left: Box::new(left),
            right: Box::new(right),
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
    pub fn new(param: String, param_set: Obj, facts: Vec<OrFactOrAndFactOrSpecFact>) -> Self {
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
    pub fn new(params_and_their_sets: Vec<ParamDefWithParamSet>, dom_facts: Vec<OrFactOrAndFactOrSpecFact>, ret_set: Obj) -> Self {
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

impl InstSetTemplateObj {
    pub fn new(set_template: Atom, param_sets: Vec<Obj>) -> Self {
        InstSetTemplateObj {
            set_template,
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
    pub fn new(element: Obj, set: Obj) -> Self {
        Choose {
            element: Box::new(element),
            set: Box::new(set),
        }
    }
}

impl SetDim {
    pub fn new(set: Obj) -> Self {
        SetDim { set: Box::new(set) }
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

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Obj::AtomWithoutModName(a) => write!(f, "{}", a),
            Obj::AtomWithModName(a) => write!(f, "{}", a),
            Obj::FnObj(a) => write!(f, "{}", a),
            Obj::Number(number) => write!(f, "{}", number),
            Obj::Add(add) => write!(f, "{}", add),
            Obj::Sub(sub) => write!(f, "{}", sub),
            Obj::Mul(mul) => write!(f, "{}", mul),
            Obj::Div(div) => write!(f, "{}", div),
            Obj::Mod(mod_) => write!(f, "{}", mod_),
            Obj::Pow(pow) => write!(f, "{}", pow),
            Obj::Union(union) => write!(f, "{}", union),
            Obj::Intersect(intersect) => write!(f, "{}", intersect),
            Obj::SetMinus(set_minus) => write!(f, "{}", set_minus),
            Obj::DisjointUnion(disjoint_union) => write!(f, "{}", disjoint_union),
            Obj::Cup(cup) => write!(f, "{}", cup),
            Obj::Cap(cap) => write!(f, "{}", cap),
            Obj::ListSet(list_set) => write!(f, "{}", list_set),
            Obj::SetBuilder(set_builder) => write!(f, "{}", set_builder),
            Obj::FnSetWithoutDom(fn_set_without_dom) => write!(f, "{}", fn_set_without_dom),
            Obj::FnSetWithDom(fn_set_with_dom) => write!(f, "{}", fn_set_with_dom),
            Obj::NPosObj(n_pos_obj) => write!(f, "{}", n_pos_obj),
            Obj::NObj(n_obj) => write!(f, "{}", n_obj),
            Obj::QObj(q_obj) => write!(f, "{}", q_obj),
            Obj::ZObj(z_obj) => write!(f, "{}", z_obj),
            Obj::RObj(r_obj) => write!(f, "{}", r_obj),
            Obj::InstSetTemplateObj(instantiated_set_template_obj) => write!(f, "{}", instantiated_set_template_obj),
            Obj::Cart(cart) => write!(f, "{}", cart),
            Obj::SetDim(set_dim) => write!(f, "{}", set_dim),
            Obj::Proj(proj) => write!(f, "{}", proj),
            Obj::Dim(dim) => write!(f, "{}", dim),
            Obj::Tuple(tuple) => write!(f, "{}", tuple),
            Obj::Count(count) => write!(f, "{}", count),
            Obj::Range(range) => write!(f, "{}", range),
            Obj::ClosedRange(closed_range) => write!(f, "{}", closed_range),
            Obj::Val(val) => write!(f, "{}", val),
            Obj::PowerSet(power_set) => write!(f, "{}", power_set),
            Obj::Choose(choice) => write!(f, "{}", choice),
            Obj::ObjAtIndex(obj_at_index) => write!(f, "{}", obj_at_index),
            Obj::QPos(x) => write!(f, "{}", x),
            Obj::ZPos(x) => write!(f, "{}", x),
            Obj::RPos(x) => write!(f, "{}", x),
            Obj::QNeg(x) => write!(f, "{}", x),
            Obj::ZNeg(x) => write!(f, "{}", x),
            Obj::RNeg(x) => write!(f, "{}", x),
            Obj::QNz(x) => write!(f, "{}", x),
            Obj::ZNz(x) => write!(f, "{}", x),
            Obj::RNz(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for ObjAtIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}", self.obj, LEFT_BRACKET, self.index, RIGHT_BRACKET)
    }
}

impl fmt::Display for Choose {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CHOICE, braced_two_strings(&self.element, &self.set))
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", RANGE, braced_two_strings(&self.start, &self.end))
    }
}

impl fmt::Display for ClosedRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CLOSED_RANGE, braced_two_strings(&self.start, &self.end))
    }
}

impl fmt::Display for Count {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", COUNT, braced_string(&self.set))
    }
}

impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}",  braced_vec_to_string(&self.elements))
    }
}

impl fmt::Display for SetDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", SET_DIM, braced_string(&self.set))
    }
}

impl fmt::Display for Proj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", PROJ, braced_two_strings(&self.set, &self.dim))
    }
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", SET_DIM, braced_string(&self.dim))
    }
}

impl fmt::Display for AtomWithoutModName {
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
        write!(f, "{}{}{}", self.left, ADD, self.right)
    }
}

impl fmt::Display for Sub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.left, SUB, self.right)
    }
}

impl fmt::Display for Mul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.left, MUL, self.right)
    }
}

impl fmt::Display for Div {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.left, DIV, self.right)
    }
}

impl fmt::Display for Mod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.left, MOD, self.right)
    }
}

impl fmt::Display for Pow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.base, POW, self.exponent)
    }
}

impl fmt::Display for Union {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", UNION, braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for Intersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", INTERSECT, braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for SetMinus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", SET_MINUS, braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for DisjointUnion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", DISJOINT_UNION, braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for Cup {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CUP, braced_string(&self.left))
    }
}

impl fmt::Display for Cap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CAP, braced_two_strings(&self.left, &self.right))
    }
}

impl fmt::Display for AtomWithModName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.mod_name, MOD_SEPARATOR, self.name)
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
        write!(f, "{}{}{}", FN, braced_vec_to_string(&self.param_sets), self.ret_set.to_string())
    }
}

impl fmt::Display for FnSetWithDom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.with_keyword_fn_with_name_to_string(None))
    }
}

impl FnSetWithDom {
    pub fn with_keyword_fn_with_name_to_string(&self, name: Option<&str>) -> String {
        format!("{} {}{}{}", FN, name.unwrap_or(""), braced_vec_to_string(&self.params_def_with_set), self.ret_set)
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

impl fmt::Display for InstSetTemplateObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let template_str = match &self.set_template {
            Atom::AtomWithoutModName(atom) => atom.to_string(),
            Atom::AtomWithModName(atom_with_mod_name) => atom_with_mod_name.to_string(),
        };
        write!(f, "{}{}{}", INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL, template_str, braced_vec_to_string(&self.param_sets))
    }
}

impl fmt::Display for Cart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", CART,  braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", VAL, braced_string(&self.value))
    }
}

impl fmt::Display for PowerSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", POWER_SET, braced_string(&self.set))
    }
}


impl Obj {
    pub fn mk(s: &str) -> Obj {
        Obj::AtomWithoutModName(AtomWithoutModName::new(s))
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