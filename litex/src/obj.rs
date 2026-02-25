use crate::consts::{
    ADD, CAP, COMMA, DIV, DISJOINT_UNION, INTERSECT, LEFT_BRACE, LEFT_CURLY_BRACE, RIGHT_CURLY_BRACE, MOD, MUL, PKG_SEPARATOR, POW, FN, INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL, SET_DIM, PROJ, CART,
    RIGHT_BRACE, SET_MINUS, SUB, UNION, CUP, N_POS, N, Q, Z, R,
};
use std::fmt;
use crate::helper::{braced_vec_to_string, curly_braced_vec_to_string};
use crate::atom::{AtomWithoutPkg, AtomWithPkg};
use crate::atom::Atom;

pub enum Obj {
    AtomWithoutPkg(AtomWithoutPkg),
    AtomWithPkg(AtomWithPkg),
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
    FnSetWithoutParams(FnSetWithoutParams),
    FnSetWithParams(FnSetWithParams),
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
}

#[allow(non_camel_case_types)]
pub type box_Obj = Box<Obj>;

pub struct Dim {
    pub dim: box_Obj,
}

pub struct SetDim {
    pub set: box_Obj,
}

pub struct Proj {
    pub set: box_Obj,
    pub dim: box_Obj,
}

pub struct FnObj {
    pub head: box_Obj,
    pub body: Vec<box_Obj>,
}


pub struct Number {
    pub value: String,
}


pub struct Add {
    pub left: box_Obj,
    pub right: box_Obj,
    pub is_arithmetic_expr: bool,
}

pub struct Sub {
    pub left: box_Obj,
    pub right: box_Obj,
    pub is_arithmetic_expr: bool,
}

pub struct Mul {
    pub left: box_Obj,
    pub right: box_Obj,
    pub is_arithmetic_expr: bool,
}

pub struct Div {
    pub left: box_Obj,
    pub right: box_Obj,
    pub is_arithmetic_expr: bool,
}

pub struct Mod {
    pub left: box_Obj,
    pub right: box_Obj,
    pub is_arithmetic_expr: bool,
}

pub struct Pow {
    pub base: box_Obj,
    pub exponent: box_Obj,
    pub is_arithmetic_expr: bool,
}

pub struct Union {
    pub left: box_Obj,
    pub right: box_Obj,
}

pub struct Intersect {
    pub left: box_Obj,
    pub right: box_Obj,
}

pub struct SetMinus {
    pub left: box_Obj,
    pub right: box_Obj,
}

pub struct DisjointUnion {
    pub left: box_Obj,
    pub right: box_Obj,
}

pub struct Cup {
    pub left: box_Obj,
}

pub struct Cap {
    pub left: box_Obj,
    pub right: box_Obj,
}

pub struct ListSet {
    pub list: Vec<box_Obj>,
}

pub struct SetBuilder {
}

pub struct FnSetWithoutParams {
    pub param_sets: Vec<box_Obj>,
    pub ret_set: box_Obj,
}

pub struct FnSetWithParams {
}

pub struct NPosObj {
}

pub struct NObj {
}

pub struct QObj {
}

pub struct ZObj {
}

pub struct RObj {   
}

pub struct InstSetTemplateObj {
    pub set_template: Box<Atom>,
    pub param_sets: Vec<box_Obj>,
}

pub struct Cart {
    pub args: Vec<box_Obj>,
}


impl Obj {
    pub fn box_atom_without_pkg(name: &str) -> box_Obj {
        Box::new(Obj::AtomWithoutPkg(AtomWithoutPkg::new(name)))
    }
    pub fn box_atom_with_pkg(pkg: &str, name: &str) -> box_Obj {
        Box::new(Obj::AtomWithPkg(AtomWithPkg::new(pkg, name)))
    }
    pub fn box_fn_obj(head: box_Obj, body: Vec<box_Obj>) -> box_Obj {
        Box::new(Obj::FnObj(FnObj::new(head, body)))
    }
    pub fn box_number(value: &str) -> box_Obj {
        Box::new(Obj::Number(Number::new(value)))
    }
    pub fn box_add(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> box_Obj {
        Box::new(Obj::Add(Add::new(left, right, is_arithmetic_expr)))
    }
    pub fn box_sub(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> box_Obj {
        Box::new(Obj::Sub(Sub::new(left, right, is_arithmetic_expr)))
    }
    pub fn box_mul(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> box_Obj {
        Box::new(Obj::Mul(Mul::new(left, right, is_arithmetic_expr)))
    }
    pub fn box_div(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> box_Obj {
        Box::new(Obj::Div(Div::new(left, right, is_arithmetic_expr)))
    }
    pub fn box_mod(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> box_Obj {
        Box::new(Obj::Mod(Mod::new(left, right, is_arithmetic_expr)))
    }
    pub fn box_pow(base: box_Obj, exponent: box_Obj, is_arithmetic_expr: bool) -> box_Obj {
        Box::new(Obj::Pow(Pow::new(base, exponent, is_arithmetic_expr)))
    }
    pub fn box_union(left: box_Obj, right: box_Obj) -> box_Obj {
        Box::new(Obj::Union(Union::new(left, right)))
    }
    pub fn box_intersect(left: box_Obj, right: box_Obj) -> box_Obj {
        Box::new(Obj::Intersect(Intersect::new(left, right)))
    }
    pub fn box_set_minus(left: box_Obj, right: box_Obj) -> box_Obj {
        Box::new(Obj::SetMinus(SetMinus::new(left, right)))
    }
    pub fn box_disjoint_union(left: box_Obj, right: box_Obj) -> box_Obj {
        Box::new(Obj::DisjointUnion(DisjointUnion::new(left, right)))
    }
    pub fn box_cup(left: box_Obj) -> box_Obj {
        Box::new(Obj::Cup(Cup::new(left)))
    }
    pub fn box_cap(left: box_Obj, right: box_Obj) -> box_Obj {
        Box::new(Obj::Cap(Cap::new(left, right)))
    }
    pub fn box_list_set(list: Vec<box_Obj>) -> box_Obj {
        Box::new(Obj::ListSet(ListSet::new(list)))
    }
    pub fn box_set_builder() -> box_Obj {
        Box::new(Obj::SetBuilder(SetBuilder::new()))
    }
    pub fn box_fn_set_without_params(param_sets: Vec<box_Obj>, ret_set: box_Obj) -> box_Obj {
        Box::new(Obj::FnSetWithoutParams(FnSetWithoutParams::new(param_sets, ret_set)))
    }
    pub fn box_fn_set_with_params() -> box_Obj {
        Box::new(Obj::FnSetWithParams(FnSetWithParams::new()))
    }
    pub fn box_n_pos_obj() -> box_Obj {
        Box::new(Obj::NPosObj(NPosObj::new()))
    }
    pub fn box_n_obj() -> box_Obj {
        Box::new(Obj::NObj(NObj::new()))
    }
    pub fn box_q_obj() -> box_Obj {
        Box::new(Obj::QObj(QObj::new()))
    }
    pub fn box_z_obj() -> box_Obj {
        Box::new(Obj::ZObj(ZObj::new()))
    }
    pub fn box_r_obj() -> box_Obj {
        Box::new(Obj::RObj(RObj::new()))
    }
    pub fn box_inst_set_template_obj(set_template: Box<Atom>, param_sets: Vec<box_Obj>) -> box_Obj {
        Box::new(Obj::InstSetTemplateObj(InstSetTemplateObj::new(set_template, param_sets)))
    }
    pub fn box_cart(args: Vec<box_Obj>) -> box_Obj {
        Box::new(Obj::Cart(Cart::new(args)))
    }
    pub fn box_set_dim(set: box_Obj) -> box_Obj {
        Box::new(Obj::SetDim(SetDim::new(set)))
    }
    pub fn box_proj(set: box_Obj, dim: box_Obj) -> box_Obj {
        Box::new(Obj::Proj(Proj::new(set, dim)))
    }
    pub fn box_dim(dim: box_Obj) -> box_Obj {
        Box::new(Obj::Dim(Dim::new(dim)))
    }
}

impl AtomWithoutPkg {
    pub fn new(name: &str) -> Self {
        AtomWithoutPkg { name: name.to_string() }
    }
}

impl AtomWithPkg {
    pub fn new(pkg: &str, name: &str) -> Self {
        AtomWithPkg { pkg: pkg.to_string(), name: name.to_string() }
    }
}

impl FnObj {
    pub fn new(head: box_Obj, body: Vec<box_Obj>) -> Self {
        FnObj { head, body }
    }
}

impl Number {
    pub fn new(value: &str) -> Self {
        Number { value: value.to_string() }
    }
}

impl Add {
    pub fn new(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> Self {
        Add { left, right, is_arithmetic_expr }
    }
}

impl Sub {
    pub fn new(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> Self {
        Sub { left, right, is_arithmetic_expr }
    }
}

impl Mul {
    pub fn new(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> Self {
        Mul { left, right, is_arithmetic_expr }
    }
}

impl Div {
    pub fn new(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> Self {
        Div { left, right, is_arithmetic_expr }
    }
}

impl Mod {
    pub fn new(left: box_Obj, right: box_Obj, is_arithmetic_expr: bool) -> Self {
        Mod { left, right, is_arithmetic_expr }
    }
}

impl Pow {
    pub fn new(base: box_Obj, exponent: box_Obj, is_arithmetic_expr: bool) -> Self {
        Pow { base, exponent, is_arithmetic_expr }
    }
}

impl Union {
    pub fn new(left: box_Obj, right: box_Obj) -> Self {
        Union { left, right }
    }
}

impl Intersect {
    pub fn new(left: box_Obj, right: box_Obj) -> Self {
        Intersect { left, right }
    }
}

impl SetMinus {
    pub fn new(left: box_Obj, right: box_Obj) -> Self {
        SetMinus { left, right }
    }
}

impl DisjointUnion {
    pub fn new(left: box_Obj, right: box_Obj) -> Self {
        DisjointUnion { left, right }
    }
}

impl Cup {
    pub fn new(left: box_Obj) -> Self {
        Cup { left }
    }
}

impl Cap {
    pub fn new(left: box_Obj, right: box_Obj) -> Self {
        Cap { left, right }
    }
}

impl ListSet {
    pub fn new(list: Vec<box_Obj>) -> Self {
        ListSet { list }
    }
}

impl SetBuilder {
    pub fn new() -> Self {
        SetBuilder {}
    }
}

impl FnSetWithoutParams {
    pub fn new(param_sets: Vec<box_Obj>, ret_set: box_Obj) -> Self {
        FnSetWithoutParams { param_sets, ret_set }
    }
}

impl FnSetWithParams {
    pub fn new() -> Self {
        FnSetWithParams {}
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

impl InstSetTemplateObj {
    pub fn new(set_template: Box<Atom>, param_sets: Vec<box_Obj>) -> Self {
        InstSetTemplateObj { set_template, param_sets }
    }
}

impl SetDim {
    pub fn new(set: box_Obj) -> Self {
        SetDim { set }
    }
}

impl Proj {
    pub fn new(set: box_Obj, dim: box_Obj) -> Self {
        Proj { set, dim }
    }
}

impl Dim {
    pub fn new(dim: box_Obj) -> Self {
        Dim { dim }
    }
}

impl Cart {
    pub fn new(args: Vec<box_Obj>) -> Self {
        Cart { args }
    }
}

// Display implementations
impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Obj::AtomWithoutPkg(a) => write!(f, "{}", a),
            Obj::AtomWithPkg(a) => write!(f, "{}", a),
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
            Obj::FnSetWithoutParams(function_set) => write!(f, "{}", function_set),
            Obj::FnSetWithParams(function_set_with_params) => write!(f, "{}", function_set_with_params),
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
        }
    }
}

impl fmt::Display for SetDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}", SET_DIM, LEFT_BRACE, self.set, RIGHT_BRACE)?;
        write!(f, "{}", RIGHT_BRACE)
    }
}

impl fmt::Display for Proj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}{}{}", PROJ, LEFT_BRACE, self.set, COMMA, self.dim, RIGHT_BRACE)?;
        write!(f, "{}", RIGHT_BRACE)
    }
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}", SET_DIM, LEFT_BRACE, self.dim, RIGHT_BRACE)
    }
}

impl fmt::Display for AtomWithoutPkg {
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
        write!(f, "{}{}{}{}{}", UNION, LEFT_BRACE, self.left, COMMA, self.right)?;
        write!(f, "{}", RIGHT_BRACE)
    }
}

impl fmt::Display for Intersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}{}", INTERSECT, LEFT_BRACE, self.left, COMMA, self.right)?;
        write!(f, "{}", RIGHT_BRACE)
    }
}

impl fmt::Display for SetMinus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}{}", SET_MINUS, LEFT_BRACE, self.left, COMMA, self.right)?;
        write!(f, "{}", RIGHT_BRACE)
    }
}

impl fmt::Display for DisjointUnion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}{}", DISJOINT_UNION, LEFT_BRACE, self.left, COMMA, self.right)?;
        write!(f, "{}", RIGHT_BRACE)
    }
}

impl fmt::Display for Cup {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", CUP, LEFT_BRACE, self.left)?;
        write!(f, "{}", RIGHT_BRACE)
    }
}

impl fmt::Display for Cap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}{}", CAP, LEFT_BRACE, self.left, COMMA, self.right)?;
        write!(f, "{}", RIGHT_BRACE)
    }
}

impl fmt::Display for AtomWithPkg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.pkg, PKG_SEPARATOR, self.name)
    }
}

impl fmt::Display for ListSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", curly_braced_vec_to_string(&self.list))
    }
}

impl fmt::Display for SetBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", LEFT_CURLY_BRACE, RIGHT_CURLY_BRACE)
    }
}

impl fmt::Display for FnSetWithoutParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FN, braced_vec_to_string(&self.param_sets), self.ret_set.to_string())
    }
}

impl fmt::Display for FnSetWithParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", FN, LEFT_BRACE, RIGHT_BRACE)
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

impl fmt::Display for InstSetTemplateObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let template_str = match self.set_template.as_ref() {
            Atom::AtomWithoutPkg(atom) => atom.to_string(),
            Atom::AtomWithPkg(atom_with_pkg) => atom_with_pkg.to_string(),
        };
        write!(f, "{}{}{}", INSTANTIATED_SET_TEMPLATE_OBJ_SIGNAL, template_str, braced_vec_to_string(&self.param_sets))
    }
}

impl fmt::Display for Cart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}{}", CART, LEFT_BRACE, braced_vec_to_string(&self.args), RIGHT_BRACE)
    }
}

// obj helper functions
impl Obj {
    pub fn equal_literally(left: &Obj, right: &Obj) -> bool {
        match left {
            Obj::AtomWithoutPkg(a) => match right {
                Obj::AtomWithoutPkg(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::AtomWithPkg(a) => match right {
                Obj::AtomWithPkg(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FnObj(f) => match right {
                Obj::FnObj(g) => f.to_string() == g.to_string(),
                _ => false,
            },
            Obj::Number(n) => match right {
                Obj::Number(m) => n.to_string() == m.to_string(),
                _ => false,
            },
            Obj::Add(a) => match right {
                Obj::Add(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Sub(a) => match right {
                Obj::Sub(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Mul(a) => match right {
                Obj::Mul(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Div(a) => match right {
                Obj::Div(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Mod(a) => match right {
                Obj::Mod(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Pow(a) => match right {
                Obj::Pow(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Union(a) => match right {
                Obj::Union(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Intersect(a) => match right {
                Obj::Intersect(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetMinus(a) => match right {
                Obj::SetMinus(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::DisjointUnion(a) => match right {
                Obj::DisjointUnion(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cup(a) => match right {
                Obj::Cup(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cap(a) => match right {
                Obj::Cap(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ListSet(a) => match right {
                Obj::ListSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetBuilder(a) => match right {
                Obj::SetBuilder(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FnSetWithoutParams(a) => match right {    
                Obj::FnSetWithoutParams(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FnSetWithParams(a) => match right {
                Obj::FnSetWithParams(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::NPosObj(_) => match right {
                Obj::NPosObj(_) => true,
                _ => false,
            },
            Obj::NObj(_) => match right {
                Obj::NObj(_) => true,
                _ => false,
            },
            Obj::QObj(_) => match right {
                Obj::QObj(_) => true,
                _ => false,
            },
            Obj::ZObj(_) => match right {
                Obj::ZObj(_) => true,
                _ => false,
            },
            Obj::RObj(_) => match right {
                Obj::RObj(_) => true,
                _ => false,
            },
            Obj::InstSetTemplateObj(a) => match right {
                Obj::InstSetTemplateObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cart(a) => match right {
                Obj::Cart(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetDim(a) => match right {
                Obj::SetDim(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Proj(a) => match right {
                Obj::Proj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Dim(a) => match right {
                Obj::Dim(b) => a.to_string() == b.to_string(),
                _ => false,
            },
        }
    }
}
