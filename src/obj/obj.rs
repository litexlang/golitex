use super::atom_obj::AtomObj;
use super::fn_set::{AnonymousFn, FnSet, FnSetBody};
use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum Obj {
    Atom(AtomObj),
    FnObj(FnObj),
    Number(Number),
    Add(Add),
    Sub(Sub),
    Mul(Mul),
    Div(Div),
    Mod(Mod),
    Pow(Pow),
    Abs(Abs),
    Log(Log),
    Max(Max),
    Min(Min),
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
    AnonymousFn(AnonymousFn),
    Cart(Cart),
    CartDim(CartDim),
    Proj(Proj),
    TupleDim(TupleDim),
    Tuple(Tuple),
    Count(Count),
    Sum(Sum),
    Product(Product),
    Range(Range),
    ClosedRange(ClosedRange),
    FnRange(FnRange),
    FnDom(FnDom),
    FiniteSeqSet(FiniteSeqSet),
    SeqSet(SeqSet),
    FiniteSeqListObj(FiniteSeqListObj),
    Choose(Choose),
    ObjAtIndex(ObjAtIndex),
    StandardSet(StandardSet),
    FamilyObj(FamilyObj),
    MatrixSet(MatrixSet),
    MatrixListObj(MatrixListObj),
    MatrixAdd(MatrixAdd),
    MatrixSub(MatrixSub),
    MatrixMul(MatrixMul),
    MatrixScalarMul(MatrixScalarMul),
    MatrixPow(MatrixPow),
    FieldAccess(FieldAccess),
    StructInstance(Box<StructInstance>),
}

#[derive(Clone)]
pub struct StructInstance {
    pub name: StructAsParamType,
    pub fields_equal_to_what: Vec<Box<Obj>>,
}

impl StructInstance {
    pub fn new(name: StructAsParamType, fields_equal_to_what: Vec<Obj>) -> Self {
        let fields_equal_to_what = fields_equal_to_what.into_iter().map(Box::new).collect();
        StructInstance {
            name,
            fields_equal_to_what,
        }
    }

    pub fn new_with_boxed_fields(
        name: StructAsParamType,
        fields_equal_to_what: Vec<Box<Obj>>,
    ) -> Self {
        StructInstance {
            name,
            fields_equal_to_what,
        }
    }
}

impl fmt::Display for StructInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", STRUCT_INSTANCE_PREFIX, self.name.struct_name())?;
        if !self.name.args.is_empty() {
            write!(
                f,
                "{}{}{}",
                LEFT_BRACE,
                vec_to_string_join_by_comma(&self.name.args),
                RIGHT_BRACE
            )?;
        }
        write!(
            f,
            "{}{}{}",
            LEFT_BRACE,
            vec_to_string_join_by_comma(&self.fields_equal_to_what),
            RIGHT_BRACE
        )
    }
}

#[derive(Clone)]
pub struct FieldAccess {
    pub left: String,
    pub right: String,
}

impl FieldAccess {
    pub fn new(left: String, right: String) -> Self {
        FieldAccess { left, right }
    }
}

impl fmt::Display for FieldAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.left, DOT_AKA_FIELD_ACCESS_SIGN, self.right
        )
    }
}

#[derive(Clone)]
pub struct Sum {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

#[derive(Clone)]
pub struct Product {
    pub start: Box<Obj>,
    pub end: Box<Obj>,
    pub func: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixAdd {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixSub {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixMul {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixScalarMul {
    pub scalar: Box<Obj>,
    pub matrix: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixPow {
    pub base: Box<Obj>,
    pub exponent: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixSet {
    pub set: Box<Obj>,
    pub row_len: Box<Obj>,
    pub col_len: Box<Obj>,
}

#[derive(Clone)]
pub struct MatrixListObj {
    pub rows: Vec<Vec<Box<Obj>>>,
}

#[derive(Clone)]
pub struct FamilyObj {
    pub name: AtomicName,
    pub params: Vec<Obj>,
}

impl FamilyObj {
    pub fn new(name: AtomicName, params: Vec<Obj>) -> Self {
        FamilyObj { name, params }
    }
}

impl fmt::Display for FamilyObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            display_family_obj_head(&self.name),
            vec_to_string_join_by_comma(&self.params)
        )
    }
}

fn display_family_obj_head(name: &AtomicName) -> String {
    format!("{}{}", FAMILY_OBJ_PREFIX, name)
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
pub struct FnRange {
    pub fn_obj: Box<Obj>,
}

#[derive(Clone)]
pub struct FnDom {
    pub fn_obj: Box<Obj>,
}

/// Set of functions `fn(x N_pos: x <= n) s` (Lit surface syntax: keyword `finite_seq(s, n)`).
#[derive(Clone)]
pub struct FiniteSeqSet {
    pub set: Box<Obj>,
    pub n: Box<Obj>,
}

/// `seq(s)` — functions `fn(x N_pos) s` (no length bound; surface: keyword `seq(s)`).
#[derive(Clone)]
pub struct SeqSet {
    pub set: Box<Obj>,
}

/// Literal `[a, b, ...]` as a finite sequence value (for membership in `finite_seq(s, n)`).
#[derive(Clone)]
pub struct FiniteSeqListObj {
    pub objs: Vec<Box<Obj>>,
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
    pub head: Box<FnObjHead>,
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
pub struct Abs {
    pub arg: Box<Obj>,
}

/// Real logarithm `log(base, x)` with `base > 0`, `base != 1`, `x > 0`.
#[derive(Clone)]
pub struct Log {
    pub base: Box<Obj>,
    pub arg: Box<Obj>,
}

#[derive(Clone)]
pub struct Max {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
}

#[derive(Clone)]
pub struct Min {
    pub left: Box<Obj>,
    pub right: Box<Obj>,
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
    pub fn new(head: FnObjHead, body: Vec<Vec<Box<Obj>>>) -> Self {
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

impl Abs {
    pub fn new(arg: Obj) -> Self {
        Abs { arg: Box::new(arg) }
    }
}

impl Log {
    pub fn new(base: Obj, arg: Obj) -> Self {
        Log {
            base: Box::new(base),
            arg: Box::new(arg),
        }
    }
}

impl Max {
    pub fn new(left: Obj, right: Obj) -> Self {
        Max {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl Min {
    pub fn new(left: Obj, right: Obj) -> Self {
        Min {
            left: Box::new(left),
            right: Box::new(right),
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
    pub fn new(
        param: String,
        param_set: Obj,
        facts: Vec<OrAndChainAtomicFact>,
    ) -> Result<Self, RuntimeError> {
        let set_builder = SetBuilder {
            param,
            param_set: Box::new(param_set),
            facts,
        };
        check_set_builder_has_no_duplicate_set_builder_free_parameter(&set_builder)?;
        Ok(set_builder)
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

impl FnRange {
    pub fn new(fn_obj: Obj) -> Self {
        FnRange {
            fn_obj: Box::new(fn_obj),
        }
    }
}

impl FnDom {
    pub fn new(fn_obj: Obj) -> Self {
        FnDom {
            fn_obj: Box::new(fn_obj),
        }
    }
}

impl FiniteSeqSet {
    pub fn new(set: Obj, n: Obj) -> Self {
        FiniteSeqSet {
            set: Box::new(set),
            n: Box::new(n),
        }
    }
}

impl SeqSet {
    pub fn new(set: Obj) -> Self {
        SeqSet { set: Box::new(set) }
    }
}

impl FiniteSeqListObj {
    pub fn new(objs: Vec<Obj>) -> Self {
        FiniteSeqListObj {
            objs: objs.into_iter().map(Box::new).collect(),
        }
    }
}

impl MatrixSet {
    pub fn new(set: Obj, row_len: Obj, col_len: Obj) -> Self {
        MatrixSet {
            set: Box::new(set),
            row_len: Box::new(row_len),
            col_len: Box::new(col_len),
        }
    }
}

impl MatrixListObj {
    pub fn new(rows: Vec<Vec<Obj>>) -> Self {
        MatrixListObj {
            rows: rows
                .into_iter()
                .map(|row| row.into_iter().map(Box::new).collect())
                .collect(),
        }
    }
}

impl MatrixAdd {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixAdd {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixSub {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixSub {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixMul {
    pub fn new(left: Obj, right: Obj) -> Self {
        MatrixMul {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

impl MatrixScalarMul {
    pub fn new(scalar: Obj, matrix: Obj) -> Self {
        MatrixScalarMul {
            scalar: Box::new(scalar),
            matrix: Box::new(matrix),
        }
    }
}

impl MatrixPow {
    pub fn new(base: Obj, exponent: Obj) -> Self {
        MatrixPow {
            base: Box::new(base),
            exponent: Box::new(exponent),
        }
    }
}

impl Sum {
    pub fn new(start: Obj, end: Obj, func: Obj) -> Self {
        Sum {
            start: Box::new(start),
            end: Box::new(end),
            func: Box::new(func),
        }
    }
}

impl Product {
    pub fn new(start: Obj, end: Obj, func: Obj) -> Self {
        Product {
            start: Box::new(start),
            end: Box::new(end),
            func: Box::new(func),
        }
    }
}

/// 算术运算符优先级：数值越小绑定越紧。^ / matrix ops =1, * / % / *. =2, + -=3；非算术=0 不参与括号。
fn precedence(o: &Obj) -> u8 {
    match o {
        Obj::Add(_) | Obj::Sub(_) => 3,
        Obj::Mul(_)
        | Obj::Div(_)
        | Obj::Mod(_)
        | Obj::Max(_)
        | Obj::Min(_)
        | Obj::MatrixScalarMul(_) => 2,
        Obj::Pow(_)
        | Obj::Abs(_)
        | Obj::Log(_)
        | Obj::MatrixAdd(_)
        | Obj::MatrixSub(_)
        | Obj::MatrixMul(_)
        | Obj::MatrixPow(_) => 1,
        _ => 0,
    }
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_precedence(f, 0)
    }
}

impl Obj {
    /// Precedence-aware display: add parens when a child binds looser than the parent (e.g. + under *).
    /// For same-precedence `+`/`-`, pass a stricter bound (2) on Sub's sides and Add's right so
    /// `a - (b + c)` and `a + (b - c)` do not print as the ambiguous `a - b + c` / `a + b - c`.
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
                a.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Sub(s) => {
                s.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", SUB)?;
                s.right.fmt_with_precedence(f, 2)?;
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
            Obj::MatrixAdd(m) => {
                m.left.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", MATRIX_ADD)?;
                m.right.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixSub(m) => {
                m.left.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", MATRIX_SUB)?;
                m.right.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixMul(m) => {
                m.left.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", MATRIX_MUL)?;
                m.right.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixPow(m) => {
                m.base.fmt_with_precedence(f, 1)?;
                write!(f, " {} ", MATRIX_POW)?;
                m.exponent.fmt_with_precedence(f, 1)?;
            }
            Obj::MatrixScalarMul(m) => {
                m.scalar.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", MATRIX_SCALAR_MUL)?;
                m.matrix.fmt_with_precedence(f, 2)?;
            }
            Obj::Abs(a) => {
                write!(f, "{} {}", ABS, LEFT_BRACE)?;
                a.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Log(l) => {
                write!(f, "{} {}", LOG, LEFT_BRACE)?;
                l.base.fmt_with_precedence(f, 0)?;
                write!(f, "{} ", COMMA)?;
                l.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Max(m) => {
                write!(f, "{} {}", MAX, LEFT_BRACE)?;
                m.left.fmt_with_precedence(f, 0)?;
                write!(f, "{} ", COMMA)?;
                m.right.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Min(m) => {
                write!(f, "{} {}", MIN, LEFT_BRACE)?;
                m.left.fmt_with_precedence(f, 0)?;
                write!(f, "{} ", COMMA)?;
                m.right.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Union(x) => write!(f, "{}", x)?,
            Obj::Intersect(x) => write!(f, "{}", x)?,
            Obj::SetMinus(x) => write!(f, "{}", x)?,
            Obj::SetDiff(x) => write!(f, "{}", x)?,
            Obj::Cup(x) => write!(f, "{}", x)?,
            Obj::Cap(x) => write!(f, "{}", x)?,
            Obj::Atom(x) => write!(f, "{}", x)?,
            Obj::FnObj(x) => write!(f, "{}", x)?,
            Obj::Number(x) => write!(f, "{}", x)?,
            Obj::ListSet(x) => write!(f, "{}", x)?,
            Obj::SetBuilder(x) => write!(f, "{}", x)?,
            Obj::FnSet(x) => write!(f, "{}", x)?,
            Obj::AnonymousFn(x) => write!(f, "{}", x)?,
            Obj::StandardSet(standard_set) => write!(f, "{}", standard_set)?,
            Obj::Cart(x) => write!(f, "{}", x)?,
            Obj::CartDim(x) => write!(f, "{}", x)?,
            Obj::Proj(x) => write!(f, "{}", x)?,
            Obj::TupleDim(x) => write!(f, "{}", x)?,
            Obj::Tuple(x) => write!(f, "{}", x)?,
            Obj::Count(x) => write!(f, "{}", x)?,
            Obj::Sum(x) => write!(f, "{}", x)?,
            Obj::Product(x) => write!(f, "{}", x)?,
            Obj::Range(x) => write!(f, "{}", x)?,
            Obj::ClosedRange(x) => write!(f, "{}", x)?,
            Obj::FnRange(x) => write!(f, "{}", x)?,
            Obj::FnDom(x) => write!(f, "{}", x)?,
            Obj::FiniteSeqSet(x) => write!(f, "{}", x)?,
            Obj::SeqSet(x) => write!(f, "{}", x)?,
            Obj::FiniteSeqListObj(x) => write!(f, "{}", x)?,
            Obj::MatrixSet(x) => write!(f, "{}", x)?,
            Obj::MatrixListObj(x) => write!(f, "{}", x)?,
            Obj::PowerSet(x) => write!(f, "{}", x)?,
            Obj::Choose(x) => write!(f, "{}", x)?,
            Obj::ObjAtIndex(x) => write!(f, "{}", x)?,
            Obj::FamilyObj(x) => write!(f, "{}", x)?,
            Obj::FieldAccess(x) => write!(f, "{}", x)?,
            Obj::StructInstance(x) => write!(f, "{}", x)?,
        }
        if need_parens {
            write!(f, "{}", RIGHT_BRACE)?;
        }
        Ok(())
    }

    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Obj {
        if from == to {
            return self;
        }
        match self {
            Obj::Atom(a) => Obj::Atom(a.replace_bound_identifier(from, to)),
            Obj::FnObj(inner) => {
                let head = replace_bound_identifier_in_fn_obj_head(*inner.head, from, to);
                let body = inner
                    .body
                    .into_iter()
                    .map(|group| {
                        group
                            .into_iter()
                            .map(|b| Box::new(Obj::replace_bound_identifier(*b, from, to)))
                            .collect()
                    })
                    .collect();
                FnObj::new(head, body).into()
            }
            Obj::Number(n) => n.into(),
            Obj::Add(x) => Add::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Sub(x) => Sub::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Mul(x) => Mul::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Div(x) => Div::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Mod(x) => Mod::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Pow(x) => Pow::new(
                Obj::replace_bound_identifier(*x.base, from, to),
                Obj::replace_bound_identifier(*x.exponent, from, to),
            )
            .into(),
            Obj::Abs(x) => Abs::new(Obj::replace_bound_identifier(*x.arg, from, to)).into(),
            Obj::Log(x) => Log::new(
                Obj::replace_bound_identifier(*x.base, from, to),
                Obj::replace_bound_identifier(*x.arg, from, to),
            )
            .into(),
            Obj::Max(x) => Max::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Min(x) => Min::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Union(x) => Union::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Intersect(x) => Intersect::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::SetMinus(x) => SetMinus::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::SetDiff(x) => SetDiff::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::Cup(x) => Cup::new(Obj::replace_bound_identifier(*x.left, from, to)).into(),
            Obj::Cap(x) => Cap::new(Obj::replace_bound_identifier(*x.left, from, to)).into(),
            Obj::PowerSet(x) => {
                PowerSet::new(Obj::replace_bound_identifier(*x.set, from, to)).into()
            }
            Obj::ListSet(x) => ListSet::new(
                x.list
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier(*b, from, to))
                    .collect(),
            )
            .into(),
            Obj::SetBuilder(sb) => {
                let param = if sb.param == from {
                    to.to_string()
                } else {
                    sb.param
                };
                let param_set = Obj::replace_bound_identifier(*sb.param_set, from, to);
                let facts = sb
                    .facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier(from, to))
                    .collect();
                Obj::SetBuilder(
                    SetBuilder::new(param, param_set, facts)
                        .expect("renaming a valid set builder preserves object scope validity"),
                )
            }
            Obj::FnSet(fs) => {
                let FnSet { body } = fs;
                let FnSetBody {
                    params_def_with_set,
                    dom_facts,
                    ret_set,
                } = body;
                let params_def_with_set = params_def_with_set
                    .into_iter()
                    .map(|pg| {
                        let params = pg
                            .params
                            .into_iter()
                            .map(|p| if p == from { to.to_string() } else { p })
                            .collect();
                        match pg.param_type {
                            ParamGroupWithSetTypeEnum::Struct(struct_ty) => {
                                ParamGroupWithSet::new_struct(
                                    params,
                                    StructAsParamType::new(
                                        struct_ty.name,
                                        struct_ty
                                            .args
                                            .into_iter()
                                            .map(|arg| {
                                                Obj::replace_bound_identifier(*arg, from, to)
                                            })
                                            .collect(),
                                    ),
                                )
                            }
                            ParamGroupWithSetTypeEnum::Set(set) => ParamGroupWithSet::new(
                                params,
                                Obj::replace_bound_identifier(set, from, to),
                            ),
                        }
                    })
                    .collect();
                let dom_facts = dom_facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier(from, to))
                    .collect();
                let ret_set = Obj::replace_bound_identifier(*ret_set, from, to);
                FnSet::new(params_def_with_set, dom_facts, ret_set)
                    .expect("renaming a valid fn set preserves object scope validity")
                    .into()
            }
            Obj::AnonymousFn(af) => {
                let AnonymousFn { body, equal_to } = af;
                let FnSetBody {
                    params_def_with_set,
                    dom_facts,
                    ret_set,
                } = body;
                let params_def_with_set = params_def_with_set
                    .into_iter()
                    .map(|pg| {
                        let params = pg
                            .params
                            .into_iter()
                            .map(|p| if p == from { to.to_string() } else { p })
                            .collect();
                        match pg.param_type {
                            ParamGroupWithSetTypeEnum::Struct(struct_ty) => {
                                ParamGroupWithSet::new_struct(
                                    params,
                                    StructAsParamType::new(
                                        struct_ty.name,
                                        struct_ty
                                            .args
                                            .into_iter()
                                            .map(|arg| {
                                                Obj::replace_bound_identifier(*arg, from, to)
                                            })
                                            .collect(),
                                    ),
                                )
                            }
                            ParamGroupWithSetTypeEnum::Set(set) => ParamGroupWithSet::new(
                                params,
                                Obj::replace_bound_identifier(set, from, to),
                            ),
                        }
                    })
                    .collect();
                let dom_facts = dom_facts
                    .into_iter()
                    .map(|f| f.replace_bound_identifier(from, to))
                    .collect();
                let ret_set = Obj::replace_bound_identifier(*ret_set, from, to);
                let equal_to = Obj::replace_bound_identifier(*equal_to, from, to);
                AnonymousFn::new(params_def_with_set, dom_facts, ret_set, equal_to)
                    .expect("renaming a valid anonymous fn preserves object scope validity")
                    .into()
            }
            Obj::Cart(c) => Cart::new(
                c.args
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier(*b, from, to))
                    .collect(),
            )
            .into(),
            Obj::CartDim(x) => CartDim::new(Obj::replace_bound_identifier(*x.set, from, to)).into(),
            Obj::Proj(x) => Proj::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.dim, from, to),
            )
            .into(),
            Obj::TupleDim(x) => {
                TupleDim::new(Obj::replace_bound_identifier(*x.arg, from, to)).into()
            }
            Obj::Tuple(t) => Tuple::new(
                t.args
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier(*b, from, to))
                    .collect(),
            )
            .into(),
            Obj::Count(x) => Count::new(Obj::replace_bound_identifier(*x.set, from, to)).into(),
            Obj::Sum(x) => Sum::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
                Obj::replace_bound_identifier(*x.func, from, to),
            )
            .into(),
            Obj::Product(x) => Product::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
                Obj::replace_bound_identifier(*x.func, from, to),
            )
            .into(),
            Obj::Range(x) => Range::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
            )
            .into(),
            Obj::ClosedRange(x) => ClosedRange::new(
                Obj::replace_bound_identifier(*x.start, from, to),
                Obj::replace_bound_identifier(*x.end, from, to),
            )
            .into(),
            Obj::FnRange(x) => {
                FnRange::new(Obj::replace_bound_identifier(*x.fn_obj, from, to)).into()
            }
            Obj::FnDom(x) => FnDom::new(Obj::replace_bound_identifier(*x.fn_obj, from, to)).into(),
            Obj::FiniteSeqSet(x) => FiniteSeqSet::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.n, from, to),
            )
            .into(),
            Obj::SeqSet(x) => SeqSet::new(Obj::replace_bound_identifier(*x.set, from, to)).into(),
            Obj::FiniteSeqListObj(x) => FiniteSeqListObj::new(
                x.objs
                    .into_iter()
                    .map(|b| Obj::replace_bound_identifier(*b, from, to))
                    .collect(),
            )
            .into(),
            Obj::MatrixSet(x) => MatrixSet::new(
                Obj::replace_bound_identifier(*x.set, from, to),
                Obj::replace_bound_identifier(*x.row_len, from, to),
                Obj::replace_bound_identifier(*x.col_len, from, to),
            )
            .into(),
            Obj::MatrixListObj(x) => MatrixListObj::new(
                x.rows
                    .into_iter()
                    .map(|row| {
                        row.into_iter()
                            .map(|b| Obj::replace_bound_identifier(*b, from, to))
                            .collect()
                    })
                    .collect(),
            )
            .into(),
            Obj::MatrixAdd(x) => MatrixAdd::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::MatrixSub(x) => MatrixSub::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::MatrixMul(x) => MatrixMul::new(
                Obj::replace_bound_identifier(*x.left, from, to),
                Obj::replace_bound_identifier(*x.right, from, to),
            )
            .into(),
            Obj::MatrixScalarMul(x) => MatrixScalarMul::new(
                Obj::replace_bound_identifier(*x.scalar, from, to),
                Obj::replace_bound_identifier(*x.matrix, from, to),
            )
            .into(),
            Obj::MatrixPow(x) => MatrixPow::new(
                Obj::replace_bound_identifier(*x.base, from, to),
                Obj::replace_bound_identifier(*x.exponent, from, to),
            )
            .into(),
            Obj::Choose(x) => Choose::new(Obj::replace_bound_identifier(*x.set, from, to)).into(),
            Obj::ObjAtIndex(x) => ObjAtIndex::new(
                Obj::replace_bound_identifier(*x.obj, from, to),
                Obj::replace_bound_identifier(*x.index, from, to),
            )
            .into(),
            Obj::StandardSet(s) => s.into(),
            Obj::FamilyObj(f) => FamilyObj::new(
                f.name,
                f.params
                    .into_iter()
                    .map(|o| Obj::replace_bound_identifier(o, from, to))
                    .collect(),
            )
            .into(),
            Obj::FieldAccess(field_access) => {
                let left = if field_access.left == from {
                    to.to_string()
                } else {
                    field_access.left
                };
                FieldAccess::new(left, field_access.right).into()
            }
            Obj::StructInstance(instance) => {
                let instance = *instance;
                let name = StructAsParamType::new(
                    instance.name.name,
                    instance
                        .name
                        .args
                        .into_iter()
                        .map(|arg| Obj::replace_bound_identifier(*arg, from, to))
                        .collect(),
                );
                let fields_equal_to_what = instance
                    .fields_equal_to_what
                    .into_iter()
                    .map(|field| Obj::replace_bound_identifier(*field, from, to))
                    .collect();
                StructInstance::new(name, fields_equal_to_what).into()
            }
        }
    }
}

/// Replace in identifier / `mod::name` name-shaped [`Obj`] values only.
fn replace_bound_identifier_in_name_obj(obj: Obj, from: &str, to: &str) -> Obj {
    if from == to {
        return obj;
    }
    match obj {
        Obj::Atom(AtomObj::Identifier(i)) => {
            if i.name == from {
                Identifier::new(to.to_string()).into()
            } else {
                Obj::Atom(AtomObj::Identifier(i))
            }
        }
        Obj::Atom(AtomObj::IdentifierWithMod(m)) => {
            let name = if m.name == from {
                to.to_string()
            } else {
                m.name
            };
            Obj::from(IdentifierWithMod::new(m.mod_name, name))
        }
        _ => obj,
    }
}

fn replace_bound_identifier_in_fn_obj_head(head: FnObjHead, from: &str, to: &str) -> FnObjHead {
    if from == to {
        return head;
    }
    match head {
        FnObjHead::Identifier(i) => {
            FnObjHead::given_an_atom_return_a_fn_obj_head(replace_bound_identifier_in_name_obj(
                Obj::Atom(AtomObj::Identifier(i.clone())),
                from,
                to,
            ))
            .expect("name replace preserves fn head shape")
        }
        FnObjHead::IdentifierWithMod(m) => {
            FnObjHead::given_an_atom_return_a_fn_obj_head(replace_bound_identifier_in_name_obj(
                Obj::Atom(AtomObj::IdentifierWithMod(m.clone())),
                from,
                to,
            ))
            .expect("name replace preserves fn head shape")
        }
        FnObjHead::Forall(p) => {
            let name = if p.name == from {
                to.to_string()
            } else {
                p.name
            };
            ForallFreeParamObj::new(name).into()
        }
        FnObjHead::DefHeader(p) => {
            let name = if p.name == from {
                to.to_string()
            } else {
                p.name
            };
            DefHeaderFreeParamObj::new(name).into()
        }
        FnObjHead::Exist(p) => {
            let name = if p.name == from {
                to.to_string()
            } else {
                p.name
            };
            ExistFreeParamObj::new(name).into()
        }
        FnObjHead::SetBuilder(p) => {
            let name = if p.name == from {
                to.to_string()
            } else {
                p.name
            };
            SetBuilderFreeParamObj::new(name).into()
        }
        FnObjHead::FnSet(p) => {
            let name = if p.name == from {
                to.to_string()
            } else {
                p.name
            };
            FnSetFreeParamObj::new(name).into()
        }
        FnObjHead::AnonymousFnLiteral(a) => {
            let inner = (*a).clone();
            let replaced = Obj::replace_bound_identifier(Obj::AnonymousFn(inner), from, to);
            let Obj::AnonymousFn(new_af) = replaced else {
                unreachable!()
            };
            FnObjHead::AnonymousFnLiteral(Box::new(new_af))
        }
        FnObjHead::Induc(p) => {
            let name = if p.name == from {
                to.to_string()
            } else {
                p.name
            };
            ByInducFreeParamObj::new(name).into()
        }
        FnObjHead::DefAlgo(p) => {
            let name = if p.name == from {
                to.to_string()
            } else {
                p.name
            };
            DefAlgoFreeParamObj::new(name).into()
        }
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

impl fmt::Display for FnRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            FN_RANGE,
            braced_vec_to_string(&vec![self.fn_obj.as_ref()])
        )
    }
}

impl fmt::Display for FnDom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            FN_DOM,
            braced_vec_to_string(&vec![self.fn_obj.as_ref()])
        )
    }
}

impl fmt::Display for FiniteSeqSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            FINITE_SEQ,
            braced_vec_to_string(&vec![self.set.as_ref(), self.n.as_ref()])
        )
    }
}

impl fmt::Display for SeqSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            SEQ,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FiniteSeqListObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", LEFT_BRACKET)?;
        for (i, o) in self.objs.iter().enumerate() {
            if i > 0 {
                write!(f, "{} ", COMMA)?;
            }
            write!(f, "{}", o)?;
        }
        write!(f, "{}", RIGHT_BRACKET)
    }
}

impl fmt::Display for MatrixSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            MATRIX,
            braced_vec_to_string(&vec![
                self.set.as_ref(),
                self.row_len.as_ref(),
                self.col_len.as_ref(),
            ])
        )
    }
}

impl fmt::Display for MatrixListObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", LEFT_BRACKET)?;
        for (ri, row) in self.rows.iter().enumerate() {
            if ri > 0 {
                write!(f, "{} ", COMMA)?;
            }
            write!(f, "{}", LEFT_BRACKET)?;
            for (ci, o) in row.iter().enumerate() {
                if ci > 0 {
                    write!(f, "{} ", COMMA)?;
                }
                write!(f, "{}", o)?;
            }
            write!(f, "{}", RIGHT_BRACKET)?;
        }
        write!(f, "{}", RIGHT_BRACKET)
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

impl fmt::Display for Sum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            SUM,
            braced_vec_to_string(&vec![
                self.start.as_ref(),
                self.end.as_ref(),
                self.func.as_ref(),
            ])
        )
    }
}

impl fmt::Display for Product {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            PRODUCT,
            braced_vec_to_string(&vec![
                self.start.as_ref(),
                self.end.as_ref(),
                self.func.as_ref(),
            ])
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

pub fn fn_obj_to_string(head: &FnObjHead, body: &Vec<Vec<Box<Obj>>>) -> String {
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

impl fmt::Display for MatrixAdd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, MATRIX_ADD, self.right)
    }
}

impl fmt::Display for MatrixSub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, MATRIX_SUB, self.right)
    }
}

impl fmt::Display for MatrixMul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.left, MATRIX_MUL, self.right)
    }
}

impl fmt::Display for MatrixScalarMul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.scalar, MATRIX_SCALAR_MUL, self.matrix)
    }
}

impl fmt::Display for MatrixPow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", self.base, MATRIX_POW, self.exponent)
    }
}

impl fmt::Display for Abs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{}", ABS, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Log {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}{}{}",
            LOG, LEFT_BRACE, self.base, COMMA, self.arg, RIGHT_BRACE
        )
    }
}

impl fmt::Display for Max {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}{}{}",
            MAX, LEFT_BRACE, self.left, COMMA, self.right, RIGHT_BRACE
        )
    }
}

impl fmt::Display for Min {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}{}{}{}{}",
            MIN, LEFT_BRACE, self.left, COMMA, self.right, RIGHT_BRACE
        )
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

impl From<Identifier> for Obj {
    fn from(id: Identifier) -> Self {
        Obj::Atom(AtomObj::Identifier(id))
    }
}

impl From<usize> for Obj {
    fn from(n: usize) -> Self {
        Number::new(n.to_string()).into()
    }
}

impl From<Number> for Obj {
    fn from(n: Number) -> Self {
        Obj::Number(n)
    }
}

impl From<Add> for Obj {
    fn from(a: Add) -> Self {
        Obj::Add(a)
    }
}

impl From<MatrixAdd> for Obj {
    fn from(m: MatrixAdd) -> Self {
        Obj::MatrixAdd(m)
    }
}

impl From<MatrixSub> for Obj {
    fn from(m: MatrixSub) -> Self {
        Obj::MatrixSub(m)
    }
}

impl From<MatrixMul> for Obj {
    fn from(m: MatrixMul) -> Self {
        Obj::MatrixMul(m)
    }
}

impl From<MatrixScalarMul> for Obj {
    fn from(m: MatrixScalarMul) -> Self {
        Obj::MatrixScalarMul(m)
    }
}

impl From<MatrixPow> for Obj {
    fn from(m: MatrixPow) -> Self {
        Obj::MatrixPow(m)
    }
}

impl From<Sub> for Obj {
    fn from(s: Sub) -> Self {
        Obj::Sub(s)
    }
}

impl From<FnObj> for Obj {
    fn from(f: FnObj) -> Self {
        Obj::FnObj(f)
    }
}

impl From<Mul> for Obj {
    fn from(m: Mul) -> Self {
        Obj::Mul(m)
    }
}

impl From<Div> for Obj {
    fn from(d: Div) -> Self {
        Obj::Div(d)
    }
}

impl From<Mod> for Obj {
    fn from(m: Mod) -> Self {
        Obj::Mod(m)
    }
}

impl From<Pow> for Obj {
    fn from(p: Pow) -> Self {
        Obj::Pow(p)
    }
}

impl From<Abs> for Obj {
    fn from(a: Abs) -> Self {
        Obj::Abs(a)
    }
}

impl From<Log> for Obj {
    fn from(l: Log) -> Self {
        Obj::Log(l)
    }
}

impl From<Max> for Obj {
    fn from(m: Max) -> Self {
        Obj::Max(m)
    }
}

impl From<Min> for Obj {
    fn from(m: Min) -> Self {
        Obj::Min(m)
    }
}

impl From<Union> for Obj {
    fn from(u: Union) -> Self {
        Obj::Union(u)
    }
}

impl From<Intersect> for Obj {
    fn from(i: Intersect) -> Self {
        Obj::Intersect(i)
    }
}

impl From<SetMinus> for Obj {
    fn from(s: SetMinus) -> Self {
        Obj::SetMinus(s)
    }
}

impl From<SetDiff> for Obj {
    fn from(s: SetDiff) -> Self {
        Obj::SetDiff(s)
    }
}

impl From<Cup> for Obj {
    fn from(c: Cup) -> Self {
        Obj::Cup(c)
    }
}

impl From<Cap> for Obj {
    fn from(c: Cap) -> Self {
        Obj::Cap(c)
    }
}

impl From<PowerSet> for Obj {
    fn from(p: PowerSet) -> Self {
        Obj::PowerSet(p)
    }
}

impl From<ListSet> for Obj {
    fn from(l: ListSet) -> Self {
        Obj::ListSet(l)
    }
}

impl From<SetBuilder> for Obj {
    fn from(s: SetBuilder) -> Self {
        Obj::SetBuilder(s)
    }
}

impl From<Cart> for Obj {
    fn from(c: Cart) -> Self {
        Obj::Cart(c)
    }
}

impl From<CartDim> for Obj {
    fn from(c: CartDim) -> Self {
        Obj::CartDim(c)
    }
}

impl From<Proj> for Obj {
    fn from(p: Proj) -> Self {
        Obj::Proj(p)
    }
}

impl From<TupleDim> for Obj {
    fn from(t: TupleDim) -> Self {
        Obj::TupleDim(t)
    }
}

impl From<Tuple> for Obj {
    fn from(t: Tuple) -> Self {
        Obj::Tuple(t)
    }
}

impl From<Count> for Obj {
    fn from(c: Count) -> Self {
        Obj::Count(c)
    }
}

impl From<Sum> for Obj {
    fn from(s: Sum) -> Self {
        Obj::Sum(s)
    }
}

impl From<Product> for Obj {
    fn from(p: Product) -> Self {
        Obj::Product(p)
    }
}

impl From<Range> for Obj {
    fn from(r: Range) -> Self {
        Obj::Range(r)
    }
}

impl From<ClosedRange> for Obj {
    fn from(r: ClosedRange) -> Self {
        Obj::ClosedRange(r)
    }
}

impl From<FnRange> for Obj {
    fn from(r: FnRange) -> Self {
        Obj::FnRange(r)
    }
}

impl From<FnDom> for Obj {
    fn from(r: FnDom) -> Self {
        Obj::FnDom(r)
    }
}

impl From<FiniteSeqSet> for Obj {
    fn from(v: FiniteSeqSet) -> Self {
        Obj::FiniteSeqSet(v)
    }
}

impl From<SeqSet> for Obj {
    fn from(v: SeqSet) -> Self {
        Obj::SeqSet(v)
    }
}

impl From<FiniteSeqListObj> for Obj {
    fn from(v: FiniteSeqListObj) -> Self {
        Obj::FiniteSeqListObj(v)
    }
}

impl From<MatrixSet> for Obj {
    fn from(v: MatrixSet) -> Self {
        Obj::MatrixSet(v)
    }
}

impl From<MatrixListObj> for Obj {
    fn from(v: MatrixListObj) -> Self {
        Obj::MatrixListObj(v)
    }
}

impl From<Choose> for Obj {
    fn from(c: Choose) -> Self {
        Obj::Choose(c)
    }
}

impl From<ObjAtIndex> for Obj {
    fn from(o: ObjAtIndex) -> Self {
        Obj::ObjAtIndex(o)
    }
}

impl From<IdentifierWithMod> for Obj {
    fn from(m: IdentifierWithMod) -> Self {
        Obj::Atom(AtomObj::IdentifierWithMod(m))
    }
}

impl From<FamilyObj> for Obj {
    fn from(f: FamilyObj) -> Self {
        Obj::FamilyObj(f)
    }
}

impl From<FieldAccess> for Obj {
    fn from(f: FieldAccess) -> Self {
        Obj::FieldAccess(f)
    }
}

impl From<StructInstance> for Obj {
    fn from(s: StructInstance) -> Self {
        Obj::StructInstance(Box::new(s))
    }
}

impl From<StandardSet> for Obj {
    fn from(s: StandardSet) -> Self {
        Obj::StandardSet(s)
    }
}

impl Identifier {
    /// Build a name-shaped [`Obj`] (via [`AtomObj::Identifier`]). Parameter is String (not &str).
    pub fn mk(name: String) -> Obj {
        Identifier::new(name).into()
    }
}
