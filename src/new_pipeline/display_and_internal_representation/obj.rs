//! Obj and related leaf types: internal representation + display_string.

use super::helper::strip_identifier_id_tags;
use crate::new_pipeline::ast::obj::*;
use crate::new_pipeline::parse::keywords::*;

macro_rules! impl_display_pair {
    () => {
        pub fn display_string(&self) -> String {
            strip_identifier_id_tags(&self.internal_representation())
        }
    };
}

impl Obj {
    pub fn internal_representation(&self) -> String {
        fn precedence(o: &Obj) -> u8 {
            match o {
                Obj::Add(_) | Obj::Sub(_) => 3,
                Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) => 2,
                Obj::Pow(_)
                | Obj::Abs(_)
                | Obj::Sin(_)
                | Obj::Arcsin(_)
                | Obj::Cos(_)
                | Obj::Tan(_)
                | Obj::Cot(_)
                | Obj::RealPart(_)
                | Obj::ImaginaryPart(_)
                | Obj::ComplexAbs(_)
                | Obj::Sqrt(_)
                | Obj::Log(_)
                | Obj::Lcm(_)
                | Obj::Quot(_)
                | Obj::Floor(_)
                | Obj::Ceil(_)
                | Obj::Min(_)
                | Obj::Max(_)
                | Obj::Exp(_)
                | Obj::Ln(_)
                | Obj::Sign(_)
                | Obj::Factorial(_) => 1,
                _ => 0,
            }
        }

        fn fmt_with_prec(o: &Obj, parent_precedent: u8) -> String {
            let precedent = precedence(o);
            let need_parens = parent_precedent != 0 && precedent != 0 && precedent > parent_precedent;
            let mut s = String::new();
            if need_parens {
                s.push_str(LEFT_PAREN);
            }
            match o {
                Obj::Add(a) => {
                    s.push_str(&fmt_with_prec(a.left.as_ref(), 3));
                    s.push_str(&format!(" {} ", ADD));
                    s.push_str(&fmt_with_prec(a.right.as_ref(), 2));
                }
                Obj::Sub(sub) => {
                    s.push_str(&fmt_with_prec(sub.left.as_ref(), 2));
                    s.push_str(&format!(" {} ", SUB));
                    s.push_str(&fmt_with_prec(sub.right.as_ref(), 2));
                }
                Obj::Mul(m) => {
                    s.push_str(&fmt_with_prec(m.left.as_ref(), 2));
                    s.push_str(&format!(" {} ", MUL));
                    s.push_str(&fmt_with_prec(m.right.as_ref(), 2));
                }
                Obj::Div(d) => {
                    s.push_str(&fmt_with_prec(d.left.as_ref(), 2));
                    s.push_str(&format!(" {} ", DIV));
                    s.push_str(&fmt_with_prec(d.right.as_ref(), 1));
                }
                Obj::Mod(m) => {
                    s.push_str(&fmt_with_prec(m.left.as_ref(), 2));
                    s.push_str(&format!(" {} ", MOD_OP));
                    s.push_str(&fmt_with_prec(m.right.as_ref(), 2));
                }
                Obj::Quot(x) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        QUOT,
                        LEFT_PAREN,
                        fmt_with_prec(x.left.as_ref(), 0),
                        COMMA,
                        fmt_with_prec(x.right.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Gcd(g) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        GCD,
                        LEFT_PAREN,
                        fmt_with_prec(g.left.as_ref(), 0),
                        COMMA,
                        fmt_with_prec(g.right.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Lcm(x) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        LCM,
                        LEFT_PAREN,
                        fmt_with_prec(x.left.as_ref(), 0),
                        COMMA,
                        fmt_with_prec(x.right.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Floor(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        FLOOR,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Ceil(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        CEIL,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Min(x) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        MIN,
                        LEFT_PAREN,
                        fmt_with_prec(x.left.as_ref(), 0),
                        COMMA,
                        fmt_with_prec(x.right.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Max(x) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        MAX,
                        LEFT_PAREN,
                        fmt_with_prec(x.left.as_ref(), 0),
                        COMMA,
                        fmt_with_prec(x.right.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Exp(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        EXP,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Ln(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        LN,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Sign(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        SIGN,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Factorial(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        FACTORIAL,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Pow(p) => {
                    s.push_str(&fmt_with_prec(p.base.as_ref(), 1));
                    s.push_str(&format!(" {} ", POW));
                    s.push_str(&fmt_with_prec(p.exponent.as_ref(), 1));
                }
                Obj::Abs(a) => {
                    s.push_str(&format!(
                        "{} {}{}{}",
                        ABS,
                        LEFT_PAREN,
                        fmt_with_prec(a.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Sin(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        SIN,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Arcsin(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        ARCSIN,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Cos(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        COS,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Tan(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        TAN,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Cot(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        COT,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::RealPart(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        RE,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::ImaginaryPart(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        IMG,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::ComplexAbs(x) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        C_ABS,
                        LEFT_PAREN,
                        fmt_with_prec(x.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Sqrt(sq) => {
                    s.push_str(&format!(
                        "{} {}{}{}",
                        SQRT,
                        LEFT_PAREN,
                        fmt_with_prec(sq.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Log(l) => {
                    s.push_str(&format!(
                        "{} {}{}{} {}{}",
                        LOG,
                        LEFT_PAREN,
                        fmt_with_prec(l.base.as_ref(), 0),
                        COMMA,
                        fmt_with_prec(l.arg.as_ref(), 0),
                        RIGHT_PAREN
                    ));
                }
                Obj::Union(x) => s.push_str(&x.internal_representation()),
                Obj::Intersect(x) => s.push_str(&x.internal_representation()),
                Obj::SetMinus(x) => s.push_str(&x.internal_representation()),
                Obj::BigUnion(x) => s.push_str(&x.internal_representation()),
                Obj::BigIntersect(x) => s.push_str(&x.internal_representation()),
                Obj::IndexUnion(x) => s.push_str(&x.internal_representation()),
                Obj::IndexIntersect(x) => s.push_str(&x.internal_representation()),
                Obj::Atom(x) => s.push_str(&x.internal_representation()),
                Obj::FnObj(x) => s.push_str(&x.internal_representation()),
                Obj::Number(x) => s.push_str(&x.internal_representation()),
                Obj::ImaginaryUnit(_) => s.push_str(I),
                Obj::EulerNumber(_) => s.push_str(E),
                Obj::Pi(_) => s.push_str(PI),
                Obj::ListSet(x) => s.push_str(&x.internal_representation()),
                Obj::SetBuilder(x) => s.push_str(&x.internal_representation()),
                Obj::FnSet(x) => s.push_str(&x.internal_representation()),
                Obj::AnonymousFn(x) => s.push_str(&x.internal_representation()),
                Obj::StandardSet(x) => s.push_str(&x.internal_representation()),
                Obj::Cart(x) => s.push_str(&x.internal_representation()),
                Obj::CartDim(x) => s.push_str(&x.internal_representation()),
                Obj::Proj(x) => s.push_str(&x.internal_representation()),
                Obj::TupleDim(x) => s.push_str(&x.internal_representation()),
                Obj::Tuple(x) => s.push_str(&x.internal_representation()),
                Obj::FiniteSetSize(x) => s.push_str(&x.internal_representation()),
                Obj::FiniteSetMax(x) => s.push_str(&x.internal_representation()),
                Obj::FiniteSetMin(x) => s.push_str(&x.internal_representation()),
                Obj::FnRange(x) => s.push_str(&x.internal_representation()),
                Obj::Replacement(x) => s.push_str(&x.internal_representation()),
                Obj::Sum(x) => s.push_str(&x.internal_representation()),
                Obj::SumOfFiniteSet(x) => s.push_str(&x.internal_representation()),
                Obj::Product(x) => s.push_str(&x.internal_representation()),
                Obj::ProductOfFiniteSet(x) => s.push_str(&x.internal_representation()),
                Obj::Reduce(x) => s.push_str(&x.internal_representation()),
                Obj::FiniteSetReduce(x) => s.push_str(&x.internal_representation()),
                Obj::Range(x) => s.push_str(&x.internal_representation()),
                Obj::ClosedRange(x) => s.push_str(&x.internal_representation()),
                Obj::FiniteSeqSet(x) => s.push_str(&x.internal_representation()),
                Obj::SeqSet(x) => s.push_str(&x.internal_representation()),
                Obj::FiniteSeqListObj(x) => s.push_str(&x.internal_representation()),
                Obj::PowerSet(x) => s.push_str(&x.internal_representation()),
                Obj::GeneralCart(x) => s.push_str(&x.internal_representation()),
                Obj::ObjAtIndex(x) => s.push_str(&x.internal_representation()),
                Obj::StructObj(x) => s.push_str(&x.internal_representation()),
                Obj::ObjAsStructInstanceWithFieldAccess(x) => s.push_str(&x.internal_representation()),
                Obj::InstantiatedTemplateObj(x) => s.push_str(&x.internal_representation()),
                Obj::OneSideInfinityIntervalObj(x) => s.push_str(&x.internal_representation()),
                Obj::IntervalObj(x) => s.push_str(&x.internal_representation()),
            }
            if need_parens {
                s.push_str(RIGHT_PAREN);
            }
            s
        }

        fmt_with_prec(self, 0)
    }

    pub fn display_string(&self) -> String {
        strip_identifier_id_tags(&self.internal_representation())
    }
}

impl Identifier {
    // Only unusual bit of internal strings: embed IdentifierId as #<id>#name.
    pub fn internal_representation(&self) -> String {
        format!("#{}#{}", self.identifier_id.value(), self.name)
    }
    impl_display_pair!();
}

impl IdentifierWithMod {
    pub fn internal_representation(&self) -> String {
        format!("{}{}#{}#{}",
            self.mod_name,
            MOD_SIGN,
            self.identifier_id.value(),
            self.name)
    }
    impl_display_pair!();
}

impl BoundParamObj {
    pub fn internal_representation(&self) -> String {
        format!("{}", self.name)
    }
    impl_display_pair!();
}

impl AtomObj {
    pub fn internal_representation(&self) -> String {

        match self {
            AtomObj::Identifier(x) => x.internal_representation(),
            AtomObj::IdentifierWithMod(x) => x.internal_representation(),
            AtomObj::Bound(x) => x.internal_representation(),
        }
    
    }
    impl_display_pair!();
}

impl FnObjHead {
    pub fn internal_representation(&self) -> String {
        match self {
            FnObjHead::Identifier(x) => x.internal_representation(),
            FnObjHead::IdentifierWithMod(x) => x.internal_representation(),
            FnObjHead::Bound(x) => x.internal_representation(),
            FnObjHead::AnonymousFnLiteral(a) => a.internal_representation(),
            FnObjHead::FiniteSeqListObj(v) => v.internal_representation(),
            FnObjHead::ObjAtIndex(v) => v.internal_representation(),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => v.internal_representation(),
            FnObjHead::InstantiatedTemplateObj(t) => t.internal_representation(),
        }
    }
    impl_display_pair!();
}

impl FnObj {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.head.internal_representation());
        for group in self.body.iter() {
            { out.push_str(LEFT_PAREN); out.push_str(&group.iter().map(|o| o.internal_representation()).collect::<Vec<_>>().join(", ")); out.push_str(RIGHT_PAREN); };
        }
        out
    }
    impl_display_pair!();
}

impl Number {
    pub fn internal_representation(&self) -> String {
        format!("{}", self.normalized_value)
    }
    impl_display_pair!();
}

macro_rules! impl_obj_kw_call {
    ($ty:ty, $kw:expr, $($field:ident),+) => {
        impl $ty {
            pub fn internal_representation(&self) -> String {
                let parts = vec![$(self.$field.internal_representation()),+];
                format!("{}{}{}{}", $kw, LEFT_PAREN, parts.join(", "), RIGHT_PAREN)
            }
            impl_display_pair!();
        }
    };
}

macro_rules! impl_obj_kw_unary {
    ($ty:ty, $kw:expr, $field:ident) => {
        impl $ty {
            pub fn internal_representation(&self) -> String {
                format!(
                    "{}{}{}{}",
                    $kw,
                    LEFT_PAREN,
                    self.$field.internal_representation(),
                    RIGHT_PAREN
                )
            }
            impl_display_pair!();
        }
    };
}

macro_rules! impl_obj_kw_binary {
    ($ty:ty, $kw:expr, $left:ident, $right:ident) => {
        impl $ty {
            pub fn internal_representation(&self) -> String {
                format!(
                    "{}{}{}{} {}{}",
                    $kw,
                    LEFT_PAREN,
                    self.$left.internal_representation(),
                    COMMA,
                    self.$right.internal_representation(),
                    RIGHT_PAREN
                )
            }
            impl_display_pair!();
        }
    };
}

impl_obj_kw_call!(Union, UNION, left, right);

impl_obj_kw_call!(Intersect, INTERSECT, left, right);

impl_obj_kw_call!(SetMinus, SET_MINUS, left, right);

impl_obj_kw_call!(BigUnion, BIG_UNION, left);

impl_obj_kw_call!(BigIntersect, BIG_INTERSECT, left);

impl IndexUnion {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}{}", INDEX_UNION, LEFT_PAREN));
        out.push_str(&self.index_set.internal_representation());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.ambient_set.internal_representation());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.family_fn.internal_representation());
        out.push_str(&format!("{}", RIGHT_PAREN));
        out
    }
    impl_display_pair!();
}
impl IndexIntersect {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}{}", INDEX_INTERSECT, LEFT_PAREN));
        out.push_str(&self.index_set.internal_representation());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.ambient_set.internal_representation());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.family_fn.internal_representation());
        out.push_str(&format!("{}", RIGHT_PAREN));
        out
    }
    impl_display_pair!();
}
impl_obj_kw_call!(PowerSet, POWER_SET, set);

impl ListSet {
    pub fn internal_representation(&self) -> String {
        format!(
            "{}{}{}",
            LEFT_CURLY,
            self.list
                .iter()
                .map(|o| o.internal_representation())
                .collect::<Vec<_>>()
                .join(", "),
            RIGHT_CURLY
        )
    }
    impl_display_pair!();
}
impl SetBuilder {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}", LEFT_CURLY));
        out.push_str(&format!("{}", self.param_binding));
        out.push_str(&format!(" "));
        out.push_str(&self.param_set.internal_representation());
        out.push_str(&format!("{}", COLON));
        out.push_str(&format!(" "));
        let fact_parts: Vec<String> = self
            .facts
            .iter()
            .map(|fact| fact.internal_representation())
            .collect();
        out.push_str(&fact_parts.join(", "));
        out.push_str(&format!("{}", RIGHT_CURLY));
        out
    }
    impl_display_pair!();
}
impl FnSetBody {
    pub fn internal_representation(&self) -> String {
        let params: Vec<String> = self
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.internal_representation())
            .collect();
        let dom: Vec<String> = self
            .dom_facts
            .iter()
            .map(|fact| fact.internal_representation())
            .collect();
        let mut out = format!("{} ", FN);
        out.push_str(LEFT_PAREN);
        if !params.is_empty() && !dom.is_empty() {
            out.push_str(&params.join(", "));
            out.push_str(&format!("{} ", COLON));
            out.push_str(&dom.join(", "));
        } else if dom.is_empty() {
            out.push_str(&params.join(", "));
        } else if params.is_empty() {
            out.push_str(COLON);
            out.push_str(&dom.join(", "));
        }
        out.push_str(RIGHT_PAREN);
        out.push(' ');
        out.push_str(&self.ret_set.internal_representation());
        out
    }
    impl_display_pair!();
}
impl FnSet {
    pub fn internal_representation(&self) -> String {
        self.body.internal_representation()
    }
    impl_display_pair!();
}
impl AnonymousFn {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.body.internal_representation());
        out.push_str(&format!("{}", LEFT_CURLY));
        out.push_str(&self.equal_to.internal_representation());
        out.push_str(&format!("{}", RIGHT_CURLY));
    
        out
    }
    impl_display_pair!();
}
impl StandardSet {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        let s = match self {
            StandardSet::NPos => N_POS,
            StandardSet::N => N,
            StandardSet::Q => Q,
            StandardSet::Z => Z,
            StandardSet::R => R,
            StandardSet::C => C,
            StandardSet::QPos => Q_POS,
            StandardSet::RPos => R_POS,
            StandardSet::QNeg => Q_NEG,
            StandardSet::ZNeg => Z_NEG,
            StandardSet::RNeg => R_NEG,
            StandardSet::QStar => Q_STAR,
            StandardSet::ZStar => Z_STAR,
            StandardSet::RStar => R_STAR,
            StandardSet::CStar => C_STAR,
        };
        out.push_str(&format!("{}", s));
    
        out
    }
    impl_display_pair!();
}

impl Cart {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}", CART));
        { out.push_str(LEFT_PAREN); out.push_str(&self.args.iter().map(|o| o.internal_representation()).collect::<Vec<_>>().join(", ")); out.push_str(RIGHT_PAREN); };
    
        out
    }
    impl_display_pair!();
}
impl_obj_kw_call!(CartDim, CART_DIM, set);

impl_obj_kw_call!(Proj, PROJ, set, dim);

impl_obj_kw_call!(TupleDim, TUPLE_DIM, arg);

impl Tuple {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        { out.push_str(LEFT_PAREN); out.push_str(&self.args.iter().map(|o| o.internal_representation()).collect::<Vec<_>>().join(", ")); out.push_str(RIGHT_PAREN); };
    
        out
    }
    impl_display_pair!();
}
impl GeneralCart {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}{}", GENERAL_CART, LEFT_PAREN));
        out.push_str(&self.index_set.internal_representation());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.family_set.internal_representation());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.family_fn.internal_representation());
        out.push_str(&format!("{}", RIGHT_PAREN));
        out
    }
    impl_display_pair!();
}
impl_obj_kw_call!(FiniteSetSize, FINITE_SET_SIZE, set);

impl_obj_kw_call!(FiniteSetMax, FINITE_SET_MAX, set);

impl_obj_kw_call!(FiniteSetMin, FINITE_SET_MIN, set);

impl_obj_kw_call!(FnRange, FN_RANGE, function);

impl Replacement {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}{}", REPLACEMENT, LEFT_PAREN));
        out.push_str(&self.prop_name.internal_representation());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.source_set.internal_representation());
        out.push_str(&format!("{}", RIGHT_PAREN));
        out
    }
    impl_display_pair!();
}
impl_obj_kw_call!(Sum, SUM, start, end, func);

impl_obj_kw_call!(SumOfFiniteSet, FINITE_SET_SUM, set, func);

impl_obj_kw_call!(Product, PRODUCT, start, end, func);

impl_obj_kw_call!(ProductOfFiniteSet, FINITE_SET_PRODUCT, set, func);

impl_obj_kw_call!(Reduce, REDUCE, start, end, func, op, seed);

impl_obj_kw_call!(FiniteSetReduce, FINITE_SET_REDUCE, set, func, op, seed);

impl_obj_kw_call!(Range, RANGE, start, end);

impl_obj_kw_call!(ClosedRange, CLOSED_RANGE, start, end);

impl_obj_kw_call!(FiniteSeqSet, FINITE_SEQ, set, n);

impl_obj_kw_call!(SeqSet, SEQ, set);

impl FiniteSeqListObj {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}", LEFT_BRACKET));
        out.push_str(&self.objs.iter().map(|o| o.internal_representation()).collect::<Vec<_>>().join(", "));
        out.push_str(&format!("{}", RIGHT_BRACKET));
        out
    }
    impl_display_pair!();
}
impl ObjAtIndex {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.obj.internal_representation());
        out.push_str(&format!("{}", LEFT_BRACKET));
        out.push_str(&self.index.internal_representation());
        out.push_str(&format!("{}", RIGHT_BRACKET));
    
        out
    }
    impl_display_pair!();
}
impl StructObj {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(STRUCT_VIEW_PREFIX);
        out.push_str(&self.name.internal_representation());
        if !self.params.is_empty() {
            out.push_str(LESS);
            out.push_str(
                &self
                    .params
                    .iter()
                    .map(|o| o.internal_representation())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            out.push_str(GREATER);
        }
        out
    }
    impl_display_pair!();
}
impl ObjAsStructInstanceWithFieldAccess {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.obj.internal_representation());
        out.push_str(&format!("{}{}", DOT_AKA_FIELD_ACCESS_SIGN, self.field_name));
    
        out
    }
    impl_display_pair!();
}
impl InstantiatedTemplateObj {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}", TEMPLATE_INSTANCE_PREFIX));
        out.push_str(&self.template_name.internal_representation());
        out.push_str(&format!("{}", LESS));
        out.push_str(&self.args.iter().map(|o| o.internal_representation()).collect::<Vec<_>>().join(", "));
        out.push_str(&format!("{}", GREATER));
        out
    }
    impl_display_pair!();
}
impl IntervalObj {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        let (left_delimiter, right_delimiter, body) = match self {
            IntervalObj::LeftOpenRightOpen(s) => (LEFT_PAREN, RIGHT_PAREN, s),
            IntervalObj::LeftOpenRightClosed(s) => (LEFT_PAREN, RIGHT_BRACKET, s),
            IntervalObj::LeftClosedRightOpen(s) => (LEFT_BRACKET, RIGHT_PAREN, s),
            IntervalObj::LeftClosedRightClosed(s) => (LEFT_BRACKET, RIGHT_BRACKET, s),
        };
        out.push_str(&format!("{}{}", INTERVAL_LITERAL_PREFIX, left_delimiter));
        out.push_str(&body.start.internal_representation());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&body.end.internal_representation());
        out.push_str(&format!("{}", right_delimiter));
    
        out
    }
    impl_display_pair!();
}
impl OneSideInfinityIntervalObj {
    pub fn internal_representation(&self) -> String {
        match self {
            OneSideInfinityIntervalObj::LeftOpen(interval) => {
                format!("'({},)", interval.start.as_ref().internal_representation())
            }
            OneSideInfinityIntervalObj::LeftClosed(interval) => {
                format!("'[{},)", interval.start.as_ref().internal_representation())
            }
            OneSideInfinityIntervalObj::RightOpen(interval) => {
                format!("'(,{})", interval.start.as_ref().internal_representation())
            }
            OneSideInfinityIntervalObj::RightClosed(interval) => {
                format!("'(,{}]", interval.start.as_ref().internal_representation())
            }
        }
    }
    impl_display_pair!();
}
// Binary/unary arithmetic leaf Display impls (surface via Obj precedence path primarily).
impl Add {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.left.internal_representation());
        out.push_str(&format!(" {} ", ADD));
        out.push_str(&self.right.internal_representation());
    
        out
    }
    impl_display_pair!();
}
impl Sub {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.left.internal_representation());
        out.push_str(&format!(" {} ", SUB));
        out.push_str(&self.right.internal_representation());
    
        out
    }
    impl_display_pair!();
}
impl Mul {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.left.internal_representation());
        out.push_str(&format!(" {} ", MUL));
        out.push_str(&self.right.internal_representation());
    
        out
    }
    impl_display_pair!();
}
impl Div {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.left.internal_representation());
        out.push_str(&format!(" {} ", DIV));
        out.push_str(&self.right.internal_representation());
    
        out
    }
    impl_display_pair!();
}
impl Mod {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.left.internal_representation());
        out.push_str(&format!(" {} ", MOD_OP));
        out.push_str(&self.right.internal_representation());
    
        out
    }
    impl_display_pair!();
}
impl_obj_kw_binary!(Quot, QUOT, left, right);

impl_obj_kw_binary!(Gcd, GCD, left, right);

impl_obj_kw_binary!(Lcm, LCM, left, right);

impl Pow {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.base.internal_representation());
        out.push_str(&format!(" {} ", POW));
        out.push_str(&self.exponent.internal_representation());
    
        out
    }
    impl_display_pair!();
}
impl_obj_kw_unary!(Floor, FLOOR, arg);

impl_obj_kw_unary!(Ceil, CEIL, arg);

impl_obj_kw_binary!(Min, MIN, left, right);

impl_obj_kw_binary!(Max, MAX, left, right);

impl_obj_kw_unary!(Exp, EXP, arg);

impl_obj_kw_unary!(Ln, LN, arg);

impl_obj_kw_unary!(Sign, SIGN, arg);

impl_obj_kw_unary!(Factorial, FACTORIAL, arg);

impl Abs {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{} {}", ABS, LEFT_PAREN));
        out.push_str(&self.arg.internal_representation());
        out.push_str(&format!("{}", RIGHT_PAREN));
        out
    }
    impl_display_pair!();
}
impl_obj_kw_unary!(Sin, SIN, arg);

impl_obj_kw_unary!(Arcsin, ARCSIN, arg);

impl_obj_kw_unary!(Cos, COS, arg);

impl_obj_kw_unary!(Tan, TAN, arg);

impl_obj_kw_unary!(Cot, COT, arg);

impl_obj_kw_unary!(RealPart, RE, arg);

impl_obj_kw_unary!(ImaginaryPart, IMG, arg);

impl_obj_kw_unary!(ComplexAbs, C_ABS, arg);

impl Sqrt {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{} {}", SQRT, LEFT_PAREN));
        out.push_str(&self.arg.internal_representation());
        out.push_str(&format!("{}", RIGHT_PAREN));
        out
    }
    impl_display_pair!();
}
impl Log {
    pub fn internal_representation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{} {}", LOG, LEFT_PAREN));
        out.push_str(&self.base.internal_representation());
        out.push_str(&format!("{} ", COMMA));
        out.push_str(&self.arg.internal_representation());
        out.push_str(&format!("{}", RIGHT_PAREN));
        out
    }
    impl_display_pair!();
}
impl ImaginaryUnit {
    pub fn internal_representation(&self) -> String {
        format!("{}", I)
    }
    impl_display_pair!();
}
impl EulerNumber {
    pub fn internal_representation(&self) -> String {
        format!("{}", E)
    }
    impl_display_pair!();
}
impl Pi {
    pub fn internal_representation(&self) -> String {
        format!("{}", PI)
    }
    impl_display_pair!();
}
