//! Obj and related leaf types: IR + display_string.

use super::types::ObjIR;
use crate::new_pipeline::ast::obj::*;
use crate::new_pipeline::parse::keywords::*;

macro_rules! impl_display_pair {
    () => {
        pub fn display_string(&self) -> String {
            self.ir().display_string()
        }
    };
}

impl Obj {
    pub fn ir(&self) -> ObjIR {
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
            let need_parens =
                parent_precedent != 0 && precedent != 0 && precedent > parent_precedent;
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
                Obj::Union(x) => s.push_str(&x.ir()),
                Obj::Intersect(x) => s.push_str(&x.ir()),
                Obj::SetMinus(x) => s.push_str(&x.ir()),
                Obj::BigUnion(x) => s.push_str(&x.ir()),
                Obj::BigIntersect(x) => s.push_str(&x.ir()),
                Obj::IndexUnion(x) => s.push_str(&x.ir()),
                Obj::IndexIntersect(x) => s.push_str(&x.ir()),
                Obj::Identifier(x) => s.push_str(&x.ir()),
                Obj::FnObj(x) => s.push_str(&x.ir()),
                Obj::Number(x) => s.push_str(&x.ir()),
                Obj::ImaginaryUnit(_) => s.push_str(I),
                Obj::EulerNumber(_) => s.push_str(E),
                Obj::Pi(_) => s.push_str(PI),
                Obj::ListSet(x) => s.push_str(&x.ir()),
                Obj::SetBuilder(x) => s.push_str(&x.ir()),
                Obj::FnSet(x) => s.push_str(&x.ir()),
                Obj::AnonymousFn(x) => s.push_str(&x.ir()),
                Obj::StandardSet(x) => s.push_str(&x.ir()),
                Obj::Cart(x) => s.push_str(&x.ir()),
                Obj::CartDim(x) => s.push_str(&x.ir()),
                Obj::Proj(x) => s.push_str(&x.ir()),
                Obj::TupleDim(x) => s.push_str(&x.ir()),
                Obj::Tuple(x) => s.push_str(&x.ir()),
                Obj::FiniteSetSize(x) => s.push_str(&x.ir()),
                Obj::FiniteSetMax(x) => s.push_str(&x.ir()),
                Obj::FiniteSetMin(x) => s.push_str(&x.ir()),
                Obj::FnRange(x) => s.push_str(&x.ir()),
                Obj::Replacement(x) => s.push_str(&x.ir()),
                Obj::Sum(x) => s.push_str(&x.ir()),
                Obj::SumOfFiniteSet(x) => s.push_str(&x.ir()),
                Obj::Product(x) => s.push_str(&x.ir()),
                Obj::ProductOfFiniteSet(x) => s.push_str(&x.ir()),
                Obj::Reduce(x) => s.push_str(&x.ir()),
                Obj::FiniteSetReduce(x) => s.push_str(&x.ir()),
                Obj::Range(x) => s.push_str(&x.ir()),
                Obj::ClosedRange(x) => s.push_str(&x.ir()),
                Obj::FiniteSeqSet(x) => s.push_str(&x.ir()),
                Obj::SeqSet(x) => s.push_str(&x.ir()),
                Obj::FiniteSeqListObj(x) => s.push_str(&x.ir()),
                Obj::PowerSet(x) => s.push_str(&x.ir()),
                Obj::GeneralCart(x) => s.push_str(&x.ir()),
                Obj::ObjAtIndex(x) => s.push_str(&x.ir()),
                Obj::StructObj(x) => s.push_str(&x.ir()),
                Obj::ObjAsStructInstanceWithFieldAccess(x) => {
                    s.push_str(&x.ir())
                }
                Obj::InstantiatedTemplateObj(x) => s.push_str(&x.ir()),
                Obj::OneSideInfinityIntervalObj(x) => s.push_str(&x.ir()),
                Obj::IntervalObj(x) => s.push_str(&x.ir()),
            }
            if need_parens {
                s.push_str(RIGHT_PAREN);
            }
            s
        }

        ObjIR(fmt_with_prec(self, 0))
    }

    pub fn display_string(&self) -> String {
        match self {
            Obj::Identifier(a) => a.display_string(),
            Obj::SetBuilder(x) => x.display_string(),
            Obj::FnSet(x) => x.display_string(),
            Obj::AnonymousFn(x) => x.display_string(),
            _ => self.ir().display_string(),
        }
    }
}

impl Identifier {
    pub fn ir(&self) -> ObjIR {
        ObjIR(self.name.clone())
    }
    pub fn display_string(&self) -> String {
        self.name.clone()
    }
}

impl IdentifierObj {
    pub fn ir(&self) -> ObjIR {
        ObjIR(self.display_string())
    }
    pub fn display_string(&self) -> String {
        match self {
            IdentifierObj::Plain { name } => name.clone(),
            IdentifierObj::WithMod { mod_name, name } => {
                format!("{}{}{}", mod_name, MOD_SIGN, name)
            }
            IdentifierObj::WithModAndExport {
                mod_name,
                export_name,
                name,
            } => format!(
                "{}{}{}{}{}",
                mod_name, MOD_SIGN, export_name, MOD_SIGN, name
            ),
        }
    }
}

impl FnObjHead {
    pub fn ir(&self) -> ObjIR {
        match self {
            FnObjHead::Identifier(x) => x.ir(),
            FnObjHead::AnonymousFnLiteral(a) => a.ir(),
            FnObjHead::FiniteSeqListObj(v) => v.ir(),
            FnObjHead::ObjAtIndex(v) => v.ir(),
            FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => v.ir(),
            FnObjHead::InstantiatedTemplateObj(t) => t.ir(),
        }
    }
    impl_display_pair!();
}

impl FnObj {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.head.ir());
        for group in self.body.iter() {
            {
                out.push_str(LEFT_PAREN);
                out.push_str(
                    &group
                        .iter()
                        .map(|o| o.ir())
                        .collect::<Vec<_>>()
                        .join(", "),
                );
                out.push_str(RIGHT_PAREN);
            };
        }
        ObjIR(out)
    }
    impl_display_pair!();
}

impl Number {
    pub fn ir(&self) -> ObjIR {
        ObjIR(self.normalized_value.clone())
    }
    impl_display_pair!();
}

macro_rules! impl_obj_kw_call {
    ($ty:ty, $kw:expr, $($field:ident),+) => {
        impl $ty {
            pub fn ir(&self) -> ObjIR {
                let parts = vec![$(self.$field.ir()),+];
                ObjIR(format!("{}{}{}{}", $kw, LEFT_PAREN, parts.join(", "), RIGHT_PAREN))
            }
            impl_display_pair!();
        }
    };
}

macro_rules! impl_obj_kw_unary {
    ($ty:ty, $kw:expr, $field:ident) => {
        impl $ty {
            pub fn ir(&self) -> ObjIR {
                ObjIR(format!(
                    "{}{}{}{}",
                    $kw,
                    LEFT_PAREN,
                    self.$field.ir(),
                    RIGHT_PAREN
                ))
            }
            impl_display_pair!();
        }
    };
}

macro_rules! impl_obj_kw_binary {
    ($ty:ty, $kw:expr, $left:ident, $right:ident) => {
        impl $ty {
            pub fn ir(&self) -> ObjIR {
                ObjIR(format!(
                    "{}{}{}{} {}{}",
                    $kw,
                    LEFT_PAREN,
                    self.$left.ir(),
                    COMMA,
                    self.$right.ir(),
                    RIGHT_PAREN
                ))
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
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}{}", INDEX_UNION, LEFT_PAREN));
        out.push_str(&self.index_set.ir());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.ambient_set.ir());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.family_fn.ir());
        out.push_str(&format!("{}", RIGHT_PAREN));
        ObjIR(out)
    }
    impl_display_pair!();
}
impl IndexIntersect {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}{}", INDEX_INTERSECT, LEFT_PAREN));
        out.push_str(&self.index_set.ir());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.ambient_set.ir());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.family_fn.ir());
        out.push_str(&format!("{}", RIGHT_PAREN));
        ObjIR(out)
    }
    impl_display_pair!();
}
impl_obj_kw_call!(PowerSet, POWER_SET, set);

impl ListSet {
    pub fn ir(&self) -> ObjIR {
        ObjIR(format!(
            "{}{}{}",
            LEFT_CURLY,
            self.list
                .iter()
                .map(|o| o.ir())
                .collect::<Vec<_>>()
                .join(", "),
            RIGHT_CURLY
        ))
    }
    impl_display_pair!();
}
impl SetBuilderBody {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}", LEFT_CURLY));
        out.push_str(&self.param_binding.ir());
        out.push_str(&format!(" "));
        out.push_str(&self.param_set.ir());
        out.push_str(&format!("{}", COLON));
        out.push_str(&format!(" "));
        let fact_parts: Vec<_> = self.facts.iter().map(|fact| fact.ir()).collect();
        out.push_str(&fact_parts.join(", "));
        out.push_str(&format!("{}", RIGHT_CURLY));
        ObjIR(out)
    }
    pub fn display_string(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{}", LEFT_CURLY));
        out.push_str(&self.param_binding.display_string());
        out.push_str(&format!(" "));
        out.push_str(&self.param_set.display_string());
        out.push_str(&format!("{}", COLON));
        out.push_str(&format!(" "));
        let fact_parts: Vec<_> = self
            .facts
            .iter()
            .map(|fact| fact.display_string())
            .collect();
        out.push_str(&fact_parts.join(", "));
        out.push_str(&format!("{}", RIGHT_CURLY));
        out
    }
}
impl SetBuilder {
    pub fn ir(&self) -> ObjIR {
        self.alpha.ir()
    }
    pub fn display_string(&self) -> String {
        self.surface.display_string()
    }
}
impl FnSetBody {
    pub fn ir(&self) -> ObjIR {
        let params: Vec<_> = self
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.ir())
            .collect();
        let dom: Vec<_> = self
            .dom_facts
            .iter()
            .map(|fact| fact.ir())
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
        out.push_str(&self.ret_set.ir());
        ObjIR(out)
    }
    pub fn display_string(&self) -> String {
        let params: Vec<_> = self
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.display_string())
            .collect();
        let dom: Vec<_> = self
            .dom_facts
            .iter()
            .map(|fact| fact.display_string())
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
        out.push_str(&self.ret_set.display_string());
        out
    }
}
impl FnSet {
    pub fn ir(&self) -> ObjIR {
        self.alpha.ir()
    }
    pub fn display_string(&self) -> String {
        self.surface.display_string()
    }
}
impl AnonymousFnBody {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.body.ir());
        out.push_str(&format!("{}", LEFT_CURLY));
        out.push_str(&self.equal_to.ir());
        out.push_str(&format!("{}", RIGHT_CURLY));
        ObjIR(out)
    }
    pub fn display_string(&self) -> String {
        let mut out = String::new();
        out.push_str(&self.body.display_string());
        out.push_str(&format!("{}", LEFT_CURLY));
        out.push_str(&self.equal_to.display_string());
        out.push_str(&format!("{}", RIGHT_CURLY));
        out
    }
}
impl AnonymousFn {
    pub fn ir(&self) -> ObjIR {
        self.alpha.ir()
    }
    pub fn display_string(&self) -> String {
        self.surface.display_string()
    }
}
impl StandardSet {
    pub fn ir(&self) -> ObjIR {
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

        ObjIR(out)
    }
    impl_display_pair!();
}

impl Cart {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}", CART));
        {
            out.push_str(LEFT_PAREN);
            out.push_str(
                &self
                    .args
                    .iter()
                    .map(|o| o.ir())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            out.push_str(RIGHT_PAREN);
        };

        ObjIR(out)
    }
    impl_display_pair!();
}
impl_obj_kw_call!(CartDim, CART_DIM, set);

impl_obj_kw_call!(Proj, PROJ, set, dim);

impl_obj_kw_call!(TupleDim, TUPLE_DIM, arg);

impl Tuple {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        {
            out.push_str(LEFT_PAREN);
            out.push_str(
                &self
                    .args
                    .iter()
                    .map(|o| o.ir())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            out.push_str(RIGHT_PAREN);
        };

        ObjIR(out)
    }
    impl_display_pair!();
}
impl GeneralCart {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}{}", GENERAL_CART, LEFT_PAREN));
        out.push_str(&self.index_set.ir());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.family_set.ir());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.family_fn.ir());
        out.push_str(&format!("{}", RIGHT_PAREN));
        ObjIR(out)
    }
    impl_display_pair!();
}
impl_obj_kw_call!(FiniteSetSize, FINITE_SET_SIZE, set);

impl_obj_kw_call!(FiniteSetMax, FINITE_SET_MAX, set);

impl_obj_kw_call!(FiniteSetMin, FINITE_SET_MIN, set);

impl_obj_kw_call!(FnRange, FN_RANGE, function);

impl Replacement {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}{}", REPLACEMENT, LEFT_PAREN));
        out.push_str(&self.prop_name.ir());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&self.source_set.ir());
        out.push_str(&format!("{}", RIGHT_PAREN));
        ObjIR(out)
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
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}", LEFT_BRACKET));
        out.push_str(
            &self
                .objs
                .iter()
                .map(|o| o.ir())
                .collect::<Vec<_>>()
                .join(", "),
        );
        out.push_str(&format!("{}", RIGHT_BRACKET));
        ObjIR(out)
    }
    impl_display_pair!();
}
impl ObjAtIndex {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.obj.ir());
        out.push_str(&format!("{}", LEFT_BRACKET));
        out.push_str(&self.index.ir());
        out.push_str(&format!("{}", RIGHT_BRACKET));

        ObjIR(out)
    }
    impl_display_pair!();
}
impl StructObj {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(STRUCT_VIEW_PREFIX);
        out.push_str(&self.name.ir());
        if !self.params.is_empty() {
            out.push_str(LESS);
            out.push_str(
                &self
                    .params
                    .iter()
                    .map(|o| o.ir())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            out.push_str(GREATER);
        }
        ObjIR(out)
    }
    impl_display_pair!();
}
impl ObjAsStructInstanceWithFieldAccess {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.obj.ir());
        out.push_str(&format!("{}{}", DOT_AKA_FIELD_ACCESS_SIGN, self.field_name));

        ObjIR(out)
    }
    impl_display_pair!();
}
impl InstantiatedTemplateObj {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}", TEMPLATE_INSTANCE_PREFIX));
        out.push_str(&self.template_name.ir());
        out.push_str(&format!("{}", LESS));
        out.push_str(
            &self
                .args
                .iter()
                .map(|o| o.ir())
                .collect::<Vec<_>>()
                .join(", "),
        );
        out.push_str(&format!("{}", GREATER));
        ObjIR(out)
    }
    impl_display_pair!();
}
impl IntervalObj {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        let (left_delimiter, right_delimiter, body) = match self {
            IntervalObj::LeftOpenRightOpen(s) => (LEFT_PAREN, RIGHT_PAREN, s),
            IntervalObj::LeftOpenRightClosed(s) => (LEFT_PAREN, RIGHT_BRACKET, s),
            IntervalObj::LeftClosedRightOpen(s) => (LEFT_BRACKET, RIGHT_PAREN, s),
            IntervalObj::LeftClosedRightClosed(s) => (LEFT_BRACKET, RIGHT_BRACKET, s),
        };
        out.push_str(&format!("{}{}", INTERVAL_LITERAL_PREFIX, left_delimiter));
        out.push_str(&body.start.ir());
        out.push_str(&format!("{COMMA} "));
        out.push_str(&body.end.ir());
        out.push_str(&format!("{}", right_delimiter));

        ObjIR(out)
    }
    impl_display_pair!();
}
impl OneSideInfinityIntervalObj {
    pub fn ir(&self) -> ObjIR {
        match self {
            OneSideInfinityIntervalObj::LeftOpen(interval) => {
                ObjIR(format!("'({},)", interval.start.as_ref().ir()))
            }
            OneSideInfinityIntervalObj::LeftClosed(interval) => {
                ObjIR(format!("'[{},)", interval.start.as_ref().ir()))
            }
            OneSideInfinityIntervalObj::RightOpen(interval) => {
                ObjIR(format!("'(,{})", interval.start.as_ref().ir()))
            }
            OneSideInfinityIntervalObj::RightClosed(interval) => {
                ObjIR(format!("'(,{}]", interval.start.as_ref().ir()))
            }
        }
    }
    impl_display_pair!();
}
// Binary/unary arithmetic leaf Display impls (surface via Obj precedence path primarily).
impl Add {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", ADD));
        out.push_str(&self.right.ir());

        ObjIR(out)
    }
    impl_display_pair!();
}
impl Sub {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", SUB));
        out.push_str(&self.right.ir());

        ObjIR(out)
    }
    impl_display_pair!();
}
impl Mul {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", MUL));
        out.push_str(&self.right.ir());

        ObjIR(out)
    }
    impl_display_pair!();
}
impl Div {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", DIV));
        out.push_str(&self.right.ir());

        ObjIR(out)
    }
    impl_display_pair!();
}
impl Mod {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", MOD_OP));
        out.push_str(&self.right.ir());

        ObjIR(out)
    }
    impl_display_pair!();
}
impl_obj_kw_binary!(Quot, QUOT, left, right);

impl_obj_kw_binary!(Gcd, GCD, left, right);

impl_obj_kw_binary!(Lcm, LCM, left, right);

impl Pow {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.base.ir());
        out.push_str(&format!(" {} ", POW));
        out.push_str(&self.exponent.ir());

        ObjIR(out)
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
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{} {}", ABS, LEFT_PAREN));
        out.push_str(&self.arg.ir());
        out.push_str(&format!("{}", RIGHT_PAREN));
        ObjIR(out)
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
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{} {}", SQRT, LEFT_PAREN));
        out.push_str(&self.arg.ir());
        out.push_str(&format!("{}", RIGHT_PAREN));
        ObjIR(out)
    }
    impl_display_pair!();
}
impl Log {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{} {}", LOG, LEFT_PAREN));
        out.push_str(&self.base.ir());
        out.push_str(&format!("{} ", COMMA));
        out.push_str(&self.arg.ir());
        out.push_str(&format!("{}", RIGHT_PAREN));
        ObjIR(out)
    }
    impl_display_pair!();
}
impl ImaginaryUnit {
    pub fn ir(&self) -> ObjIR {
        ObjIR(I.to_string())
    }
    impl_display_pair!();
}
impl EulerNumber {
    pub fn ir(&self) -> ObjIR {
        ObjIR(E.to_string())
    }
    impl_display_pair!();
}
impl Pi {
    pub fn ir(&self) -> ObjIR {
        ObjIR(PI.to_string())
    }
    impl_display_pair!();
}
