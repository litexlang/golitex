//! Obj and related leaf types: IR + display_string.

use super::types::ObjIR;
use crate::ast::obj::*;
use crate::parse::keywords::*;

macro_rules! impl_display_pair {
    () => {
        pub fn display_string(&self) -> String {
            self.ir().display_string()
        }

        // Human-facing: IR text with `#id#` wrappers stripped.
        pub fn readable_string(&self) -> String {
            crate::display_and_ir::readable_string_from_ir_text(self.ir().as_str())
        }
    };
}

impl Obj {
    pub fn ir(&self) -> ObjIR {
        fn fmt_obj(o: &Obj) -> String {
            // IR is an identity/index key, not only presentation. Preserve every
            // arithmetic constructor: (a^b)^c and a^(b^c) must never share a key.
            let need_parens = matches!(
                o,
                Obj::ArithmeticOperator(
                    ArithmeticOperator::Add(_)
                        | ArithmeticOperator::Sub(_)
                        | ArithmeticOperator::Mul(_)
                        | ArithmeticOperator::Div(_)
                        | ArithmeticOperator::Pow(_)
                        | ArithmeticOperator::Neg(_)
                ) | Obj::IntegerOperator(IntegerOperator::Mod(_))
            );
            let mut s = String::new();
            if need_parens {
                s.push_str(LEFT_PAREN);
            }
            match o {
                Obj::DerivativeOperator(DerivativeOperator::AtPoint(x)) => {
                    s.push_str(x.ir().as_str())
                }
                Obj::BoundOperator(BoundOperator::Supremum(x)) => s.push_str(x.ir().as_str()),
                Obj::BoundOperator(BoundOperator::Infimum(x)) => s.push_str(x.ir().as_str()),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => {
                    s.push_str(&fmt_obj(a.left.as_ref()));
                    s.push_str(&format!(" {} ", ADD));
                    s.push_str(&fmt_obj(a.right.as_ref()));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) => {
                    s.push_str(&fmt_obj(sub.left.as_ref()));
                    s.push_str(&format!(" {} ", SUB));
                    s.push_str(&fmt_obj(sub.right.as_ref()));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(m)) => {
                    s.push_str(&fmt_obj(m.left.as_ref()));
                    s.push_str(&format!(" {} ", MUL));
                    s.push_str(&fmt_obj(m.right.as_ref()));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Div(d)) => {
                    s.push_str(&fmt_obj(d.left.as_ref()));
                    s.push_str(&format!(" {} ", DIV));
                    s.push_str(&fmt_obj(d.right.as_ref()));
                }
                Obj::IntegerOperator(IntegerOperator::Mod(m)) => {
                    s.push_str(&fmt_obj(m.left.as_ref()));
                    s.push_str(&format!(" {} ", MOD_OP));
                    s.push_str(&fmt_obj(m.right.as_ref()));
                }
                Obj::IntegerOperator(IntegerOperator::Quot(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        QUOT,
                        LEFT_PAREN,
                        fmt_obj(x.left.as_ref()),
                        COMMA,
                        fmt_obj(x.right.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::IntegerOperator(IntegerOperator::Gcd(g)) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        GCD,
                        LEFT_PAREN,
                        fmt_obj(g.left.as_ref()),
                        COMMA,
                        fmt_obj(g.right.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::IntegerOperator(IntegerOperator::Lcm(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        LCM,
                        LEFT_PAREN,
                        fmt_obj(x.left.as_ref()),
                        COMMA,
                        fmt_obj(x.right.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Floor(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        FLOOR,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Ceil(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        CEIL,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Min(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        MIN,
                        LEFT_PAREN,
                        fmt_obj(x.left.as_ref()),
                        COMMA,
                        fmt_obj(x.right.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Max(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{} {}{}",
                        MAX,
                        LEFT_PAREN,
                        fmt_obj(x.left.as_ref()),
                        COMMA,
                        fmt_obj(x.right.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ExpLogOperator(ExpLogOperator::Exp(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        EXP,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ExpLogOperator(ExpLogOperator::Ln(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        LN,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Sign(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        SIGN,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::IntegerOperator(IntegerOperator::Factorial(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        FACTORIAL,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => {
                    s.push_str(&fmt_obj(p.base.as_ref()));
                    s.push_str(&format!(" {} ", POW));
                    s.push_str(&fmt_obj(p.exponent.as_ref()));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Neg(n)) => {
                    s.push_str(SUB);
                    s.push_str(&fmt_obj(n.arg.as_ref()));
                }
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => {
                    s.push_str(&format!(
                        "{} {}{}{}",
                        ABS,
                        LEFT_PAREN,
                        fmt_obj(a.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::TrigOperator(TrigOperator::Sec(x)) => s.push_str(&x.ir()),
                Obj::TrigOperator(TrigOperator::Csc(x)) => s.push_str(&x.ir()),
                Obj::ComplexOperator(ComplexOperator::Conjugate(x)) => s.push_str(&x.ir()),
                Obj::HyperbolicOperator(HyperbolicOperator::Sinh(x)) => s.push_str(&x.ir()),
                Obj::HyperbolicOperator(HyperbolicOperator::Cosh(x)) => s.push_str(&x.ir()),
                Obj::HyperbolicOperator(HyperbolicOperator::Tanh(x)) => s.push_str(&x.ir()),
                Obj::HyperbolicOperator(HyperbolicOperator::Coth(x)) => s.push_str(&x.ir()),
                Obj::HyperbolicOperator(HyperbolicOperator::Sech(x)) => s.push_str(&x.ir()),
                Obj::HyperbolicOperator(HyperbolicOperator::Csch(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::SymmetricDifference(x)) => s.push_str(&x.ir()),
                Obj::TrigOperator(TrigOperator::Sin(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        SIN,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::TrigOperator(TrigOperator::Arcsin(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        ARCSIN,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::TrigOperator(TrigOperator::Arccos(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        ARCCOS,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::TrigOperator(TrigOperator::Arctan(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        ARCTAN,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::TrigOperator(TrigOperator::Arccot(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        ARCCOT,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::TrigOperator(TrigOperator::Cos(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        COS,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::TrigOperator(TrigOperator::Tan(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        TAN,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::TrigOperator(TrigOperator::Cot(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        COT,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ComplexOperator(ComplexOperator::RealPart(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        RE,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ComplexOperator(ComplexOperator::ImaginaryPart(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        IMG,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ComplexOperator(ComplexOperator::ComplexAbs(x)) => {
                    s.push_str(&format!(
                        "{}{}{}{}",
                        C_ABS,
                        LEFT_PAREN,
                        fmt_obj(x.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ExpLogOperator(ExpLogOperator::Sqrt(sq)) => {
                    s.push_str(&format!(
                        "{} {}{}{}",
                        SQRT,
                        LEFT_PAREN,
                        fmt_obj(sq.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::ExpLogOperator(ExpLogOperator::Log(l)) => {
                    s.push_str(&format!(
                        "{} {}{}{} {}{}",
                        LOG,
                        LEFT_PAREN,
                        fmt_obj(l.base.as_ref()),
                        COMMA,
                        fmt_obj(l.arg.as_ref()),
                        RIGHT_PAREN
                    ));
                }
                Obj::SetOperator(SetOperator::Union(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::Intersect(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::SetMinus(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::FamilyUnion(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::FamilyIntersect(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::IndexUnion(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::IndexIntersect(x)) => s.push_str(&x.ir()),
                Obj::Identifier(x) => s.push_str(&x.ir()),
                Obj::FnObj(x) => s.push_str(&x.ir()),
                Obj::Literal(Literal::Number(x)) => s.push_str(&x.ir()),
                Obj::Literal(Literal::ImaginaryUnit(_)) => s.push_str(I),
                Obj::Literal(Literal::EulerNumber(_)) => s.push_str(E),
                Obj::Literal(Literal::Pi(_)) => s.push_str(PI),
                Obj::SetFormer(SetFormer::ListSet(x)) => s.push_str(&x.ir()),
                Obj::SetFormer(SetFormer::SetBuilder(x)) => s.push_str(&x.ir()),
                Obj::FunctionSpace(FunctionSpace::FnSet(x)) => s.push_str(&x.ir()),
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(x)) => s.push_str(&x.ir()),
                Obj::LimitOperator(LimitOperator::Sequence(x)) => s.push_str(&x.ir()),
                Obj::LimitOperator(LimitOperator::SequenceLimsup(x)) => s.push_str(&x.ir()),
                Obj::LimitOperator(LimitOperator::SequenceLiminf(x)) => s.push_str(&x.ir()),
                Obj::LimitOperator(LimitOperator::Function(x)) => s.push_str(&x.ir()),
                Obj::StandardSet(x) => s.push_str(&x.ir()),
                Obj::ProductShape(ProductShape::Cart(x)) => s.push_str(&x.ir()),
                Obj::ProductShape(ProductShape::Tuple(x)) => s.push_str(&x.ir()),
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(x)) => s.push_str(&x.ir()),
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(x)) => s.push_str(&x.ir()),
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(x)) => s.push_str(&x.ir()),
                Obj::FunctionSpace(FunctionSpace::FnRange(x)) => s.push_str(&x.ir()),
                Obj::FunctionSpace(FunctionSpace::Composition(x)) => s.push_str(&x.ir()),
                Obj::FunctionSpace(FunctionSpace::Preimage(x)) => s.push_str(&x.ir()),
                Obj::FunctionSpace(FunctionSpace::PreimageSet(x)) => s.push_str(&x.ir()),
                Obj::IteratedOperator(IteratedOperator::Sum(x)) => s.push_str(&x.ir()),
                Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(x)) => s.push_str(&x.ir()),
                Obj::IteratedOperator(IteratedOperator::Product(x)) => s.push_str(&x.ir()),
                Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(x)) => {
                    s.push_str(&x.ir())
                }
                Obj::IteratedOperator(IteratedOperator::Reduce(x)) => s.push_str(&x.ir()),
                Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(x)) => s.push_str(&x.ir()),
                Obj::SetFormer(SetFormer::Range(x)) => s.push_str(&x.ir()),
                Obj::SetFormer(SetFormer::ClosedRange(x)) => s.push_str(&x.ir()),
                Obj::SetFormer(SetFormer::FiniteSeqSet(x)) => s.push_str(&x.ir()),
                Obj::SetFormer(SetFormer::SeqSet(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::PowerSet(x)) => s.push_str(&x.ir()),
                Obj::SetOperator(SetOperator::IndexCart(x)) => s.push_str(&x.ir()),
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(x)) => {
                    s.push_str(&x.ir())
                }
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(x)) => {
                    s.push_str(&x.ir())
                }
                Obj::InstantiatedTemplateObj(x) => s.push_str(&x.ir()),
                Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(x)) => s.push_str(&x.ir()),
                Obj::SetFormer(SetFormer::IntervalObj(x)) => s.push_str(&x.ir()),
            }
            if need_parens {
                s.push_str(RIGHT_PAREN);
            }
            s
        }

        ObjIR(fmt_obj(self))
    }

    pub fn display_string(&self) -> String {
        match self {
            Obj::Identifier(a) => a.display_string(),
            Obj::SetFormer(SetFormer::SetBuilder(x)) => x.display_string(),
            Obj::FunctionSpace(FunctionSpace::FnSet(x)) => x.display_string(),
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(x)) => x.display_string(),
            _ => self.ir().display_string(),
        }
    }

    // Human-facing: IR text with `#id#` wrappers stripped.
    pub fn readable_string(&self) -> String {
        crate::display_and_ir::readable_string_from_ir_text(self.ir().as_str())
    }
}

impl IdentifierObj {
    pub fn ir(&self) -> ObjIR {
        ObjIR(self.ir_string())
    }
}

impl FnObjHead {
    pub fn ir(&self) -> ObjIR {
        match self {
            FnObjHead::Object(obj) => match obj.as_ref() {
                Obj::ProductShape(ProductShape::Tuple(_)) => obj.ir(),
                _ => ObjIR(format!("({})", obj.ir())),
            },
            FnObjHead::Identifier(x) => x.ir(),
            FnObjHead::AnonymousFnLiteral(a) => a.ir(),
            FnObjHead::FieldAccess(v) => v.ir(),
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
                out.push_str(&group.iter().map(|o| o.ir()).collect::<Vec<_>>().join(", "));
                out.push_str(RIGHT_PAREN);
            };
        }
        ObjIR(out)
    }
    impl_display_pair!();
}

impl Number {
    pub fn ir(&self) -> ObjIR {
        // Generated negative literals and parsed unary negatives denote the
        // same number. Group the sign so a negative power base reparses intact.
        if self.normalized_value.starts_with('-') {
            ObjIR(format!("({})", self.normalized_value))
        } else {
            ObjIR(self.normalized_value.clone())
        }
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

impl_obj_kw_call!(FamilyUnion, FAMILY_UNION, left);

impl_obj_kw_call!(FamilyIntersect, FAMILY_INTERSECT, left);

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
impl SetBuilder {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}", LEFT_CURLY));
        out.push_str(&self.param_binding.ir_string());
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
        out.push_str(&self.param_binding.name);
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
impl FnSet {
    pub fn ir(&self) -> ObjIR {
        let params: Vec<_> = self
            .set_bound_parameters
            .groups
            .iter()
            .map(|g| g.ir())
            .collect();
        let dom: Vec<_> = self.dom_facts.iter().map(|fact| fact.ir()).collect();
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
impl AnonymousFn {
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

impl Tuple {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        // Bare `()` is invalid; use the explicit empty constructor.
        if self.args.is_empty() {
            out.push_str(TUPLE);
        }
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
            if self.args.len() == 1 {
                out.push_str(COMMA);
            }
            out.push_str(RIGHT_PAREN);
        };

        ObjIR(out)
    }
    impl_display_pair!();
}
impl IndexCart {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&format!("{}{}", INDEX_CART, LEFT_PAREN));
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
impl_obj_kw_call!(Composition, COMPOSE, outer, inner);
impl_obj_kw_call!(Preimage, PREIMAGE, function, value);
impl_obj_kw_call!(PreimageSet, PREIMAGE_SET, function, target_set);

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
impl FieldAccess {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(&self.obj.ir());
        out.push_str(
            &self
                .fields
                .iter()
                .map(|f| format!("{}{}", DOT_AKA_FIELD_ACCESS_SIGN, f))
                .collect::<String>(),
        );

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
            OneSideInfinityIntervalObj::LowerOpen(interval) => {
                ObjIR(format!("'({},)", interval.start.as_ref().ir()))
            }
            OneSideInfinityIntervalObj::LowerClosed(interval) => {
                ObjIR(format!("'[{},)", interval.start.as_ref().ir()))
            }
            OneSideInfinityIntervalObj::UpperOpen(interval) => {
                ObjIR(format!("'(,{})", interval.start.as_ref().ir()))
            }
            OneSideInfinityIntervalObj::UpperClosed(interval) => {
                ObjIR(format!("'(,{}]", interval.start.as_ref().ir()))
            }
        }
    }
    impl_display_pair!();
}
// Binary/unary arithmetic leaf IR impls. Keep them identical to the `Obj::ir()`
// arms above: wrap the same constructors in the same parentheses so a leaf
// `ir()` never diverges from the identity key.
impl Add {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(LEFT_PAREN);
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", ADD));
        out.push_str(&self.right.ir());
        out.push_str(RIGHT_PAREN);

        ObjIR(out)
    }
    impl_display_pair!();
}
impl Sub {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(LEFT_PAREN);
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", SUB));
        out.push_str(&self.right.ir());
        out.push_str(RIGHT_PAREN);

        ObjIR(out)
    }
    impl_display_pair!();
}
impl Neg {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(LEFT_PAREN);
        out.push_str(SUB);
        out.push_str(&self.arg.ir());
        out.push_str(RIGHT_PAREN);
        ObjIR(out)
    }
    impl_display_pair!();
}
impl Mul {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(LEFT_PAREN);
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", MUL));
        out.push_str(&self.right.ir());
        out.push_str(RIGHT_PAREN);

        ObjIR(out)
    }
    impl_display_pair!();
}
impl Div {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(LEFT_PAREN);
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", DIV));
        out.push_str(&self.right.ir());
        out.push_str(RIGHT_PAREN);

        ObjIR(out)
    }
    impl_display_pair!();
}
impl Mod {
    pub fn ir(&self) -> ObjIR {
        let mut out = String::new();
        out.push_str(LEFT_PAREN);
        out.push_str(&self.left.ir());
        out.push_str(&format!(" {} ", MOD_OP));
        out.push_str(&self.right.ir());
        out.push_str(RIGHT_PAREN);

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
        out.push_str(LEFT_PAREN);
        out.push_str(&self.base.ir());
        out.push_str(&format!(" {} ", POW));
        out.push_str(&self.exponent.ir());
        out.push_str(RIGHT_PAREN);

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

impl_obj_kw_unary!(Arccos, ARCCOS, arg);

impl_obj_kw_unary!(Arctan, ARCTAN, arg);

impl_obj_kw_unary!(Arccot, ARCCOT, arg);

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

impl_obj_kw_unary!(Sec, SEC, arg);
impl_obj_kw_unary!(Csc, CSC, arg);
impl_obj_kw_unary!(Conjugate, CONJ, arg);
impl_obj_kw_unary!(Sinh, SINH, arg);
impl_obj_kw_unary!(Cosh, COSH, arg);
impl_obj_kw_unary!(Tanh, TANH, arg);
impl_obj_kw_unary!(Coth, COTH, arg);
impl_obj_kw_unary!(Sech, SECH, arg);
impl_obj_kw_unary!(Csch, CSCH, arg);
impl_obj_kw_call!(SymmetricDifference, SET_DIFF, left, right);

impl_obj_kw_call!(SequenceLimit, LIM, sequence);
impl_obj_kw_call!(Supremum, "sup", set);
impl_obj_kw_call!(Infimum, "inf", set);
impl_obj_kw_call!(SequenceLimsup, LIMSUP, sequence);
impl_obj_kw_call!(SequenceLiminf, LIMINF, sequence);

impl FunctionLimit {
    pub fn ir(&self) -> ObjIR {
        ObjIR(match self.approach.point() {
            Some(point) => format!(
                "{}({}, {})",
                self.approach.value_name(),
                self.function.ir(),
                point.ir()
            ),
            None => format!("{}({})", self.approach.value_name(), self.function.ir()),
        })
    }
    impl_display_pair!();
}

impl DerivativeAt {
    pub fn ir(&self) -> ObjIR {
        ObjIR(format!(
            "derivative({}, {})",
            self.function.ir(),
            self.point.ir()
        ))
    }
    impl_display_pair!();
}
