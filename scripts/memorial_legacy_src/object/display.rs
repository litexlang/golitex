//! Litex source rendering for object syntax.

use crate::prelude::*;
use std::fmt;

/// Arithmetic precedence for display; smaller numbers bind tighter.
fn precedence(o: &Obj) -> u8 {
    match o {
        Obj::Add(_) | Obj::Sub(_) => 3,
        Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::MatrixScalarMul(_) => 2,
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
        | Obj::Factorial(_)
        | Obj::MatrixAdd(_)
        | Obj::MatrixSub(_)
        | Obj::MatrixMul(_)
        | Obj::MatrixPow(_) => 1,
        _ => 0,
    }
}

impl fmt::Display for Obj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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
    ) -> Result<(), fmt::Error> {
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
                d.right.fmt_with_precedence(f, 1)?;
            }
            Obj::Mod(m) => {
                m.left.fmt_with_precedence(f, 2)?;
                write!(f, " {} ", MOD)?;
                m.right.fmt_with_precedence(f, 2)?;
            }
            Obj::Quot(x) => {
                write!(f, "{}{}", QUOT, LEFT_BRACE)?;
                x.left.fmt_with_precedence(f, 0)?;
                write!(f, "{COMMA} ")?;
                x.right.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Gcd(g) => {
                write!(f, "{}{}", GCD, LEFT_BRACE)?;
                g.left.fmt_with_precedence(f, 0)?;
                write!(f, "{COMMA} ")?;
                g.right.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Lcm(x) => {
                write!(f, "{}{}", LCM, LEFT_BRACE)?;
                x.left.fmt_with_precedence(f, 0)?;
                write!(f, "{COMMA} ")?;
                x.right.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Floor(x) => write!(f, "{}{}{}{}", FLOOR, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Ceil(x) => write!(f, "{}{}{}{}", CEIL, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Min(x) => write!(
                f,
                "{}{}{}, {}{}",
                MIN, LEFT_BRACE, x.left, x.right, RIGHT_BRACE
            )?,
            Obj::Max(x) => write!(
                f,
                "{}{}{}, {}{}",
                MAX, LEFT_BRACE, x.left, x.right, RIGHT_BRACE
            )?,
            Obj::Exp(x) => write!(f, "{}{}{}{}", EXP, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Ln(x) => write!(f, "{}{}{}{}", LN, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Sign(x) => write!(f, "{}{}{}{}", SIGN, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
            Obj::Factorial(x) => write!(f, "{}{}{}{}", FACTORIAL, LEFT_BRACE, x.arg, RIGHT_BRACE)?,
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
            Obj::Sin(x) => {
                write!(f, "{}{}", SIN, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Arcsin(x) => {
                write!(f, "{}{}", ARCSIN, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Cos(x) => {
                write!(f, "{}{}", COS, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Tan(x) => {
                write!(f, "{}{}", TAN, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Cot(x) => {
                write!(f, "{}{}", COT, LEFT_BRACE)?;
                x.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::RealPart(real_part) => {
                write!(f, "{}{}", RE, LEFT_BRACE)?;
                real_part.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::ImaginaryPart(imaginary_part) => {
                write!(f, "{}{}", IMG, LEFT_BRACE)?;
                imaginary_part.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::ComplexAbs(complex_abs) => {
                write!(f, "{}{}", C_ABS, LEFT_BRACE)?;
                complex_abs.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Sqrt(s) => {
                write!(f, "{} {}", SQRT, LEFT_BRACE)?;
                s.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Log(l) => {
                write!(f, "{} {}", LOG, LEFT_BRACE)?;
                l.base.fmt_with_precedence(f, 0)?;
                write!(f, "{} ", COMMA)?;
                l.arg.fmt_with_precedence(f, 0)?;
                write!(f, "{}", RIGHT_BRACE)?;
            }
            Obj::Union(x) => write!(f, "{}", x)?,
            Obj::Intersect(x) => write!(f, "{}", x)?,
            Obj::SetMinus(x) => write!(f, "{}", x)?,
            Obj::FamilyUnion(x) => write!(f, "{}", x)?,
            Obj::FamilyIntersect(x) => write!(f, "{}", x)?,
            Obj::IndexUnion(x) => write!(f, "{}", x)?,
            Obj::IndexIntersect(x) => write!(f, "{}", x)?,
            Obj::Atom(x) => write!(f, "{}", x)?,
            Obj::FnObj(x) => write!(f, "{}", x)?,
            Obj::Number(x) => write!(f, "{}", x)?,
            Obj::ImaginaryUnit(_) => write!(f, "{}", I)?,
            Obj::EulerNumber(_) => write!(f, "{}", E)?,
            Obj::Pi(_) => write!(f, "{}", PI)?,
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
            Obj::FiniteSetSize(x) => write!(f, "{}", x)?,
            Obj::FiniteSetMax(x) => write!(f, "{}", x)?,
            Obj::FiniteSetMin(x) => write!(f, "{}", x)?,
            Obj::FnRange(x) => write!(f, "{}", x)?,
            Obj::Replacement(x) => write!(f, "{}", x)?,
            Obj::Sum(x) => write!(f, "{}", x)?,
            Obj::SumOfFiniteSet(x) => write!(f, "{}", x)?,
            Obj::Product(x) => write!(f, "{}", x)?,
            Obj::ProductOfFiniteSet(x) => write!(f, "{}", x)?,
            Obj::Reduce(x) => write!(f, "{}", x)?,
            Obj::FiniteSetReduce(x) => write!(f, "{}", x)?,
            Obj::Range(x) => write!(f, "{}", x)?,
            Obj::ClosedRange(x) => write!(f, "{}", x)?,
            Obj::FiniteSeqSet(x) => write!(f, "{}", x)?,
            Obj::SeqSet(x) => write!(f, "{}", x)?,
            Obj::FiniteSeqListObj(x) => write!(f, "{}", x)?,
            Obj::MatrixSet(x) => write!(f, "{}", x)?,
            Obj::MatrixListObj(x) => write!(f, "{}", x)?,
            Obj::PowerSet(x) => write!(f, "{}", x)?,
            Obj::IndexCart(x) => write!(f, "{}", x)?,
            Obj::ObjAtIndex(x) => write!(f, "{}", x)?,
            Obj::StructObj(x) => write!(f, "{}", x)?,
            Obj::ObjAsStructInstanceWithFieldAccess(x) => write!(f, "{}", x)?,
            Obj::InstantiatedTemplateObj(x) => write!(f, "{}", x)?,
            Obj::OneSideInfinityIntervalObj(x) => write!(f, "{}", x)?,
            Obj::IntervalObj(x) => write!(f, "{}", x)?,
        }
        if need_parens {
            write!(f, "{}", RIGHT_BRACE)?;
        }
        Ok(())
    }
}

impl fmt::Display for ObjAtIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}{}{}",
            self.obj, LEFT_BRACKET, self.index, RIGHT_BRACKET
        )
    }
}

impl fmt::Display for StructObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}", STRUCT_VIEW_PREFIX, self.name)?;
        if !self.params.is_empty() {
            write!(
                f,
                "{}{}{}",
                LESS,
                vec_to_string_join_by_comma(&self.params),
                GREATER
            )?;
        }
        Ok(())
    }
}

impl fmt::Display for InstantiatedTemplateObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.surface_name())
    }
}

impl fmt::Display for ObjAsStructInstanceWithFieldAccess {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}{}",
            self.obj, DOT_AKA_FIELD_ACCESS_SIGN, self.field_name
        )
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            RANGE,
            braced_vec_to_string(&vec![self.start.as_ref(), self.end.as_ref()])
        )
    }
}

impl fmt::Display for ClosedRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            CLOSED_RANGE,
            braced_vec_to_string(&vec![self.start.as_ref(), self.end.as_ref()])
        )
    }
}

impl fmt::Display for IntervalObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        let (left_delimiter, right_delimiter) = match self {
            IntervalObj::LeftOpenRightOpen(_) => (LEFT_BRACE, RIGHT_BRACE),
            IntervalObj::LeftOpenRightClosed(_) => (LEFT_BRACE, RIGHT_BRACKET),
            IntervalObj::LeftClosedRightOpen(_) => (LEFT_BRACKET, RIGHT_BRACE),
            IntervalObj::LeftClosedRightClosed(_) => (LEFT_BRACKET, RIGHT_BRACKET),
        };
        let interval_struct = self.interval_struct();
        write!(
            f,
            "{}{}{}, {}{}",
            INTERVAL_LITERAL_PREFIX,
            left_delimiter,
            interval_struct.start.as_ref(),
            interval_struct.end.as_ref(),
            right_delimiter
        )
    }
}

impl fmt::Display for OneSideInfinityIntervalObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            OneSideInfinityIntervalObj::LeftOpen(interval) => write!(f, "'({},)", interval.start),
            OneSideInfinityIntervalObj::LeftClosed(interval) => write!(f, "'[{},)", interval.start),
            OneSideInfinityIntervalObj::RightOpen(interval) => write!(f, "'(,{})", interval.start),
            OneSideInfinityIntervalObj::RightClosed(interval) => {
                write!(f, "'(,{}]", interval.start)
            }
        }
    }
}

impl fmt::Display for FiniteSeqSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SEQ,
            braced_vec_to_string(&vec![self.set.as_ref(), self.n.as_ref()])
        )
    }
}

impl fmt::Display for SeqSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            SEQ,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FiniteSeqListObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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

impl fmt::Display for FiniteSetSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_SIZE,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FiniteSetMax {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_MAX,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FiniteSetMin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_MIN,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for FnRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FN_RANGE,
            braced_vec_to_string(&vec![self.function.as_ref()])
        )
    }
}

impl fmt::Display for Replacement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}{}, {}{}",
            REPLACEMENT, LEFT_BRACE, self.prop_name, self.source_set, RIGHT_BRACE
        )
    }
}

impl fmt::Display for Sum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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

impl fmt::Display for SumOfFiniteSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_SUM,
            braced_vec_to_string(&vec![self.set.as_ref(), self.func.as_ref()])
        )
    }
}

impl fmt::Display for Product {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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

impl fmt::Display for ProductOfFiniteSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_PRODUCT,
            braced_vec_to_string(&vec![self.set.as_ref(), self.func.as_ref()])
        )
    }
}

impl fmt::Display for Reduce {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            REDUCE,
            braced_vec_to_string(&vec![
                self.start.as_ref(),
                self.end.as_ref(),
                self.func.as_ref(),
                self.op.as_ref(),
                self.seed.as_ref(),
            ])
        )
    }
}

impl fmt::Display for FiniteSetReduce {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FINITE_SET_REDUCE,
            braced_vec_to_string(&vec![
                self.set.as_ref(),
                self.func.as_ref(),
                self.op.as_ref(),
                self.seed.as_ref(),
            ])
        )
    }
}

impl fmt::Display for Tuple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for CartDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            CART_DIM,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}

impl fmt::Display for Proj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            PROJ,
            braced_vec_to_string(&vec![self.set.as_ref(), self.dim.as_ref()])
        )
    }
}

impl fmt::Display for TupleDim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            TUPLE_DIM,
            braced_vec_to_string(&vec![self.arg.as_ref()])
        )
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.symbol.as_ref() {
            Some(symbol) => write!(f, "{}", symbol.canonical_identity_spine(&self.name)),
            None => write!(f, "{}", self.name),
        }
    }
}

impl fmt::Display for FnObj {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.normalized_value)
    }
}

impl fmt::Display for Add {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, ADD, self.right)
    }
}

impl fmt::Display for Sub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, SUB, self.right)
    }
}

impl fmt::Display for Mul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MUL, self.right)
    }
}

impl fmt::Display for Div {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, DIV, self.right)
    }
}

impl fmt::Display for Mod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MOD, self.right)
    }
}

impl fmt::Display for Gcd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({}, {})", GCD, self.left, self.right)
    }
}

impl fmt::Display for Lcm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({}, {})", LCM, self.left, self.right)
    }
}

impl fmt::Display for Floor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", FLOOR, self.arg)
    }
}

impl fmt::Display for Ceil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", CEIL, self.arg)
    }
}

impl fmt::Display for Min {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({}, {})", MIN, self.left, self.right)
    }
}

impl fmt::Display for Max {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({}, {})", MAX, self.left, self.right)
    }
}

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", EXP, self.arg)
    }
}

impl fmt::Display for Ln {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", LN, self.arg)
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", SIGN, self.arg)
    }
}

impl fmt::Display for Factorial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({})", FACTORIAL, self.arg)
    }
}

impl fmt::Display for Pow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.base, POW, self.exponent)
    }
}

impl fmt::Display for MatrixAdd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MATRIX_ADD, self.right)
    }
}

impl fmt::Display for MatrixSub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MATRIX_SUB, self.right)
    }
}

impl fmt::Display for MatrixMul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.left, MATRIX_MUL, self.right)
    }
}

impl fmt::Display for MatrixScalarMul {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.scalar, MATRIX_SCALAR_MUL, self.matrix)
    }
}

impl fmt::Display for MatrixPow {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {} {}", self.base, MATRIX_POW, self.exponent)
    }
}

impl fmt::Display for Abs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {}{}{}", ABS, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Sin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", SIN, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Arcsin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", ARCSIN, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Cos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", COS, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Tan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", TAN, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Cot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", COT, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for RealPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", RE, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for ImaginaryPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", IMG, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for ComplexAbs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}{}{}", C_ABS, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Sqrt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} {}{}{}", SQRT, LEFT_BRACE, self.arg, RIGHT_BRACE)
    }
}

impl fmt::Display for Log {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}{}{}{}{}",
            LOG, LEFT_BRACE, self.base, COMMA, self.arg, RIGHT_BRACE
        )
    }
}

impl fmt::Display for Union {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            UNION,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for Intersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            INTERSECT,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for SetMinus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            SET_MINUS,
            braced_vec_to_string(&vec![self.left.as_ref(), self.right.as_ref()])
        )
    }
}

impl fmt::Display for FamilyUnion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FAMILY_UNION,
            braced_vec_to_string(&vec![self.left.as_ref()])
        )
    }
}

impl fmt::Display for FamilyIntersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            FAMILY_INTERSECT,
            braced_vec_to_string(&vec![self.left.as_ref()])
        )
    }
}

impl fmt::Display for IndexUnion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}({}, {}, {})",
            INDEX_UNION, self.index_set, self.ambient_set, self.family_fn
        )
    }
}

impl fmt::Display for IndexIntersect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}({}, {}, {})",
            INDEX_INTERSECT, self.index_set, self.ambient_set, self.family_fn
        )
    }
}

impl fmt::Display for IdentifierWithMod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.symbol.as_ref() {
            Some(symbol) => write!(f, "{}", symbol.canonical_identity_spine(&self.name)),
            None => write!(f, "{}{}{}", self.mod_name, MOD_SIGN, self.name),
        }
    }
}

impl fmt::Display for ListSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", curly_braced_vec_to_string(&self.list))
    }
}

impl fmt::Display for SetBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{} {}{} {}{}",
            LEFT_CURLY_BRACE,
            self.param_binding,
            self.param_set,
            COLON,
            vec_to_string_join_by_comma(&self.facts),
            RIGHT_CURLY_BRACE
        )
    }
}

impl fmt::Display for IndexCart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}({}, {}, {})",
            INDEX_CART, self.index_set, self.family_set, self.family_fn
        )
    }
}

impl fmt::Display for Cart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}{}", CART, braced_vec_to_string(&self.args))
    }
}

impl fmt::Display for PowerSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{}{}",
            POWER_SET,
            braced_vec_to_string(&vec![self.set.as_ref()])
        )
    }
}
