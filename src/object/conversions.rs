//! Conversions from object payloads into the object sum type.

use crate::prelude::*;

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

impl From<ImaginaryUnit> for Obj {
    fn from(i: ImaginaryUnit) -> Self {
        Obj::ImaginaryUnit(i)
    }
}

impl From<EulerNumber> for Obj {
    fn from(e: EulerNumber) -> Self {
        Obj::EulerNumber(e)
    }
}

impl From<Pi> for Obj {
    fn from(pi: Pi) -> Self {
        Obj::Pi(pi)
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

impl From<Quot> for Obj {
    fn from(x: Quot) -> Self {
        Obj::Quot(x)
    }
}

impl From<Gcd> for Obj {
    fn from(g: Gcd) -> Self {
        Obj::Gcd(g)
    }
}

impl From<Lcm> for Obj {
    fn from(x: Lcm) -> Self {
        Obj::Lcm(x)
    }
}

impl From<Floor> for Obj {
    fn from(x: Floor) -> Self {
        Obj::Floor(x)
    }
}

impl From<Ceil> for Obj {
    fn from(x: Ceil) -> Self {
        Obj::Ceil(x)
    }
}

impl From<Min> for Obj {
    fn from(x: Min) -> Self {
        Obj::Min(x)
    }
}

impl From<Max> for Obj {
    fn from(x: Max) -> Self {
        Obj::Max(x)
    }
}

impl From<Exp> for Obj {
    fn from(x: Exp) -> Self {
        Obj::Exp(x)
    }
}

impl From<Ln> for Obj {
    fn from(x: Ln) -> Self {
        Obj::Ln(x)
    }
}

impl From<Sign> for Obj {
    fn from(x: Sign) -> Self {
        Obj::Sign(x)
    }
}

impl From<Factorial> for Obj {
    fn from(x: Factorial) -> Self {
        Obj::Factorial(x)
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

impl From<Sin> for Obj {
    fn from(x: Sin) -> Self {
        Obj::Sin(x)
    }
}

impl From<Arcsin> for Obj {
    fn from(x: Arcsin) -> Self {
        Obj::Arcsin(x)
    }
}

impl From<Cos> for Obj {
    fn from(x: Cos) -> Self {
        Obj::Cos(x)
    }
}

impl From<Tan> for Obj {
    fn from(x: Tan) -> Self {
        Obj::Tan(x)
    }
}

impl From<Cot> for Obj {
    fn from(x: Cot) -> Self {
        Obj::Cot(x)
    }
}

impl From<RealPart> for Obj {
    fn from(real_part: RealPart) -> Self {
        Obj::RealPart(real_part)
    }
}

impl From<ImaginaryPart> for Obj {
    fn from(imaginary_part: ImaginaryPart) -> Self {
        Obj::ImaginaryPart(imaginary_part)
    }
}

impl From<ComplexAbs> for Obj {
    fn from(complex_abs: ComplexAbs) -> Self {
        Obj::ComplexAbs(complex_abs)
    }
}

impl From<Sqrt> for Obj {
    fn from(s: Sqrt) -> Self {
        Obj::Sqrt(s)
    }
}

impl From<Log> for Obj {
    fn from(l: Log) -> Self {
        Obj::Log(l)
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

impl From<BigUnion> for Obj {
    fn from(c: BigUnion) -> Self {
        Obj::BigUnion(c)
    }
}

impl From<BigIntersect> for Obj {
    fn from(c: BigIntersect) -> Self {
        Obj::BigIntersect(c)
    }
}

impl From<IndexUnion> for Obj {
    fn from(value: IndexUnion) -> Self {
        Obj::IndexUnion(value)
    }
}

impl From<IndexIntersect> for Obj {
    fn from(value: IndexIntersect) -> Self {
        Obj::IndexIntersect(value)
    }
}

impl From<PowerSet> for Obj {
    fn from(p: PowerSet) -> Self {
        Obj::PowerSet(p)
    }
}

impl From<GeneralCart> for Obj {
    fn from(g: GeneralCart) -> Self {
        Obj::GeneralCart(g)
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

impl From<FiniteSetSize> for Obj {
    fn from(c: FiniteSetSize) -> Self {
        Obj::FiniteSetSize(c)
    }
}

impl From<FiniteSetMax> for Obj {
    fn from(x: FiniteSetMax) -> Self {
        Obj::FiniteSetMax(x)
    }
}

impl From<FiniteSetMin> for Obj {
    fn from(x: FiniteSetMin) -> Self {
        Obj::FiniteSetMin(x)
    }
}

impl From<FnRange> for Obj {
    fn from(r: FnRange) -> Self {
        Obj::FnRange(r)
    }
}

impl From<Replacement> for Obj {
    fn from(r: Replacement) -> Self {
        Obj::Replacement(r)
    }
}

impl From<Sum> for Obj {
    fn from(s: Sum) -> Self {
        Obj::Sum(s)
    }
}

impl From<SumOfFiniteSet> for Obj {
    fn from(s: SumOfFiniteSet) -> Self {
        Obj::SumOfFiniteSet(s)
    }
}

impl From<Product> for Obj {
    fn from(p: Product) -> Self {
        Obj::Product(p)
    }
}

impl From<ProductOfFiniteSet> for Obj {
    fn from(p: ProductOfFiniteSet) -> Self {
        Obj::ProductOfFiniteSet(p)
    }
}

impl From<Reduce> for Obj {
    fn from(r: Reduce) -> Self {
        Obj::Reduce(r)
    }
}

impl From<FiniteSetReduce> for Obj {
    fn from(r: FiniteSetReduce) -> Self {
        Obj::FiniteSetReduce(r)
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

impl From<IntervalObj> for Obj {
    fn from(r: IntervalObj) -> Self {
        Obj::IntervalObj(r)
    }
}

impl From<OneSideInfinityIntervalObj> for Obj {
    fn from(r: OneSideInfinityIntervalObj) -> Self {
        Obj::OneSideInfinityIntervalObj(r)
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

impl From<StructObj> for Obj {
    fn from(s: StructObj) -> Self {
        Obj::StructObj(s)
    }
}

impl From<ObjAsStructInstanceWithFieldAccess> for Obj {
    fn from(s: ObjAsStructInstanceWithFieldAccess) -> Self {
        Obj::ObjAsStructInstanceWithFieldAccess(s)
    }
}

impl From<InstantiatedTemplateObj> for Obj {
    fn from(t: InstantiatedTemplateObj) -> Self {
        Obj::InstantiatedTemplateObj(t)
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
