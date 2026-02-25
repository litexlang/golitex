enum Fact {
    AtomicFact(Box<AtomicFact>),
    ExistFact(ExistFact),
    OrFact(OrFact),
    ForallFact(ForallFact),
    ChainFact(ChainFact),
    ForallFactWithIff(ForallFactWithIff),
}

enum AtomicFact {
    OrdinaryAtomicFact(OrdinaryAtomicFact),
    EqualFact(EqualFact),
    LessFact(LessFact),
    GreaterFact(GreaterFact),
    LessEqualFact(LessEqualFact),
    GreaterEqualFact(GreaterEqualFact),
    IsSetFact(IsSetFact),
    IsNonemptySetFact(IsNonemptySetFact),
    IsFiniteSetFact(IsFiniteSetFact),
}

struct OrdinaryAtomicFact {
    pub predicate: Box<Predicate>,
    pub body: Vec<Box<Obj>>,
}

