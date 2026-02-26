enum MatchableFact {
    AtomicFact(Box<AtomicFact>),
    ExistFact(Box<ExistFact>),
    AndFact(AndFact),
    OrFact(OrFact),
}