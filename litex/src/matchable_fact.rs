enum MatchableFact {
    AtomicFact(AtomicFact),
    ExistFact(ExistFact),
    AndFact(AndFact),
    OrFact(OrFact),
}