package litexmemory

import (
	parser "golitex/litex_parser"
)

func (fact *StoredSpecFact) String(atom parser.FcAtom) string {
	knownFact := parser.SpecFactStmt{IsTrue: fact.IsTrue, Opt: atom, Params: fact.Params}
	return knownFact.String()
}

func (fact *StoredCondSpecFact) String() string {
	return fact.Fact.String()
}

func (fact *StoredUniSpecFact) String() string {
	return fact.Fact.String()
}
