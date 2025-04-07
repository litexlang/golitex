package litexmemory

import (
	st "golitex/litex_statements"
)

func (fact *StoredSpecFact) String(atom st.FcAtom) string {
	knownFact := st.SpecFactStmt{IsTrue: fact.IsTrue, PropName: atom, Params: fact.Params}
	return knownFact.String()
}

func (fact *StoredCondSpecFact) String() string {
	return fact.Fact.String()
}

func (fact *StoredUniSpecFact) String() string {
	return fact.Fact.String()
}
