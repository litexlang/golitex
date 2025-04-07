package litexmemory

import ast "golitex/litex_ast"

func (fact *StoredSpecFact) String(atom ast.FcAtom) string {
	knownFact := ast.SpecFactStmt{IsTrue: fact.IsTrue, PropName: atom, Params: fact.Params}
	return knownFact.String()
}

func (fact *StoredCondSpecFact) String() string {
	return fact.Fact.String()
}

func (fact *StoredUniSpecFact) String() string {
	return fact.Fact.String()
}
