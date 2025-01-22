package parser

import "golitex/symbol"

type Stmt interface {
}

type TypeVarPair struct {
	Var  string
	Type string
}

type Fact interface{}
type ExistFact struct{}

type DefConceptStmt struct {
	ConceptVar    string
	ConceptName   string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	ExistFacts    []ExistFact
	Facts         []Fact
}

type DefPropertyStmt struct {
	ConceptVar    string
	ConceptName   string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	ExistFacts    []ExistFact
	Facts         []Fact
}

type IfFact struct {
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

type OptFact struct {
	name string
	args []symbol.Symbol
}
