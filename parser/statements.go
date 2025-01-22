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
	pub           bool
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
	pub           bool
	Name          string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

type IfFactStmt struct {
	pub bool
	IfFact
}

type IfFact struct {
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}

type OptFactStmt struct {
	pub bool
	OptFact
}

type OptFact struct {
	Name string
	Args []symbol.Symbol
}

type LocalStmt struct {
	Statements []Stmt
}

type DefFnStmt struct {
	pub           bool
	Name          string
	ConceptParams []TypeVarPair
	ConceptFacts  []Fact
	VarParams     []TypeVarPair
	VarFacts      []Fact
	Facts         []Fact
}
