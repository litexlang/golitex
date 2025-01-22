package parser

type Stmt interface {
	String() string
}

type TypeVarPair struct {
	Var  string
	Type string
}

type Fact struct{}
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
