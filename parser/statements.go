package parser

type DefConceptStmt struct {
	ConceptVar    string
	ConceptName   string
	ConceptParams []VarTypePair
	ConceptFacts  []Fact
	VarParams     []VarTypePair
	VarFacts      []Fact
	ExistFacts    []ExistFact
	Facts         []Fact
}

type DefPropertyStmt struct {
	Name          string
	ConceptParams []VarTypePair
	ConceptFacts  []Fact
	VarParams     []VarTypePair
	VarFacts      []Fact
	Facts         []Fact
}

type IfStmt struct {
	ConceptParams []VarTypePair
	ConceptFacts  []Fact
	VarParams     []VarTypePair
	VarFacts      []Fact
	Facts         []Fact
}

type CalledPropertyStmt struct {
	Name string
	Args []Var
}

type LocalStmt struct {
	Statements []TopStmt
}
