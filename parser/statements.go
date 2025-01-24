package parser

type Stmt interface {
	toTopStmt() TopStmt
}

type DefConceptStmt struct {
	ConceptVar    string
	ConceptName   string
	ConceptParams []VarTypePair
	ConceptFacts  []FactStmt
	VarParams     []VarTypePair
	VarFacts      []FactStmt
	ExistFacts    []ExistStmt
	Facts         []FactStmt
}

type DefPropertyStmt struct {
	Name          string
	ConceptParams []VarTypePair
	ConceptFacts  []FactStmt
	VarParams     []VarTypePair
	VarFacts      []FactStmt
	Facts         []FactStmt
}

type LocalStmt struct {
	Statements []Stmt
}

type FactExprStmt interface{}
type FactStmt interface {
	toTopStmt() TopStmt
}
type ExistStmt struct{}

type IfStmt struct {
	ConceptParams []VarTypePair
	ConceptFacts  []FactStmt
	VarParams     []VarTypePair
	VarFacts      []FactStmt
	Facts         []FactStmt
}

type PtyStmt struct {
	Name   string
	params []Var
}
