package parser

type Stmt interface {
}

type TopStmt struct {
	stmt  Stmt
	isTop bool
}

type DefConceptStmt struct {
	ConceptVar    string
	ConceptName   string
	ConceptParams []VarTypePair
	ConceptFacts  []FactExprStmt
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
}
type ExistStmt struct{}

type IfStmt struct {
	ConceptParams []VarTypePair
	ConceptFacts  []FactExprStmt
	VarParams     []VarTypePair
	VarFacts      []FactExprStmt
	Facts         []FactStmt
}

type PtyStmt struct {
	Name   string
	params []Var
}
