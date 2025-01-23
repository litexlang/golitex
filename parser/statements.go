package parser

type Stmt interface {
	toTopStmt() TopStmt
}

type DefConceptStmt struct {
	ConceptVar    string
	ConceptName   string
	ConceptParams *[]VarTypePair
	ConceptFacts  *[]FactStmt
	VarParams     *[]VarTypePair
	VarFacts      *[]FactStmt
	ExistFacts    *[]ExistFactStmt
	Facts         *[]FactStmt
}

type DefPropertyStmt struct {
	Name          string
	ConceptParams []VarTypePair
	ConceptFacts  []FactStmt
	VarParams     []VarTypePair
	VarFacts      []FactStmt
	Facts         []FactStmt
}

type IfStmt struct {
	ConceptParams []VarTypePair
	ConceptFacts  []FactStmt
	VarParams     []VarTypePair
	VarFacts      []FactStmt
	Facts         []FactStmt
}

type CalledPropertyStmt struct {
	Name string
	Args []Var
}

type LocalStmt struct {
	Statements []TopStmt
}

type FactStmt interface{}
type ExistFactStmt struct{}
