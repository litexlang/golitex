package parser

type Stmt interface {
}

type TopStmt struct {
	stmt  Stmt
	isTop bool
}

type DefConceptStmt struct {
	conceptVar  string
	conceptName string
	typeMember  []Declaration
	varMember   []Declaration
	inherit     []string
	thenFacts   []FactStmt
}

type DefPropertyStmt struct {
	name       string
	typeParams []varTypePair
	varParams  []varTypePair
	ifFacts    []FactStmt
	thenFacts  []FactStmt
}

type LocalStmt struct {
	Statements []Stmt
}

type FactStmt interface {
}

type ForallStmt struct {
	typeParams []varTypePair
	varParams  []varTypePair
	ifFacts    []FactStmt
	thenFacts  []FactStmt
}

type PtyStmt struct {
	Name       string
	typeParams []string
	varParams  []Var
}
