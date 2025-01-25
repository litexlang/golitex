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
	isT() bool
}

type ForallStmt struct {
	isTrue     bool
	typeParams []varTypePair
	varParams  []varTypePair
	ifFacts    []FactStmt
	thenFacts  []FactStmt
}

func (f *ForallStmt) IsT() bool {
	return f.isTrue
}

type PtyStmt struct {
	isTrue     bool
	Name       string
	typeParams []string
	varParams  []Var
}

func (f *PtyStmt) isT() bool {
	return f.isTrue
}
