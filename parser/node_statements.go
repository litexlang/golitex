package parser

type Stmt interface {
	stmt()
}

type TopStmt struct {
	stmt  Stmt
	isPub bool
}

type DefConceptStmt struct {
	conceptVar  string
	conceptName string
	typeMember  []Declaration
	varMember   []Declaration
	inherit     []string
	thenFacts   []FactStmt
}

func (c *DefConceptStmt) stmt() {}

type DefPropertyStmt struct {
	name       string
	typeParams []varTypePair
	varParams  []varTypePair
	ifFacts    []FactStmt
	thenFacts  []FactStmt
}

func (c *DefPropertyStmt) stmt() {}

type LocalStmt struct {
	Statements []Stmt
}

func (l *LocalStmt) stmt() {}

type FactStmt interface {
	stmt()
	isT() bool
}

type ForallStmt struct {
	isTrue     bool
	typeParams []varTypePair
	varParams  []varTypePair
	ifFacts    []FactStmt
	thenFacts  []FactStmt
}

func (l *ForallStmt) stmt() {}

func (f *ForallStmt) IsT() bool {
	return f.isTrue
}

type PtyStmt struct {
	isTrue     bool
	Name       string
	typeParams []string
	varParams  []Var
}

func (p *PtyStmt) stmt() {}

func (f *PtyStmt) isT() bool {
	return f.isTrue
}
