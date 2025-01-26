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
	factStmt()
	stmt()
}

type ForallStmt struct {
	isTrue     bool
	typeParams []varTypePair
	varParams  []varTypePair
	ifFacts    []FactStmt
	thenFacts  []FactStmt
}

func (l *ForallStmt) factStmt() {}
func (l *ForallStmt) stmt()     {}

type FuncPtyStmt struct {
	isTrue bool
	fc     Fc
}

func (p *FuncPtyStmt) factStmt() {}
func (p *FuncPtyStmt) stmt()     {}

func (f *FuncPtyStmt) setT(b bool) {
	f.isTrue = b
}
