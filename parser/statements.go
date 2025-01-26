package parser

type Stmt interface {
	stmt()
}

type TopStmt struct {
	stmt  Stmt
	isPub bool
}

type DefConceptStmt struct {
	conceptVar    varType
	conceptName   typeConcept
	inherit       []typeConcept
	typeVarMember []varType
	typeFnMember  []fnType
	varMember     []varType
	fnMember      []fnType
	thenFacts     []FactStmt
}

func (c *DefConceptStmt) stmt() {}

type DefPropertyStmt struct {
	name       propertyName
	typeParams []typeConceptPair
	varParams  []varTypePair
	ifFacts    []FactStmt
	thenFacts  []FactStmt
}

func (c *DefPropertyStmt) stmt() {}

type LocalStmt struct {
	statements []Stmt
}

func (l *LocalStmt) stmt() {}

type FactStmt interface {
	factStmt()
	stmt()
}

type ptyStmt interface {
	setT()
	factStmt()
	stmt()
}

type ForallStmt struct {
	typeParams []typeConceptPair
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
