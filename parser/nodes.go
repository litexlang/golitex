package parser

type Stmt interface {
	stmt()
}

type TopStmt struct {
	stmt  Stmt
	isPub bool
}

type typeConcept string

type DefVarStmt struct {
	decl  fcVarDecl
	facts []FactStmt
}

func (stmt *DefVarStmt) stmt() {}

type DefConceptStmt struct {
	typeVar            typeVar
	conceptName        typeConcept
	inherit            []typeConcept
	typeVarMember      []fcVarDecl
	typeFnMember       []fcFnDecl
	typePropertyMember []propertyDecl
	varMember          []fcVarDecl
	fnMember           []fcFnDecl
	propertyMember     []propertyDecl
	thenFacts          []FactStmt
}

func (c *DefConceptStmt) stmt() {}

type DefTypeStmt struct {
	typeVar        typeVar
	conceptName    typeConcept
	varMember      []fcVarDecl
	fnMember       []fcFnDecl
	propertyMember []propertyDecl
	thenFacts      []FactStmt
}

func (t *DefTypeStmt) stmt() {}

type fcVarDecl struct {
	name string
	tp   fcVarType
}

type fcFnDecl struct {
	name string
	tp   fcFnType
}

type propertyDecl struct {
	name string
	tp   propertyType
}

type DefPropertyStmt struct {
	decl      propertyDecl
	ifFacts   []FactStmt
	thenFacts []FactStmt
}

func (c *DefPropertyStmt) stmt() {}

type DefFnStmt struct {
	decl      fcFnDecl
	ifFacts   []FactStmt
	thenFacts []FactStmt
}

func (f *DefFnStmt) stmt() {}

type localStmt struct {
	statements []Stmt
}

func (l *localStmt) stmt() {}

type FactStmt interface {
	factStmt()
	stmt()
}

type ForallStmt struct {
	typeParams []typeConceptPair
	varParams  []fcTypePair
	ifFacts    []FactStmt
	thenFacts  []FactStmt
}

func (l *ForallStmt) factStmt() {}
func (l *ForallStmt) stmt()     {}

type FuncPtyStmt struct {
	isTrue bool
	fc     Fc
}

type propertyFactStmt interface {
	setT(b bool)
	factStmt()
	stmt()
	propertyFactStmt()
}

func (p *FuncPtyStmt) factStmt() {}
func (p *FuncPtyStmt) stmt()     {}

func (f *FuncPtyStmt) setT(b bool) {
	f.isTrue = b
}
func (f *FuncPtyStmt) propertyFactStmt() {
}

type typeConceptPair struct {
	Var  typeVar
	Type typeConcept
}

type typeVar string

type fcTypePair struct {
	Var  FcStr
	Type fcType
}

type fcType interface {
	fcType()
}

type fcVarType string

func (f fcVarType) fcType() {}

type fcFnType struct {
	typeParamsTypes []typeConceptPair
	varParamsTypes  []fcTypePair
	retType         fnRetType
}

func (f *fcFnType) fcType() {}

type propertyType struct {
	typeParams []typeConceptPair
	varParams  []fcTypePair
}

func (f *propertyType) fcType() {}

type fnRetType interface {
	fnRetType()
}

func (f fcVarType) fnRetType() {}
func (f *fcFnType) fnRetType() {}

type claimStmt struct {
	toCheck []FactStmt
	proof   []Stmt
}

func (f *claimStmt) stmt() {}

type defAliasStmt struct {
	name     string
	variable Fc
}

func (f *defAliasStmt) stmt() {}

type knowStmt struct {
	facts []FactStmt
}

func (f *knowStmt) stmt() {}

type defExistStmt struct {
	decl      propertyDecl
	ifFacts   []FactStmt
	fnMember  []fcFnDecl
	varMember []fcVarDecl
	thenFacts []FactStmt
}

func (s *defExistStmt) stmt() {}
