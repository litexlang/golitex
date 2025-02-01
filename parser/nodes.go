package parser

import "fmt"

type Stmt interface {
	stmt()
}

type topStmt struct {
	stmt  Stmt
	isPub bool
}

type typeConcept string

type defVarStmt struct {
	decl  fcVarDecl
	facts []factStmt
}

func (stmt *defVarStmt) stmt() {}

type defConceptStmt struct {
	typeVar            typeVar
	conceptName        typeConcept
	inherit            []typeConcept
	typeVarMember      []fcVarDecl
	typeFnMember       []fcFnDecl
	typePropertyMember []propertyDecl
	varMember          []fcVarDecl
	fnMember           []fcFnDecl
	propertyMember     []propertyDecl
	thenFacts          []factStmt
}

func (c *defConceptStmt) stmt() {}

type defTypeStmt struct {
	typeVar        typeVar
	conceptName    typeConcept
	varMember      []fcVarDecl
	fnMember       []fcFnDecl
	propertyMember []propertyDecl
	thenFacts      []factStmt
}

func (f *defTypeStmt) stmt() {}

type fcVarDecl struct {
	varTypePairs []fcStrTypePair
}

type fcFnDecl struct {
	name string
	tp   fcFnType
}

type propertyDecl struct {
	name string
	tp   propertyType
}

type defPropertyStmt struct {
	decl      propertyDecl
	ifFacts   []factStmt
	thenFacts []factStmt
}

func (c *defPropertyStmt) stmt() {}

type defFnStmt struct {
	decl      fcFnDecl
	ifFacts   []factStmt
	thenFacts []factStmt
}

func (f *defFnStmt) stmt() {}

type localStmt struct {
	statements []Stmt
}

func (l *localStmt) stmt() {}

type factStmt interface {
	factStmt()
	stmt()
}

type forallStmt struct {
	typeParams []typeConceptPair
	varParams  []fcStrTypePair
	ifFacts    []factStmt
	thenFacts  []factStmt
}

func (l *forallStmt) factStmt() {}
func (l *forallStmt) stmt()     {}

type funcPtyStmt struct {
	isTrue bool
	fc     Fc
}

// 1 = 2 -1 = 1 * 1, vars = [1, 2 -1, 1 * 1], opt = "="
type relationFactStmt struct {
	isTrue bool
	vars   []Fc
	opt    Fc
}

func (r *relationFactStmt) factStmt()         {}
func (r *relationFactStmt) stmt()             {}
func (r *relationFactStmt) setT(b bool)       { r.isTrue = b }
func (r *relationFactStmt) propertyFactStmt() {}

type notFactStmt interface {
	setT(b bool)
	factStmt()
	stmt()
	propertyFactStmt()
}

type typedFuncPtyStmt struct {
	name        string
	typeParams  []typeVar
	fcTypePairs []fcTypePair
}

type fcTypePair struct {
	fc Fc
	tp fcType
}

func (p *funcPtyStmt) factStmt() {}
func (p *funcPtyStmt) stmt()     {}

func (f *funcPtyStmt) setT(b bool) {
	f.isTrue = b
}
func (f *funcPtyStmt) propertyFactStmt() {
}

type typeConceptPair struct {
	Var  typeVar
	Type typeConcept
}

type typeVar string

type fcStrTypePair struct {
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
	varParamsTypes  []fcStrTypePair
	retType         fnRetType
}

func (f *fcFnType) fcType() {}

// 需要让 property 不能是 fctype
type propertyType struct {
	typeParams []typeConceptPair
	varParams  []fcStrTypePair
}

func (f *propertyType) fcType() {}

type fnRetType interface {
	fnRetType()
}

func (f fcVarType) fnRetType() {}
func (f *fcFnType) fnRetType() {}

type claimStmt struct {
	toCheck []factStmt
	proof   []Stmt
}

func (f *claimStmt) stmt() {}

type defuseStmt struct {
	name     string
	variable Fc
}

func (f *defuseStmt) stmt() {}

type knowStmt struct {
	facts []factStmt
}

func (f *knowStmt) stmt() {}

type fnRetTypeMemberDecl interface {
	fnRetTypeMemberDecl()
}

func (f *fcVarDecl) fnRetTypeMemberDecl() {}
func (f *fcFnDecl) fnRetTypeMemberDecl()  {}

type defExistStmt struct {
	decl      propertyDecl
	ifFacts   []factStmt
	member    []fnRetTypeMemberDecl
	thenFacts []factStmt
}

func (s *defExistStmt) stmt() {}

type haveStmt struct {
	propertyStmt notFactStmt
	member       []string
}

func (s *haveStmt) stmt() {}

type fcDecl interface{ fcDecl() }

func (f *fcVarDecl) fcDecl()    {}
func (f *fcFnDecl) fcDecl()     {}
func (f *propertyDecl) fcDecl() {}

type defMemberStmt struct {
	typeConcept typeConceptPair
	varType     fcStrTypePair
	member      fcDecl
	facts       []factStmt
}

func (s *defMemberStmt) stmt() {}

type defTypeMemberStmt struct {
	typeConcept typeConceptPair
	member      fcDecl
	facts       []factStmt
}

func (s *defTypeMemberStmt) stmt() {}

type parseStmtErr struct {
	previous error
	stmt     tokenBlock
}

func (e *parseStmtErr) Error() string {
	curTok, err := e.stmt.header.currentToken()
	if err != nil {
		return fmt.Sprintf("error at %s, column %d: %s", e.stmt.header.String(), e.stmt.header.getIndex(), e.previous.Error())
	} else {
		return fmt.Sprintf("error at %s, column %d, at '%s': %s", e.stmt.header.String(), e.stmt.header.getIndex(), curTok, e.previous.Error())
	}
}
