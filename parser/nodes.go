package parser

import (
	"fmt"
	"strings"
)

type Stmt interface {
	stmt()
}

type TopStmt struct {
	stmt  Stmt
	isPub bool
}

type DefConceptStmt struct {
	conceptVar         typeVar
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

func (c *DefConceptStmt) stmt() {}

type DefPropertyStmt struct {
	name       propertyName
	typeParams []typeConceptPair
	varParams  []forallVarTypePair
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
	varParams  []forallVarTypePair
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

type forallVarType interface {
	forallVarType()
}

type typeConceptPair struct {
	Var  typeVar
	Type typeConcept
}

type forallVarTypePair struct {
	Var  Fc
	Type forallVarType
}

type typeVar string

type fcTypePair struct {
	Var  FcStr
	Type fcType
}

type SingletonVar string

type Declaration interface{}
type Var interface{}

type Fc interface {
	fc()
	String() string
}

type FcFnRetVal struct {
	fn         Fc
	typeParams []FcStr
	varParams  []Fc
}

func (f *FcFnRetVal) fc() {}
func (f *FcFnRetVal) String() string {
	typeParams := []string{}
	for _, p := range f.typeParams {
		typeParams = append(typeParams, string(p))
	}
	strTypeParams := ""
	if len(typeParams) > 0 {
		strTypeParams = fmt.Sprintf("[%s]", strings.Join(typeParams, ", "))
	}

	varParams := []string{}
	for _, p := range f.varParams {
		varParams = append(varParams, p.String())
	}
	strVarParams := ""
	if len(varParams) > 0 {
		strVarParams = fmt.Sprintf("(%s)", strings.Join(varParams, ", "))
	}

	return fmt.Sprintf("%s%s%s", f.fn, strTypeParams, strVarParams)
}

type FcStr string

func (f FcStr) fc() {}
func (f FcStr) String() string {
	return string(f)
}

type FcMemberAccessExpr []Fc

func (f *FcMemberAccessExpr) fc() {}
func (f *FcMemberAccessExpr) String() string {
	ret := ""
	for i := 0; i < len(*f)-1; i++ {
		ret += fmt.Sprintf("%s.", (*f)[i])
	}
	return ret + fmt.Sprintf("%s", (*f)[len(*f)-1])
}

type typeConcept string
type propertyName string
type fcType interface {
	fcType()
	forallVarType()
}

type fcVarType string

func (f fcVarType) fcType()        {}
func (f fcVarType) forallVarType() {}

type fcFnType struct {
	typeParamsTypes []typeConceptPair
	varParamsTypes  []fcTypePair
	retType         fcType
}

func (f *fcFnType) fcType()        {}
func (f *fcFnType) forallVarType() {}

type propertyType struct {
	typeParams []typeConceptPair
	varParams  []forallVarTypePair
}

func (f *propertyType) forallVarType() {}
