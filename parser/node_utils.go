package parser

import (
	"fmt"
	"strings"
)

type typeConceptPair struct {
	Var  typeVar
	Type typeConcept
}
type typeVar string

type varTypePair struct {
	Var  FcStr
	Type varType
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
type varType string
type fnType struct {
	typeParamsTypes []typeConcept
	varParamsTypes  []varType
	retType         fnRetType
}

type fnRetType interface {
	fnRetType()
}

func (f *fnType) fnRetType() {}

func (v *varType) fnRetType() {}
