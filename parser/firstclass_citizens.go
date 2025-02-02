package parser

import (
	"fmt"
	"strings"
)

type Fc interface {
	fc()
	String() string
}

type typedFc struct {
	value Fc
	tp    fcType
}

func (fc *typedFc) String() string {
	return fmt.Sprintf("@(%s,%s)", fc.value.String(), fc.tp)
}

func (fc *typedFc) fc() {
}

// used for variables that are returned by called function
type calledFcFnRetValue struct {
	fn         Fc
	typeParams []typeVar
	varParams  []Fc
}

func (f *calledFcFnRetValue) fc() {}
func (f *calledFcFnRetValue) String() string {
	typeParams := []string{}
	for _, p := range f.typeParams {
		if s, ok := p.(typeVarStr); ok {
			typeParams = append(typeParams, string(s))
		}
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

// used for variables that are returned by called function
type FcExpr []Fc

func (f *FcExpr) fc() {}
func (f *FcExpr) String() string {
	ret := ""
	for i := 0; i < len(*f)-1; i++ {
		ret += fmt.Sprintf("%s.", (*f)[i])
	}
	return ret + (*f)[len(*f)-1].String()
}
