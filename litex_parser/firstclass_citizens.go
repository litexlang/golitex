package litexparser

import (
	"fmt"
	"strings"
)

type Fc interface {
	fc()
	String() string
}

func (fc *TypedFc) fc()           {}
func (f *CalledFcFnRetValue) fc() {}
func (f FcStr) fc()               {}
func (f *FcFnCallChain) fc()      {}

type TypedFc struct {
	value Fc
	tp    FcPropType
}

func (fc *TypedFc) String() string {
	return fmt.Sprintf("@(%s,%s)", fc.value.String(), fc.tp)
}

// used for variables that are returned by called function
type CalledFcFnRetValue struct {
	Fn         Fc
	TypeParams []typeVar
	VarParams  []Fc
}

func (f *CalledFcFnRetValue) String() string {
	typeParams := []string{}
	for _, p := range f.TypeParams {
		if s, ok := p.(TypeVarStr); ok {
			typeParams = append(typeParams, string(s))
		}
	}
	strTypeParams := ""
	if len(typeParams) > 0 {
		strTypeParams = fmt.Sprintf("[%s]", strings.Join(typeParams, ", "))
	}

	varParams := []string{}
	for _, p := range f.VarParams {
		varParams = append(varParams, p.String())
	}
	strVarParams := ""
	if len(varParams) > 0 {
		strVarParams = fmt.Sprintf("(%s)", strings.Join(varParams, ", "))
	}

	return fmt.Sprintf("%s%s%s", f.Fn, strTypeParams, strVarParams)
}

type FcStr string

func (f FcStr) String() string {
	return string(f)
}

// used for variables that are returned by called function, e,g. f().g().h().  The chain is connected by dots
type FcFnCallChain []Fc

func (f *FcFnCallChain) String() string {
	ret := ""
	for i := 0; i < len(*f)-1; i++ {
		ret += fmt.Sprintf("%s.", (*f)[i])
	}
	return ret + (*f)[len(*f)-1].String()
}

type fcUndefinedType interface {
	fcUndefinedType()
	fcType()
}

func (f *UndefinedFnType) fcUndefinedType()   {}
func (f *UndefinedVarType) fcUndefinedType()  {}
func (f *UndefinedPropType) fcUndefinedType() {}
