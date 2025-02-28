package litexparser

import (
	"fmt"
)

type Fc interface {
	fc()
	String() string
}

func (f FcStr) fc()         {}
func (f *FcFnRetValue) fc() {}
func (f *FcMemChain) fc()   {}

type TypeParamsAndParamsPair struct {
	TypeParams []TypeVarStr
	VarParams  []Fc
}

type FcFnRetValue struct {
	FnName                   FcStr
	TypeParamsVarParamsPairs []TypeParamsAndParamsPair
}

// type FcFnRetValue struct {
// 	Fn         Fc
// 	TypeParams []TypeVarStr
// 	VarParams  []Fc
// }

// used for variables that are returned by called function

func (f *FcFnRetValue) String() string {
	outPut := ""

	return outPut

	// typeParams := []string{}
	// for _, p := range f.TypeParams {
	// 	if s, ok := p.(TypeVarStr); ok {
	// 		typeParams = append(typeParams, string(s))
	// 	}
	// }
	// strTypeParams := ""
	// if len(typeParams) > 0 {
	// 	strTypeParams = fmt.Sprintf("[%s]", strings.Join(typeParams, ", "))
	// }

	// varParams := []string{}
	// for _, p := range f.VarParams {
	// 	varParams = append(varParams, p.String())
	// }
	// strVarParams := ""
	// if len(varParams) > 0 {
	// 	strVarParams = fmt.Sprintf("(%s)", strings.Join(varParams, ", "))
	// }

	// return fmt.Sprintf("%s%s%s", f.Fn, strTypeParams, strVarParams)
}

type FcStr string

func (f FcStr) String() string {
	return string(f)
}

// used for variables that are returned by called function, e,g. f().g().h().  The chain is connected by dots
type FcMemChain []Fc

func (f *FcMemChain) String() string {
	ret := ""
	for i := 0; i < len(*f)-1; i++ {
		ret += fmt.Sprintf("%s.", (*f)[i])
	}
	return ret + (*f)[len(*f)-1].String()
}
