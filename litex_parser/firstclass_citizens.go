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

type FcStr string

type FcFnRetValue struct {
	FnName                   FcStr
	TypeParamsVarParamsPairs []TypeParamsAndParamsPair
}

type FcMemChain []Fc

type TypeParamsAndParamsPair struct {
	TypeParams []TypeVarStr
	VarParams  []Fc
}

func (f *FcFnRetValue) String() string {
	outPut := string(f.FnName)

	for _, pair := range f.TypeParamsVarParamsPairs {
		if len(pair.TypeParams) > 0 {
			outPut += "["
			for i := 0; i < len(pair.TypeParams)-1; i++ {
				outPut += string(pair.TypeParams[i])
				outPut += ", "
			}
			outPut += string(pair.TypeParams[len(pair.TypeParams)-1])
			outPut += "]"
		}

		if len(pair.VarParams) > 0 {
			outPut += "("
			for i := 0; i < len(pair.VarParams)-1; i++ {
				outPut += pair.VarParams[i].String()
				outPut += ", "
			}
			outPut += pair.VarParams[len(pair.VarParams)-1].String()
			outPut += ")"
		}
	}

	return outPut
}

func (f FcStr) String() string {
	return string(f)
}

// used for variables that are returned by called function, e,g. f().g().h().  The chain is connected by dots

func (f *FcMemChain) String() string {
	ret := ""
	for i := 0; i < len(*f)-1; i++ {
		ret += fmt.Sprintf("%s.", (*f)[i])
	}
	return ret + (*f)[len(*f)-1].String()
}
