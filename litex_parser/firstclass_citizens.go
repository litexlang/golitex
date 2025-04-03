package litexparser

import (
	"fmt"
	glob "golitex/litex_global"
	"strconv"
	"strings"
)

type Fc interface {
	fc()
	String() string
	GetPkgName() string
}

type FcAtom struct {
	PkgName string
	Value   string
}

type FcFnPipe struct {
	FnHead   FcAtom
	CallPipe []FcFnPipeSeg
}

type FcFnPipeSeg struct {
	Params []Fc
}

func FcSliceString(params []Fc) string {
	output := make([]string, len(params))
	for i, param := range params {
		output[i] = param.String()
	}
	return strings.Join(output, ", ")
}

func (f *FcAtom) fc()                  {}
func (f *FcFnPipe) fc()                {}
func (f *FcAtom) GetPkgName() string   { return f.PkgName }
func (f *FcFnPipe) GetPkgName() string { return f.FnHead.PkgName }

func (f *FcAtom) String() string {
	if f.PkgName == "" {
		return string(f.Value)
	} else {
		return fmt.Sprintf("%s::%s", f.PkgName, string(f.Value))
	}
}

func (f *FcFnPipe) String() string {
	outPut := string(f.FnHead.Value)

	for _, pair := range f.CallPipe {
		if len(pair.Params) > 0 {
			outPut += "("
			for i := 0; i < len(pair.Params)-1; i++ {
				outPut += pair.Params[i].String()
				outPut += ", "
			}
			outPut += pair.Params[len(pair.Params)-1].String()
			outPut += ")"
		} else {
			outPut += "()"
		}
	}

	return outPut
}

func IsEqualOpt(f Fc) bool {
	ptr, ok := f.(*FcAtom)
	if !ok {
		return false
	}
	return ptr.Value == glob.KeywordEqual && ptr.PkgName == ""
}

func IsNumber(f Fc) bool {
	ptr, ok := f.(*FcAtom)
	if !ok {
		return false
	}
	_, err := strconv.ParseFloat(ptr.Value, 64)
	return err == nil
}

// used for objects that are returned by called function, e,g. f().g().h().  The chain is connected by dots

// func (f *FcChain) String() string {
// 	ret := ""
// 	for i := 0; i < len(f.ChainOfMembers)-1; i++ {
// 		ret += fmt.Sprintf("%s.", (f.ChainOfMembers)[i])
// 	}
// 	return ret + (f.ChainOfMembers)[len(f.ChainOfMembers)-1].String()
// }

// func (f *FcChain) fc() {}
// type FcChainMem interface {
// 	fc()
// 	fcMemChainMemType()
// 	String() string
// }

// func (f FcStr) fcMemChainMemType()         {}
// func (f *FcFnRetValue) fcMemChainMemType() {}

// type FcChain struct{ ChainOfMembers []FcChainMem }
