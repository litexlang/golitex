package litexparser

import "fmt"

type Fc interface {
	fc()
	String() string
	PkgName() string
}

type FcAtom struct {
	FromPkg string
	Value   string
}

type FcFnCallPipe struct {
	FnName   FcAtom
	CallPipe []FcFnCallPipeSeg
}

type FcFnCallPipeSeg struct {
	Params []Fc
}

func (f *FcAtom) fc()                   {}
func (f *FcFnCallPipe) fc()             {}
func (f *FcAtom) PkgName() string       { return f.FromPkg }
func (f *FcFnCallPipe) PkgName() string { return f.FnName.FromPkg }

func (f *FcAtom) String() string {
	if f.FromPkg == "" {
		return string(f.Value)
	} else {
		return fmt.Sprintf("%s::%s", f.FromPkg, string(f.Value))
	}
}

func (f *FcFnCallPipe) String() string {
	outPut := string(f.FnName.Value)

	for _, pair := range f.CallPipe {
		if len(pair.Params) > 0 {
			outPut += "("
			for i := 0; i < len(pair.Params)-1; i++ {
				outPut += pair.Params[i].String()
				outPut += ", "
			}
			outPut += pair.Params[len(pair.Params)-1].String()
			outPut += ")"
		}
	}

	return outPut
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
