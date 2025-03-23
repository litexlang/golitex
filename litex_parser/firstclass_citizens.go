package litexparser

import "fmt"

type Fc interface {
	fc()
	String() string
	PkgName() string
}

func (f FcAtom) fc()               {}
func (f *FcFnRet) fc()             {}
func (f FcAtom) PkgName() string   { return f.FromPkg }
func (f *FcFnRet) PkgName() string { return f.FnName.FromPkg }

type FcAtom struct {
	FromPkg string
	Value   string
}

type FcFnRet struct {
	FnName FcAtom
	Params []ObjParams
}

type ObjParams struct {
	ObjParams []Fc
}

func (f *FcFnRet) String() string {
	outPut := string(f.FnName.Value)

	for _, pair := range f.Params {
		if len(pair.ObjParams) > 0 {
			outPut += "("
			for i := 0; i < len(pair.ObjParams)-1; i++ {
				outPut += pair.ObjParams[i].String()
				outPut += ", "
			}
			outPut += pair.ObjParams[len(pair.ObjParams)-1].String()
			outPut += ")"
		}
	}

	return outPut
}

func (f FcAtom) String() string {
	if f.FromPkg == "" {
		return string(f.Value)
	} else {
		return fmt.Sprintf("%s::%s", f.FromPkg, string(f.Value))
	}
}

// used for variables that are returned by called function, e,g. f().g().h().  The chain is connected by dots

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
