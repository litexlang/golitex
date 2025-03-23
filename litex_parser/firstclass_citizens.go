package litexparser

type Fc interface {
	fc()
	String() string
	// PackageName() string
}

func (f FcStr) fc()         {}
func (f *FcFnRetValue) fc() {}

type FcStr struct{ Value string }

type FcFnRetValue struct {
	FnName                   FcStr
	TypeParamsObjParamsPairs []ObjParams
}

type ObjParams struct {
	ObjParams []Fc
}

func (f *FcFnRetValue) String() string {
	outPut := string(f.FnName.Value)

	for _, pair := range f.TypeParamsObjParamsPairs {

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

func (f FcStr) String() string {
	// TODO: PackageName
	return string(f.Value)
}

// used for variables that are returned by called function, e,g. f().g().h().  The chain is connected by dots

// func (f *FcChain) String() string {
// 	ret := ""
// 	for i := 0; i < len(f.ChainOfMembers)-1; i++ {
// 		ret += fmt.Sprintf("%s.", (f.ChainOfMembers)[i])
// 	}
// 	return ret + (f.ChainOfMembers)[len(f.ChainOfMembers)-1].String()
// }

type ReversedFc struct {
	// TODO
}

// TODO: Fc 可能还要加一个函数，reverse，即从parameters作为第一位的key。这样貌似做compare更容易
func Reverse(f Fc) *ReversedFc {
	panic("")
}

// func (f *FcChain) fc() {}
// type FcChainMem interface {
// 	fc()
// 	fcMemChainMemType()
// 	String() string
// }

// func (f FcStr) fcMemChainMemType()         {}
// func (f *FcFnRetValue) fcMemChainMemType() {}

// type FcChain struct{ ChainOfMembers []FcChainMem }
