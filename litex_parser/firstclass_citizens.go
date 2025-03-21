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
func (f *FcChain) fc()      {}

type FcStr string

type FcFnRetValue struct {
	FnName                   FcStr
	TypeParamsObjParamsPairs []TypeParamsAndObjParamsPair
}

type FcChainMem interface {
	fc()
	fcMemChainMemType()
	String() string
}

func (f FcStr) fcMemChainMemType()         {}
func (f *FcFnRetValue) fcMemChainMemType() {}

type FcChain struct{ ChainOfMembers []FcChainMem }

type TypeParamsAndObjParamsPair struct {
	// TypeParams []TypeObjStr
	ObjParams []Fc
}

func (f *FcFnRetValue) String() string {
	outPut := string(f.FnName)

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
	return string(f)
}

// used for variables that are returned by called function, e,g. f().g().h().  The chain is connected by dots

func (f *FcChain) String() string {
	ret := ""
	for i := 0; i < len(f.ChainOfMembers)-1; i++ {
		ret += fmt.Sprintf("%s.", (f.ChainOfMembers)[i])
	}
	return ret + (f.ChainOfMembers)[len(f.ChainOfMembers)-1].String()
}

type ReversedFc struct {
	// TODO
}

// TODO: Fc 可能还要加一个函数，reverse，即从parameters作为第一位的key。这样貌似做compare更容易
func Reverse(f Fc) *ReversedFc {
	panic("")
}
