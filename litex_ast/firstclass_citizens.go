package litex_ast

import (
	"fmt"
	glob "golitex/litex_global"
	"strings"
)

type Fc interface {
	fc()
	String() string
	GetPkgName() string
	Instantiate(map[string]Fc) Fc
}

type FcAtom struct {
	PkgName string
	Value   string
}

type FcFn struct {
	FnHead    FcAtom
	ParamSegs []*FcFnSeg
}

type FcFnSeg struct {
	Params []Fc
}

func NewFcAtom(pkgName string, value string) *FcAtom {
	return &FcAtom{pkgName, value}
}

func NewFcFnPipe(fnHead FcAtom, callPipe []*FcFnSeg) *FcFn {
	return &FcFn{fnHead, callPipe}
}

func NewFcFnPipeSeg(params []Fc) *FcFnSeg {
	return &FcFnSeg{params}
}

func FcSliceString(params []Fc) string {
	output := make([]string, len(params))
	for i, param := range params {
		output[i] = param.String()
	}
	return strings.Join(output, ", ")
}

func (f *FcAtom) fc()                {}
func (f *FcFn) fc()                  {}
func (f *FcAtom) GetPkgName() string { return f.PkgName }
func (f *FcFn) GetPkgName() string   { return f.FnHead.PkgName }

func (f *FcAtom) String() string {
	if f.PkgName == "" {
		return string(f.Value)
	} else {
		return fmt.Sprintf("%s::%s", f.PkgName, string(f.Value))
	}
}

func (f *FcFn) String() string {
	outPut := string(f.FnHead.Value)

	if glob.IsKeySymbolRelaFn(outPut) {
		return fmt.Sprintf("%s %s %s", f.ParamSegs[0].Params[0], outPut, f.ParamSegs[0].Params[1])
	}

	for _, pair := range f.ParamSegs {
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
	return ptr.Value == glob.KeySymbolEqual && ptr.PkgName == ""
}

func IsNumLitFcAtom(f Fc) (string, bool) {
	ptr, ok := f.(*FcAtom)
	if !ok || ptr.Value == "" {
		return "", false
	}

	if isNumLitStr(ptr.Value) {
		return ptr.Value, true
	}
	return "", false
}

func isNumLitStr(s string) bool {
	if s == "" {
		return false
	}

	hasDigit := false
	hasDot := false

	for _, c := range s {
		if c >= '0' && c <= '9' {
			hasDigit = true
		} else if c == '.' {
			if hasDot { // 不能有多个小数点
				return false
			}
			hasDot = true
		} else {
			return false // 非法字符
		}
	}

	return hasDigit
}
