package litexparser

import (
	"fmt"
	glob "golitex/litex_global"
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
	CallPipe []*FcFnPipeSeg
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

	if glob.IsBuiltinRelaFn(outPut) {
		return fmt.Sprintf("%s %s %s", f.CallPipe[0].Params[0], outPut, f.CallPipe[0].Params[1])
	}

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

func IsNumber(f Fc) (string, bool) {
	ptr, ok := f.(*FcAtom)
	if !ok {
		return "", false
	}

	s := ptr.Value
	if s == "" {
		return "", false
	}

	i := 0
	hasDigit := false
	hasDot := false

	for ; i < len(s); i++ {
		c := s[i]
		if c >= '0' && c <= '9' {
			hasDigit = true
		} else if c == '.' {
			if hasDot { // 不能有多个小数点
				return "", false
			}
			hasDot = true
		} else {
			return "", false // 非法字符
		}
	}

	if !hasDigit { // 至少要有一个数字
		return "", false
	}

	return s, true
}
