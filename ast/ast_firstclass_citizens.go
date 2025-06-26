// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

import (
	"fmt"
	glob "golitex/glob"
	"strings"
)

type Fc interface {
	fc()
	String() string
	Instantiate(map[string]Fc) (Fc, error)
	IsAtom() bool
}

func (f FcAtom) fc()          {}
func (f FcAtom) IsAtom() bool { return true }
func (f *FcFn) fc()           {}
func (f *FcFn) IsAtom() bool  { return false }

type FcAtom string // 把 FcAtom 从 {pkgName string, Name string} 改成 string, 本质上是因为后者更合理，实际上还是让速度快了10%

type FcFn struct {
	FnHead Fc // 必须是 fc, 而不是 fcAtom，因为函数头可能是另一个函数的返回值
	Params []Fc
}

// func NewFcAtom(value string) FcAtom {
// 	return FcAtom(value)
// }

func NewFcFn(fnHead Fc, callPipe []Fc) *FcFn {
	return &FcFn{fnHead, callPipe}
}

func FcSliceString(params []Fc) string {
	output := make([]string, len(params))
	for i, param := range params {
		output[i] = param.String()
	}
	return strings.Join(output, ", ")
}

func hasBuiltinOptAndToString(f *FcFn) (bool, string) {
	// if ok, str := isFnSetAndToString(f); ok {
	// 	return true, str
	// }

	ptr, ok := f.FnHead.(FcAtom)
	if !ok {
		return false, ""
	}

	// if ptr.PkgName == glob.EmptyPkg && ptr.Name == glob.AtIndexOp {
	// if ptr.Name == glob.AtIndexOp {
	if string(ptr) == glob.AtIndexOp {
		return true, fmt.Sprintf("%s[%s]", f.Params[0], f.Params[1])
	}

	// if ptr.PkgName == glob.EmptyPkg && ptr.Name == glob.GetIndexOfOp {
	// if ptr.Name == glob.GetIndexOfOp {
	if string(ptr) == glob.GetIndexOfOp {
		return true, fmt.Sprintf("%s[[%s]]", f.Params[0], f.Params[1])
	}

	// if ptr.PkgName == glob.EmptyPkg && ptr.Name == glob.KeySymbolMinus {
	// if ptr.Name == glob.KeySymbolMinus {
	if string(ptr) == glob.KeySymbolMinus {
		if len(f.Params) == 1 {
			return true, fmt.Sprintf("(%s %s)", string(ptr), f.Params[0])
		}

		return true, fmt.Sprintf("(%s %s %s)", f.Params[0], string(ptr), f.Params[1])
	}

	// if ptr.PkgName != glob.EmptyPkg {
	// 	return false, ""
	// }

	// TODO 如何处理unary?

	outPut := string(ptr)
	if glob.IsKeySymbolRelaFn(outPut) {
		return true, fmt.Sprintf("(%s %s %s)", f.Params[0], outPut, f.Params[1])
	}

	return false, ""
}

func IsNumLitFcAtom(f Fc) (string, bool) {
	ptr, ok := f.(FcAtom)
	if !ok || string(ptr) == "" {
		return "", false
	}

	if glob.IsNumLitStr(string(ptr)) {
		return string(ptr), true
	}
	return "", false
}

func IsFcBuiltinInfixOpt(f FcFn) bool {
	ptrHeadAsAtom, ok := f.FnHead.(FcAtom)
	if !ok {
		return false
	}

	return ptrHeadAsAtom.IsBuiltinRelaFn() && len(f.Params) == 2
}

func IsFcBuiltinUnaryFn(fc FcFn) bool {
	fcAsFnHead, ok := fc.FnHead.(FcAtom)
	if !ok {
		return false
	}

	return fcAsFnHead.IsBuiltinUnaryOpt() && len(fc.Params) == 1
}

func (f FcAtom) IsBuiltinUnaryOpt() bool {
	// return f.PkgName == glob.EmptyPkg && glob.IsKeySymbolUnaryFn(f.Name)
	return glob.IsKeySymbolUnaryFn(string(f))
}

func (f FcAtom) IsBuiltinRelaFn() bool {
	// return f.PkgName == glob.EmptyPkg && glob.IsKeySymbolRelaFn(f.Name)
	return glob.IsKeySymbolRelaFn(string(f))
}

func (fcAtom FcAtom) NameIsBuiltinKw_PkgNameEmpty() bool {
	// if fcAtom.PkgName == glob.EmptyPkg {
	_, ok := glob.BuiltinKeywordsSet[string(fcAtom)]
	return ok
	// }
	// return false
}

func IsFcAtomAndHasBuiltinPropName(fc Fc) bool {
	fcAtom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	// if fcAtom.PkgName != glob.EmptyPkg {
	// 	return false
	// }

	return glob.IsBuiltinInfixRelaPropSymbol(string(fcAtom))
}

// func (fc FcAtom) HasGivenNameAndEmptyPkgName(kw string) bool {
// return fc.PkgName == glob.EmptyPkg && fc.Name == kw
// 不含有 ::
// 	return string(fc) == kw && !strings.Contains(string(fc), glob.KeySymbolColonColon)
// }

func IsFcAtomEqualToGivenString(fc Fc, kw string) bool {
	fcAtom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	return string(fcAtom) == kw && !strings.Contains(string(fcAtom), glob.KeySymbolColonColon)
}

func (f *FcFn) HasTwoParamsAndSwitchOrder() (*FcFn, bool) {
	if len(f.Params) != 2 {
		return nil, false
	}

	return NewFcFn(f.FnHead, []Fc{f.Params[0], f.Params[1]}), true
}

func (f *FcFn) HasTwoParams_FirstParamHasTheSameNameAsItself() (*FcFn, bool) {
	if len(f.Params) != 2 {
		return nil, false
	}

	var fHeadAsAtom FcAtom
	var ok bool = false
	fHeadAsAtom, ok = f.FnHead.(FcAtom)
	if !ok {
		return nil, false
	}

	if f_firstParam_as_fn, ok := f.Params[0].(*FcFn); ok {
		if f_firstParam_headAsAtom, ok := f_firstParam_as_fn.FnHead.(FcAtom); ok {
			if string(f_firstParam_headAsAtom) == string(fHeadAsAtom) {
				// if f_firstParam_headAsAtom.PkgName == fHeadAsAtom.PkgName {
				if len(f_firstParam_as_fn.Params) != 2 {
					return nil, false
				}

				newRight := NewFcFn(f.FnHead, []Fc{f_firstParam_as_fn.Params[0], f.Params[1]})

				return NewFcFn(f.FnHead, []Fc{f_firstParam_as_fn.Params[0], newRight}), true
			}
		}
	}

	return nil, false
}

func GetAtomsInFc(fc Fc) []FcAtom {
	ret := []FcAtom{}

	if fcAtom, ok := fc.(FcAtom); ok {
		ret = append(ret, fcAtom)
		return ret
	}

	if fcFn, ok := fc.(*FcFn); ok {
		for _, param := range fcFn.Params {
			atoms := GetAtomsInFc(param)
			ret = append(ret, atoms...)
		}
		return ret
	}

	return nil
}

// Return the name of the function if it is in the slice, otherwise return empty string
func IsFn_WithHeadNameInSlice(fc Fc, names []string) bool {
	if fc.IsAtom() || len(names) == 0 {
		return false
	}

	asFcFn, ok := fc.(*FcFn)
	if !ok {
		return false
	}

	asFcFnHeadAsAtom, ok := asFcFn.FnHead.(FcAtom)
	if !ok {
		return false
	}

	for _, name := range names {
		// if asFcFnHeadAsAtom.Name == name && asFcFnHeadAsAtom.PkgName == glob.EmptyPkg {
		if string(asFcFnHeadAsAtom) == name {
			return true
		}
	}

	return false
}

func IsFnWithHeadName(fc Fc, name string) bool {
	if fc.IsAtom() || name == "" {
		return false
	}

	fcAsFn, ok := fc.(*FcFn)
	if !ok {
		return false
	}

	fcAsFnHeadAsAtom, ok := fcAsFn.FnHead.(FcAtom)
	if !ok {
		return false
	}

	// return fcAsFnHeadAsAtom.Name == name && fcAsFnHeadAsAtom.PkgName == glob.EmptyPkg
	return string(fcAsFnHeadAsAtom) == name
}
