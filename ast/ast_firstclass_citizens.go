// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_ast

import (
	"fmt"
	glob "golitex/glob"
	"strings"
)

type Fc interface {
	fc()
	String() string
	// GetPkgName() string
	Instantiate(map[string]Fc) (Fc, error)
	IsAtom() bool
}

func (f *FcAtom) fc()          {}
func (f *FcAtom) IsAtom() bool { return true }
func (f *FcFn) fc()            {}
func (f *FcFn) IsAtom() bool   { return false }

type FcAtom struct {
	PkgName string
	Name    string
	As      Fc
}

type FcFn struct {
	FnHead    Fc // 必须是 fc, 而不是 fcAtom，因为函数头可能是另一个函数的返回值
	ParamSegs [][]Fc
	As        Fc
}

func NewFcAtom(pkgName string, value string, as Fc) *FcAtom {
	return &FcAtom{pkgName, value, as}
}

func NewFcFn(fnHead Fc, callPipe [][]Fc, as Fc) *FcFn {
	return &FcFn{fnHead, callPipe, as}
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

	ptr, ok := f.FnHead.(*FcAtom)
	if !ok {
		return false, ""
	}

	if ptr.PkgName == glob.EmptyPkg && ptr.Name == glob.KeySymbolMinus {
		if len(f.ParamSegs[0]) == 1 {
			return true, fmt.Sprintf("(%s %s)", ptr.Name, f.ParamSegs[0][0])
		}

		return true, fmt.Sprintf("(%s %s %s)", f.ParamSegs[0][0], ptr.Name, f.ParamSegs[0][1])
	}

	if ptr.PkgName != glob.EmptyPkg {
		return false, ""
	}

	// TODO 如何处理unary?

	outPut := string(ptr.Name)
	if glob.IsKeySymbolRelaFn(outPut) {
		return true, fmt.Sprintf("(%s %s %s)", f.ParamSegs[0][0], outPut, f.ParamSegs[0][1])
	}

	return false, ""
}

func IsNumLitFcAtom(f Fc) (string, bool) {
	ptr, ok := f.(*FcAtom)
	if !ok || ptr.Name == "" {
		return "", false
	}

	if glob.IsNumLitStr(ptr.Name) {
		return ptr.Name, true
	}
	return "", false
}

func IsFcBuiltinInfixOpt(f FcFn) bool {
	ptrHeadAsAtom, ok := f.FnHead.(*FcAtom)
	if !ok {
		return false
	}

	return ptrHeadAsAtom.IsBuiltinRelaFn() && len(f.ParamSegs) == 1 && len(f.ParamSegs[0]) == 2
}

func IsFcBuiltinUnaryFn(fc FcFn) bool {
	fcAsFnHead, ok := fc.FnHead.(*FcAtom)
	if !ok {
		return false
	}

	return fcAsFnHead.IsBuiltinUnaryOpt() && len(fc.ParamSegs) == 1 && len(fc.ParamSegs[0]) == 1
}

func (f *FcAtom) IsBuiltinUnaryOpt() bool {
	return f.PkgName == glob.EmptyPkg && glob.IsKeySymbolUnaryFn(f.Name)
}

func (f *FcAtom) IsBuiltinRelaFn() bool {
	return f.PkgName == glob.EmptyPkg && glob.IsKeySymbolRelaFn(f.Name)
}

// func (f *FcFn) IsBuiltinFcSet() bool {
// 	ptrHeadAsAtom, ok := f.FnHead.(*FcAtom)
// 	if !ok {
// 		return false
// 	}

// 	return ptrHeadAsAtom.PkgName == glob.BuiltinEmptyPkgName && ptrHeadAsAtom.Name == glob.KeywordFn
// }

func (fcAtom *FcAtom) NameIsUniParam_PkgNameEmpty() (string, bool) {
	if strings.HasPrefix(fcAtom.Name, glob.UniParamPrefix) && fcAtom.PkgName == glob.EmptyPkg {
		return fcAtom.Name, true
	}
	return "", false
}

func (fcAtom *FcAtom) NameIsBuiltinKw_PkgNameEmpty() bool {
	if fcAtom.PkgName == glob.EmptyPkg {
		_, ok := glob.BuiltinKeywordsSet[fcAtom.Name]
		return ok
	}
	return false
}

func IsFcAtomAndHasBuiltinPropName(fc Fc) bool {
	fcAtom, ok := fc.(*FcAtom)
	if !ok {
		return false
	}

	if fcAtom.PkgName != glob.EmptyPkg {
		return false
	}

	return glob.IsBuiltinInfixRelaPropSymbol(fcAtom.Name)
}

func (fc *FcAtom) HasGivenNameAndEmptyPkgName(kw string) bool {
	return fc.PkgName == glob.EmptyPkg && fc.Name == kw
}

func IsFcAtom_HasGivenName_EmptyPkgName(fc Fc, kw string) bool {
	fcAtom, ok := fc.(*FcAtom)
	if !ok {
		return false
	}
	return fcAtom.HasGivenNameAndEmptyPkgName(kw)
}

func (f *FcFn) HasTwoParamsAndSwitchOrder() (*FcFn, bool) {
	if len(f.ParamSegs) != 1 {
		return nil, false
	}

	if len(f.ParamSegs[0]) != 2 {
		return nil, false
	}

	return NewFcFn(f.FnHead, [][]Fc{{f.ParamSegs[0][1], f.ParamSegs[0][0]}}, f.As), true
}

func (f *FcFn) HasTwoParams_FirstParamHasTheSameNameAsItself() (*FcFn, bool) {
	if len(f.ParamSegs) != 1 {
		return nil, false
	}

	if len(f.ParamSegs[0]) != 2 {
		return nil, false
	}

	var fHeadAsAtom *FcAtom
	var ok bool = false
	fHeadAsAtom, ok = f.FnHead.(*FcAtom)
	if !ok {
		return nil, false
	}

	if f_firstParam_as_fn, ok := f.ParamSegs[0][0].(*FcFn); ok {
		if f_firstParam_headAsAtom, ok := f_firstParam_as_fn.FnHead.(*FcAtom); ok {
			if f_firstParam_headAsAtom.Name == fHeadAsAtom.Name && f_firstParam_headAsAtom.PkgName == fHeadAsAtom.PkgName {
				if len(f_firstParam_as_fn.ParamSegs) != 1 {
					return nil, false
				}

				if len(f_firstParam_as_fn.ParamSegs[0]) != 2 {
					return nil, false
				}

				newRight := NewFcFn(f.FnHead, [][]Fc{{f_firstParam_as_fn.ParamSegs[0][1], f.ParamSegs[0][1]}}, f.As)

				return NewFcFn(f.FnHead, [][]Fc{{f_firstParam_as_fn.ParamSegs[0][0], newRight}}, f.As), true
			}
		}
	}

	return nil, false
}
