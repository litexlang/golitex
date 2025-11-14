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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_ast

import (
	"fmt"
	glob "golitex/glob"
	"slices"
	"strings"
)

type Obj interface {
	fc()
	String() string
	Instantiate(map[string]Obj) (Obj, error)
	ToLatexString() string
	ReplaceFc(oldFc Obj, newFc Obj) Obj // 这是必要的，因为 have fn 的 proof 里可能出现 replace fc 的情况
}

func (f FcAtom) fc() {}
func (f *FcFn) fc()  {}

func (f FcAtom) ReplaceFc(oldFc Obj, newFc Obj) Obj {
	if f.String() == oldFc.String() {
		return newFc
	}
	return f
}

func (f *FcFn) ReplaceFc(oldFc Obj, newFc Obj) Obj {
	if f.String() == oldFc.String() {
		return newFc
	}

	var newFcFnHead = f.FnHead.ReplaceFc(oldFc, newFc)

	newFcParams := make([]Obj, len(f.Params))
	for i, param := range f.Params {
		newFcParams[i] = param.ReplaceFc(oldFc, newFc)
	}

	newFcFn := NewFcFn(newFcFnHead, newFcParams)
	return newFcFn
}

type FcAtom string

type FcFn struct {
	FnHead Obj
	Params []Obj
}

func NewFcFn(fnHead Obj, callPipe []Obj) *FcFn {
	return &FcFn{fnHead, callPipe}
}

func fcSliceString(params []Obj) string {
	output := make([]string, len(params))
	for i, param := range params {
		output[i] = param.String()
	}
	return strings.Join(output, ", ")
}

func hasBuiltinOptAndToString(f *FcFn) (bool, string) {
	ptr, ok := f.FnHead.(FcAtom)
	if !ok {
		return false, ""
	}

	if string(ptr) == glob.KeySymbolMinus {
		return true, fmt.Sprintf("(%s %s %s)", f.Params[0], string(ptr), f.Params[1])
	}

	outPut := string(ptr)
	if glob.IsKeySymbolRelaFn(outPut) {
		return true, fmt.Sprintf("(%s %s %s)", f.Params[0], outPut, f.Params[1])
	}

	return false, ""
}

func IsNumLitFcAtom(f Obj) (string, bool) {
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

	return glob.IsKeySymbolRelaFn(string(ptrHeadAsAtom)) && len(f.Params) == 2
}

func IsFcBuiltinUnaryFn(fc FcFn) bool {
	fcAsFnHead, ok := fc.FnHead.(FcAtom)
	if !ok {
		return false
	}

	return fcAsFnHead.IsBuiltinUnaryOpt() && len(fc.Params) == 1
}

func (f FcAtom) IsBuiltinUnaryOpt() bool {
	return (string(f)) == glob.KeySymbolMinus
}

func IsFcAtomAndHasBuiltinPropName(fc Obj) bool {
	fcAtom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	return glob.IsBuiltinInfixRelaPropSymbol(string(fcAtom))
}

func IsFcAtomAndEqualToStr(fc Obj, name string) bool {
	fcAsFcAtom, ok := fc.(FcAtom)
	if !ok {
		return false
	}

	return string(fcAsFcAtom) == name
}

func GetAtomsInFc(fc Obj) []FcAtom {
	ret := []FcAtom{}

	switch asFc := fc.(type) {
	case FcAtom:
		ret = append(ret, asFc)
	case *FcFn:
		for _, param := range asFc.Params {
			atoms := GetAtomsInFc(param)
			ret = append(ret, atoms...)
		}
	}
	return ret
}

// Return the name of the function if it is in the slice, otherwise return empty string
func IsFn_WithHeadNameInSlice(fc Obj, names []string) bool {
	asFcFn, ok := fc.(*FcFn)
	if !ok {
		return false
	}

	asFcFnHeadAsAtom, ok := asFcFn.FnHead.(FcAtom)
	if !ok {
		return false
	}

	return slices.Contains(names, string(asFcFnHeadAsAtom))
}

func (atom FcAtom) HasPkgName() bool {
	// 如果 atom 里有 :: 就是true
	return strings.Contains(string(atom), glob.KeySymbolColonColon)
}
