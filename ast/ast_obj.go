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
	"strings"
)

type Obj interface {
	obj()
	String() string
	Instantiate(map[string]Obj) (Obj, error)
	ToLatexString() string
	ReplaceObj(oldObj Obj, newObj Obj) Obj // 这是必要的，因为 have fn 的 proof 里可能出现 replace obj 的情况
}

func (f Atom) obj()   {}
func (f *FnObj) obj() {}

func (f Atom) ReplaceObj(oldObj Obj, newObj Obj) Obj {
	if f.String() == oldObj.String() {
		return newObj
	}
	return f
}

func (f *FnObj) ReplaceObj(oldObj Obj, newObj Obj) Obj {
	if f.String() == oldObj.String() {
		return newObj
	}

	var newFnObjHead = f.FnHead.ReplaceObj(oldObj, newObj)

	newObjParams := make([]Obj, len(f.Params))
	for i, param := range f.Params {
		newObjParams[i] = param.ReplaceObj(oldObj, newObj)
	}

	newFnObj := NewFnObj(newFnObjHead, newObjParams)
	return newFnObj
}

type Atom string

type FnObj struct {
	FnHead Obj
	Params []Obj
}

func NewFnObj(fnHead Obj, callPipe []Obj) *FnObj {
	return &FnObj{fnHead, callPipe}
}

func objSliceString(params []Obj) string {
	output := make([]string, len(params))
	for i, param := range params {
		output[i] = param.String()
	}
	return strings.Join(output, ", ")
}

func hasBuiltinOptAndToString(f *FnObj) (bool, string) {
	ptr, ok := f.FnHead.(Atom)
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

func IsNumLitAtomObj(f Obj) (string, bool) {
	ptr, ok := f.(Atom)
	if !ok || string(ptr) == "" {
		return "", false
	}

	if glob.IsNumLitStr(string(ptr)) {
		return string(ptr), true
	}
	return "", false
}

func IsObjBuiltinInfixOpt(f FnObj) bool {
	ptrHeadAsAtom, ok := f.FnHead.(Atom)
	if !ok {
		return false
	}

	return glob.IsKeySymbolRelaFn(string(ptrHeadAsAtom)) && len(f.Params) == 2
}

func IsObjBuiltinUnaryFn(obj FnObj) bool {
	objAsFnHead, ok := obj.FnHead.(Atom)
	if !ok {
		return false
	}

	return objAsFnHead.IsBuiltinUnaryOpt() && len(obj.Params) == 1
}

func (f Atom) IsBuiltinUnaryOpt() bool {
	return (string(f)) == glob.KeySymbolMinus
}

func IsAtomObjAndHasBuiltinPropName(obj Obj) bool {
	atomObj, ok := obj.(Atom)
	if !ok {
		return false
	}

	return glob.IsBuiltinInfixRelaPropSymbol(string(atomObj))
}

func IsAtomObjAndEqualToStr(obj Obj, name string) bool {
	atomObj, ok := obj.(Atom)
	if !ok {
		return false
	}

	return string(atomObj) == name
}

func GetAtomsInObj(obj Obj) []Atom {
	ret := []Atom{}

	switch asObj := obj.(type) {
	case Atom:
		ret = append(ret, asObj)
	case *FnObj:
		for _, param := range asObj.Params {
			atoms := GetAtomsInObj(param)
			ret = append(ret, atoms...)
		}

		// 这里用了性质：intensional set obj的第一位是atom，会出现在这里的ret的第一位；param并不是atom，所以不会出现在ret里
		// 对于内涵集对象，需要特殊处理：移除绑定变量（第一个参数）
		if IsIntensionalSetObj(asObj) {
			atomsFromIntensionalSet := GetAtomsInIntensionalSetObj(asObj)
			ret = append(ret, atomsFromIntensionalSet...)
		}
	}
	return ret
}

func GetAtomsInIntensionalSetObj(f *FnObj) []Atom {
	// Convert FnObj to IntensionalSetObjStruct for easier processing
	intensionalSet, err := FnObjToIntensionalSetObjStruct(f)
	if err != nil {
		// Fallback: extract atoms from all params except the bound parameter
		ret := []Atom{}
		if len(f.Params) > 1 {
			atoms := GetAtomsInObj(f.Params[1])
			ret = append(ret, atoms...)
		}
		// Try to extract from remaining params
		for i := 2; i < len(f.Params); i++ {
			atoms := GetAtomsInObj(f.Params[i])
			ret = append(ret, atoms...)
		}
		return ret
	}

	ret := []Atom{}

	// Extract atoms from parentSet (skip the bound parameter)
	atoms := GetAtomsInObj(intensionalSet.ParentSet)
	ret = append(ret, atoms...)

	// Extract atoms from facts
	for _, fact := range intensionalSet.Facts {
		atoms := fact.GetAtoms()
		ret = append(ret, atoms...)
	}

	return ret
}
