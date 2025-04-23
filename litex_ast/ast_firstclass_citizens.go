// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

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
	Instantiate(map[string]Fc) (Fc, error)
}

func (f *FcAtom) fc()                {}
func (f *FcFn) fc()                  {}
func (f *FcAtom) GetPkgName() string { return f.PkgName }
func (f *FcFn) GetPkgName() string   { return f.FnHead.PkgName }

type FcAtom struct {
	PkgName string
	Name    string
}

type FcFn struct {
	FnHead    FcAtom
	ParamSegs []*FcFnSeg
}

type FcFnSeg struct {
	Params []Fc
}

type FcEnum uint8

const (
	FcAtomEnum FcEnum = 0
	FcFnEnum   FcEnum = 1
)

func CmpFcType(left, right Fc) (int, FcEnum, error) {
	var knownEnum FcEnum
	switch left.(type) {
	case *FcAtom:
		knownEnum = FcAtomEnum
	case *FcFn:
		knownEnum = FcFnEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", left)
	}

	var givenEnum FcEnum
	switch right.(type) {
	case *FcAtom:
		givenEnum = FcAtomEnum
	case *FcFn:
		givenEnum = FcFnEnum
	default:
		return 0, FcAtomEnum, fmt.Errorf("unknown Fc type: %T", right)
	}

	return int(knownEnum - givenEnum), knownEnum, nil
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

func (f *FcAtom) String() string {
	if f.PkgName == glob.EmptyPkgName {
		return string(f.Name)
	} else {
		return fmt.Sprintf("%s::%s", f.PkgName, string(f.Name))
	}
}

func isFcFnAndToString(f *FcFn) (bool, string) {
	if f.FnHead.Name != "" {
		return false, ""
	}

	// TODO 如何处理unary?

	outPut := string(f.FnHead.Name)
	if glob.IsKeySymbolRelaFn(outPut) {
		return true, fmt.Sprintf("%s %s %s", f.ParamSegs[0].Params[0], outPut, f.ParamSegs[0].Params[1])
	}

	return false, ""
}

func (f *FcFn) String() string {

	// if len(f.ParamSegs) == 1 {
	// 	if len(f.ParamSegs[0].Params) == 1 {
	// 		if glob.IsKeySymbolRelaFn(outPut) {
	// 			return fmt.Sprintf("%s %s", outPut, f.ParamSegs[0].Params[0])
	// 		}
	// 	}
	// }

	// if glob.IsKeySymbolRelaFn(outPut) {
	// 	return fmt.Sprintf("%s %s %s", f.ParamSegs[0].Params[0], outPut, f.ParamSegs[0].Params[1])
	// }

	if ok, str := isFcFnAndToString(f); ok {
		return str
	}

	outPut := string(f.FnHead.Name)
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

func IsEqualOptFc(f Fc) bool {
	ptr, ok := f.(*FcAtom)
	if !ok {
		return false
	}
	return ptr.Name == glob.KeySymbolEqual && ptr.PkgName == ""
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

func (f *FcAtom) IsBuiltinInfixOpt() bool {
	if f.PkgName != "" {
		return false
	}
	if glob.IsKeySymbolRelaFn(f.Name) {
		return true
	}
	return false
}

func (f *FcAtom) IsBuiltinUnaryOpt() bool {
	if f.PkgName != glob.BuiltinUnaryPkgName {
		return false
	}
	if glob.IsKeySymbolUniFn(f.Name) {
		return true
	}
	return false
}

var BuiltinHaveFactExistParamPropParmSepAtom = &FcAtom{glob.BuiltinPkgName, glob.BuiltinHaveFactExistParamPropParmSep}
