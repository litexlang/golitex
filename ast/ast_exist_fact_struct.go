// Copyright Jiachen Shen.
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
	"strconv"
)

type ExistStFactStruct struct {
	FactType           SpecFactType
	PropName           Atom
	ExistFreeParams    []string
	ExistFreeParamSets []Obj
	Params             []Obj
	Line               uint
}

func NewExistStFactStruct(factType SpecFactType, propName Atom, existFreeParams []string, existFreeParamSets []Obj, params []Obj, line uint) *ExistStFactStruct {
	return &ExistStFactStruct{
		FactType:           factType,
		PropName:           propName,
		ExistFreeParams:    existFreeParams,
		ExistFreeParamSets: existFreeParamSets,
		Params:             params,
		Line:               line,
	}
}

func NewExistStFact(factType SpecFactType, propName Atom, existFreeParams []string, existFreeParamSets []Obj, params []Obj, line uint) *SpecFactStmt {
	s := NewExistStFactStruct(factType, propName, existFreeParams, existFreeParamSets, params, line)
	return s.ToExistStFact()
}

func (s *ExistStFactStruct) ToExistStFact() *SpecFactStmt {
	params := []Obj{}
	params = append(params, Atom(fmt.Sprintf("%d", len(s.ExistFreeParams))))
	for i := range s.ExistFreeParamSets {
		params = append(params, Atom(s.ExistFreeParams[i]))
		params = append(params, s.ExistFreeParamSets[i])
	}

	for i := range s.Params {
		params = append(params, s.Params[i])
	}

	return NewSpecFactStmt(s.FactType, s.PropName, params, s.Line)
}

func (f *SpecFactStmt) ToExistStFactStruct() *ExistStFactStruct {
	ft := f.FactType
	propName := f.PropName
	lenOfExistFreeParams, _ := strconv.Atoi(string(f.Params[0].(Atom))) // 第一param变成string然后变成int
	existFreeParams := []string{}
	existFreeParamSets := []Obj{}
	for i := 1; i <= lenOfExistFreeParams*2; i++ {
		existFreeParams = append(existFreeParams, string(f.Params[i].(Atom)))
		i++
		existFreeParamSets = append(existFreeParamSets, f.Params[i])
	}

	params := []Obj{}
	for i := lenOfExistFreeParams*2 + 1; i < len(f.Params); i++ {
		params = append(params, f.Params[i])
	}

	return NewExistStFactStruct(ft, propName, existFreeParams, existFreeParamSets, params, f.Line)
}

func (s *ExistStFactStruct) GetTruePureFact() *SpecFactStmt {
	return NewSpecFactStmt(TruePure, s.PropName, s.Params, s.Line)
}
