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
	IsPropTrue         bool
	PropName           Atom
	ExistFreeParams    []string
	ExistFreeParamSets []Obj
	Params             []Obj
	Line               uint
}

func NewExistStFactStruct(factType SpecFactType, propName Atom, isPropTrue bool, existFreeParams []string, existFreeParamSets []Obj, params []Obj, line uint) *ExistStFactStruct {
	return &ExistStFactStruct{
		FactType:           factType,
		PropName:           propName,
		IsPropTrue:         isPropTrue,
		ExistFreeParams:    existFreeParams,
		ExistFreeParamSets: existFreeParamSets,
		Params:             params,
		Line:               line,
	}
}

func NewExistStFact(factType SpecFactType, propName Atom, isPropTrue bool, existFreeParams []string, existFreeParamSets []Obj, params []Obj, line uint) *SpecFactStmt {
	s := NewExistStFactStruct(factType, propName, isPropTrue, existFreeParams, existFreeParamSets, params, line)
	return s.ToExistStFact()
}

func (s *ExistStFactStruct) ToExistStFact() *SpecFactStmt {
	params := []Obj{}

	if !s.IsPropTrue {
		params = append(params, Atom("-1"))
	}

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

	if f.Params[0].String() == "-1" {
		lenOfExistFreeParams, _ := strconv.Atoi(string(f.Params[1].(Atom))) // 第一param变成string然后变成int
		existFreeParams := []string{}
		existFreeParamSets := []Obj{}
		for i := 2; i <= lenOfExistFreeParams*2+1; i++ {
			existFreeParams = append(existFreeParams, string(f.Params[i].(Atom)))
			i++
			existFreeParamSets = append(existFreeParamSets, f.Params[i])
		}

		params := []Obj{}
		for i := lenOfExistFreeParams*2 + 2; i < len(f.Params); i++ {
			params = append(params, f.Params[i])
		}

		return NewExistStFactStruct(ft, propName, false, existFreeParams, existFreeParamSets, params, f.Line)

	} else {
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

		return NewExistStFactStruct(ft, propName, true, existFreeParams, existFreeParamSets, params, f.Line)
	}
}

func (s *ExistStFactStruct) GetTruePureFact() *SpecFactStmt {
	return NewSpecFactStmt(TruePure, s.PropName, s.Params, s.Line)
}

// 作用：know forall x set, cup_x_item cup(x) => exist x_item x st cup_x_item $in x_item 能用到 existParamSet 中出现的 x 去匹配 forall cup_c_item cup(c) => exist c_item c st $in(cup_c_item, c_item)
func (s *ExistStFactStruct) GetTruePureFactWithParamSets() *SpecFactStmt {
	params := []Obj{}
	for _, param := range s.Params {
		params = append(params, param)
	}

	for _, existParamSet := range s.ExistFreeParamSets {
		params = append(params, existParamSet)
	}

	return NewSpecFactStmt(TruePure, s.PropName, params, s.Line)
}
