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
	glob "golitex/glob"
	"maps"
	"strings"
)

type FnSetObj struct {
	FnName    string
	Params    []string
	ParamSets ObjSlice
	DomFacts  ReversibleFacts
	RetSet    Obj
	ThenFacts ReversibleFacts
}

func NewFnSetObj(fnName string, params []string, paramSets ObjSlice, domFacts ReversibleFacts, retSet Obj, thenFacts ReversibleFacts) *FnSetObj {
	return &FnSetObj{fnName, params, paramSets, domFacts, retSet, thenFacts}
}

func (f *FnSetObj) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordFn)

	builder.WriteString(f.FnName)

	builder.WriteString("(")
	builder.WriteString(StrObjSetPairs(f.Params, f.ParamSets))

	if len(f.DomFacts) > 0 {
		builder.WriteString(glob.KeySymbolColon)
		builder.WriteString(" ")
		builder.WriteString(inlineReversibleFactsString(f.DomFacts))
	}

	builder.WriteString(")")

	builder.WriteString(f.RetSet.String())

	if len(f.ThenFacts) > 0 {
		builder.WriteString(" ")
		builder.WriteString(glob.KeySymbolLeftCurly)
		builder.WriteString(inlineReversibleFactsString(f.ThenFacts))
		builder.WriteString(glob.KeySymbolRightCurly)
	}

	return builder.String()
}

func (f *FnSetObj) Instantiate(uniMap map[string]Obj) (Obj, error) {
	// 把 uniMap 里的 和 params 冲突的拿出来
	newUniMap := maps.Clone(uniMap)
	for _, param := range f.Params {
		if _, ok := newUniMap[string(param)]; ok {
			delete(newUniMap, string(param))
		}
	}

	newParamSets, err := f.ParamSets.Instantiate(newUniMap)
	if err != nil {
		return nil, err
	}

	newDomFacts, err := f.DomFacts.InstantiateFact(newUniMap)
	if err != nil {
		return nil, err
	}

	newThenFacts, err := f.ThenFacts.InstantiateFact(newUniMap)
	if err != nil {
		return nil, err
	}

	return NewFnSetObj(f.FnName, f.Params, newParamSets, newDomFacts, f.RetSet, newThenFacts), nil
}
