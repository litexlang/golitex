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

type FnSetObj interface {
	obj()
	String() string
	Instantiate(map[string]Obj) (Obj, error)
	ToLatexString() string
	fnSetObj()
	GetRetSet() Obj
}

func (f *FnSetObjWithoutName) fnSetObj() {}
func (f *FnSetObjWithName) fnSetObj()    {}

type FnSetObjWithoutName struct {
	ParamSets ObjSlice
	DomFacts  ReversibleFacts
	RetSet    Obj
}

// 有两种情况： 有名字，没名字
// 有名字：fn f(x, y R: ... ) ret {...}
// 没名字：fn (R, R) ret {...}。这时候 param 和 fnName 和 dom 和 then 全是空的
type FnSetObjWithName struct {
	FnName    string
	Params    []string
	ParamSets ObjSlice
	DomFacts  ReversibleFacts
	RetSet    Obj
	ThenFacts ReversibleFacts
}

func NewFnSetObjWithName(fnName string, params []string, paramSets ObjSlice, domFacts ReversibleFacts, retSet Obj, thenFacts ReversibleFacts) *FnSetObjWithName {
	return &FnSetObjWithName{fnName, params, paramSets, domFacts, retSet, thenFacts}
}

func (f *FnSetObjWithName) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeywordFn)
	builder.WriteString(" ")
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

func (f *FnSetObjWithName) Instantiate(uniMap map[string]Obj) (Obj, error) {
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

	return NewFnSetObjWithName(f.FnName, f.Params, newParamSets, newDomFacts, f.RetSet, newThenFacts), nil
}

func (f *FnSetObjWithName) GetRetSet() Obj {
	return f.RetSet
}

func (f *FnSetObjWithoutName) GetRetSet() Obj {
	return f.RetSet
}
