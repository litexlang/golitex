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
	"strconv"
	"strings"

	glob "golitex/glob"
)

// set builder 是如何写成 FnObj 的：
// 1. 第一个参数是 param
// 2. 第二个参数是 parent set
// 3. 第三个参数是 facts
// 4. facts 的格式是：[typeEnumInt] [paramCountInt] [propName] [params...] [next fact typeEnumInt] ...
// 5. typeEnumInt 是 fact 的类型，0 表示 FalsePure, 1 表示 FalseExist_St, 2 表示 TrueExist_St, 3 表示 TruePure
// 6. paramCountInt 是 fact 的参数个数
// 7. propName 是 fact 的属性名
type SetBuilderStruct struct {
	Param     string
	ParentSet Obj
	Facts     SpecFactPtrSlice
}

func IsSetBuilder(obj Obj) bool {
	if asSetBuilderObj, ok := obj.(*FnObj); ok {
		return asSetBuilderObj.FnHead.String() == glob.KeywordSetBuilder
	}
	return false
}

// ToSetBuilderStruct converts a FnObj representing an set builder to SetBuilderStruct
func (fnObj *FnObj) ToSetBuilderStruct() (*SetBuilderStruct, error) {
	if len(fnObj.Params) < 2 {
		return nil, fmt.Errorf("set builder expects at least param and parent set, got %d params", len(fnObj.Params))
	}

	// Extract param (first parameter)
	paramAtom, ok := fnObj.Params[0].(Atom)
	if !ok {
		return nil, fmt.Errorf("expected parameter as atom, got %T", fnObj.Params[0])
	}
	param := string(paramAtom)

	// Extract parentSet (second parameter)
	parentSet := fnObj.Params[1]

	// Parse facts from Params[2:]
	// Format: [typeEnumInt] [paramCountInt] [propName] [params...] [next fact typeEnumInt] ...
	facts := SpecFactPtrSlice{}
	i := 2
	for i < len(fnObj.Params) {
		// Read type enum (as integer string)
		typeEnumAtom, ok := fnObj.Params[i].(Atom)
		if !ok {
			return nil, fmt.Errorf("expected type enum as atom at index %d, got %T", i, fnObj.Params[i])
		}
		typeEnumStr := string(typeEnumAtom)
		typeEnumInt, err := strconv.Atoi(typeEnumStr)
		if err != nil {
			return nil, fmt.Errorf("failed to parse type enum at index %d: %s", i, err)
		}
		typeEnum := SpecFactEnum(typeEnumInt)
		if typeEnum > FalseExist_St {
			return nil, fmt.Errorf("invalid type enum value: %d", typeEnumInt)
		}
		i++

		if i >= len(fnObj.Params) {
			return nil, fmt.Errorf("unexpected end of params after type enum at index %d", i-1)
		}

		// Read param count (as integer string)
		paramCountAtom, ok := fnObj.Params[i].(Atom)
		if !ok {
			return nil, fmt.Errorf("expected param count as atom at index %d, got %T", i, fnObj.Params[i])
		}
		paramCountStr := string(paramCountAtom)
		paramCount, err := strconv.Atoi(paramCountStr)
		if err != nil {
			return nil, fmt.Errorf("failed to parse param count at index %d: %s", i, err)
		}
		i++

		if i >= len(fnObj.Params) {
			return nil, fmt.Errorf("unexpected end of params after param count at index %d", i-1)
		}

		// Read propName
		propNameAtom, ok := fnObj.Params[i].(Atom)
		if !ok {
			return nil, fmt.Errorf("expected propName as atom at index %d, got %T", i, fnObj.Params[i])
		}
		i++

		// Read params
		if i+paramCount > len(fnObj.Params) {
			return nil, fmt.Errorf("not enough params: expected %d params, but only %d remaining", paramCount, len(fnObj.Params)-i)
		}
		params := make([]Obj, paramCount)
		for j := 0; j < paramCount; j++ {
			params[j] = fnObj.Params[i+j]
		}
		i += paramCount

		// Create SpecFactStmt
		specFact := NewSpecFactStmt(typeEnum, propNameAtom, params, glob.BuiltinLine)
		facts = append(facts, specFact)
	}

	return NewSetBuilderStruct(param, parentSet, facts), nil
}

func (setBuilderStruct *SetBuilderStruct) ReplaceParamWithNewParam(newParam string) (*SetBuilderStruct, error) {
	uniMap := map[string]Obj{setBuilderStruct.Param: Atom(newParam)}

	newParentSet, err := setBuilderStruct.ParentSet.Instantiate(uniMap)
	if err != nil {
		return nil, err
	}

	newFacts := make(SpecFactPtrSlice, len(setBuilderStruct.Facts))
	for i, fact := range setBuilderStruct.Facts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return nil, err
		}
		newFacts[i] = newFact.(*SpecFactStmt)
	}

	return NewSetBuilderStruct(newParam, newParentSet, newFacts), nil
}

func NewSetBuilderStruct(param string, parentSet Obj, facts SpecFactPtrSlice) *SetBuilderStruct {
	return &SetBuilderStruct{
		Param:     param,
		ParentSet: parentSet,
		Facts:     facts,
	}
}

func (setBuilderStruct *SetBuilderStruct) ToFnObj() (*FnObj, error) {
	return MakeSetBuilderObj(setBuilderStruct.Param, setBuilderStruct.ParentSet, setBuilderStruct.Facts)
}

func (setBuilderStruct *SetBuilderStruct) String() string {
	var builder strings.Builder
	builder.WriteString(glob.KeySymbolLeftCurly)
	builder.WriteString(setBuilderStruct.Param)
	builder.WriteByte(' ')
	builder.WriteString(setBuilderStruct.ParentSet.String())
	builder.WriteString(glob.KeySymbolColon)

	// Convert facts to strings
	if len(setBuilderStruct.Facts) > 0 {
		factStrings := make([]string, len(setBuilderStruct.Facts))
		for i, fact := range setBuilderStruct.Facts {
			factStrings[i] = fact.String()
		}
		builder.WriteByte(' ')
		builder.WriteString(strings.Join(factStrings, ", "))
	}

	builder.WriteString(glob.KeySymbolRightCurly)
	return builder.String()
}
