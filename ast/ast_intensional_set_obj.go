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

	glob "golitex/glob"
)

type IntensionalSetObjStruct struct {
	Param     string
	ParentSet Obj
	Facts     SpecFactPtrSlice
}

func IsIntensionalSetObj(obj Obj) bool {
	if asIntensionalSetStmt, ok := obj.(*FnObj); ok {
		return asIntensionalSetStmt.FnHead.String() == glob.KeywordIntensionalSet
	}
	return false
}

// FnObjToIntensionalSetObjStruct converts a FnObj representing an intensional set to IntensionalSetObj
func FnObjToIntensionalSetObjStruct(fnObj *FnObj) (*IntensionalSetObjStruct, error) {
	if len(fnObj.Params) < 2 {
		return nil, fmt.Errorf("intensional set expects at least param and parent set, got %d params", len(fnObj.Params))
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

	return &IntensionalSetObjStruct{
		Param:     param,
		ParentSet: parentSet,
		Facts:     facts,
	}, nil
}

// IntensionalSetObjStructToFnObj converts an IntensionalSetObj to a FnObj
func IntensionalSetObjStructToFnObj(intensionalSet *IntensionalSetObjStruct) (*FnObj, error) {
	obj, err := MakeIntensionalSetObj(intensionalSet.Param, intensionalSet.ParentSet, intensionalSet.Facts)
	if err != nil {
		return nil, err
	}
	fnObj, ok := obj.(*FnObj)
	if !ok {
		return nil, fmt.Errorf("MakeIntensionalSetObj returned %T, expected *FnObj", obj)
	}
	return fnObj, nil
}
