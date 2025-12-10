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
	facts := SpecFactPtrSlice{}
	i := 2
	for i < len(fnObj.Params) {
		paramStr := fnObj.Params[i].String()
		var typeEnum SpecFactEnum
		var isMarker bool

		// Check if it's a double underscore marker
		switch paramStr {
		case glob.KeywordDoubleUnderscoreTruePure:
			typeEnum = TruePure
			isMarker = true
		case glob.DoubleUnderscoreNotPure:
			typeEnum = FalsePure
			isMarker = true
		case glob.DoubleUnderscoreExist:
			typeEnum = TrueExist_St
			isMarker = true
		case glob.KeywordDoubleUnderscoreNotExist:
			typeEnum = FalseExist_St
			isMarker = true
		}

		if !isMarker {
			i++
			continue
		}

		// Found a marker, start parsing a new spec fact
		i++ // Skip the marker
		if i >= len(fnObj.Params) {
			break
		}

		// Next param is the PropName
		propNameAtom, ok := fnObj.Params[i].(Atom)
		if !ok {
			return nil, fmt.Errorf("expected propName as atom, got %T", fnObj.Params[i])
		}
		i++

		// Collect params until we hit another marker or end
		params := []Obj{}
		for i < len(fnObj.Params) {
			nextParamStr := fnObj.Params[i].String()
			if glob.IsIntensionalSetObjSeparator(nextParamStr) {
				break // Found next marker, stop collecting params
			}
			params = append(params, fnObj.Params[i])
			i++
		}

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
