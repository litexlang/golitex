// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_ast

import (
	"fmt"
	glob "golitex/litex_global"
	"strings"
)

type NameDepthMap map[string]int

func AddUniPrefixToFcAtom(atom *FcAtom, uniParams NameDepthMap) *FcAtom {
	if prefixNum, ok := fcAtomInUniParams(atom, uniParams); ok {
		atom.Name = strings.Repeat(glob.UniParamPrefix, prefixNum) + atom.Name
	}
	return atom
}

func AddUniPrefixToFc(fc Fc, uniParams NameDepthMap) (Fc, error) {
	fcAsAtom, ok := fc.(*FcAtom)
	if ok {
		return AddUniPrefixToFcAtom(fcAsAtom, uniParams), nil
	}

	fcAsFcFn, ok := fc.(*FcFn)
	if !ok {
		return nil, fmt.Errorf("invalid fc %s", fc.String())
	}

	newFcFn := FcFn{&FcAtom{}, [][]Fc{}}
	var err error = nil

	newFcFn.FnHead, err = AddUniPrefixToFc(fcAsFcFn.FnHead, uniParams)
	if err != nil {
		return nil, err
	}

	for _, seg := range fcAsFcFn.ParamSegs {
		curSeg := []Fc{}
		for _, param := range seg {
			newFc, err := AddUniPrefixToFc(param, uniParams)
			if err != nil {
				return nil, err
			}
			curSeg = append(curSeg, newFc)
		}
		newFcFn.ParamSegs = append(newFcFn.ParamSegs, curSeg)
	}

	return &newFcFn, nil
}

func fcAtomInUniParams(atom *FcAtom, uniParams NameDepthMap) (int, bool) {
	if atom.PkgName == glob.BuiltinEmptyPkgName {
		if prefixNum, ok := uniParams[atom.Name]; ok {
			return prefixNum, true
		}
	}
	return 0, false
}
