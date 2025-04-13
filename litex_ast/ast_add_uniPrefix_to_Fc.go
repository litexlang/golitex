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

type NameDepthMap map[string]int

func AddUniPrefixToFcAtom(atom *FcAtom, uniParams NameDepthMap) *FcAtom {
	if prefixNum, ok := fcAtomInUniParams(atom, uniParams); ok {
		atom.Value = strings.Repeat(glob.UniParamPrefix, prefixNum) + atom.Value
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

	newFcFn := FcFn{FcAtom{}, []*FcFnSeg{}}
	newFcFn.FnHead = *AddUniPrefixToFcAtom(&fcAsFcFn.FnHead, uniParams)

	for _, seg := range fcAsFcFn.ParamSegs {
		curSeg := &FcFnSeg{[]Fc{}}
		newFcFn.ParamSegs = append(newFcFn.ParamSegs, curSeg)
		for _, param := range seg.Params {
			newFc, err := AddUniPrefixToFc(param, uniParams)
			if err != nil {
				return nil, err
			}
			curSeg.Params = append(curSeg.Params, newFc)
		}
	}

	return &newFcFn, nil
}

func fcAtomInUniParams(atom *FcAtom, uniParams NameDepthMap) (int, bool) {
	if atom.PkgName == glob.EmptyPkgName {
		if prefixNum, ok := uniParams[atom.Value]; ok {
			return prefixNum, true
		}
	}
	return 0, false
}
