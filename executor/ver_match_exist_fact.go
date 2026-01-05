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

package litex_executor

import (
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) MatchExistFact(given *ast.SpecFactStmt, stored *ast.SpecFactStmt, verState *VerState) *glob.VerRet {
	givenExistFactStruct := given.ToExistStFactStruct()
	storedExistFactStruct := stored.ToExistStFactStruct()

	return ver.MatchExistFactStruct(givenExistFactStruct, storedExistFactStruct)
}

func (ver *Verifier) MatchExistFactStruct(given *ast.ExistStFactStruct, stored *ast.ExistStFactStruct) *glob.VerRet {
	if len(given.ExistFreeParams) != len(stored.ExistFreeParams) {
		return glob.NewEmptyVerRetUnknown()
	}

	if given.IsPropTrue != given.IsPropTrue {
		return glob.NewEmptyVerRetUnknown()
	}

	// given: exist x Z : x > 0; stored: exist y N: y > 0
	uniMap := map[string]ast.Obj{}
	for i := range stored.ExistFreeParams {
		uniMap[stored.ExistFreeParams[i]] = ast.Atom(given.ExistFreeParams[i])
	}

	propStoredFact := stored.GetPureFactInside()
	instPropStoredFact, err := propStoredFact.Instantiate(uniMap)
	if err != nil {
		return glob.NewEmptyVerRetUnknown()
	}

	instPropStoredFactStr := instPropStoredFact.String()
	givenPropStr := given.GetPureFactInside().String()
	if instPropStoredFactStr != givenPropStr {
		return glob.NewEmptyVerRetUnknown()
	}

	uniMap2 := map[string]ast.Obj{}
	for i := range stored.ExistFreeParamSets {
		instSet, err := stored.ExistFreeParamSets[i].Instantiate(uniMap2)
		if err != nil {
			return glob.NewEmptyVerRetErr()
		}

		if instSet.String() != given.ExistFreeParamSets[i].String() {
			return glob.NewEmptyVerRetUnknown()
		}

		uniMap[stored.ExistFreeParams[i]] = ast.Atom(given.ExistFreeParams[i])
	}

	return glob.NewEmptyVerRetTrue()
}

// match给定的specFact和uniFact下面的specFact的多个行为 1. 如果不涉及到freeParam，那么要确保他们符号相等 2. 获得各个freeParam对应了哪些哪些givenParam 3. 如果某个freeParam对应了多个givenParam，那就要验证他们都相等否则就unknown
func (ver *Verifier) matchExistFactWithExistFactInKnownUniFact(knownSpecFactInUniFact *env.KnownSpecFact_InUniFact, given *ast.SpecFactStmt) (bool, map[string]ast.Obj, error) {
	knownStruct := knownSpecFactInUniFact.SpecFact.ToExistStFactStruct()
	givenStruct := given.ToExistStFactStruct()

	if len(knownStruct.ExistFreeParams) != len(givenStruct.ExistFreeParams) {
		return false, nil, nil
	}

	if knownStruct.IsPropTrue != givenStruct.IsPropTrue {
		return false, nil, nil
	}

	var err error
	givenStruct, err = ver.Env.MakeExistFactStructDoesNotConflictWithDefinedNames(givenStruct, knownSpecFactInUniFact.UniFact.Params)
	if err != nil {
		return false, nil, err
	}

	uniMap := map[string]ast.Obj{}
	for i := range knownStruct.ExistFreeParams {
		uniMap[knownStruct.ExistFreeParams[i]] = ast.Atom(givenStruct.ExistFreeParams[i])
	}

	knownPropFact := knownStruct.GetPureFactWithParamSets()
	instKnownPureFact, err := knownPropFact.Instantiate(uniMap)
	if err != nil {
		return false, nil, err
	}

	// matchParamsInGivenExistFactWithKnownExistFactInUniFact
	// REMARK 应该有问题
	// TODO: 这里的match我还是有点慌，因为涉及到的参数其实是不存在的，应该用纯symbol去匹配好像更好一点
	tmp := env.MakeKnownSpecFact_InUniFact(instKnownPureFact.(*ast.SpecFactStmt), knownSpecFactInUniFact.UniFact)
	ok, m, err := ver.matchUniFactParamsWithSpecFactParams(&tmp, givenStruct.GetPureFactWithParamSets())

	if err != nil || !ok {
		return false, nil, nil
	} else {
		// 它的 set 也能对应上
		newUniMap := map[string]ast.Obj{}
		for i := range knownStruct.ExistFreeParamSets {
			instParamSet, err := knownStruct.ExistFreeParamSets[i].Instantiate(m)
			if err != nil {
				return false, nil, err
			}

			instParamSet, err = instParamSet.Instantiate(newUniMap)
			if err != nil {
				return false, nil, err
			}

			if instParamSet.String() != givenStruct.ExistFreeParamSets[i].String() {
				return false, nil, nil
			}

			newUniMap[knownStruct.ExistFreeParams[i]] = ast.Atom(givenStruct.ExistFreeParams[i])
		}

		return ok, m, err
	}
}
