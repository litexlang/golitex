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
	"fmt"
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

	// given: exist x Z : x > 0; stored: exist y N: y > 0
	uniMap := map[string]ast.Obj{}
	for i := range stored.ExistFreeParams {
		uniMap[stored.ExistFreeParams[i]] = ast.Atom(given.ExistFreeParams[i])
	}

	propStoredFact := stored.ToTruePureFact()
	instPropStoredFact, err := propStoredFact.Instantiate(uniMap)
	if err != nil {
		return glob.NewEmptyVerRetUnknown()
	}

	instPropStoredFactStr := instPropStoredFact.String()
	givenPropStr := given.ToTruePureFact().String()
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

func (ver *Verifier) matchExistFactWithExistFactInKnownUniFact(knownSpecFactInUniFact *env.KnownSpecFact_InUniFact, given *ast.SpecFactStmt) (bool, map[string]ast.Obj, error) {
	knownStruct := knownSpecFactInUniFact.SpecFact.ToExistStFactStruct()
	givenStruct := given.ToExistStFactStruct()

	if len(knownStruct.ExistFreeParams) != len(givenStruct.ExistFreeParams) {
		return false, nil, fmt.Errorf("length of exist free params is not equal")
	}

	uniMap := map[string]ast.Obj{}
	for i := range knownStruct.ExistFreeParams {
		uniMap[knownStruct.ExistFreeParams[i]] = ast.Atom(givenStruct.ExistFreeParams[i])
	}

	knownPropFact := knownStruct.ToTruePureFact()
	instKnownPureFact, err := knownPropFact.Instantiate(uniMap)
	if err != nil {
		return false, nil, err
	}

	// matchParamsInGivenExistFactWithKnownExistFactInUniFact
	// TODO: 这里的match我还是有点慌，因为涉及到的参数其实是不存在的，应该用纯symbol去匹配好像更好一点
	tmp := env.MakeKnownSpecFact_InUniFact(instKnownPureFact.(*ast.SpecFactStmt), knownSpecFactInUniFact.UniFact)
	ok, m, err := ver.matchUniFactParamsWithSpecFactParams(&tmp, givenStruct.ToTruePureFact())

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
				return false, nil, fmt.Errorf("param set %s in known exist fact is not equal to param set %s in given exist fact", knownStruct.ExistFreeParamSets[i].String(), givenStruct.ExistFreeParamSets[i].String())
			}

			newUniMap[knownStruct.ExistFreeParams[i]] = ast.Atom(givenStruct.ExistFreeParams[i])
		}

		return ok, m, err
	}
}

// func (ver *Verifier) matchParamsInGivenExistFactWithKnownExistFactInUniFact(existParamMap map[string]ast.Obj, givenPureFactOfExistFact *ast.SpecFactStmt, knownInstPureFactOfExistFact *ast.SpecFactStmt) (bool, map[string]ast.Obj, error) {
// 	for i, param := givenPureFactOfExistFact.Params {
// 		ok, map[string]ast.Obj = ver.matchObjOfParamsInGivenExistFactWithKnownExistFactInUniFact(param, knownInstPureFactOfExistFact.Params[i])
// 	}
// }
