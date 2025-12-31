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
