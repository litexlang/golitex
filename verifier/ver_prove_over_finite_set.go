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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) ProveOverFiniteSet(stmt *ast.ProveOverFiniteSetStmt) (glob.ExecState, error) {
	enums := [][]ast.Fc{}
	for _, paramSet := range stmt.Fact.ParamSets {
		enumFacts, ok := ver.env.GetEnumFact(paramSet.String())
		if !ok {
			return glob.ExecState_Error, fmt.Errorf("prove over finite set statement error: enum not found")
		}
		enums = append(enums, enumFacts)
	}

	cartesianProductOfFcs := glob.CartesianProduct(enums)

	if len(cartesianProductOfFcs) == 0 {
		return ver.verProveOverFiniteSet_ProveForall(stmt, cartesianProductOfFcs)
	} else {
		if len(cartesianProductOfFcs) != numberOfItemsOfCartesianProduct(cartesianProductOfFcs) {
			return glob.ExecState_False, fmt.Errorf("prove over finite set statement error: cartesian product of fcs is not correct")
		} else {

		}
		return ver.verProveOverFiniteSet_ProveForall(stmt, cartesianProductOfFcs)
	}
}

func numberOfItemsOfCartesianProduct(cartesianProductOfFcs [][]ast.Fc) int {
	numberSlice := make([]int, len(cartesianProductOfFcs))
	for i, fcSlice := range cartesianProductOfFcs {
		numberSlice[i] = len(fcSlice)
	}
	ret := 1
	for _, number := range numberSlice {
		ret *= number
	}
	return ret
}

func (ver *Verifier) verProveOverFiniteSet_ProveForall(stmt *ast.ProveOverFiniteSetStmt, cartesianProductOfFcs [][]ast.Fc) (glob.ExecState, error) {
	for _, fcSlice := range cartesianProductOfFcs {
		uniMap := map[string]ast.Fc{}
		for i, param := range stmt.Fact.Params {
			uniMap[param] = fcSlice[i]
		}

		instantiatedThenFacts := []ast.FactStmt{}
		for _, thenFact := range stmt.Fact.ThenFacts {
			instantiatedThenFact, err := thenFact.Instantiate(uniMap)
			if err != nil {
				return glob.ExecState_Error, err
			}
			instantiatedThenFacts = append(instantiatedThenFacts, instantiatedThenFact)
		}

		// ver facts
		for _, fact := range instantiatedThenFacts {
			ok, err := ver.VerFactStmt(fact, Round0NoMsg)
			if err != nil {
				return glob.ExecState_Error, err
			}
			if !ok {
				return glob.ExecState_False, fmt.Errorf("failed to prove instantiated then facts: %s", fact)
			}
		}
	}

	return glob.ExecState_True, nil
}
