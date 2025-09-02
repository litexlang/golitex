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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) ProveOverFiniteSet(stmt *ast.ProveOverFiniteSetStmt) (glob.ExecState, error) {
	enums := [][]ast.Fc{}
	for _, paramSet := range stmt.Fact.ParamSets {
		enumFacts, ok := exec.env.GetEnumFact(paramSet.String())
		if !ok {
			return glob.ExecState_Error, fmt.Errorf("prove over finite set statement error: enum not found")
		}
		enums = append(enums, enumFacts)
	}

	cartesianProductOfFcs := glob.CartesianProduct(enums)

	if len(cartesianProductOfFcs) == 0 {
		return exec.verProveOverFiniteSet_ProveForall(stmt, cartesianProductOfFcs)
	} else {
		if len(cartesianProductOfFcs) != numberOfItemsOfCartesianProduct(cartesianProductOfFcs) {
			return glob.ExecState_False, fmt.Errorf("prove over finite set statement error: cartesian product of fcs is not correct")
		} else {
			for i := 0; i < numberOfItemsOfCartesianProduct(cartesianProductOfFcs); i++ {
				cartesianProductAtI := cartesianAt(cartesianProductOfFcs, i)

				ok, err := exec.verProveOverFiniteSet_ProveAtProveSectionI(stmt, cartesianProductAtI)
				if err != nil {
					return glob.ExecState_Error, err
				}
				if !ok {
					return glob.ExecState_False, fmt.Errorf("failed to prove at prove section %d", i)
				}
			}
			return glob.ExecState_True, nil
		}
	}
}

func (exec *Executor) verProveOverFiniteSet_ProveAtProveSectionI(stmt *ast.ProveOverFiniteSetStmt, cartesianProductAtI []ast.Fc) (bool, error) {
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	err := exec.defObjStmt(ast.NewDefObjStmt(stmt.Fact.Params, stmt.Fact.ParamSets, getParamEqualFcSlice(stmt.Fact.Params, cartesianProductAtI)), false)
	if err != nil {
		return false, err
	}

	for _, domFact := range stmt.Fact.DomFacts {
		err := exec.env.NewFact(domFact)
		if err != nil {
			return false, err
		}
	}

	for _, fact := range stmt.Proofs {
		state, err := exec.Stmt(fact)
		if err != nil {
			return false, err
		}
		if state != glob.ExecState_True {
			return false, nil
		}
	}

	for _, fact := range stmt.Fact.ThenFacts {
		state, err := exec.factStmt(fact)
		if err != nil {
			return false, err
		}
		if state != glob.ExecState_True {
			return false, nil
		}
	}

	return true, nil
}

func getParamEqualFcSlice(params []string, equalTo []ast.Fc) []ast.FactStmt {
	result := []ast.FactStmt{}
	for i, param := range params {
		result = append(result, ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom(param), equalTo[i]}))
	}
	return result
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

func cartesianAt(sets [][]ast.Fc, idx int) []ast.Fc {
	n := len(sets)
	result := make([]ast.Fc, n)

	// 先算出每一维的 stride (步长)
	strides := make([]int, n)
	stride := 1
	for i := n - 1; i >= 0; i-- {
		strides[i] = stride
		stride *= len(sets[i])
	}

	// 逐维展开 idx
	for i := 0; i < n; i++ {
		size := len(sets[i])
		result[i] = sets[i][(idx/strides[i])%size]
	}

	return result
}

func (exec *Executor) verProveOverFiniteSet_ProveForall(stmt *ast.ProveOverFiniteSetStmt, cartesianProductOfFcs [][]ast.Fc) (glob.ExecState, error) {
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
			state, err := exec.factStmt(fact)
			if err != nil {
				return glob.ExecState_Error, err
			}
			if state != glob.ExecState_True {
				return glob.ExecState_False, fmt.Errorf("failed to prove instantiated then facts: %s", fact)
			}
		}
	}

	return glob.ExecState_True, nil
}
