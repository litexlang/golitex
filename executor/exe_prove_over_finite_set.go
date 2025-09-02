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
		if len(stmt.Proofs) != len(cartesianProductOfFcs) {
			return glob.ExecState_False, fmt.Errorf("there are %d kind(s) of cartesian product of parameters %s, but there are %d prove sections", len(cartesianProductOfFcs), stmt.Fact.Params, len(stmt.Proofs))
		} else {
			for i := range len(cartesianProductOfFcs) {
				ok, err := exec.verProveOverFiniteSet_ProveAtProveSectionI(stmt, cartesianProductOfFcs[i], i)
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

func (exec *Executor) verProveOverFiniteSet_ProveAtProveSectionI(stmt *ast.ProveOverFiniteSetStmt, cartesianProductAtI []ast.Fc, i int) (bool, error) {
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	err := exec.defObjStmt(ast.NewDefObjStmt(stmt.Fact.Params, stmt.Fact.ParamSets, getParamEqualFcSlice(stmt.Fact.Params, cartesianProductAtI)), false)
	if err != nil {
		return false, err
	}

	for _, fact := range stmt.Proofs[i] {
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
