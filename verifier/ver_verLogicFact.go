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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) verLogicExpr(stmt *ast.LogicExprStmt, state VerState) (bool, error) {
	if ok, err := ver.isValidLogicalFact(stmt); err != nil || !ok {
		return ver.factDefer(stmt, state, false, err, "")
	}

	if !stmt.IsOr {
		return ver.verAndFact(stmt, state)
	} else {
		return ver.verOrFact(stmt, state)
	}
}

func (ver *Verifier) isValidLogicalFact(stmt *ast.LogicExprStmt) (bool, error) {
	if len(stmt.Facts) > glob.MaxLogicExprFactsNum {
		return false, fmt.Errorf("logic expr has too many facts: %d, expect no more than %d. Please use prove_or to prove long or facts", len(stmt.Facts), glob.MaxLogicExprFactsNum)
	}

	return true, nil
}

func (ver *Verifier) verAndFact(stmt *ast.LogicExprStmt, state VerState) (bool, error) {
	for _, fact := range stmt.Facts {
		ok, err := ver.FactStmt(fact, state)
		if err != nil {
			return ver.factDefer(stmt, state, false, err, "")
		}
		if !ok {
			return ver.factDefer(stmt, state, false, nil, "")
		}
	}
	return ver.factDefer(stmt, state, true, nil, "")
}

func (ver *Verifier) verOrFact(stmt *ast.LogicExprStmt, state VerState) (bool, error) {
	totalIndexes := []int{}
	for i := range stmt.Facts {
		totalIndexes = append(totalIndexes, i)
	}
	totoalSubsetOfIndexes := 1 << len(totalIndexes)

	// iterate all subsets of totalIndexes
	for i := range totoalSubsetOfIndexes {

		for j := range totalIndexes {
			if i == 0 && j == 0 {
				continue
			}

			if i&(1<<j) != 0 {
				indexes := map[int]struct{}{}
				for k := range totalIndexes {
					if i&(1<<k) != 0 {
						indexes[k] = struct{}{}
					}
				}

				ok, err := ver.IfFactsNotTrueThenOtherPartOfLogicalExprIsTrue(indexes, stmt, state)
				if err != nil {
					return false, err
				}
				if ok {
					return ver.factDefer(stmt, state, ok, nil, "")
				}
			}
		}
	}
	return false, nil
}

func (ver *Verifier) IfFactsNotTrueThenOtherPartOfLogicalExprIsTrue(notTrueFactIndexes map[int]struct{}, stmt *ast.LogicExprStmt, state VerState) (bool, error) {
	ver.newEnv(ver.env, ver.env.CurMatchEnv)
	defer ver.deleteEnvAndRetainMsg()

	for index := range notTrueFactIndexes {
		err := ver.env.NewFact(stmt.Facts[index].ReverseIsTrue())
		if err != nil {
			return false, err
		}
	}

	newOrFacts := make([]ast.Reversable_LogicOrSpec_Stmt, 0, len(notTrueFactIndexes))
	for index := range len(stmt.Facts) {
		if _, ok := notTrueFactIndexes[index]; ok {
			continue
		}
		newOrFacts = append(newOrFacts, stmt.Facts[index])
	}

	if len(newOrFacts) == 0 {
		return false, nil
	} else if len(newOrFacts) == 1 {
		ok, err := ver.FactStmt(newOrFacts[0], state)
		if err != nil {
			return false, err
		}
		return ok, nil
	} else if len(newOrFacts) > 1 {
		ok, err := ver.verLogicExpr(ast.NewOrAndFact(true, newOrFacts), state)
		if err != nil {
			return false, err
		}
		return ok, nil
	} else {
		return false, nil
	}
}
