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
	glob "golitex/glob"
)

func (exec *Executor) proveByEnumMainLogic(stmt *ast.ProveByEnumStmt) (glob.GlobRet, error) {
	enums := [][]ast.Obj{}
	for _, paramSet := range stmt.Fact.ParamSets {
		enumSet := exec.Env.GetListSetEqualToObj(paramSet)
		if enumSet == nil {
			return glob.NewEmptyGlobErr(), fmt.Errorf("prove over finite set statement error: enum set not found")
		}
		enums = append(enums, enumSet.(*ast.FnObj).Params)
	}

	cartesianProductOfObjs := glob.CartesianProduct(enums)

	if len(stmt.Proof) == 0 {
		return exec.verProveOverFiniteSet_NoProveSection(stmt, cartesianProductOfObjs)
	} else {
		for i := range len(cartesianProductOfObjs) {
			ok, err := exec.verProveOverFiniteSet_ProveAtProveSectionI(stmt, cartesianProductOfObjs[i])
			if err != nil {
				return glob.NewEmptyGlobErr(), err
			}
			if !ok {
				return glob.NewEmptyGlobErr(), fmt.Errorf("failed to prove at prove section %d", i)
			}
		}
		return glob.NewEmptyGlobTrue(), nil
	}
}

func (exec *Executor) verProveOverFiniteSet_ProveAtProveSectionI(stmt *ast.ProveByEnumStmt, cartesianProductAtI []ast.Obj) (bool, error) {
	exec.NewEnv()
	defer exec.deleteEnv()

	defObjStmt := ast.NewDefLetStmt(stmt.Fact.Params, stmt.Fact.ParamSets, getParamEqualObjSlice(stmt.Fact.Params, cartesianProductAtI), stmt.Line)
	execState := exec.defLetStmt(defObjStmt)
	if execState.IsNotTrue() {
		return false, fmt.Errorf(execState.String())
	}

	uniMap := map[string]ast.Obj{}
	for i, param := range stmt.Fact.Params {
		uniMap[param] = cartesianProductAtI[i]
	}

	for _, fact := range stmt.Fact.DomFacts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return false, err
		}
		state := exec.factStmt(instFact)
		if state.IsErr() {
			return false, fmt.Errorf(state.String())
		}
		if state.IsNotTrue() {
			revFacts := instFact.(ast.Spec_OrFact).ReverseIsTrue()
			for _, revFact := range revFacts {
				state := exec.factStmt(revFact)
				if state.IsNotTrue() {
					return false, fmt.Errorf("domain fact in universal fact in prove over finite set statement must be true or not true, it can not be unknown:\n%s", instFact)
				}
			}
			return true, nil
		}
	}

	for _, stmt := range stmt.Proof {
		state := exec.Stmt(stmt)
		if state.IsNotTrue() {
			return false, fmt.Errorf(state.String())
		}
	}

	for _, fact := range stmt.Fact.ThenFacts {
		instFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return false, err
		}
		state := exec.factStmt(instFact)
		if state.IsNotTrue() {
			return false, fmt.Errorf("failed to prove instantiated then facts: %s", instFact)
		}
	}

	return true, nil
}

func getParamEqualObjSlice(params []string, equalTo []ast.Obj) []ast.FactStmt {
	result := []ast.FactStmt{}
	for i, param := range params {
		result = append(result, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{ast.Atom(param), equalTo[i]}, glob.BuiltinLine))
	}
	return result
}

func (exec *Executor) verProveOverFiniteSet_NoProveSection(stmt *ast.ProveByEnumStmt, cartesianProductOfObjs [][]ast.Obj) (glob.GlobRet, error) {
	for _, ObjSlice := range cartesianProductOfObjs {
		uniMap := map[string]ast.Obj{}
		for i, param := range stmt.Fact.Params {
			uniMap[param] = ObjSlice[i]
		}

		hasFalseDomFact := false
		for _, domFact := range stmt.Fact.DomFacts {
			instantiatedDomFact, err := domFact.InstantiateFact(uniMap)
			if err != nil {
				return glob.NewEmptyGlobErr(), err
			}

			state := exec.factStmt(instantiatedDomFact)
			if state.IsErr() {
				return glob.NewEmptyGlobErr(), err
			}
			if state.IsUnknown() {
				domFactAs := instantiatedDomFact.(ast.Spec_OrFact)
				for _, fact := range domFactAs.ReverseIsTrue() {
					state := exec.factStmt(fact)
					if state.IsErr() {
						return glob.NewEmptyGlobErr(), err
					}
					if state.IsUnknown() {
						return glob.NewEmptyGlobErr(), fmt.Errorf("domain fact in universal fact in prove over finite set statement must be true or not true, it can not be unknown:\n%s", instantiatedDomFact)
					}
				}

				hasFalseDomFact = true
				break
			}
		}

		if hasFalseDomFact {
			continue
		}

		instantiatedThenFacts := []ast.FactStmt{}
		for _, thenFact := range stmt.Fact.ThenFacts {
			instantiatedThenFact, err := thenFact.InstantiateFact(uniMap)
			if err != nil {
				return glob.NewEmptyGlobErr(), err
			}
			instantiatedThenFacts = append(instantiatedThenFacts, instantiatedThenFact)
		}

		// ver facts
		for _, fact := range instantiatedThenFacts {
			state := exec.factStmt(fact)
			if state.IsErr() {
				return glob.NewEmptyGlobErr(), fmt.Errorf(state.String())
			}
			if state.IsUnknown() {
				return glob.NewEmptyGlobErr(), fmt.Errorf("failed to prove instantiated then facts: %s", fact)
			}
		}
	}

	return glob.NewEmptyGlobTrue(), nil
}
