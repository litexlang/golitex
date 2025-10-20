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
// Litex website: https://litexlang.com
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (exec *Executor) proveByEnumMainLogic(stmt *ast.ProveByEnumStmt) (glob.ExecState, error) {
	enums := [][]ast.Fc{}
	for _, paramSet := range stmt.Fact.ParamSets {
		enumFacts, ok := exec.env.GetEnumFact(paramSet.String())
		if !ok {
			return glob.ExecStateError, fmt.Errorf("prove over finite set statement error: enum not found")
		}
		enums = append(enums, enumFacts)
	}

	cartesianProductOfFcs := glob.CartesianProduct(enums)

	if len(stmt.Proof) == 0 {
		return exec.verProveOverFiniteSet_NoProveSection(stmt, cartesianProductOfFcs)
	} else {
		for i := range len(cartesianProductOfFcs) {
			ok, err := exec.verProveOverFiniteSet_ProveAtProveSectionI(stmt, cartesianProductOfFcs[i])
			if err != nil {
				return glob.ExecStateError, err
			}
			if !ok {
				return glob.ExecStateError, fmt.Errorf("failed to prove at prove section %d", i)
			}
		}
		return glob.ExecStateTrue, nil
	}
}

func (exec *Executor) verProveOverFiniteSet_ProveAtProveSectionI(stmt *ast.ProveByEnumStmt, cartesianProductAtI []ast.Fc) (bool, error) {
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	defObjStmt := ast.NewDefObjStmt(stmt.Fact.Params, stmt.Fact.ParamSets, getParamEqualFcSlice(stmt.Fact.Params, cartesianProductAtI), stmt.Line)
	err := exec.defObjStmt(defObjStmt)
	if err != nil {
		return false, err
	}

	uniMap := map[string]ast.Fc{}
	for i, param := range stmt.Fact.Params {
		uniMap[param] = cartesianProductAtI[i]
	}

	for _, fact := range stmt.Fact.DomFacts {
		instFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return false, err
		}
		state, err := exec.factStmt(instFact)
		if notOkExec(state, err) {
			revFacts := instFact.(ast.Spec_OrFact).ReverseIsTrue()
			for _, revFact := range revFacts {
				state, err := exec.factStmt(revFact)
				if notOkExec(state, err) {
					return false, fmt.Errorf("domain fact in universal fact in prove over finite set statement must be true or not true, it can not be unknown:\n%s", instFact)
				}
			}
			return true, nil
		}
	}

	for _, stmt := range stmt.Proof {
		state, _, err := exec.Stmt(stmt)
		if notOkExec(state, err) {
			return false, err
		}
	}

	for _, fact := range stmt.Fact.ThenFacts {
		instFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return false, err
		}
		state, err := exec.factStmt(instFact)
		if notOkExec(state, err) {
			return false, fmt.Errorf("failed to prove instantiated then facts: %s", instFact)
		}
	}

	return true, nil
}

// func (exec *Executor) verProveOverFiniteSet_ProveAtProveSectionI(stmt *ast.ProveByEnumStmt, cartesianProductAtI []ast.Fc, i int) (bool, error) {
// 	exec.NewEnv(exec.env)
// 	defer exec.deleteEnvAndRetainMsg()

// 	err := exec.defObjStmt(ast.NewDefObjStmt(stmt.Fact.Params, stmt.Fact.ParamSets, getParamEqualFcSlice(stmt.Fact.Params, cartesianProductAtI), stmt.Line))
// 	if err != nil {
// 		return false, err
// 	}

// 	uniMap := map[string]ast.Fc{}
// 	for i, param := range stmt.Fact.Params {
// 		uniMap[param] = cartesianProductAtI[i]
// 	}

// 	hasFalseDomFact := false
// 	for _, domFact := range stmt.Fact.DomFacts {
// 		instantiatedDomFact, err := domFact.Instantiate(uniMap)
// 		if err != nil {
// 			return false, err
// 		}

// 		state, err := exec.factStmt(instantiatedDomFact)
// 		if err != nil {
// 			return false, err
// 		}
// 		if state != glob.ExecStateTrue {
// 			domFactAs := instantiatedDomFact.(ast.Spec_OrFact)
// 			for _, fact := range domFactAs.ReverseIsTrue() {
// 				state, err := exec.factStmt(fact)
// 				if err != nil {
// 					return false, err
// 				}
// 				if state != glob.ExecStateTrue {
// 					return false, fmt.Errorf("domain fact in universal fact in prove over finite set statement must be true or not true, it can not be unknown:\n%s", instantiatedDomFact)
// 				}
// 			}

// 			hasFalseDomFact = true
// 			break
// 		}
// 	}

// 	if hasFalseDomFact {
// 		return true, nil
// 	}

// 	for _, fact := range stmt.ProofsSlice[i] {
// 		state, _, err := exec.Stmt(fact)
// 		if err != nil {
// 			return false, err
// 		}
// 		if state != glob.ExecStateTrue {
// 			return false, nil
// 		}
// 	}

// 	for _, fact := range stmt.Fact.ThenFacts {
// 		state, err := exec.factStmt(fact)
// 		if err != nil {
// 			return false, err
// 		}
// 		if state != glob.ExecStateTrue {
// 			return false, nil
// 		}
// 	}

// 	return true, nil
// }

func getParamEqualFcSlice(params []string, equalTo []ast.Fc) []ast.FactStmt {
	result := []ast.FactStmt{}
	for i, param := range params {
		result = append(result, ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{ast.FcAtom(param), equalTo[i]}, glob.InnerGenLine))
	}
	return result
}

func (exec *Executor) verProveOverFiniteSet_NoProveSection(stmt *ast.ProveByEnumStmt, cartesianProductOfFcs [][]ast.Fc) (glob.ExecState, error) {
	for _, fcSlice := range cartesianProductOfFcs {
		uniMap := map[string]ast.Fc{}
		for i, param := range stmt.Fact.Params {
			uniMap[param] = fcSlice[i]
		}

		hasFalseDomFact := false
		for _, domFact := range stmt.Fact.DomFacts {
			instantiatedDomFact, err := domFact.Instantiate(uniMap)
			if err != nil {
				return glob.ExecStateError, err
			}

			state, err := exec.factStmt(instantiatedDomFact)
			if err != nil {
				return glob.ExecStateError, err
			}
			if state != glob.ExecStateTrue {
				domFactAs := instantiatedDomFact.(ast.Spec_OrFact)
				for _, fact := range domFactAs.ReverseIsTrue() {
					state, err := exec.factStmt(fact)
					if err != nil {
						return glob.ExecStateError, err
					}
					if state != glob.ExecStateTrue {
						return glob.ExecStateError, fmt.Errorf("domain fact in universal fact in prove over finite set statement must be true or not true, it can not be unknown:\n%s", instantiatedDomFact)
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
			instantiatedThenFact, err := thenFact.Instantiate(uniMap)
			if err != nil {
				return glob.ExecStateError, err
			}
			instantiatedThenFacts = append(instantiatedThenFacts, instantiatedThenFact)
		}

		// ver facts
		for _, fact := range instantiatedThenFacts {
			state, err := exec.factStmt(fact)
			if err != nil {
				return glob.ExecStateError, err
			}
			if state != glob.ExecStateTrue {
				return glob.ExecStateError, fmt.Errorf("failed to prove instantiated then facts: %s", fact)
			}
		}
	}

	return glob.ExecStateTrue, nil
}
