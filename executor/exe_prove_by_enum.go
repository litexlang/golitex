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

func (exec *Executor) proveByEnumMainLogic(stmt *ast.ProveByEnumStmt) (ExecRet, error) {
	enums := [][]ast.Obj{}
	for _, paramSet := range stmt.Fact.ParamSets {
		enumFacts, ok := exec.Env.GetEnumFact(paramSet.String())
		if !ok {
			return NewExecErr(""), fmt.Errorf("prove over finite set statement error: enum not found")
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
				return NewExecErr(""), err
			}
			if !ok {
				return NewExecErr(""), fmt.Errorf("failed to prove at prove section %d", i)
			}
		}
		return NewExecTrue(""), nil
	}
}

func (exec *Executor) verProveOverFiniteSet_ProveAtProveSectionI(stmt *ast.ProveByEnumStmt, cartesianProductAtI []ast.Obj) (bool, error) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	defObjStmt := ast.NewDefLetStmt(stmt.Fact.Params, stmt.Fact.ParamSets, getParamEqualFcSlice(stmt.Fact.Params, cartesianProductAtI), stmt.Line)
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

func getParamEqualFcSlice(params []string, equalTo []ast.Obj) []ast.FactStmt {
	result := []ast.FactStmt{}
	for i, param := range params {
		result = append(result, ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{ast.Atom(param), equalTo[i]}, glob.BuiltinLine))
	}
	return result
}

func (exec *Executor) verProveOverFiniteSet_NoProveSection(stmt *ast.ProveByEnumStmt, cartesianProductOfFcs [][]ast.Obj) (ExecRet, error) {
	for _, fcSlice := range cartesianProductOfFcs {
		uniMap := map[string]ast.Obj{}
		for i, param := range stmt.Fact.Params {
			uniMap[param] = fcSlice[i]
		}

		hasFalseDomFact := false
		for _, domFact := range stmt.Fact.DomFacts {
			instantiatedDomFact, err := domFact.InstantiateFact(uniMap)
			if err != nil {
				return NewExecErr(""), err
			}

			state := exec.factStmt(instantiatedDomFact)
			if state.IsErr() {
				return NewExecErr(""), err
			}
			if state.IsUnknown() {
				domFactAs := instantiatedDomFact.(ast.Spec_OrFact)
				for _, fact := range domFactAs.ReverseIsTrue() {
					state := exec.factStmt(fact)
					if state.IsErr() {
						return NewExecErr(""), err
					}
					if state.IsUnknown() {
						return NewExecErr(""), fmt.Errorf("domain fact in universal fact in prove over finite set statement must be true or not true, it can not be unknown:\n%s", instantiatedDomFact)
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
				return NewExecErr(""), err
			}
			instantiatedThenFacts = append(instantiatedThenFacts, instantiatedThenFact)
		}

		// ver facts
		for _, fact := range instantiatedThenFacts {
			state := exec.factStmt(fact)
			if state.IsErr() {
				return NewExecErr(""), fmt.Errorf(state.String())
			}
			if state.IsUnknown() {
				return NewExecErr(""), fmt.Errorf("failed to prove instantiated then facts: %s", fact)
			}
		}
	}

	return NewExecTrue(""), nil
}
