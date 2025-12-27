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

func (exec *Executor) proveIsCommutativePropStmt(stmt *ast.ProveIsCommutativePropStmt) *glob.StmtRet {
	innerStmtRets := []*glob.StmtRet{}
	verifyProcessMsgs := []*glob.VerMsg{}
	newFactMsgs := []string{}

	exec.NewEnv()
	defer exec.deleteEnv()

	if exec.Env.IsCommutativeProp(stmt.SpecFact) {
		newFactMsgs = append(newFactMsgs, fmt.Sprintf("%s is commutative prop", stmt.SpecFact.PropName.String()))
		return exec.NewTrueStmtRet(stmt).AddNewFacts(newFactMsgs)
	}

	def := exec.Env.GetPropDef(stmt.SpecFact.PropName)
	if def == nil {
		return glob.ErrRet(fmt.Sprintf("prop %s is not defined", stmt.SpecFact.PropName))
	}

	if len(def.DefHeader.Params) != 2 {
		return glob.ErrRet(fmt.Sprintf("prop %s has %d params, but 2 params are expected", stmt.SpecFact.PropName, len(def.DefHeader.Params)))
	}

	ret := exec.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(def.DefHeader.ParamSets[0], map[string]struct{}{})
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}
	ret = exec.Env.LookupNamesInObjOrObjStringIsSetNonemptySetFiniteSet(def.DefHeader.ParamSets[1], map[string]struct{}{})
	if ret.IsErr() {
		return glob.ErrRet(ret.String())
	}

	// 这里最好检查一下，是不是 Param set 依赖了 Param，如果依赖了，那其实是要报错了，不过暂时不管了

	params := []string{}
	for _, param := range stmt.SpecFact.Params {
		asAtomObj, ok := param.(ast.Atom)
		if !ok {
			return glob.ErrRet(fmt.Sprintf("param %s is not an atom", param))
		}
		params = append(params, string(asAtomObj))
	}

	execState := exec.defLetStmt(ast.NewDefLetStmt(params, []ast.Obj{def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1]}, []ast.FactStmt{}, stmt.Line))
	if execState.IsNotTrue() {
		return execState
	}
	innerStmtRets = append(innerStmtRets, execState.InnerStmtRetSlice...)

	// if len(def.DomFacts) > 0 {
	// 	return glob.ErrRet(fmt.Sprintf("dom facts are not allowed in %s", glob.KeywordProveIsCommutativeProp))
	// }

	leftToRightFact := stmt.SpecFact
	rightToLeftFact, err := leftToRightFact.ReverseParameterOrder()
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	// Prove left to right
	execState, verifyMsgs, innerRets := exec.proveIsCommutativePropStmtBody(stmt.Proofs, leftToRightFact, rightToLeftFact)
	if execState.IsNotTrue() {
		return execState
	}
	verifyProcessMsgs = append(verifyProcessMsgs, verifyMsgs...)
	innerStmtRets = append(innerStmtRets, innerRets...)

	// Prove right to left
	execState, verifyMsgs, innerRets = exec.proveIsCommutativePropStmtBody(stmt.ProofsRightToLeft, rightToLeftFact, leftToRightFact)
	if execState.IsNotTrue() {
		return execState
	}
	verifyProcessMsgs = append(verifyProcessMsgs, verifyMsgs...)
	innerStmtRets = append(innerStmtRets, innerRets...)

	exec.NewCommutativeProp(stmt.SpecFact)

	newFactMsgs = append(newFactMsgs, fmt.Sprintf("%s is commutative prop", stmt.SpecFact.PropName.String()))

	return exec.NewTrueStmtRet(stmt).AddInnerStmtRets(innerStmtRets).AddVerifyProcesses(verifyProcessMsgs).AddNewFacts(newFactMsgs)
}

func (exec *Executor) proveIsCommutativePropStmtBody(proofs []ast.Stmt, fact *ast.SpecFactStmt, rightToLeft *ast.SpecFactStmt) (*glob.StmtRet, []*glob.VerMsg, []*glob.StmtRet) {
	innerStmtRets := []*glob.StmtRet{}
	verifyProcessMsgs := []*glob.VerMsg{}

	exec.NewEnv()
	defer exec.deleteEnv()

	ret := exec.Env.NewFactWithoutCheckingNameDefined(fact)
	if ret.IsErr() {
		return glob.ErrRet(ret.String()), nil, nil
	}

	for _, proof := range proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return execState, nil, nil
		}
		innerStmtRets = append(innerStmtRets, execState)
	}

	state := exec.factStmt(rightToLeft)
	if state.IsErr() {
		return state, nil, nil
	}
	if state.IsUnknown() {
		return glob.ErrRet(fmt.Sprintf("proof in %s must be proved to be true, but %s is not true", glob.KeywordProveIsCommutativeProp, rightToLeft)), nil, nil
	}
	verifyProcessMsgs = append(verifyProcessMsgs, state.VerifyProcess...)

	return glob.NewEmptyStmtTrue(), verifyProcessMsgs, innerStmtRets
}
