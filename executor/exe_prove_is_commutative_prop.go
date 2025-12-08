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

func (exec *Executor) proveIsCommutativePropStmt(stmt *ast.ProveIsCommutativePropStmt) ExecRet {
	ok, err := exec.proveIsCommutativePropStmtMainLogic(stmt)
	if !ok || err != nil {
		return NewExecErr(err.Error())
	}

	exec.NewCommutativeProp(stmt.SpecFact)

	return NewEmptyExecTrue()
}

func (exec *Executor) proveIsCommutativePropStmtMainLogic(stmt *ast.ProveIsCommutativePropStmt) (bool, error) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	if exec.Env.IsCommutativeProp(stmt.SpecFact) {
		return true, nil
	}

	def := exec.Env.GetPropDef(stmt.SpecFact.PropName)
	if def == nil {
		return false, fmt.Errorf("prop %s is not defined", stmt.SpecFact.PropName)
	}

	if len(def.DefHeader.Params) != 2 {
		return false, fmt.Errorf("prop %s has %d params, but 2 params are expected", stmt.SpecFact.PropName, len(def.DefHeader.Params))
	}

	ret := exec.Env.AreAtomsInObjDefined(def.DefHeader.ParamSets[0], map[string]struct{}{})
	if ret.IsErr() {
		return false, fmt.Errorf(ret.String())
	}
	ret = exec.Env.AreAtomsInObjDefined(def.DefHeader.ParamSets[1], map[string]struct{}{})
	if ret.IsErr() {
		return false, fmt.Errorf(ret.String())
	}

	// 这里最好检查一下，是不是 Param set 依赖了 Param，如果依赖了，那其实是要报错了，不过暂时不管了

	params := []string{}
	for _, param := range stmt.SpecFact.Params {
		asFcAtom, ok := param.(ast.Atom)
		if !ok {
			return false, fmt.Errorf("param %s is not an atom", param)
		}
		params = append(params, string(asFcAtom))
	}

	execState := exec.defLetStmt(ast.NewDefLetStmt(params, []ast.Obj{def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1]}, []ast.FactStmt{}, stmt.Line))
	if execState.IsNotTrue() {
		return false, fmt.Errorf(execState.String())
	}

	// if len(def.DomFacts) > 0 {
	// 	return false, fmt.Errorf("dom facts are not allowed in %s", glob.KeywordProveIsCommutativeProp)
	// }

	leftToRightFact := stmt.SpecFact
	rightToLeftFact, err := leftToRightFact.ReverseParameterOrder()
	if err != nil {
		return false, err
	}

	var ok bool
	ok, err = exec.proveIsCommutativePropStmtBody(stmt.Proofs, leftToRightFact, rightToLeftFact)
	if !ok || err != nil {
		return false, err
	}

	ok, err = exec.proveIsCommutativePropStmtBody(stmt.ProofsRightToLeft, rightToLeftFact, leftToRightFact)
	if !ok || err != nil {
		return false, err
	}

	return true, nil
}

func (exec *Executor) proveIsCommutativePropStmtBody(proofs []ast.Stmt, fact *ast.SpecFactStmt, rightToLeft *ast.SpecFactStmt) (bool, error) {
	exec.NewEnv(exec.Env)
	defer exec.deleteEnv()

	ret := exec.Env.NewFact(fact)
	if ret.IsErr() {
		return false, fmt.Errorf(ret.String())
	}

	for _, proof := range proofs {
		execState := exec.Stmt(proof)
		if execState.IsNotTrue() {
			return false, fmt.Errorf(execState.String())
		}
	}

	state := exec.factStmt(rightToLeft)
	if state.IsErr() {
		return false, fmt.Errorf(state.String())
	}
	if state.IsUnknown() {
		return false, fmt.Errorf("proof in %s must be proved to be true, but %s is not true", glob.KeywordProveIsCommutativeProp, rightToLeft)
	}

	return true, nil
}
