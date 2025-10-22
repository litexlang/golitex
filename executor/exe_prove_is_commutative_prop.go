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

func (exec *Executor) proveIsCommutativePropStmt(stmt *ast.ProveIsCommutativePropStmt) (glob.ExecState, error) {
	ok, err := exec.proveIsCommutativePropStmtMainLogic(stmt)
	if !ok || err != nil {
		return glob.ExecStateError, err
	}

	exec.env.CommutativePropMem[string(stmt.Prop)] = struct{}{}

	return glob.ExecStateTrue, nil
}

func (exec *Executor) proveIsCommutativePropStmtMainLogic(stmt *ast.ProveIsCommutativePropStmt) (bool, error) {
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	if exec.env.IsCommutativeProp(stmt.Prop) {
		return true, nil
	}

	def, ok := exec.env.GetPropDef(stmt.Prop)
	if !ok {
		return false, fmt.Errorf("prop %s is not defined", stmt.Prop)
	}

	if len(def.DefHeader.Params) != 2 {
		return false, fmt.Errorf("prop %s has %d params, but 2 params are expected", stmt.Prop, len(def.DefHeader.Params))
	}

	// // def 的 paramSet 必须相等
	// state, err := exec.factStmt(ast.NewEqualFact(def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1]))
	// if err != nil {
	// 	return false, err
	// }
	// if state != glob.ExecStateTrue {
	// 	return false, fmt.Errorf("prop in %s must have equal parameter sets, but parameter sets %s and %s of %s are not equal", glob.KeywordProveIsTransitiveProp, def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1], def.DefHeader.Name)
	// }

	ok = exec.env.AreAtomsInFcAreDeclared(def.DefHeader.ParamSets[0], map[string]struct{}{})
	if !ok {
		return false, fmt.Errorf("param %s is not declared", def.DefHeader.ParamSets[0])
	}
	ok = exec.env.AreAtomsInFcAreDeclared(def.DefHeader.ParamSets[1], map[string]struct{}{})
	if !ok {
		return false, fmt.Errorf("param %s is not declared", def.DefHeader.ParamSets[1])
	}

	// 这里最好检查一下，是不是 Param set 依赖了 Param，如果依赖了，那其实是要报错了，不过暂时不管了
	err := exec.defObjStmt(ast.NewDefObjStmt(stmt.Params, []ast.Fc{def.DefHeader.ParamSets[0], def.DefHeader.ParamSets[1]}, []ast.FactStmt{}, stmt.Line))
	if err != nil {
		return false, err
	}

	// if len(def.DomFacts) > 0 {
	// 	return false, fmt.Errorf("dom facts are not allowed in %s", glob.KeywordProveIsCommutativeProp)
	// }

	leftToRightFact := ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.Prop), []ast.Fc{ast.FcAtom(stmt.Params[0]), ast.FcAtom(stmt.Params[1])}, stmt.Line)
	rightToLeftFact, err := leftToRightFact.ReverseParameterOrder()
	if err != nil {
		return false, err
	}

	ok, err = exec.proveIsCommutativePropStmtBody(stmt, leftToRightFact, rightToLeftFact)
	if !ok || err != nil {
		return false, err
	}

	ok, err = exec.proveIsCommutativePropStmtBody(stmt, rightToLeftFact, leftToRightFact)
	if !ok || err != nil {
		return false, err
	}

	return true, nil
}

func (exec *Executor) proveIsCommutativePropStmtBody(stmt *ast.ProveIsCommutativePropStmt, fact *ast.SpecFactStmt, rightToLeft *ast.SpecFactStmt) (bool, error) {
	exec.NewEnv(exec.env)
	defer exec.deleteEnvAndRetainMsg()

	err := exec.env.NewFact(fact)
	if err != nil {
		return false, err
	}

	for _, proof := range stmt.Proofs {
		execState, _, err := exec.Stmt(proof)
		if notOkExec(execState, err) {
			return false, err
		}
	}

	state, err := exec.factStmt(rightToLeft)
	if notOkExec(state, err) {
		return false, err
	}
	if state != glob.ExecStateTrue {
		return false, fmt.Errorf("proof in %s must be proved to be true, but %s is not true", glob.KeywordProveIsCommutativeProp, rightToLeft)
	}

	return true, nil
}
