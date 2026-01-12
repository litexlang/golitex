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

func (exec *Executor) proveByInductionStmt(stmt *ast.ProveByInductionStmt) *glob.StmtRet {
	// 验证步骤（在局部环境中）
	execRet := exec.proveByInductionStmtProveProcess(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}

	// 存储步骤（在主环境中）
	finalUniFact := ast.NewUniFact([]string{stmt.Param}, []ast.Obj{ast.Atom(glob.KeywordNPos)}, []ast.FactStmt{}, []ast.FactStmt{stmt.Fact}, stmt.Line)
	factRet := exec.Env.NewFactWithCheckingNameDefined(finalUniFact)
	if factRet.IsErr() {
		return glob.ErrRet(fmt.Sprintf("failed to store final universal fact: %s", factRet.String()))
	}

	return exec.NewTrueStmtRet(stmt).AddNewFact(finalUniFact.String())
}

func (exec *Executor) proveByInductionStmtProveProcess(stmt *ast.ProveByInductionStmt) *glob.StmtRet {
	// 步骤1：开一个局部环境
	exec.NewEnv()
	defer exec.deleteEnv()

	// 检查 param 是否已经声明过
	ret := exec.Env.LookupNamesInObj(ast.Atom(stmt.Param), map[string]struct{}{})
	if ret.IsTrue() {
		return glob.ErrRet(fmt.Sprintf("parameter %s is already defined. To avoid ambiguity, please use a different name for the parameter", stmt.Param))
	}

	// 定义 param 在 N_pos 里
	defLetStmt := ast.NewDefLetStmt([]string{stmt.Param}, []ast.Obj{ast.Atom(glob.KeywordNPos)}, []ast.FactStmt{}, stmt.Line)
	execRet := exec.defLetStmt(defLetStmt)
	if execRet.IsNotTrue() {
		return execRet.AddError(fmt.Sprintf("failed to define parameter %s in N_pos", stmt.Param))
	}

	// 运行整个 Proof
	execRet = exec.execStmtsAtCurEnv(stmt.Proof)
	if execRet.IsNotTrue() {
		return execRet.AddError(fmt.Sprintf("proof in prove_by_induction failed"))
	}

	ver := NewVerifier(exec.Env)

	// 证明 1：如果把 stmt.Fact 的 param 改成 1，是否成立
	startFact, err := stmt.Fact.InstantiateFact(map[string]ast.Obj{stmt.Param: ast.Atom("1")})
	if err != nil {
		return glob.ErrRet(fmt.Sprintf("failed to instantiate fact with param=1: %s", err.Error()))
	}
	verRet := ver.VerFactStmt(startFact, Round0NoMsg())
	if verRet.IsErr() {
		return glob.ErrRet(fmt.Sprintf("base case failed: %s", verRet.String()))
	}
	if verRet.IsUnknown() {
		return glob.NewEmptyStmtUnknown().AddUnknown(fmt.Sprintf("base case is unknown: %s", startFact.String()))
	}

	// 证明 2：生成 uniFact: forall randomParam N_pos: stmt.Fact 的 param 替换成 randomParam => stmt.Fact 的 param 替换成 randomParam + 1
	randomParam := exec.Env.GenerateUndeclaredRandomName()

	// domFacts: stmt.Fact 的 param 替换成 randomParam
	domFact, err := stmt.Fact.InstantiateFact(map[string]ast.Obj{stmt.Param: ast.Atom(randomParam)})
	if err != nil {
		return glob.ErrRet(fmt.Sprintf("failed to instantiate fact with randomParam: %s", err.Error()))
	}

	// thenFacts: stmt.Fact 的 param 替换成 randomParam + 1
	randomParamPlus1 := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{ast.Atom(randomParam), ast.Atom("1")})
	thenFact, err := stmt.Fact.InstantiateFact(map[string]ast.Obj{stmt.Param: randomParamPlus1})
	if err != nil {
		return glob.ErrRet(fmt.Sprintf("failed to instantiate fact with randomParam+1: %s", err.Error()))
	}

	// 创建 uniFact
	inductionStep := ast.NewUniFact([]string{randomParam}, []ast.Obj{ast.Atom(glob.KeywordNPos)}, []ast.FactStmt{domFact}, []ast.FactStmt{thenFact}, stmt.Line)

	// 验证 induction step
	verRet = ver.VerFactStmt(inductionStep, Round0NoMsg())
	if verRet.IsErr() {
		return glob.ErrRet(fmt.Sprintf("induction step failed: %s", verRet.String()))
	}
	if verRet.IsUnknown() {
		return glob.NewEmptyStmtUnknown().AddUnknown(fmt.Sprintf("induction step is unknown: %s", inductionStep.String()))
	}

	return glob.NewEmptyStmtTrue()
}
