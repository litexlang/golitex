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
	// 如果结论是uniFact，那么dom和then全部不能是uniFact；然后不允许是uniFactIff
	_, ok := stmt.Fact.(ast.SpecificFactStmt)
	if !ok {
		return exec.AddStmtToStmtRet(glob.ErrRet(fmt.Sprintf("expect specific fact for induction, get:\n%s", stmt.Fact.String())), stmt)
	}

	// 证明 start 是 整数
	startIsInt := ast.NewInFactWithObj(stmt.InducFrom, ast.Atom(glob.KeywordInteger))
	startIsIntRet := exec.factStmt(startIsInt)
	if startIsIntRet.IsNotTrue() {
		return startIsIntRet.AddError(fmt.Sprintf("start is not an integer: %s", stmt.InducFrom.String()))
	}

	// 验证步骤（在局部环境中）
	execRet := exec.proveByInductionStmtProveProcess(stmt)
	if execRet.IsNotTrue() {
		return execRet
	}

	// 存储步骤（在主环境中）
	finalUniFact := ast.NewUniFact([]string{stmt.Param}, []ast.Obj{ast.Atom(glob.KeywordNPos)}, []ast.Spec_OrFact{}, []ast.Spec_OrFact{stmt.Fact}, stmt.Line)
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

	// 运行整个 Proof
	execRet := exec.execStmtsAtCurEnv(stmt.Proof)
	if execRet.IsNotTrue() {
		return execRet.AddError(fmt.Sprintf("proof in induc failed"))
	}

	ver := NewVerifier(exec.Env)

	// 证明 1：如果把 stmt.Fact 的 param 改成 1，是否成立
	startFact, err := stmt.Fact.InstantiateFact(map[string]ast.Obj{stmt.Param: stmt.InducFrom})
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

	domFact := stmt.Fact

	// thenFacts: stmt.Fact 的 param 替换成 randomParam + 1
	paramPlus1 := ast.NewFnObj(ast.Atom(glob.KeySymbolPlus), []ast.Obj{ast.Atom(stmt.Param), ast.Atom("1")})
	thenFact, err := stmt.Fact.InstantiateFact(map[string]ast.Obj{stmt.Param: paramPlus1})
	if err != nil {
		return glob.ErrRet(fmt.Sprintf("failed to instantiate fact with randomParam+1: %s", err.Error()))
	}

	// 创建 uniFact
	inductionStep := ast.NewUniFact([]string{stmt.Param}, []ast.Obj{ast.Atom(glob.KeywordNPos)}, []ast.Spec_OrFact{domFact}, []ast.Spec_OrFact{thenFact.(ast.Spec_OrFact)}, stmt.Line)

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

// 等 inline Parser 能 parse depth的时候删了这个
// func (exec *Executor) checkProveByInductionStmtFact(fact ast.FactStmt) *glob.StmtRet {
// 	// 如果结论是uniFact，那么dom和then全部不能是uniFact；然后不允许是uniFactIff
// 	if uniFact, ok := fact.(*ast.UniFactStmt); ok {
// 		for _, domFact := range uniFact.DomFacts {
// 			if _, ok := domFact.(*ast.UniFactStmt); ok {
// 				return glob.ErrRet(fmt.Sprintf("dom is uniFact: %s", domFact.String()))
// 			}
// 		}
// 		for _, thenFact := range uniFact.ThenFacts {
// 			if _, ok := thenFact.(*ast.UniFactStmt); ok {
// 				return glob.ErrRet(fmt.Sprintf("then is uniFact: %s", thenFact.String()))
// 			}
// 		}
// 	}

// 	if uniFactIff, ok := fact.(*ast.UniFactWithIffStmt); ok {
// 		for _, iffFact := range uniFactIff.IffFacts {
// 			if _, ok := iffFact.(*ast.UniFactStmt); ok {
// 				return glob.ErrRet(fmt.Sprintf("iff is uniFact: %s", iffFact.String()))
// 			}
// 		}
// 		for _, thenFact := range uniFactIff.UniFact.DomFacts {
// 			if _, ok := thenFact.(*ast.UniFactStmt); ok {
// 				return glob.ErrRet(fmt.Sprintf("then is uniFact: %s", thenFact.String()))
// 			}
// 		}

// 		for _, thenFact := range uniFactIff.UniFact.ThenFacts {
// 			if _, ok := thenFact.(*ast.UniFactStmt); ok {
// 				return glob.ErrRet(fmt.Sprintf("then is uniFact: %s", thenFact.String()))
// 			}
// 		}
// 	}

// 	return glob.NewEmptyStmtTrue()
// }
