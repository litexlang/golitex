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
)

func (ver *Verifier) verUniFact(oldStmt *ast.UniFactStmt, state *VerState) ExecRet {
	if state.isFinalRound() {
		return NewEmptyExecUnknown()
	}

	// 在局部环境声明新变量
	ver.newEnv()
	defer ver.deleteEnv()

	newStmtPtr, err := ver.PreprocessUniFactParams_DeclareParams(oldStmt)
	if err != nil {
		return NewExecErr(err.Error())
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		ret := ver.Env.NewFactWithAtomsDefined(condFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	return ver.uniFact_checkThenFacts(newStmtPtr, state)
}

func (ver *Verifier) uniFact_checkThenFacts(stmt *ast.UniFactStmt, state *VerState) ExecRet {
	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		verRet := ver.VerFactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
		if verRet.IsErr() {
			return NewExecErr(verRet.String())
		}
		if verRet.IsUnknown() {
			execRet := NewEmptyExecUnknown()
			if state.WithMsg {
				execRet.AddMsg(fmt.Sprintf("%s is unknown", thenFact))
			}
			return execRet
		}

		// if true, store it
		ret := ver.Env.NewFactWithAtomsDefined(thenFact)
		if ret.IsErr() {
			return NewExecErr(ret.String())
		}
	}

	execRet := NewEmptyExecTrue()
	if state.WithMsg {
		execRet = execRet.AddMsg(fmt.Sprintf("%s\nis true", stmt))
	}
	return execRet
}

func (ver *Verifier) PreprocessUniFactParams_DeclareParams(oldStmt *ast.UniFactStmt) (*ast.UniFactStmt, error) {
	newStmtPtr, _, err := ver.instantiateUniFactWithoutDuplicate(oldStmt)
	if err != nil {
		return nil, err
	}

	// declare
	stmtForDef := ast.NewDefLetStmt(newStmtPtr.Params, newStmtPtr.ParamSets, []ast.FactStmt{}, oldStmt.Line)
	ret := ver.Env.DefineNewObjsAndCheckAllAtomsInDefLetStmtAreDefined(stmtForDef)
	if ret.IsErr() {
		return nil, fmt.Errorf(ret.String())
	}

	// 查看param set 是否已经声明
	for _, paramSet := range newStmtPtr.ParamSets {
		ret := ver.Env.AtomsInObjDefinedOrBuiltinOrSetNonemptySetFiniteSet(paramSet, map[string]struct{}{})
		if ret.IsErr() {
			return nil, fmt.Errorf(ret.String())
		}
	}

	return newStmtPtr, nil
}

func (ver *Verifier) verUniFactWithIff(stmt *ast.UniFactWithIffStmt, state *VerState) ExecRet {
	thenToIff := stmt.NewUniFactWithThenToIff()
	verRet := ver.verUniFact(thenToIff, state)
	if verRet.IsErr() || verRet.IsUnknown() {
		return verRet
	}

	iffToThen := stmt.NewUniFactWithIffToThen()
	verRet = ver.verUniFact(iffToThen, state)
	return verRet
}
