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

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
)

func (ver *Verifier) verUniFact(oldStmt *ast.ForallFactStmt, state *VerState) (bool, error) {
	if state.isFinalRound() {
		return false, nil
	}

	// 在局部环境声明新变量
	ver.newEnv(ver.env)
	defer ver.deleteEnvAndRetainMsg()

	newStmtPtr, err := ver.PreprocessUniFactParams_DeclareParams(oldStmt)
	if err != nil {
		return false, err
	}

	// know cond facts
	for _, condFact := range newStmtPtr.DomFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	return ver.uniFact_checkThenFacts(newStmtPtr, state)
}

func (ver *Verifier) uniFact_checkThenFacts(stmt *ast.ForallFactStmt, state *VerState) (bool, error) {
	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		verRet := ver.VerFactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
		if verRet.IsErr() {
			return false, fmt.Errorf(verRet.String())
		}
		if verRet.IsUnknown() {
			if state.WithMsg {
				ver.env.Msgs = append(ver.env.Msgs, fmt.Sprintf("%s is unknown", thenFact))
			}
			return false, nil
		}

		// if true, store it
		err := ver.env.NewFact(thenFact)
		if err != nil {
			return false, err
		}
	}

	if state.WithMsg {
		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt))
		if err != nil {
			return false, err
		}
	}

	return true, nil
}

func (ver *Verifier) PreprocessUniFactParams_DeclareParams(oldStmt *ast.ForallFactStmt) (*ast.ForallFactStmt, error) {
	newStmtPtr, _, err := ver.instantiateUniFactWithoutDuplicate(oldStmt)
	if err != nil {
		return nil, err
	}

	// declare
	err = ver.NewDefObj_InsideAtomsDeclared(ast.NewDefObjStmt(newStmtPtr.Params, newStmtPtr.ParamSets, []ast.FactStmt{}, oldStmt.Line))
	if err != nil {
		return nil, err
	}

	// 查看param set 是否已经声明
	for _, paramSet := range newStmtPtr.ParamSets {
		ok := ver.env.AreAtomsInFcAreDeclared(paramSet, map[string]struct{}{})
		if !ok {
			return nil, fmt.Errorf(env.AtomsInFcNotDeclaredMsg(paramSet))
		}
	}

	return newStmtPtr, nil
}
