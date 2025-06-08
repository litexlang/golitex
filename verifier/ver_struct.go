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
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex discord server: https://discord.gg/uvrHM7eS
// Litex zulip chat: https://litex.zulipchat.com/

// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

// 所有verifier的方法里，只有它和switch里的三大函数可能读入anyState
func (ver *Verifier) FactStmt(stmt ast.FactStmt, state VerState) (bool, error) {
	if asSpecFact, ok := isTrueEqualFact(stmt); ok {
		return ver.verEqualFact(asSpecFact, state)
	}

	if asSpecFact, ok := stmt.(*ast.SpecFactStmt); ok {
		return ver.verSpecFact(asSpecFact, state)
	}

	// if asLogicExpr, ok := stmt.(*ast.LogicExprStmt); ok {
	// 	return ver.verLogicExpr(asLogicExpr, state)
	// }

	if asOrStmt, ok := stmt.(*ast.OrStmt); ok {
		return ver.verOrStmt(asOrStmt, state)
	}

	if asUniFact, ok := stmt.(*ast.UniFactStmt); ok {
		return ver.verUniFact(asUniFact, state)
	}

	return false, fmt.Errorf("unexpected fact statement: %v", stmt)
}

type Verifier struct {
	env *env.Env
}

func NewVerifier(curEnv *env.Env) *Verifier {
	if curEnv == nil {
		return &Verifier{env: env.NewEnv(nil, nil)}
	} else {
		return &Verifier{env: curEnv}
	}
}

func (ver *Verifier) successWithMsg(stmtString, storedStmtString string) {
	ver.successMsgEnd(stmtString, storedStmtString)
}

func (ver *Verifier) successNoMsg() {
}

func (ver *Verifier) newEnv(parent *env.Env, curMatchEnv *ast.SpecFactStmt) {
	newEnv := env.NewEnv(parent, curMatchEnv)
	ver.env = newEnv
}

func (ver *Verifier) deleteEnvAndRetainMsg() error {
	if ver.env.Parent != nil {
		for _, msg := range ver.env.Msgs {
			ver.env.Parent.NewMsg(msg)
		}
		ver.env = ver.env.Parent
		return nil
	} else {
		return fmt.Errorf("parent env does not exist")
	}
}

func (ver *Verifier) newMsgAtParent(s string) error {
	if ver.env.Parent == nil {
		return fmt.Errorf("no parent env")
	} else {
		ver.env.Parent.NewMsg(s)
		return nil
	}
}

// func (ver *Verifier)

func (ver *Verifier) appendInternalWarningMsg(s string, args ...any) {
	ver.env.Msgs = append(ver.env.Msgs, glob.InternalWarningMsg(s, args...))
}
