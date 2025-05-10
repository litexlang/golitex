// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
)

// 所有verifier的方法里，只有它和switch里的三大函数可能读入anyState
func (ver *Verifier) FactStmt(stmt ast.FactStmt, state VerState) (bool, error) {
	switch stmt := stmt.(type) {
	case *ast.SpecFactStmt:
		return ver.SpecFact(stmt, state)
	case *ast.LogicExprStmt:
		return ver.LogicalExprFact(stmt, state)
	case *ast.UniFactStmt:
		return ver.uniFact(stmt, state)
	default:
		return false, fmt.Errorf("unexpected")
	}
}

type Verifier struct {
	env    *env.Env
	curPkg string
}

func NewVerifier(curEnv *env.Env, pkgName string) *Verifier {
	if curEnv == nil {
		return &Verifier{env: env.NewEnv(nil), curPkg: pkgName}
	} else {
		return &Verifier{env: curEnv}
	}
}

func (ver *Verifier) successWithMsg(stmtString, storedStmtString string) {
	ver.successMsgEnd(stmtString, storedStmtString)
}

func (ver *Verifier) successNoMsg() {
}

func (ver *Verifier) newEnv() {
	newEnv := env.NewEnv(ver.env)
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

// TODO: 有严重问题
func (ver *Verifier) LogicalExprFact(stmt *ast.LogicExprStmt, state VerState) (bool, error) {
	if !stmt.IsOr {
		for _, fact := range stmt.Facts {
			ok, err := ver.FactStmt(fact, state)
			if err != nil {
				return ver.factDefer(stmt, state, false, err, "")
			}
			if !ok {
				return ver.factDefer(stmt, state, false, nil, "")
			}
		}
		return ver.factDefer(stmt, state, true, nil, "")
	} else {
		for i := range stmt.Facts {
			ok, err := ver.proveEachFactInOrExpr(stmt, i, state)
			if err != nil {
				return ver.factDefer(stmt, state, false, err, "")
			}
			if !ok {
				return ver.factDefer(stmt, state, false, nil, "")
			}
		}
		return ver.factDefer(stmt, state, true, nil, "")
	}
}

func (ver *Verifier) proveEachFactInOrExpr(stmt *ast.LogicExprStmt, index int, state VerState) (bool, error) {
	ver.newEnv()
	defer ver.deleteEnvAndRetainMsg()

	// not others are stored to be true
	for i := range stmt.Facts {
		if i == index {
			continue
		}
		err := ver.env.NewFact(stmt.Facts[i].ReverseIsTrue())
		if err != nil {
			return false, err
		}
	}

	ok, err := ver.FactStmt(stmt.Facts[index], state.toNoMsg())
	if err != nil {
		return false, err
	}

	if !ok {
		return false, nil
	}

	if state.requireMsg() {
		ver.successWithMsg(stmt.String(), stmt.Facts[index].String())
	} else {
		ver.unknownMsgEnd(stmt.String())
	}

	return true, nil
}

func (ver *Verifier) factDefer(stmt ast.FactStmt, state VerState, proved bool, err error, proveBy string) (bool, error) {
	if err != nil {
		return proved, err
	}

	if state.requireMsg() {
		if proved {
			ver.successWithMsg(stmt.String(), proveBy)
		} else {
			ver.unknownMsgEnd(stmt.String())
		}
	}
	return proved, err
}

func (ver *Verifier) appendInternalWarningMsg(s string, args ...any) {
	ver.env.Msgs = append(ver.env.Msgs, fmt.Sprintf(`warning (current version of Litex has not implemented some features you might expect): %s\n`, fmt.Sprintf(s, args...)))
}
