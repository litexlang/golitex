// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

// verifier 的方法的命名方式：factType+?UseWhatMemToVerify+?atEnv, 比如 RelaFactSpecAtEnv 就是说 证明 relaFact, 方法是用SpecFact，在当前环境里.
package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
	env "golitex/litex_env"
)

// 所有verifier的方法里，只有它和switch里的三大函数可能读入anyState
func (ver *Verifier) FactStmt(stmt ast.FactStmt, state VerState) (bool, error) {
	switch stmt := stmt.(type) {
	// 只有这里的三大函数+FcEqual+propProp验证，可能读入anyState；也只有这三个函数，用得到 state,isSpec()，其他函数貌似都用不到？
	case *ast.SpecFactStmt:
		return ver.SpecFact(stmt, state)
	case *ast.CondFactStmt:
		return ver.CondFact(stmt, state)
	case *ast.ConUniFactStmt:
		return ver.UniFact(stmt, state)
	case *ast.LogicExprStmt:
		return ver.OrAndFact(stmt, state)
	default:
		return false, fmt.Errorf("unexpected")
	}
}

type Verifier struct {
	env *env.Env
}

func NewVerifier(curEnv *env.Env, pkgName string) *Verifier {
	if curEnv == nil {
		return &Verifier{env: env.NewEnv(nil, nil, pkgName)}
	} else {
		return &Verifier{env: curEnv}
	}
}

func (ver *Verifier) successWithMsg(stmtString, storedStmtString string) {
	ver.successMsgEnd(stmtString, storedStmtString)
}

func (ver *Verifier) successNoMsg() {
}

func (ver *Verifier) newEnv(uniParamsMap map[string]ast.Fc) {
	newEnv := env.NewEnv(ver.env, uniParamsMap, ver.env.CurPkg)
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

func (ver *Verifier) OrAndFact(stmt *ast.LogicExprStmt, state VerState) (bool, error) {
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
		for _, fact := range stmt.Facts {
			ok, err := ver.FactStmt(fact, state)
			if err != nil {
				return ver.factDefer(stmt, state, false, err, "")
			}
			if ok {
				return ver.factDefer(stmt, state, true, nil, "")
			}
		}
		return ver.factDefer(stmt, state, false, nil, "")
	}
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
