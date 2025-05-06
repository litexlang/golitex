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

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
)

func (ver *Verifier) ConUniFact(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	// 在局部环境声明新变量
	ver.newEnv(nil)
	defer ver.deleteEnvAndRetainMsg()
	for _, param := range stmt.Params {
		// TODO: 需要在这里know一下 涉及到的变量是 in 某个集合的
		ver.env.Declare(nil, param)
	}

	// know cond facts
	for _, condFact := range stmt.DomFacts {
		err := ver.env.NewFactWithOutEmit(condFact)
		if err != nil {
			return false, err
		}
	}

	if stmt.IffFacts == nil {
		return ver.uniFactWithoutIff(stmt, state)
	} else {
		return ver.uniFactWithIff(stmt, state)
	}
}

func (ver *Verifier) uniFactWithoutIff(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				ver.unknownMsgEnd("%s is unknown", thenFact.String())
			}
			return false, nil
		}

		// if true, store it
		err = ver.env.NewFactWithOutEmit(thenFact)
		if err != nil {
			return false, err
		}
	}

	if state.requireMsg() {
		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
		if err != nil {
			return false, err
		}
	}

	return true, nil
}

func (ver *Verifier) uniFactWithIff(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	ok, err := ver.uniFactWithIffThenToIff(stmt, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	ok, err = ver.uniFactWithIffToThen(stmt, state)
	if err != nil {
		return false, err
	}
	if !ok {
		return false, nil
	}

	return true, nil
}

func (ver *Verifier) uniFactWithIffThenToIff(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	ver.newEnv(nil)
	defer ver.deleteEnvAndRetainMsg()
	for _, condFact := range stmt.ThenFacts {
		err := ver.env.NewFactWithOutEmit(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, toCheckFact := range stmt.IffFacts {
		ok, err := ver.FactStmt(toCheckFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				ver.unknownMsgEnd("%s is unknown", toCheckFact.String())
			}
			return false, nil
		}

		err = ver.env.NewFactWithOutEmit(toCheckFact)
		if err != nil {
			return false, err
		}
	}

	if state.requireMsg() {
		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
		if err != nil {
			return false, err
		}
	}

	return true, nil
}

func (ver *Verifier) uniFactWithIffToThen(stmt *ast.UniFactStmt, state VerState) (bool, error) {
	ver.newEnv(nil)
	defer ver.deleteEnvAndRetainMsg()
	for _, condFact := range stmt.IffFacts {
		err := ver.env.NewFactWithOutEmit(condFact)
		if err != nil {
			return false, err
		}
	}

	for _, toCheckFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(toCheckFact, state)
		if err != nil {
			return false, err
		}
		if !ok {
			if state.requireMsg() {
				ver.unknownMsgEnd("%s is unknown", toCheckFact.String())
			}
			return false, nil
		}

		err = ver.env.NewFactWithOutEmit(toCheckFact)
		if err != nil {
			return false, err
		}
	}

	if state.requireMsg() {
		err := ver.newMsgAtParent(fmt.Sprintf("%s\nis true", stmt.String()))
		if err != nil {
			return false, err
		}
	}

	return true, nil
}
