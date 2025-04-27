// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

package litex_verifier

import (
	"fmt"
	ast "golitex/litex_ast"
)

func (ver *Verifier) UniFact(stmt *ast.ConUniFactStmt, state VerState) (bool, error) {
	// TODO: 需要在这里know一下 涉及到的变量是 in 某个集合的

	// 在局部环境声明新变量
	ver.newEnv(nil)
	defer ver.deleteEnvAndRetainMsg()
	for _, param := range stmt.Params {
		ver.env.Declare(nil, param)
	}

	// know cond facts
	for _, condFact := range stmt.DomFacts {
		err := ver.env.NewFact(condFact)
		if err != nil {
			return false, err
		}
	}

	// check then facts
	for _, thenFact := range stmt.ThenFacts {
		ok, err := ver.FactStmt(thenFact, state) // 这个地方有点tricky，这里是可能读入state是any的，而且我要允许读入any
		if err != nil {
			return false, err
		}
		if !ok {
			ver.unknownMsgEnd("%s is unknown", thenFact.String())
			return false, nil
		}

		// if true, store it
		err = ver.env.NewFact(thenFact)
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
