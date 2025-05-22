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
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func theUpMostEnvWhereRelatedThingsAreDeclared(stmt *ast.SpecFactStmt) *env.Env {
	// TODO: 避免找一定不相关的环境：如果所有涉及到的东西是在 底层环境里声明的 那就 没必要往上找了, 最顶层是 nil
	var ret *env.Env = nil
	_ = stmt
	return ret
}

func isTrueEqualFact(stmt ast.FactStmt) (*ast.SpecFactStmt, bool) {
	asSpecFact, ok := stmt.(*ast.SpecFactStmt)
	if !ok {
		return nil, false
	}

	if asSpecFact.TypeEnum != ast.TruePure {
		return nil, false
	}

	if asSpecFact.PropName.Name == glob.KeySymbolEqual {
		return asSpecFact, true
	}

	return nil, false
}

func (ver *Verifier) eqaulTrueAddSuccessMsg(left ast.Fc, right ast.Fc, state VerState, msg string) (bool, error) {
	if state.requireMsg() {
		ver.successMsgEnd(fmt.Sprintf("%s = %s", left.String(), right.String()), msg)
	}
	return true, nil
}

func (ver *Verifier) makeEqualFact(left ast.Fc, right ast.Fc) *ast.SpecFactStmt {
	return ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(glob.KeySymbolEqual), []ast.Fc{left, right})
}
