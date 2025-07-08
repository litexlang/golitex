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
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_verifier

import (
	"fmt"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
)

func (ver *Verifier) todo_theUpMostEnvWhereRelatedThingsAreDeclared(stmt *ast.SpecFactStmt) *env.Env {
	_ = stmt
	return nil
}

func (ver *Verifier) equalTrueAddSuccessMsg(left ast.Fc, right ast.Fc, state VerState, msg string) (bool, error) {
	if state.requireMsg() {
		ver.successWithMsg(fmt.Sprintf("%s = %s", left, right), msg)
	}
	return true, nil
}

func (ver *Verifier) makeEqualFact(left ast.Fc, right ast.Fc) *ast.SpecFactStmt {
	return ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeySymbolEqual), []ast.Fc{left, right})
}

func isErrOrOk(ok bool, err error) bool {
	return err != nil || ok
}

func (ver *Verifier) processOkMsg(state VerState, msg string, verifiedBy string, args ...any) (bool, error) {
	if state.requireMsg() {
		ver.successWithMsg(msg, fmt.Sprintf(verifiedBy, args...))
	}
	return true, nil
}

func (ver *Verifier) verErr(err error, msg string, args ...any) error {
	return fmt.Errorf("%s\n%s", err.Error(), fmt.Sprintf(msg, args...))
}

func (ver *Verifier) isCommutativeProp_BuiltinRule(stmt *ast.SpecFactStmt) bool {
	return stmt.PropName == glob.KeySymbolEqual
}
