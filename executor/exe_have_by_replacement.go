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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	verifier "golitex/verifier"
)

func (exec *Executor) haveByReplacementStmt(stmt *ast.HaveByReplacementStmt) (glob.ExecState, error) {
	exec.newEnv(exec.env, exec.env.CurMatchProp)
	defer exec.deleteEnvAndRetainMsg()

	ver := verifier.NewVerifier(exec.env)

	// domSet and rangeSet are sets
	ok, err := ver.VerFactStmt(ast.NewInFactWithParamFc(stmt.DomSet, ast.FcAtom(glob.KeywordSet)), verifier.Round0NoMsg)
	if err != nil {
		return glob.ExecState_Error, fmt.Errorf("error verifying domSet and rangeSet: %v", err)
	}

	if !ok {
		return glob.ExecState_Error, fmt.Errorf("domSet and rangeSet are not sets")
	}

	ok, err = ver.VerFactStmt(ast.NewInFactWithParamFc(stmt.RangeSet, ast.FcAtom(glob.KeywordSet)), verifier.Round0NoMsg)
	if err != nil {
		return glob.ExecState_Error, fmt.Errorf("error verifying rangeSet: %v", err)
	}

	if !ok {
		return glob.ExecState_Error, fmt.Errorf("rangeSet is not a set")
	}

	params := []string{"x", "y1", "y2"}
	paramSets := []ast.Fc{stmt.DomSet, stmt.RangeSet, stmt.RangeSet}
	domFacts := []ast.FactStmt{
		ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.PropName), []ast.Fc{ast.FcAtom("x"), ast.FcAtom("y1")}),
		ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(stmt.PropName), []ast.Fc{ast.FcAtom("x"), ast.FcAtom("y2")}),
	}
	thenFacts := []ast.FactStmt{
		ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(glob.KeywordLastTwoObjectsAreEqual), []ast.Fc{ast.FcAtom("x"), ast.FcAtom("y1"), ast.FcAtom("y2")}),
	}

	uniFact := ast.NewUniFact(params, paramSets, domFacts, thenFacts)

	ok, err = ver.VerFactStmt(uniFact, verifier.Round0NoMsg)
	if err != nil {
		return glob.ExecState_Error, fmt.Errorf("error verifying have by replacement: %v", err)
	}

	if !ok {
		return glob.ExecState_Error, fmt.Errorf("have by replacement is not true")
	}

	// properties of introduced symbol
	return glob.ExecState_True, nil
}
