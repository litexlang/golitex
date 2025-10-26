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
	glob "golitex/glob"
)

// 所有verifier的方法里，只有它和switch里的三大函数可能读入anyState
func (ver *Verifier) VerFactStmt(stmt ast.FactStmt, state *VerState) VerRet {
	var ok bool
	var err error

	switch asStmt := stmt.(type) {
	case *ast.SpecFactStmt:
		if asStmt.NameIs(glob.KeySymbolEqual) && asStmt.TypeEnum == ast.TruePure {
			ok, err = ver.verTrueEqualFact(asStmt, state, true)
		} else {
			ok, err = ver.verSpecFactThatIsNotTrueEqualFact_UseCommutativity(asStmt, state)
		}
	case *ast.OrStmt:
		ok, err = ver.verOrStmt(asStmt, state)
	case *ast.UniFactStmt:
		ok, err = ver.verUniFact(asStmt, state)
	case *ast.UniFactWithIffStmt:
		ok, err = ver.verUniFactWithIff(asStmt, state)
	case *ast.EqualsFactStmt:
		ok, err = ver.verEqualsFactStmt(asStmt, state)
	case *ast.IntensionalSetStmt:
		ok, err = ver.verIntensionalSetStmt(asStmt, state)
	case *ast.EnumStmt:
		ok, err = ver.verEnumStmt(asStmt, state)
	default:
		return newVerErr(fmt.Sprintf("unexpected fact statement: %s", asStmt))
	}

	return BoolErrToVerRet(ok, err)
}

func ExecFactsAtCurEnv_retFailedFact(facts []ast.FactStmt, env *env.Env, state *VerState) (glob.ExecRet, ast.FactStmt, error) {
	ver := NewVerifier(env)

	for _, fact := range facts {
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() {
			return glob.NewExecErr(""), fact, fmt.Errorf(verRet.String())
		} else if verRet.IsUnknown() {
			return glob.NewExecUnknown(""), fact, nil
		}
		err := env.NewFact(fact)
		if err != nil {
			return glob.NewExecErr(""), fact, err
		}
	}
	return glob.NewExecTrue(""), nil, nil
}

func ExecSpecFactsAtCurEnv_retRailedFact(facts []*ast.SpecFactStmt, env *env.Env) (glob.ExecRet, *ast.SpecFactStmt, error) {
	ver := NewVerifier(env)

	for _, fact := range facts {
		verRet := ver.VerFactStmt(fact, Round0Msg)
		if verRet.IsErr() {
			return glob.NewExecErr(""), fact, fmt.Errorf(verRet.String())
		} else if verRet.IsUnknown() {
			return glob.NewExecUnknown(""), fact, nil
		}
		err := env.NewFact(fact)
		if err != nil {
			return glob.NewExecErr(""), fact, err
		}
	}
	return glob.NewExecTrue(""), nil, nil
}
