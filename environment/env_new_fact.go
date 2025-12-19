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

package litex_env

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (env *Env) NewFactWithAtomsDefined(stmt ast.FactStmt) glob.GlobRet {
	// 检查是否符合要求：比如涉及到的符号是否都定义了
	if ret := env.AtomObjsInFactProperlyDefined(stmt, map[string]struct{}{}); ret.IsNotTrue() {
		return glob.NewGlobErr(stmt.String()).AddMsg(ret.String())
	}

	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return env.newSpecFact(f)
	case *ast.OrStmt:
		return env.newOrFact(f)
	case *ast.UniFactStmt:
		return env.newUniFact(f)
	case *ast.UniFactWithIffStmt:
		return env.newUniFactWithIff(f)
	case *ast.EqualsFactStmt:
		return env.newEqualsFact(f)
	default:
		return glob.ErrRet(fmt.Errorf("unknown fact type: %T", stmt))
	}
}

func (env *Env) newUniFact(stmt *ast.UniFactStmt) glob.GlobRet {
	for _, thenStmt := range stmt.ThenFacts {
		var ret glob.GlobRet
		switch asFact := thenStmt.(type) {
		case *ast.SpecFactStmt:
			ret = env.newUniFact_ThenFactIsSpecFact(stmt, asFact)
		case *ast.OrStmt:
			ret = env.newUniFact_ThenFactIsOrStmt(stmt, asFact)
		case *ast.UniFactWithIffStmt:
			ret = env.newUniFact_ThenFactIsIffStmt(stmt, asFact)
		case *ast.UniFactStmt:
			ret = env.newUniFact_ThenFactIsUniFactStmt(stmt, asFact)
		case *ast.EqualsFactStmt:
			ret = env.newUniFact_ThenFactIsEqualsFactStmt(stmt, asFact)
		default:
			return glob.ErrRet(fmt.Errorf("invalid then fact type: %s", thenStmt))
		}

		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}

func (e *Env) newUniFactWithIff(stmt *ast.UniFactWithIffStmt) glob.GlobRet {
	thenToIff := stmt.NewUniFactWithThenToIff()
	ret := e.newUniFact(thenToIff)
	if ret.IsErr() {
		return ret
	}

	iffToThen := stmt.NewUniFactWithIffToThen()
	ret = e.newUniFact(iffToThen)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

func (env *Env) newOrFact(fact *ast.OrStmt) glob.GlobRet {
	ret := env.KnownFactsStruct.SpecFactInLogicExprMem.newFact(fact)
	return ret
}

func (env *Env) newSpecFact(fact *ast.SpecFactStmt) glob.GlobRet {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return env.newTrueEqual(fact)
	}

	defer func() {
		if fact.TypeEnum == ast.TruePure && env.IsTransitiveProp(string(fact.PropName)) {
			if env.TransitivePropMem[string(fact.PropName)] == nil {
				env.TransitivePropMem[string(fact.PropName)] = make(map[string][]ast.Obj)
			}
			env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()] = append(env.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()], fact.Params[1])
		}
	}()

	ret := env.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}

	ie := NewInferenceEngine(env)
	switch fact.TypeEnum {
	case ast.TrueExist_St:
		return ie.newTrueExist(fact)
	case ast.FalseExist_St:
		return ie.newFalseExist(fact)
	default:
		return ie.newPureFact(fact)
	}
}

func (env *Env) newTrueEqual(fact *ast.SpecFactStmt) glob.GlobRet {
	ret := env.newTrueEqualNoInfer(fact)
	if ret.IsNotTrue() {
		return ret
	}

	// postprocess for cart: if x = cart(x1, x2, ..., xn)
	ie := NewInferenceEngine(env)
	ret = ie.newTrueEqual(fact)
	return ret
}

func (env *Env) newEqualsFact(stmt *ast.EqualsFactStmt) glob.GlobRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := env.NewFactWithAtomsDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}
