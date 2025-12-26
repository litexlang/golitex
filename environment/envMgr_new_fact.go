// Copyright Jiachen Shen.
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

func (envMgr *EnvMgr) NewFactWithoutCheckingNameDefined(stmt ast.FactStmt) *glob.GlobRet {
	// 检查是否符合要求：比如涉及到的符号是否都定义了
	if ret := envMgr.LookUpNamesInFact(stmt, map[string]struct{}{}); ret.IsNotTrue() {
		return glob.NewGlobErr(stmt.String()).AddMsg(ret.String())
	}

	switch f := stmt.(type) {
	case *ast.SpecFactStmt:
		return envMgr.newSpecFact(f)
	case *ast.OrStmt:
		return envMgr.newOrFact(f)
	case *ast.UniFactStmt:
		return envMgr.newUniFact(f)
	case *ast.UniFactWithIffStmt:
		return envMgr.newUniFactWithIff(f)
	case *ast.EqualsFactStmt:
		return envMgr.newEqualsFact(f)
	default:
		return glob.ErrRet(fmt.Errorf("unknown fact type: %T", stmt))
	}
}

func (envMgr *EnvMgr) newUniFact(stmt *ast.UniFactStmt) *glob.GlobRet {
	for _, thenStmt := range stmt.ThenFacts {
		var ret *glob.GlobRet
		switch asFact := thenStmt.(type) {
		case *ast.SpecFactStmt:
			ret = envMgr.newUniFact_ThenFactIsSpecFact(stmt, asFact)
		case *ast.OrStmt:
			ret = envMgr.newUniFact_ThenFactIsOrStmt(stmt, asFact)
		case *ast.UniFactWithIffStmt:
			ret = envMgr.newUniFact_ThenFactIsIffStmt(stmt, asFact)
		case *ast.UniFactStmt:
			ret = envMgr.newUniFact_ThenFactIsUniFactStmt(stmt, asFact)
		case *ast.EqualsFactStmt:
			ret = envMgr.newUniFact_ThenFactIsEqualsFactStmt(stmt, asFact)
		default:
			return glob.ErrRet(fmt.Errorf("invalid then fact type: %s", thenStmt))
		}

		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}

func (envMgr *EnvMgr) newUniFactWithIff(stmt *ast.UniFactWithIffStmt) *glob.GlobRet {
	thenToIff := stmt.NewUniFactWithThenToIff()
	ret := envMgr.newUniFact(thenToIff)
	if ret.IsErr() {
		return ret
	}

	iffToThen := stmt.NewUniFactWithIffToThen()
	ret = envMgr.newUniFact(iffToThen)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

func (envMgr *EnvMgr) newOrFact(fact *ast.OrStmt) *glob.GlobRet {
	ret := envMgr.CurEnv().KnownFactsStruct.SpecFactInLogicExprMem.newFact(fact)
	return ret
}

func (envMgr *EnvMgr) newSpecFact(fact *ast.SpecFactStmt) *glob.GlobRet {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return envMgr.newTrueEqual(fact)
	}

	defer func() {
		if fact.TypeEnum == ast.TruePure && envMgr.IsTransitiveProp(string(fact.PropName)) {
			curEnv := envMgr.CurEnv()
			if curEnv.TransitivePropMem[string(fact.PropName)] == nil {
				curEnv.TransitivePropMem[string(fact.PropName)] = make(map[string][]ast.Obj)
			}
			curEnv.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()] = append(curEnv.TransitivePropMem[string(fact.PropName)][fact.Params[0].String()], fact.Params[1])
		}
	}()

	ret := envMgr.storeSpecFactInMem(fact)
	if ret.IsNotTrue() {
		return ret
	}

	ie := NewInferenceEngine(envMgr)

	var ieRet *glob.GlobRet
	switch fact.TypeEnum {
	case ast.TrueExist_St:
		ieRet = ie.newTrueExist(fact)
	case ast.FalseExist_St:
		ieRet = ie.newFalseExist(fact)
	default:
		ieRet = ie.newPureFact(fact)
	}

	if ieRet.IsNotTrue() {
		return ieRet
	}

	return ret.AddMsgs(ieRet.GetMsgs())
}

func (envMgr *EnvMgr) newTrueEqual(fact *ast.SpecFactStmt) *glob.GlobRet {
	ret := envMgr.newTrueEqualNoInfer(fact)
	if ret.IsNotTrue() {
		return ret
	}

	// postprocess for cart: if x = cart(x1, x2, ..., xn)
	ie := NewInferenceEngine(envMgr)
	ret = ie.newTrueEqual(fact)
	return ret
}

func (envMgr *EnvMgr) newEqualsFact(stmt *ast.EqualsFactStmt) *glob.GlobRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := envMgr.NewFactWithoutCheckingNameDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsSpecFact(stmt *ast.UniFactStmt, thenFact *ast.SpecFactStmt) *glob.GlobRet {
	return envMgr.storeUniFactInMem(thenFact, stmt)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsOrStmt(stmt *ast.UniFactStmt, thenFact *ast.OrStmt) *glob.GlobRet {
	return envMgr.CurEnv().KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenFact)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsIffStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactWithIffStmt) *glob.GlobRet {
	thenToIff := thenFact.NewUniFactWithThenToIff()
	iffToThen := thenFact.NewUniFactWithIffToThen()

	mergedThenToIff := ast.MergeOuterInnerUniFacts(stmt, thenToIff)
	ret := envMgr.newUniFact(mergedThenToIff)
	if ret.IsErr() {
		return ret
	}

	mergedIffToThen := ast.MergeOuterInnerUniFacts(stmt, iffToThen)
	ret = envMgr.newUniFact(mergedIffToThen)
	if ret.IsErr() {
		return ret
	}

	return glob.NewGlobTrue("")
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsUniFactStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactStmt) *glob.GlobRet {
	mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, thenFact)
	return envMgr.newUniFact(mergedUniFact)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsEqualsFactStmt(stmt *ast.UniFactStmt, thenFact *ast.EqualsFactStmt) *glob.GlobRet {
	equalFacts := thenFact.ToEqualFacts_PairwiseCombination()
	for _, equalFact := range equalFacts {
		ret := envMgr.newUniFact_ThenFactIsSpecFact(stmt, equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewGlobTrue("")
}

func (envMgr *EnvMgr) storeUniFactInMem(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) *glob.GlobRet {
	return envMgr.CurEnv().KnownFactsStruct.SpecFactInUniFactMem.newFact(specFact, uniFact)
}
