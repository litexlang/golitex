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

func (envMgr *EnvMgr) NewFactWithCheckingNameDefined(stmt ast.FactStmt) *glob.StmtRet {
	// 检查是否符合要求：比如涉及到的符号是否都定义了
	if ret := envMgr.LookUpNamesInFact(stmt, map[string]struct{}{}); ret.IsNotTrue() {
		// return glob.ErrRet(stmt.String()).AddMsg(ret.String())
		return glob.ErrRet(fmt.Sprintf(stmt.String())).AddError(ret.String())
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
		return glob.ErrRet(fmt.Sprintf("unknown fact type: %T", stmt))
	}
}

func (envMgr *EnvMgr) newUniFact(stmt *ast.UniFactStmt) *glob.StmtRet {
	for _, thenStmt := range stmt.ThenFacts {
		var ret *glob.StmtRet
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
			return glob.ErrRet(fmt.Sprintf("invalid then fact type: %s", thenStmt))
		}

		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) newUniFactWithIff(stmt *ast.UniFactWithIffStmt) *glob.StmtRet {
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

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) newOrFact(fact *ast.OrStmt) *glob.StmtRet {
	ret := envMgr.CurEnv().KnownFactsStruct.SpecFactInLogicExprMem.newFact(fact)
	if ret.IsErr() {
		return ret
	}

	// Post-processing: a != 0 or b != 0 => a^2 + b^2 > 0
	ie := NewInferenceEngine(envMgr)
	orPostProcessRet := ie.orFactPostProcess(fact)
	if orPostProcessRet.IsTrue() {
		return ret.AddShortRetAsInfers(orPostProcessRet)
	}

	return ret
}

func (envMgr *EnvMgr) newSpecFact(fact *ast.SpecFactStmt) *glob.StmtRet {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return envMgr.newTrueEqual(fact)
	}

	defer func() {
		if fact.FactType == ast.TruePure && envMgr.IsTransitiveProp(string(fact.PropName)) {
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

	var ieShortRet *glob.ShortRet
	switch fact.FactType {
	case ast.TrueExist_St:
		// ieShortRet = ie.newTrueExist(fact)
		ieShortRet = glob.NewEmptyShortTrueRet()
	case ast.FalseExist_St:
		ieShortRet = ie.newFalseExist(fact)
	default:
		ieShortRet = ie.newPureFact(fact)
	}

	return ret.AddInfers(ieShortRet.Msgs)
}

func (envMgr *EnvMgr) newTrueEqual(fact *ast.SpecFactStmt) *glob.StmtRet {
	ret := envMgr.newTrueEqualNoInfer(fact)
	if ret.IsNotTrue() {
		return ret
	}

	// postprocess for cart: if x = cart(x1, x2, ..., xn)
	ie := NewInferenceEngine(envMgr)
	shortRet := ie.newTrueEqual(fact)

	return ret.AddInfers(shortRet.Msgs)

	// if shortRet.IsErr() {
	// 	return ret.AddShortRetAsInfers(shortRet)
	// }

	// // 将 infer 消息添加到结果中
	// if shortRet.IsTrue() && len(shortRet.Msgs) > 0 {
	// 	return ret.AddInfers(shortRet.Msgs)
	// }

	// return ret
}

func (envMgr *EnvMgr) newEqualsFact(stmt *ast.EqualsFactStmt) *glob.StmtRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := envMgr.NewFactWithCheckingNameDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsSpecFact(stmt *ast.UniFactStmt, thenFact *ast.SpecFactStmt) *glob.StmtRet {
	return envMgr.storeUniFactInMem(thenFact, stmt)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsOrStmt(stmt *ast.UniFactStmt, thenFact *ast.OrStmt) *glob.StmtRet {
	return envMgr.CurEnv().KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenFact)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsIffStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactWithIffStmt) *glob.StmtRet {
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

	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsUniFactStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactStmt) *glob.StmtRet {
	mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, thenFact)
	return envMgr.newUniFact(mergedUniFact)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsEqualsFactStmt(stmt *ast.UniFactStmt, thenFact *ast.EqualsFactStmt) *glob.StmtRet {
	equalFacts := thenFact.ToEqualFacts_PairwiseCombination()
	for _, equalFact := range equalFacts {
		ret := envMgr.newUniFact_ThenFactIsSpecFact(stmt, equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return glob.NewEmptyStmtTrue()
}

func (envMgr *EnvMgr) storeUniFactInMem(specFact *ast.SpecFactStmt, uniFact *ast.UniFactStmt) *glob.StmtRet {
	return envMgr.CurEnv().KnownFactsStruct.SpecFactInUniFactMem.newFact(specFact, uniFact)
}

func (envMgr *EnvMgr) ProveImplyNewThenFactInPropDef(stmt *ast.ProveInferStmt) *glob.StmtRet {
	specFactAsParams, err := ast.ParamsInSpecFactAreStrings(stmt.SpecFact)
	if err != nil {
		return glob.ErrRet(err.Error())
	}

	definedStuff, ok := envMgr.GetPropDef(stmt.SpecFact.PropName)
	if !ok {
		return glob.ErrRet(fmt.Sprintf("undefined prop: %s", stmt.SpecFact.PropName))
	}

	def := definedStuff.Defined

	if len(specFactAsParams) != len(def.DefHeader.Params) {
		return glob.ErrRet(fmt.Sprintf("prop %s has %d params, but %d params are expected", stmt.SpecFact.PropName, len(def.DefHeader.Params), len(specFactAsParams)))
	}

	uniMap := map[string]ast.Obj{}
	for i, param := range specFactAsParams {
		uniMap[param] = ast.Atom(def.DefHeader.Params[i])
	}

	for _, stmtFact := range stmt.ImplicationFact {
		instStmtFact, err := stmtFact.InstantiateFact(uniMap)
		if err != nil {
			return glob.ErrRet(err.Error())
		}
		if def.ImplicationFactsOrNil == nil {
			def.ImplicationFactsOrNil = make([]ast.FactStmt, 0)
		}
		def.ImplicationFactsOrNil = append(def.ImplicationFactsOrNil, instStmtFact)
	}

	return glob.NewEmptyStmtTrue()
}
