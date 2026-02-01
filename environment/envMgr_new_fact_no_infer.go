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
)

// newFactNoInfer stores facts without performing any inference.
// This is used to prevent circular definitions (e.g., p => q, q => p).
func (envMgr *EnvMgr) newFactNoInfer(stmt ast.FactStmt) ast.InferRet {
	switch f := stmt.(type) {
	case ast.SpecificFactStmt:
		return envMgr.newSpecFactNoInfer(f)
	case *ast.OrStmt:
		return envMgr.newOrFactNoInfer(f)
	case *ast.UniFactStmt:
		return envMgr.newUniFactNoInfer(f)
	case *ast.UniFactWithIffStmt:
		return envMgr.newUniFactWithIffNoInfer(f)
	case *ast.EqualsFactStmt:
		return envMgr.newEqualsFactNoInfer(f)
	default:
		return ast.NewErrInferRet(stmt).AddExtraInfo(fmt.Sprintf("unknown fact type: %T", stmt))
	}
}

// newSpecFactNoInfer stores a SpecFact without performing any inference.
// It only stores the fact in memory, without triggering post-processing.
func (envMgr *EnvMgr) newSpecFactNoInfer(fact ast.SpecificFactStmt) ast.InferRet {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return envMgr.newTrueEqualNoInfer(fact.(*ast.PureSpecificFactStmt))
	}

	ret := envMgr.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ret
	}

	return ast.NewTrueInferRet(fact)
}

// newTrueEqualNoInfer stores an equality fact without performing any inference.
// It stores the equality in the equal memory and simplifies symbol values,
// but does not trigger equality-related inferences (e.g., cart, tuple, listSet).
func (envMgr *EnvMgr) newTrueEqualNoInfer(fact *ast.PureSpecificFactStmt) ast.InferRet {
	if len(fact.Params) != 2 {
		return ast.NewErrInferRet(fact).AddExtraInfo(fmt.Sprintf("'=' fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	ret := envMgr.storeTrueEqualInEqualMemNoInfer(fact)
	if ret.IsErr() {
		return ret
	}

	// 如果 a = b 中，某一项是 数值型，那就算出来这个数值，卷后把它保留在equalMem中
	ret = envMgr.storeSymbolSimplifiedValue(fact.Params[0], fact.Params[1])
	if ret.IsErr() {
		return ret
	}

	return ast.NewTrueInferRet(fact)
}

// newEqualsFactNoInfer stores an EqualsFact without performing any inference.
// It converts the EqualsFact to individual equality facts and stores them without inference.
func (envMgr *EnvMgr) newEqualsFactNoInfer(stmt *ast.EqualsFactStmt) ast.InferRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := envMgr.newSpecFactNoInfer(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return ast.NewTrueInferRet(stmt)
}

// func (envMgr *EnvMgr) newOrFactNoInfer(fact *ast.OrStmt) ast.InferRet{
// 	ret := envMgr.CurEnv().KnownFactsStruct.SpecFactInLogicExprMem.newFact(fact)
// 	return ret
// }

func (envMgr *EnvMgr) newUniFactNoInfer(stmt *ast.UniFactStmt) ast.InferRet {
	for index, thenStmt := range stmt.ThenFacts {
		var ret ast.InferRet
		switch thenStmt.(type) {
		case ast.SpecificFactStmt:
			ret = envMgr.newUniFact_ThenFactIsSpecFact(stmt, index)
		case *ast.OrStmt:
			// ret = envMgr.newUniFact_ThenFactIsOrStmt(stmt, asFact)
			ret = ast.NewTrueInferRet(stmt)
		default:
			return ast.NewErrInferRet(stmt).AddExtraInfo(fmt.Sprintf("invalid then fact type: %s", thenStmt))
		}

		if ret.IsErr() {
			return ret
		}
	}
	return ast.NewTrueInferRet(stmt)
}

func (envMgr *EnvMgr) newUniFactWithIffNoInfer(stmt *ast.UniFactWithIffStmt) ast.InferRet {
	thenToIff := stmt.NewUniFactWithThenToIff()
	ret := envMgr.newUniFactNoInfer(thenToIff)
	if ret.IsErr() {
		return ret
	}

	iffToThen := stmt.NewUniFactWithIffToThen()
	ret = envMgr.newUniFactNoInfer(iffToThen)
	if ret.IsErr() {
		return ret
	}

	return ast.NewTrueInferRet(stmt)
}

func (envMgr *EnvMgr) newOrFactNoInfer(fact *ast.OrStmt) ast.InferRet {
	for _, specFact := range fact.Facts {
		propName := specFact.GetPropName()
		knowns, ok := envMgr.CurEnv().OrFactsMem[propName.String()]
		if ok {
			envMgr.CurEnv().OrFactsMem[propName.String()] = append(knowns, fact)
		} else {
			envMgr.CurEnv().OrFactsMem[propName.String()] = []*ast.OrStmt{fact}
		}
	}
	return ast.NewTrueInferRet(fact)
}

func (envMgr *EnvMgr) storeOrFactInUniFactMem(orFact *ast.OrStmt, uniFact *ast.UniFactStmt) ast.InferRet {
	propName := orFact.Facts[0].GetPropName()
	knowns, ok := envMgr.CurEnv().OrFactInUniFactMem[propName.String()]
	if ok {
		envMgr.CurEnv().OrFactInUniFactMem[propName.String()] = append(knowns, NewOrFactInUniFactMem(orFact, uniFact))
	} else {
		envMgr.CurEnv().OrFactInUniFactMem[propName.String()] = []*OrFactInUniFact{NewOrFactInUniFactMem(orFact, uniFact)}
	}
	return ast.NewTrueInferRet(orFact)
}
