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

func (envMgr *EnvMgr) NewFactWithCheckingNameDefined(stmt ast.FactStmt) ast.InferRet {
	// 检查是否符合要求：比如涉及到的符号是否都定义了
	if ret := envMgr.LookUpNamesInFact(stmt, map[string]struct{}{}); ret.IsNotTrue() {
		return ast.NewErrInferRet(stmt).AddExtraInfos(ret.GetMsg())
	}

	switch f := stmt.(type) {
	case ast.SpecificFactStmt:
		return envMgr.newSpecFact(f)
	case *ast.OrStmt:
		return envMgr.newOrFact(f)
	case *ast.UniFactStmt:
		return envMgr.NewFactWithCheckingNameDefined_UniFact(f)
	case *ast.UniFactWithIffStmt:
		return envMgr.newUniFactWithIff(f)
	case *ast.EqualsFactStmt:
		return envMgr.newEqualsFact(f)
	default:
		return ast.NewErrInferRet(stmt).AddExtraInfo(fmt.Sprintf("unknown fact type: %T", stmt))
	}
}

// storeUniFactAsInferTemplateIfApplicable checks if all DomFacts and ThenFacts are SpecFactStmt or OrStmt,
// and if so, stores them as InferTemplateStmt in SpecFactInImplyTemplateMem.
// This function does not return errors - it silently skips storage if conditions are not met.
func (envMgr *EnvMgr) storeUniFactAsInferTemplateIfApplicable(stmt *ast.UniFactStmt, ifFacts []ast.FactStmt) {
	// 如果dom和then全是spec 或者 or，那做成 imply存起来
	// Check if all DomFacts and ThenFacts are SpecFactStmt or OrStmt
	domFactsReversible := []ast.Spec_OrFact{}
	for _, domFact := range stmt.DomFacts {
		if specFact, ok := domFact.(ast.SpecificFactStmt); ok {
			domFactsReversible = append(domFactsReversible, specFact)
		} else if orStmt, ok := domFact.(*ast.OrStmt); ok {
			domFactsReversible = append(domFactsReversible, orStmt)
		} else {
			// Not all facts are Spec_OrFact, skip storing as InferTemplate
			return
		}
	}

	thenFactsReversible := []ast.Spec_OrFact{}
	for _, thenFact := range stmt.ThenFacts {
		if specFact, ok := thenFact.(ast.SpecificFactStmt); ok {
			thenFactsReversible = append(thenFactsReversible, specFact)
		} else if orStmt, ok := thenFact.(*ast.OrStmt); ok {
			thenFactsReversible = append(thenFactsReversible, orStmt)
		} else {
			// Not all facts are Spec_OrFact, skip storing as InferTemplate
			return
		}
	}

	// All facts are Spec_OrFact, create InferTemplateStmt and store
	inferTemplate := ast.NewInferTemplateStmt(stmt.Params, stmt.ParamSets, domFactsReversible, thenFactsReversible, ifFacts, []ast.Stmt{}, stmt.Line)

	// Store each thenFact in SpecFactInImplyTemplateMem
	for _, thenFact := range inferTemplate.ThenFacts {
		storeRet := envMgr.StoreSpecFactInImplyTemplateMem(thenFact, inferTemplate)
		if storeRet.IsErr() {
			// If storage fails, silently skip (don't fail the whole operation)
			return
		}
	}
}

func (envMgr *EnvMgr) NewFactWithCheckingNameDefined_UniFact(stmt *ast.UniFactStmt) ast.InferRet {
	ret := envMgr.newUniFact(stmt)
	if ret.IsNotTrue() {
		return ret
	}

	// Try to store as InferTemplate if applicable
	envMgr.storeUniFactAsInferTemplateIfApplicable(stmt, []ast.FactStmt{})

	return ast.NewTrueInferRet(stmt)
}

func (envMgr *EnvMgr) newUniFact(stmt *ast.UniFactStmt) ast.InferRet {
	for i, thenStmt := range stmt.ThenFacts {
		var ret ast.InferRet
		switch asFact := thenStmt.(type) {
		case ast.SpecificFactStmt:
			ret = envMgr.newUniFact_ThenFactIsSpecFact(stmt, i)
		case *ast.OrStmt:
			ret = envMgr.newUniFact_ThenFactIsOrStmt(stmt, asFact)
		default:
			return ast.NewErrInferRet(stmt).AddExtraInfo(fmt.Sprintf("invalid then fact type: %s", thenStmt))
		}

		if ret.IsErr() {
			return ret
		}
	}
	return ast.NewTrueInferRet(stmt)
}

func (envMgr *EnvMgr) newUniFactWithIff(stmt *ast.UniFactWithIffStmt) ast.InferRet {
	thenToIff := stmt.NewUniFactWithThenToIff()
	ret := envMgr.newUniFact(thenToIff)
	if ret.IsErr() {
		return ret
	}

	// Try to store as InferTemplate if applicable (with IffFacts as ifFacts)
	envMgr.storeUniFactAsInferTemplateIfApplicable(thenToIff, []ast.FactStmt{})

	iffToThen := stmt.NewUniFactWithIffToThen()
	ret = envMgr.newUniFact(iffToThen)
	if ret.IsErr() {
		return ret
	}

	// Try to store as InferTemplate if applicable (with IffFacts as ifFacts)
	envMgr.storeUniFactAsInferTemplateIfApplicable(iffToThen, []ast.FactStmt{})

	return ast.NewTrueInferRet(stmt)
}

func (envMgr *EnvMgr) newOrFact(fact *ast.OrStmt) ast.InferRet {
	ret := envMgr.newOrFactNoInfer(fact)
	if ret.IsNotTrue() {
		return ast.NewErrInferRet(fact).AddExtraInfo(fmt.Sprintf("newOrFact: %s", fact))
	}

	return ast.NewTrueInferRet(fact)
}

func (envMgr *EnvMgr) newSpecFact(fact ast.SpecificFactStmt) ast.InferRet {
	if isEqualFact := ast.IsTrueEqualFact(fact); isEqualFact {
		return envMgr.newTrueEqual(fact.(*ast.PureSpecificFactStmt))
	}

	defer func() {
		if asFact, ok := fact.(*ast.PureSpecificFactStmt); ok && asFact.IsTrue && envMgr.IsTransitiveProp(string(asFact.PropName)) {
			curEnv := envMgr.CurEnv()
			if curEnv.TransitivePropMem[string(asFact.PropName)] == nil {
				curEnv.TransitivePropMem[string(asFact.PropName)] = make(map[string][]ast.Obj)
			}
			curEnv.TransitivePropMem[string(asFact.PropName)][asFact.Params[0].String()] = append(curEnv.TransitivePropMem[string(asFact.PropName)][asFact.Params[0].String()], asFact.Params[1])
		}
	}()

	ret := envMgr.storeSpecFactInMem(fact)
	if ret.IsNotTrue() {
		return ret
	}

	ie := NewInferenceEngine(envMgr)

	var ieInferRet ast.InferRet
	switch asFact := fact.(type) {
	case *ast.ExistSpecificFactStmt:
		if asFact.IsTrue {
			ieInferRet = ast.NewTrueInferRet(fact)
		} else {
			ieInferRet = ie.newFalseExist(asFact)
		}
	case *ast.PureSpecificFactStmt:
		ieInferRet = ie.newPureFact(asFact)
	}

	if ieInferRet.IsNotTrue() {
		return ieInferRet
	} else {
		return ast.NewTrueInferRet(fact).AddInfers(ieInferRet.(*ast.TrueInferRet).Infer)
	}
}

func (envMgr *EnvMgr) newTrueEqual(fact *ast.PureSpecificFactStmt) ast.InferRet {
	ret := envMgr.newTrueEqualNoInfer(fact)
	if ret.IsNotTrue() {
		return ret
	}

	// postprocess for cart: if x = cart(x1, x2, ..., xn)
	ie := NewInferenceEngine(envMgr)
	shortRet := ie.newTrueEqual(fact)

	return shortRet
}

func (envMgr *EnvMgr) newEqualsFact(stmt *ast.EqualsFactStmt) ast.InferRet {
	equalFacts := stmt.ToEqualFacts()
	for _, equalFact := range equalFacts {
		ret := envMgr.NewFactWithCheckingNameDefined(equalFact)
		if ret.IsErr() {
			return ret
		}
	}
	return ast.NewTrueInferRet(stmt)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsSpecFact(stmt *ast.UniFactStmt, thenFactIndex int) ast.InferRet {
	// return envMgr.storeUniFactInMem(thenFact, stmt)
	return envMgr.CurEnv().KnownFactsStruct.SpecFactInUniFactMem.newFact(thenFactIndex, stmt)
}

// func (envMgr *EnvMgr) newUniFact_ThenFactIsOrStmt(stmt *ast.UniFactStmt, thenFact *ast.OrStmt) ast.InferRet{
// 	return envMgr.CurEnv().KnownFactsStruct.SpecFact_InLogicExpr_InUniFactMem.NewFact(stmt, thenFact)
// }

func (envMgr *EnvMgr) newUniFact_ThenFactIsIffStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactWithIffStmt) ast.InferRet {
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

	return ast.NewTrueInferRet(thenFact)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsUniFactStmt(stmt *ast.UniFactStmt, thenFact *ast.UniFactStmt) ast.InferRet {
	mergedUniFact := ast.MergeOuterInnerUniFacts(stmt, thenFact)
	return envMgr.newUniFact(mergedUniFact)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsEqualsFactStmt(stmt *ast.UniFactStmt, thenFact *ast.EqualsFactStmt) ast.InferRet {
	equalFacts := thenFact.ToEqualFacts_PairwiseCombination()

	newUniFact := ast.NewUniFact(stmt.Params, stmt.ParamSets, stmt.DomFacts, equalFacts, stmt.Line)

	for i, _ := range equalFacts {
		ret := envMgr.newUniFact_ThenFactIsSpecFact(newUniFact, i)
		if ret.IsErr() {
			return ret
		}
	}
	return ast.NewTrueInferRet(thenFact)
}

// func (envMgr *EnvMgr) storeUniFactInMem(specFact ast.SpecificFactStmt, uniFact *ast.UniFactStmt) ast.InferRet{
// 	return envMgr.CurEnv().KnownFactsStruct.SpecFactInUniFactMem.newFact(specFact, uniFact)
// }

func (envMgr *EnvMgr) ProveImplyNewThenFactInPropDef(stmt *ast.ProveInferStmt) ast.InferRet {
	specFactAsParams, err := ast.ParamsInSpecFactAreStrings(stmt.SpecFact)
	if err != nil {
		return ast.NewErrInferRet(stmt.SpecFact).AddExtraInfo(err.Error())
	}

	definedStuff, ok := envMgr.GetPropDef(stmt.SpecFact.PropName)
	if !ok {
		return ast.NewErrInferRet(stmt.SpecFact).AddExtraInfo(fmt.Sprintf("undefined prop: %s", stmt.SpecFact.PropName))
	}

	def := definedStuff.Defined

	if len(specFactAsParams) != len(def.DefHeader.Params) {
		return ast.NewErrInferRet(stmt.SpecFact).AddExtraInfo(fmt.Sprintf("prop %s has %d params, but %d params are expected", stmt.SpecFact.PropName, len(def.DefHeader.Params), len(specFactAsParams)))
	}

	uniMap := map[string]ast.Obj{}
	for i, param := range specFactAsParams {
		uniMap[param] = ast.Atom(def.DefHeader.Params[i])
	}

	for _, stmtFact := range stmt.ImplicationFact {
		instStmtFact, err := stmtFact.InstantiateFact(uniMap)
		if err != nil {
			return ast.NewErrInferRet(stmtFact).AddExtraInfo(err.Error())
		}
		if def.ImplicationFactsOrNil == nil {
			def.ImplicationFactsOrNil = make([]ast.Spec_OrFact, 0)
		}
		def.ImplicationFactsOrNil = append(def.ImplicationFactsOrNil, instStmtFact.(ast.Spec_OrFact))
	}

	return ast.NewTrueInferRet(stmt.SpecFact)
}

func (envMgr *EnvMgr) newUniFact_ThenFactIsOrStmt(stmt *ast.UniFactStmt, thenFact *ast.OrStmt) ast.InferRet {
	return envMgr.storeOrFactInUniFactMem(thenFact, stmt)
}

func (envMgr *EnvMgr) StoreFnIsAFn(fnName ast.Obj, fnSet *ast.FnSetObj) {
	envMgr.CurEnv().FnInFnSetMem[fnName.String()] = fnSet
}
