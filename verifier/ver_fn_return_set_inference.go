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

func (ver *Verifier) parasSatisfyFnReq(fcFn *ast.FcFn, state *VerState) (bool, error) {
	// f(a)(b,c)(e,d,f) 返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
	fnHeadChain_AndItSelf, paramsChain := ast.GetFnHeadChain_AndItSelf(fcFn)

	// 从后往前找，直到找到有个 fnHead 被已知在一个 fnInFnTInterface 中
	// 比如 f(a)(b,c)(e,d,f) 我不知道 f(a)(b,c) 是哪个 fn_template 里的，但我发现 f(a) $in T 是知道的。那之后就是按T的返回值去套入b,c，然后再把e,d,f套入T的返回值的返回值
	indexWhereLatestFnTIsGot, FnToFnItemWhereLatestFnTIsGot := ver.get_Index_Where_LatestFnTIsGot(fnHeadChain_AndItSelf)

	curFnTStruct := ver.getFnTStructOfFnInFnTMemItem(FnToFnItemWhereLatestFnTIsGot)
	curIndex := indexWhereLatestFnTIsGot + 1

	// TODO 得到当前的 fnTStruct， 验证其 paramsChain 是否满足
	for curIndex < len(fnHeadChain_AndItSelf)-1 {
		ok, err := ver.checkParamsSatisfyFnTStruct(paramsChain[curIndex], curFnTStruct, state)
		if err != nil || !ok {
			return false, err
		}

		curRetSet, ok := curFnTStruct.RetSet.(*ast.FcFn)
		if !ok {
			return false, fmt.Errorf("curRetSet is not an FcFn")
		}

		curFnTStruct, err = ver.GetFnStructFromFnTName(curRetSet)
		if err != nil {
			return false, err
		}

		curIndex++
	}

	ok, err := ver.checkParamsSatisfyFnTStruct(paramsChain[curIndex], curFnTStruct, state)
	if err != nil || !ok {
		return false, err
	}

	return true, nil
}

func (ver *Verifier) getFnTStructOfFnInFnTMemItem(fnInFnTMemItem *env.FnInFnTMemItem) *ast.FnTStruct {
	if fnInFnTMemItem.AsFcFn != nil {
		if ok, paramSets, retSet := fnInFnTMemItem.AsFcFn.IsFnT_FcFn_Ret_ParamSets_And_RetSet(fnInFnTMemItem.AsFcFn); ok {
			excelNames := glob.GenerateNamesLikeExcelColumnNames(len(paramSets))
			return ast.NewFnTStruct(excelNames, paramSets, retSet, []ast.FactStmt{}, []ast.FactStmt{})
		}
	}

	return fnInFnTMemItem.AsFnTStruct
}

func (ver *Verifier) get_Index_Where_LatestFnTIsGot(fnHeadChain_AndItSelf []ast.Fc) (int, *env.FnInFnTMemItem) {
	indexWhereLatestFnTIsGot := 0
	var latestFnT *env.FnInFnTMemItem = nil
	for i := len(fnHeadChain_AndItSelf) - 2; i >= 0; i-- {
		fnHead := fnHeadChain_AndItSelf[i]
		if fnInFnTMemItem, ok := ver.env.GetLatestFnT_GivenNameIsIn(fnHead.String()); ok {
			latestFnT = fnInFnTMemItem
			indexWhereLatestFnTIsGot = i
			break
		}
	}

	return indexWhereLatestFnTIsGot, latestFnT
}

func (ver *Verifier) GetFnStructFromFnTName(fnTName *ast.FcFn) (*ast.FnTStruct, error) {
	if ok, paramSets, retSet := fnTName.IsFnT_FcFn_Ret_ParamSets_And_RetSet(fnTName); ok {
		excelNames := glob.GenerateNamesLikeExcelColumnNames(len(paramSets))
		return ast.NewFnTStruct(excelNames, paramSets, retSet, []ast.FactStmt{}, []ast.FactStmt{}), nil
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.FcAtom)
		if !ok {
			return nil, fmt.Errorf("fnTNameHead is not an atom")
		}

		return ver.getFnTDef_InstFnTStructOfIt(fnTNameHeadAsAtom, fnTName.Params)
	}
}

func (ver *Verifier) getFnTDef_InstFnTStructOfIt(fnTDefName ast.FcAtom, templateParams []ast.Fc) (*ast.FnTStruct, error) {
	defOfT, ok := ver.env.GetFnTemplateDef(fnTDefName)
	if !ok {
		return nil, fmt.Errorf("fnTNameHead is not a fn template")
	}

	uniMap, err := ast.MakeUniMap(defOfT.TemplateDefHeader.Params, templateParams)
	if err != nil {
		return nil, err
	}

	ok, err = ver.getFnTDef_InstFnTStructOfIt_CheckTemplateParamsDomFactsAreTrue(defOfT, uniMap)
	if err != nil {
		return nil, err
	}
	if !ok {
		return nil, fmt.Errorf("template params dom facts are not true")
	}

	return defOfT.Fn.Instantiate(uniMap)
}

func (ver *Verifier) getFnTDef_InstFnTStructOfIt_CheckTemplateParamsDomFactsAreTrue(fnTDef *ast.FnTemplateDefStmt, uniMap map[string]ast.Fc) (bool, error) {
	ver.newEnv(ver.env)
	defer ver.deleteEnvAndRetainMsg()

	for _, fact := range fnTDef.TemplateDomFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return false, err
		}

		ok, err := ver.VerFactStmt(newFact, Round0NoMsg)
		if err != nil {
			return false, err
		}

		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func (ver *Verifier) checkParamsSatisfyFnTStruct(concreteParams []ast.Fc, fnTStruct *ast.FnTStruct, state *VerState) (bool, error) {
	curState := state.GetNoMsg()

	uniMap, err := ast.MakeUniMap(fnTStruct.Params, concreteParams)
	if err != nil {
		return false, err
	}

	instFnTStruct, err := fnTStruct.Instantiate(uniMap)
	if err != nil {
		return false, err
	}

	for i := range concreteParams {
		ok, err := ver.VerFactStmt(ast.NewInFactWithFc(concreteParams[i], instFnTStruct.ParamSets[i]), curState)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	for _, fact := range instFnTStruct.DomFacts {
		ok, err := ver.VerFactStmt(fact, curState)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	return true, nil
}
