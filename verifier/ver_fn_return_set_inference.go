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
)

func (ver *Verifier) parasSatisfyFnReq(fcFn *ast.FcFn, state *VerState) (bool, error) {
	// f(a)(b,c)(e,d,f) 返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
	fnHeadChain_AndItSelf, paramsChain := ast.GetFnHeadChain_AndItSelf(fcFn)

	// 从后往前找，直到找到有个 fnHead 被已知在一个 fnInFnTInterface 中
	// 比如 f(a)(b,c)(e,d,f) 我不知道 f(a)(b,c) 是哪个 fn_template 里的，但我发现 f(a) $in T 是知道的。那之后就是按T的返回值去套入b,c，然后再把e,d,f套入T的返回值的返回值
	// 此时 indexWhereLatestFnTIsGot 就是 1, FnToFnItemWhereLatestFnTIsGot 就是 f(a) 的 fnInFnTMemItem
	indexWhereLatestFnTIsGot, FnToFnItemWhereLatestFnTIsGot := ver.env.FindRightMostResolvedFn_Return_ResolvedIndexAndFnTMemItem(fnHeadChain_AndItSelf)

	// 比如 f(a)(b,c)(e,d,f) 我们现在得到了 f(a) 的 fnTStruct，那 curParamsChainIndex 就是 2, 表示 f(a) 对应的params就是 (b,c)
	// curFnTStruct := ver.env.GetFnTStructOfFnInFnTMemItem(FnToFnItemWhereLatestFnTIsGot)
	if FnToFnItemWhereLatestFnTIsGot == nil {
		return false, fmt.Errorf("%s is not defined", fnHeadChain_AndItSelf[len(fnHeadChain_AndItSelf)-1])
	}

	curFnTStruct := FnToFnItemWhereLatestFnTIsGot.AsFnTStruct
	curParamsChainIndex := indexWhereLatestFnTIsGot + 1

	// 验证 paramsChain 是否满足 fnTStruct，比如 b,c 是否满足 f(a) 的参数要求
	for curParamsChainIndex < len(fnHeadChain_AndItSelf)-1 {
		uniMap, err := ast.MakeUniMap(curFnTStruct.Params, paramsChain[curParamsChainIndex])
		if err != nil {
			return false, err
		}

		instCurFnTStruct, err := curFnTStruct.Instantiate(uniMap)
		if err != nil {
			return false, err
		}

		ok, err := ver.checkParamsSatisfyFnTStruct(paramsChain[curParamsChainIndex], instCurFnTStruct, state)
		if err != nil || !ok {
			return false, err
		}

		curRetSet, ok := instCurFnTStruct.RetSet.(*ast.FcFn)
		if !ok {
			return false, fmt.Errorf("curRetSet is not an FcFn")
		}

		curFnTStruct, err = ver.GetFnStructFromFnTName_CheckFnTParamsReq(curRetSet, state)
		if err != nil {
			return false, err
		}

		curParamsChainIndex++
	}

	uniMap, err := ast.MakeUniMap(curFnTStruct.Params, paramsChain[curParamsChainIndex])
	if err != nil {
		return false, err
	}

	instCurFnTStruct, err := curFnTStruct.Instantiate(uniMap)
	if err != nil {
		return false, err
	}

	ok, err := ver.checkParamsSatisfyFnTStruct(paramsChain[curParamsChainIndex], instCurFnTStruct, state)
	if err != nil || !ok {
		return false, err
	}

	return true, nil
}

func (ver *Verifier) GetFnStructFromFnTName_CheckFnTParamsReq(fnTName *ast.FcFn, state *VerState) (*ast.FnTStruct, error) {
	if fcFnTypeToFnTStruct, ok := ast.FcFnT_To_FnTStruct(fnTName); ok {
		return fcFnTypeToFnTStruct, nil
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.FcAtom)
		if !ok {
			return nil, fmt.Errorf("fnTNameHead is not an atom")
		}

		return ver.getFnTDef_InstFnTStructOfIt_CheckParamsSatisfyFnTReq(fnTNameHeadAsAtom, fnTName.Params, state)
	}
}

func (ver *Verifier) getFnTDef_InstFnTStructOfIt_CheckParamsSatisfyFnTReq(fnTDefName ast.FcAtom, templateParams []ast.Fc, state *VerState) (*ast.FnTStruct, error) {
	defOfT, ok := ver.env.GetFnTemplateDef(fnTDefName)
	if !ok {
		return nil, fmt.Errorf("fnTNameHead %s is not a fn template", fnTDefName)
	}

	uniMap, err := ast.MakeUniMap(defOfT.TemplateDefHeader.Params, templateParams)
	if err != nil {
		return nil, err
	}

	ok, err = ver.getFnTDef_InstFnTStructOfIt_CheckTemplateParamsDomFactsAreTrue(defOfT, uniMap, state)
	if err != nil {
		return nil, err
	}
	if !ok {
		return nil, fmt.Errorf("template params dom facts are not true")
	}

	return defOfT.Fn.Instantiate(uniMap)
}

func (ver *Verifier) getFnTDef_InstFnTStructOfIt_CheckTemplateParamsDomFactsAreTrue(fnTDef *ast.FnTemplateDefStmt, uniMap map[string]ast.Fc, state *VerState) (bool, error) {
	ver.newEnv(ver.env)
	defer ver.deleteEnvAndRetainMsg()

	for _, fact := range fnTDef.TemplateDomFacts {
		newFact, err := fact.Instantiate(uniMap)
		if err != nil {
			return false, err
		}

		ok, err := ver.VerFactStmt(newFact, state)
		if err != nil {
			return false, err
		}

		if !ok {
			return false, nil
		}
	}

	return true, nil
}

func (ver *Verifier) checkParamsSatisfyFnTStruct(concreteParams ast.FcSlice, fnTStruct *ast.FnTStruct, state *VerState) (bool, error) {
	failed := false

	// curState := state.GetNoMsg().ToReqOk()
	curState := state.GetNoMsg()
	defer func() {
		if failed {
			ver.env.Msgs = append(ver.env.Msgs, fmt.Sprintf("failed to check param(s) %s satisfy domain of\n%s", concreteParams, fnTStruct))
		}
	}()

	uniMap, err := ast.MakeUniMap(fnTStruct.Params, concreteParams)
	if err != nil {
		failed = true
		return false, err
	}

	instFnTStruct, err := fnTStruct.Instantiate(uniMap)
	if err != nil {
		failed = true
		return false, err
	}

	// 检查里面的 param 是否符合 requirement
	for _, param := range concreteParams {
		curStateFinalRound := curState.GetFinalRound()
		ok, err := ver.fcSatisfyFnRequirement(param, curStateFinalRound)
		if err != nil {
			return false, err
		}
		if !ok {
			return false, nil
		}
	}

	curStateReqOk := curState.ToReqOk()
	ok, err := ver.paramsInSets(concreteParams, instFnTStruct.ParamSets, curStateReqOk)
	if err != nil || !ok {
		failed = true
		return false, err
	}

	for _, fact := range instFnTStruct.DomFacts {
		curStateFinalRound := curState.GetFinalRound()
		switch asFact := fact.(type) {
		case *ast.SpecFactStmt:
			// 检查 fact 的 param 是否符合 requirement
			for _, param := range asFact.Params {
				ok, err := ver.fcSatisfyFnRequirement(param, curStateFinalRound)
				if err != nil {
					return false, err
				}
				if !ok {
					return false, nil
				}
			}

			ok, err := ver.VerFactStmt(asFact, curStateReqOk)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		case *ast.OrStmt:
			for _, fact := range asFact.Facts {
				// 证明所有的 参数符合要求
				for _, param := range fact.Params {
					ok, err := ver.fcSatisfyFnRequirement(param, curStateFinalRound)
					if err != nil {
						return false, err
					}
					if !ok {
						return false, nil
					}
				}
			}

			ok, err := ver.VerFactStmt(asFact, curStateReqOk)
			if err != nil {
				return false, err
			}
			if !ok {
				return false, nil
			}
		default:
			return false, fmt.Errorf("for current Litex version, dom fact only supports SpecFactStmt, but got %s", asFact)
		}
	}

	// ok, err = ver.factsAreTrue(instFnTStruct.DomFacts, curState)
	// if err != nil || !ok {
	// 	failed = true
	// 	return false, err
	// }

	return true, nil
}

// func (ver *Verifier) checkParamsSatisfyFnTStruct(concreteParams ast.FcSlice, fnTStruct *ast.FnTStruct, state *VerState) (bool, error) {
// 	failed := false

// 	curState := state.GetNoMsg()
// 	defer func() {
// 		if failed {
// 			ver.env.Msgs = append(ver.env.Msgs, fmt.Sprintf("failed to check param(s) %s satisfy domain of\n%s", concreteParams, fnTStruct))
// 		}
// 	}()

// 	uniMap, err := ast.MakeUniMap(fnTStruct.Params, concreteParams)
// 	if err != nil {
// 		failed = true
// 		return false, err
// 	}

// 	instFnTStruct, err := fnTStruct.Instantiate(uniMap)
// 	if err != nil {
// 		failed = true
// 		return false, err
// 	}

// 	ok, err := ver.paramsInSets(concreteParams, instFnTStruct.ParamSets, curState)
// 	if err != nil || !ok {
// 		failed = true
// 		return false, err
// 	}

// 	ok, err = ver.factsAreTrue(instFnTStruct.DomFacts, curState)
// 	if err != nil || !ok {
// 		failed = true
// 		return false, err
// 	}

// 	return true, nil
// }
