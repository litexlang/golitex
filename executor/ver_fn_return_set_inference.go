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

package litex_executor

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (ver *Verifier) parasSatisfyFnReq(fnObj *ast.FnObj, state *VerState) *glob.VerRet {
	// f(a)(b,c)(e,d,f) 返回 {f, f(a), f(a)(b,c), f(a)(b,c)(e,d,f)}, {nil, {a}, {b,c}, {e,d,f}}
	fnHeadChain_AndItSelf, paramsChain := ast.GetFnHeadChain_AndItSelf(fnObj)

	// 从后往前找，直到找到有个 fnHead 被已知在一个 fnInFnTInterface 中
	// 比如 f(a)(b,c)(e,d,f) 我不知道 f(a)(b,c) 是哪个 fn_template 里的，但我发现 f(a) $in T 是知道的。那之后就是按T的返回值去套入b,c，然后再把e,d,f套入T的返回值的返回值
	// 此时 indexWhereLatestFnTIsGot 就是 1, FnToFnItemWhereLatestFnTIsGot 就是 f(a) 的 fnInFnTMemItem
	indexWhereLatestFnTIsGot, FnToFnItemWhereLatestFnTIsGot := ver.Env.FindRightMostResolvedFn_Return_ResolvedIndexAndFnTMemItem(fnHeadChain_AndItSelf)

	// 比如 f(a)(b,c)(e,d,f) 我们现在得到了 f(a) 的 fnTStruct，那 curParamsChainIndex 就是 2, 表示 f(a) 对应的params就是 (b,c)
	// curFnTStruct := ver.env.GetFnTStructOfFnInFnTMemItem(FnToFnItemWhereLatestFnTIsGot)
	if FnToFnItemWhereLatestFnTIsGot == nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("%s is not defined", fnHeadChain_AndItSelf[len(fnHeadChain_AndItSelf)-1])})
	}

	curFnTStruct := FnToFnItemWhereLatestFnTIsGot.AsFnTStruct
	curParamsChainIndex := indexWhereLatestFnTIsGot + 1

	// 验证 paramsChain 是否满足 fnTStruct，比如 b,c 是否满足 f(a) 的参数要求
	for curParamsChainIndex < len(fnHeadChain_AndItSelf)-1 {
		uniMap, err := ast.MakeUniMap(curFnTStruct.Params, paramsChain[curParamsChainIndex])
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{err.Error()})
		}

		instCurFnTStruct, err := curFnTStruct.Instantiate(uniMap)
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{err.Error()})
		}

		verRet := ver.checkParamsSatisfyFnTStruct(fnObj, paramsChain[curParamsChainIndex], instCurFnTStruct, state)
		if verRet.IsErr() {
			return verRet
		}
		if verRet.IsUnknown() {
			return verRet
		}

		curRetSet, ok := instCurFnTStruct.RetSet.(*ast.FnObj)
		if !ok {
			return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{"curRetSet is not an FnObj"})
		}

		curFnTStruct, err = ver.GetInstFnSet_CheckFnSetParamsReq(curRetSet, state)
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{err.Error()})
		}

		curParamsChainIndex++
	}

	uniMap, err := ast.MakeUniMap(curFnTStruct.Params, paramsChain[curParamsChainIndex])
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{err.Error()})
	}

	instCurFnTStruct, err := curFnTStruct.Instantiate(uniMap)
	if err != nil {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{err.Error()})
	}

	verRet := ver.checkParamsSatisfyFnTStruct(fnObj, paramsChain[curParamsChainIndex], instCurFnTStruct, state)
	if verRet.IsErr() {
		return verRet
	}
	if verRet.IsUnknown() {
		return verRet
	}

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) GetInstFnSet_CheckFnSetParamsReq(fnTName *ast.FnObj, state *VerState) (*ast.AnonymousFn, error) {
	if FnObjTypeToFnTStruct, ok := ast.AnonymousFnToInstFnTemplate(fnTName); ok {
		return FnObjTypeToFnTStruct, nil
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.Atom)
		if !ok {
			return nil, fmt.Errorf("fnTNameHead is not an atom")
		}

		return ver.getFnSetDef_InstFnInFnSet_CheckParamsSatisfyFnSetReq(fnTNameHeadAsAtom, fnTName.Params, state)
	}
}

func (ver *Verifier) getFnSetDef_InstFnInFnSet_CheckParamsSatisfyFnSetReq(fnTDefName ast.Atom, templateParams []ast.Obj, state *VerState) (*ast.AnonymousFn, error) {
	defOfT := ver.Env.GetFnTemplateDef(fnTDefName)
	if defOfT == nil {
		return nil, fmt.Errorf("fnTNameHead %s is not a fn template", fnTDefName)
	}

	uniMap, err := ast.MakeUniMap(defOfT.TemplateDefHeader.Params, templateParams)
	if err != nil {
		return nil, err
	}

	verRet := ver.getFnTDef_InstFnTStructOfIt_CheckTemplateParamsDomFactsAreTrue(defOfT, uniMap, state)
	if verRet.IsErr() {
		return nil, err
	}
	if verRet.IsUnknown() {
		return nil, fmt.Errorf("template params dom facts are not true")
	}

	return defOfT.AnonymousFn.Instantiate(uniMap)
}

func (ver *Verifier) getFnTDef_InstFnTStructOfIt_CheckTemplateParamsDomFactsAreTrue(fnTDef *ast.DefFnSetStmt, uniMap map[string]ast.Obj, state *VerState) *glob.VerRet {
	ver.newEnv()
	defer ver.deleteEnv()

	for _, fact := range fnTDef.TemplateDomFacts {
		newFact, err := fact.InstantiateFact(uniMap)
		if err != nil {
			return glob.NewVerMsg(glob.StmtRetTypeError, fact.String(), fact.GetLine(), []string{err.Error()})
		}

		verRet := ver.VerFactStmt(newFact, state)
		if verRet.IsErr() || verRet.IsUnknown() {
			return verRet
		}
	}

	return glob.NewEmptyVerRetTrue()
}

func (ver *Verifier) checkParamsSatisfyFnTStruct(fnObj *ast.FnObj, concreteParams ast.ObjSlice, fnTStruct *ast.AnonymousFn, state *VerState) *glob.VerRet {
	if len(concreteParams) != len(fnTStruct.ParamSets) {
		return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{"params and sets length mismatch"})
	}

	for i := range concreteParams {
		fact := ast.NewInFactWithObj(concreteParams[i], fnTStruct.ParamSets[i])
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() {
			return paramsOfFnObjMustInDomainSetErrMsg(fnObj, i, fact)
		}
		if verRet.IsUnknown() {
			return paramsOfFnObjMustInDomainSetErrMsg(fnObj, i, fact)
		}
	}

	// // verRet := ver.paramsInSets(concreteParams, fnTStruct.ParamSets, state.GetNoMsg())
	// if verRet.IsErr() {
	// 	return verRet
	// }
	// if verRet.IsUnknown() {
	// 	return verRet
	// }

	for i, fact := range fnTStruct.DomFacts {
		verRet := ver.VerFactStmt(fact, state)
		if verRet.IsErr() {
			return domainFactOfFnObjMustBeTrueErrMsg(fnObj, i, fact)
		}
		if verRet.IsUnknown() {
			return domainFactOfFnObjMustBeTrueErrMsg(fnObj, i, fact)
		}
	}

	// verRet = ver.factsAreTrue(fnTStruct.DomFacts, state.GetNoMsg())
	// if verRet.IsErr() {
	// 	return verRet
	// }
	// if verRet.IsUnknown() {
	// 	return verRet
	// }

	return glob.NewEmptyVerRetTrue()
}

func paramsOfFnObjMustInDomainSetErrMsg(fnObj *ast.FnObj, i int, fact ast.FactStmt) *glob.VerRet {
	return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("Function %s requires its %s argument to satisfy the domain constraint:\n%s\nbut verification failed\n", fnObj.FnHead, ordinalSuffix(i+1), fact.String())})
}

func domainFactOfFnObjMustBeTrueErrMsg(fnObj *ast.FnObj, i int, fact ast.FactStmt) *glob.VerRet {
	return glob.NewVerMsg(glob.StmtRetTypeError, fnObj.String(), 0, []string{fmt.Sprintf("Function %s requires its %s domain constraint to hold:\n%s\nbut verification failed\n", fnObj.FnHead, ordinalSuffix(i+1), fact.String())})
}
