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
	cmp "golitex/cmp"
	glob "golitex/glob"
)

func (envMgr *EnvMgr) GenerateUnusedRandomName() string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := envMgr.IsNameUnavailable((randomStr), map[string]struct{}{})
		if !ret {
			return randomStr
		}
		i++
	}
}

func (envMgr *EnvMgr) GenerateUnusedRandomNameWhichIsAlsoNotInGivenMap(m map[string]struct{}) string {
	i := 4
	var randomStr string
	for {
		randomStr = glob.RandomString(i)
		// check if the string is undeclared
		ret := envMgr.IsNameUnavailable(randomStr, map[string]struct{}{})
		if !ret {
			_, ok := m[randomStr]
			if !ok {
				return randomStr
			}
		}
		i++
	}
}

func (envMgr *EnvMgr) GenerateNUnusedRandomNames(n int) []string {
	if n <= 0 {
		return []string{}
	}

	usedNames := make(map[string]struct{})
	result := make([]string, n)

	for i := 0; i < n; i++ {
		randomName := envMgr.GenerateUnusedRandomNameWhichIsAlsoNotInGivenMap(usedNames)
		result[i] = randomName
		usedNames[randomName] = struct{}{}
	}

	return result
}

func (envMgr *EnvMgr) GetFnStructFromFnTName(fnTName *ast.FnObj) (*ast.AnonymousFn, ast.ShortRet) {
	if objFnTypeToFnTStruct, ok := envMgr.AnonymousFnToInstFnTemplate(fnTName); ok {
		return objFnTypeToFnTStruct, ast.NewTrueShortRet()
	} else {
		fnTNameHeadAsAtom, ok := fnTName.FnHead.(ast.Atom)
		if !ok {
			return nil, ast.NewTrueShortRetWithMsg(fmt.Sprintf("fnTNameHead is not an atom"))
		}

		return envMgr.getFnTDef_InstFnTStructOfIt(fnTNameHeadAsAtom, fnTName.Params)
	}
}

func (envMgr *EnvMgr) getFnTDef_InstFnTStructOfIt(fnTDefName ast.Atom, templateParams []ast.Obj) (*ast.AnonymousFn, ast.ShortRet) {
	defOfT := envMgr.GetFnTemplateDef(fnTDefName)
	if defOfT == nil {
		return nil, ast.NewErrShortRetWithMsg(fmt.Sprintf("fnTNameHead %s is not a fn template", fnTDefName))
	}

	uniMap, err := ast.MakeUniMap(defOfT.TemplateDefHeader.Params, templateParams)
	if err != nil {
		return nil, ast.NewErrShortRetWithMsg(err.Error())
	}

	fnTStruct, err := defOfT.AnonymousFn.Instantiate(uniMap)
	if err != nil {
		return nil, ast.NewErrShortRetWithMsg(err.Error())
	}

	return fnTStruct, ast.NewTrueShortRet()
}

func (envMgr *EnvMgr) storeSpecFactInMem(stmt ast.SpecificFactStmt) ast.InferRet {
	switch asFact := stmt.(type) {
	case *ast.PureSpecificFactStmt:
		if asFact.IsTrue {
			_, ok := envMgr.CurEnv().KnownFactsStruct.SpecFactMem.PureFacts[string(asFact.GetPropName())]
			if !ok {
				envMgr.CurEnv().KnownFactsStruct.SpecFactMem.PureFacts[string(asFact.GetPropName())] = []*ast.PureSpecificFactStmt{}
			}

			envMgr.CurEnv().KnownFactsStruct.SpecFactMem.PureFacts[string(asFact.GetPropName())] = append(envMgr.CurEnv().KnownFactsStruct.SpecFactMem.PureFacts[string(asFact.GetPropName())], asFact)
			return ast.NewTrueInferRet(stmt)
		} else {
			_, ok := envMgr.CurEnv().KnownFactsStruct.SpecFactMem.NotPureFacts[string(asFact.GetPropName())]
			if !ok {
				envMgr.CurEnv().KnownFactsStruct.SpecFactMem.NotPureFacts[string(asFact.GetPropName())] = []*ast.PureSpecificFactStmt{}
			}
			envMgr.CurEnv().KnownFactsStruct.SpecFactMem.NotPureFacts[string(asFact.GetPropName())] = append(envMgr.CurEnv().KnownFactsStruct.SpecFactMem.NotPureFacts[string(asFact.GetPropName())], asFact)
			return ast.NewTrueInferRet(stmt)
		}
	case *ast.ExistSpecificFactStmt:
		if asFact.IsTrue {
			_, ok := envMgr.CurEnv().KnownFactsStruct.SpecFactMem.Exist_St_Facts[string(asFact.GetPropName())]
			if !ok {
				envMgr.CurEnv().KnownFactsStruct.SpecFactMem.Exist_St_Facts[string(asFact.GetPropName())] = []*ast.ExistSpecificFactStmt{}
			}
			envMgr.CurEnv().KnownFactsStruct.SpecFactMem.Exist_St_Facts[string(asFact.GetPropName())] = append(envMgr.CurEnv().KnownFactsStruct.SpecFactMem.Exist_St_Facts[string(asFact.GetPropName())], asFact)
			return ast.NewTrueInferRet(stmt)
		} else {
			_, ok := envMgr.CurEnv().KnownFactsStruct.SpecFactMem.NotExist_St_Facts[string(asFact.GetPropName())]
			if !ok {
				envMgr.CurEnv().KnownFactsStruct.SpecFactMem.NotExist_St_Facts[string(asFact.GetPropName())] = []*ast.ExistSpecificFactStmt{}
			}
			envMgr.CurEnv().KnownFactsStruct.SpecFactMem.NotExist_St_Facts[string(asFact.GetPropName())] = append(envMgr.CurEnv().KnownFactsStruct.SpecFactMem.NotExist_St_Facts[string(asFact.GetPropName())], asFact)
			return ast.NewTrueInferRet(stmt)
		}
	}

	return ast.NewErrInferRet(stmt).AddExtraInfo(fmt.Sprintf("invalid spec fact type: %T", stmt))
}

func (envMgr *EnvMgr) StoreSpecFactInImplyTemplateMem(specFact ast.Spec_OrFact, implyTemplate *ast.InferTemplateStmt) ast.StmtRet {
	return envMgr.CurEnv().KnownFactsStruct.SpecFactInImplyTemplateMem.newFact(specFact, implyTemplate)
}

func (envMgr *EnvMgr) storeTrueEqualInEqualMemNoInfer(fact *ast.PureSpecificFactStmt) ast.InferRet {
	mem := envMgr.CurEnv().EqualMem

	if len(fact.Params) != 2 {
		return ast.NewErrInferRet(fact).AddExtraInfo(fmt.Sprintf("commutative transitive fact expect 2 parameters, get %d in %s", len(fact.Params), fact))
	}

	leftAsStr := fact.Params[0].String()
	rightAsStr := fact.Params[1].String()

	storedEqualLeftFcs, leftGot := mem[leftAsStr]
	storedEqualRightFcs, rightGot := mem[rightAsStr]

	if leftGot && rightGot {
		if storedEqualLeftFcs == storedEqualRightFcs {
			return ast.NewTrueInferRet(fact)
		} else {
			newEqualFcs := []ast.Obj{}
			newEqualFcs = append(newEqualFcs, *storedEqualLeftFcs...)
			newEqualFcs = append(newEqualFcs, *storedEqualRightFcs...)
			*storedEqualLeftFcs = newEqualFcs
			*storedEqualRightFcs = newEqualFcs
			return ast.NewTrueInferRet(fact)
		}
	}

	if leftGot && !rightGot {
		*storedEqualLeftFcs = append(*storedEqualLeftFcs, fact.Params[1])
		mem[rightAsStr] = storedEqualLeftFcs
		return ast.NewTrueInferRet(fact)
	}

	if !leftGot && rightGot {
		*storedEqualRightFcs = append(*storedEqualRightFcs, fact.Params[0])
		mem[leftAsStr] = storedEqualRightFcs
		return ast.NewTrueInferRet(fact)
	}

	if !leftGot && !rightGot {
		newEqualFcs := []ast.Obj{fact.Params[0], fact.Params[1]}
		mem[leftAsStr] = &newEqualFcs
		mem[rightAsStr] = &newEqualFcs
		return ast.NewTrueInferRet(fact)
	}

	return ast.NewTrueInferRet(fact)
}

func (envMgr *EnvMgr) StoreTrueEqualValues(key, value ast.Obj) {
	// 如果已经知道它的值了，那不能存了；否则比如我在外部环境里知道了a = 3，内部环境在反证法证明 a != 1，那我 a = 1就把a = 3覆盖掉了，a = 3这个取值貌似就不work了。某种程度上就是弄了个const
	if v := envMgr.GetSymbolSimplifiedValue(key); v != nil {
		return
	}
	envMgr.CurEnv().SymbolSimplifiedValueMem[key.String()] = value
}

func (envMgr *EnvMgr) storeSymbolSimplifiedValue(left, right ast.Obj) ast.InferRet {
	_, newLeft := envMgr.GetStoredSymbolValue(left)
	if cmp.IsNumExprLitObj(newLeft) {
		simplifiedNewLeft := cmp.IsNumExprObjThenSimplify(newLeft)
		envMgr.StoreTrueEqualValues(right, simplifiedNewLeft)
	}

	_, newRight := envMgr.GetStoredSymbolValue(right)
	if cmp.IsNumExprLitObj(newRight) {
		simplifiedNewRight := cmp.IsNumExprObjThenSimplify(newRight)
		envMgr.StoreTrueEqualValues(left, simplifiedNewRight)
	}

	return ast.NewTrueInferRet(ast.EqualFact(left, right))
}

func (envMgr *EnvMgr) GetEqualObjs(obj ast.Obj) (*[]ast.Obj, bool) {
	objAsStr := obj.String()
	facts, ok := envMgr.CurEnv().EqualMem[objAsStr]
	if ok {
		return facts, ok
	}

	// Search in builtin env
	facts, ok = BuiltinEnvMgrWithEmptyEnvPkgMgr.EnvSlice[0].EqualMem[objAsStr]
	return facts, ok
}

func (envMgr *EnvMgr) FnObjHeadIsAtomAndIsFnSet(fnObj *ast.FnObj) bool {
	if asAtom, ok := fnObj.FnHead.(ast.Atom); ok {
		_, ok := envMgr.AllDefinedFnSetNames[string(asAtom)]
		return ok
	}

	return false
}

func (envMgr *EnvMgr) GetEnvMgrOfPkgName(pkgName string) *EnvMgr {
	path, ok := envMgr.EnvPkgMgr.PkgMgr.NameAbsPathMap[pkgName]
	if !ok {
		return nil
	}

	return envMgr.EnvPkgMgr.AbsPkgPathEnvMgrMap[path]
}

var BuiltinEnvMgrWithEmptyEnvPkgMgr *EnvMgr = nil

func (envMgr *EnvMgr) MakeExistFactStructDoesNotConflictWithDefinedNames(existFactStruct *ast.ExistSpecificFactStmt, definedParams []string) (*ast.ExistSpecificFactStmt, error) {
	uniMap := map[string]struct{}{}
	for _, param := range definedParams {
		uniMap[param] = struct{}{}
	}

	defined := false
	for _, existParam := range existFactStruct.ExistFreeParams {
		if envMgr.lookupAtomObjName(ast.Atom(existParam), uniMap).IsTrue() {
			defined = true
			break
		}
	}

	if !defined {
		return existFactStruct, nil
	}

	// 生产一个不冲突的exist fact struct
	newExistParams := make([]string, len(existFactStruct.ExistFreeParams))
	for i := range existFactStruct.ExistFreeParams {
		newExistParams[i] = envMgr.GenerateUnusedRandomNameWhichIsAlsoNotInGivenMap(uniMap)
	}

	// // 把 set 也换成不冲突的
	uniMap2 := map[string]ast.Obj{}
	newExistParamSets := make([]ast.Obj, len(existFactStruct.ExistFreeParamSets))
	for i, paramSet := range existFactStruct.ExistFreeParamSets {
		newParamSet, err := paramSet.Instantiate(uniMap2)
		if err != nil {
			return nil, err
		}
		newExistParamSets[i] = newParamSet
		uniMap2[existFactStruct.ExistFreeParams[i]] = ast.Atom(newExistParams[i])
	}

	newParams := make([]ast.Obj, len(existFactStruct.PureFact.Params))
	for i, param := range existFactStruct.PureFact.Params {
		newParam, err := param.Instantiate(uniMap2)
		if err != nil {
			return nil, err
		}
		newParams[i] = newParam
	}

	return ast.NewExistSpecificFactStmt(existFactStruct.IsTrue, newExistParams, newExistParamSets, ast.NewPureSpecificFactStmt(existFactStruct.PureFact.IsTrue, existFactStruct.PureFact.PropName, newParams, existFactStruct.Line), existFactStruct.Line), nil
}

// storeSpecFactInMemAndCollect collects the fact string for derived facts tracking
func (ie *InferEngine) storeSpecFactInMemAndCollect(fact ast.SpecificFactStmt, derivedFacts *[]string) ast.ShortRet {
	ret := ie.EnvMgr.storeSpecFactInMem(fact)
	if ret.IsErr() {
		return ast.NewErrShortRetWithMsg(fmt.Sprintf("failed to store spec fact %s", fact.String()))
	}
	*derivedFacts = append(*derivedFacts, fact.String())
	return ast.NewTrueShortRet()
}

func (envMgr *EnvMgr) AnonymousFnToInstFnTemplate(objFnTypeT *ast.FnObj) (*ast.AnonymousFn, bool) {
	ok, paramSets, retSet := objFnTypeT.GetParamSetsAndRetSetOfAnonymousFn(objFnTypeT)
	if !ok {
		return nil, false
	}

	randomParams := []string{}
	for range len(paramSets) {
		randomParams = append(randomParams, envMgr.GenerateUnusedRandomName())
	}

	return ast.NewFnTStruct(randomParams, paramSets, retSet, []ast.FactStmt{}, []ast.FactStmt{}, glob.BuiltinLine0), true
}

func (envMgr *EnvMgr) GetUniFactFactFreeParamsNotConflictWithDefinedParams(fact *ast.UniFactStmt, extraNamesThatCanNotBeUsed map[string]struct{}) *ast.UniFactStmt {
	uniMap := map[string]ast.Obj{}
	newFreeParams := []string{}
	moreUnAvailableParams := map[string]struct{}{}

	updated := false

	for _, freeParam := range fact.Params {
		if envMgr.IsNameUnavailable(freeParam, moreUnAvailableParams) {
			noConflictedParam := envMgr.GenerateUnusedRandomNameWhichIsAlsoNotInGivenMap(extraNamesThatCanNotBeUsed)
			newFreeParams = append(newFreeParams, noConflictedParam)
			moreUnAvailableParams[noConflictedParam] = struct{}{}
			uniMap[freeParam] = ast.Atom(noConflictedParam)
		} else {
			newFreeParams = append(newFreeParams, freeParam)
			moreUnAvailableParams[freeParam] = struct{}{}
		}
	}

	if !updated {
		return fact
	} else {
		curUniMap := map[string]ast.Obj{}
		newParamSets := []ast.Obj{}
		for i, freeParam := range fact.Params {
			paramSet, _ := fact.ParamSets[i].Instantiate(curUniMap)
			newParamSets = append(newParamSets, paramSet)
			if freeParamNewParam, ok := uniMap[freeParam]; ok {
				curUniMap[freeParam] = freeParamNewParam
			}
		}
		newDomFacts, _ := fact.DomFacts.InstantiateFact(uniMap)
		newThenFacts, _ := fact.ThenFacts.InstantiateFact(uniMap)

		return ast.NewUniFact(newFreeParams, newParamSets, newDomFacts, newThenFacts, glob.BuiltinLine0)
	}
}
