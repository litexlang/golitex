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
)

// func (ver *Verifier) matchUniFactParamsWithSpecFactParams(knownSpecFactInUniFact *env.KnownSpecFact_InUniFact, specFact *ast.SpecFactStmt) (bool, map[string]ast.Obj, error) {
func (ver *Verifier) matchUniFactParamsWithSpecFactParams(knownFcs []ast.Obj, freeVars []string, specFact *ast.SpecFactStmt) (bool, map[string]ast.Obj, error) {
	// knownFcs := knownSpecFactInUniFact.SpecFact.Params
	givenFcs := specFact.Params
	// freeVars := knownSpecFactInUniFact.UniFact.Params
	freeVarsMap := map[string]struct{}{}
	for _, freeVar := range freeVars {
		freeVarsMap[freeVar] = struct{}{}
	}

	matchedMaps, unmatchedFcPairs, err := ver.matchFcsInKnownSpecFactAndGivenFc_ReturnSliceOfFreeParamFcMapAndSliceOfUnmatchedFcPairs(knownFcs, givenFcs, freeVarsMap, string(specFact.PropName))
	if err != nil {
		return false, nil, err
	}
	matchedMap, unMatchedFcPairs := ver.mergeMultipleMatchedMapAndUnMatchedFcPairs(matchedMaps, unmatchedFcPairs, map[string][]ast.Obj{}, []fcPair{})

	// 所有的自由变量必须被匹配到了
	for freeVar := range freeVarsMap {
		if _, ok := matchedMap[freeVar]; !ok {
			return false, nil, nil // 有freeVar没有匹配到，说明specFact的参数和uniFact的参数不匹配
		}
	}

	// 所有自由变量对应的instVar必须相等
	for _, instVars := range matchedMap {
		firstVar := instVars[0]
		for j := 1; j < len(instVars); j++ {
			verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewEqualFact(firstVar, instVars[j]), FinalRoundNoMsg().CopyAndReqOkToTrue())
			if verRet.IsErr() {
				return false, nil, err
			}
			if verRet.IsUnknown() {
				return false, nil, nil
			}
		}
	}

	freeVarToInstVar := map[string]ast.Obj{}
	for freeVar, instVars := range matchedMap {
		freeVarToInstVar[freeVar] = instVars[0]
	}

	// 把实例化了的没被匹配的fcPair拿出来，检查是否是equal
	for _, fcPair := range unMatchedFcPairs {
		instKnownFreeVar, err := fcPair.knownFc.Instantiate(freeVarToInstVar)
		if err != nil {
			return false, nil, err
		}
		verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewEqualFact(instKnownFreeVar, fcPair.givenFc), FinalRoundNoMsg().CopyAndReqOkToTrue())

		// REMARK
		// 注：这里err != nil 也是返回 false, 因为有可能会把 sqrt(x) ^ 2 = x 拿来证明 y = z，但是 匹配的时候，可能会导致 x 是 -1 之类的。如果error了，其实就是说明没证明通过
		if verRet.IsErr() || verRet.IsUnknown() {
			return false, nil, nil
		}
	}

	return true, freeVarToInstVar, nil
}

type fcPair struct {
	knownFc ast.Obj
	givenFc ast.Obj
}

// 非常重要的函数
// 返回：freeParam和给定obj的map，没有对应上的所有fc对构成的列表
func (ver *Verifier) matchFcInSpecFactInKnownForallFactAndGivenFc_ReturnFreeParamFcMapAndUnmatchedFcPairs(knownFc ast.Obj, givenFc ast.Obj, freeVars map[string]struct{}, specFactName string) (map[string][]ast.Obj, []fcPair, error) {
	switch asKnownFc := knownFc.(type) {
	case ast.Atom:
		if _, ok := freeVars[string(asKnownFc)]; ok {
			retMap := map[string][]ast.Obj{
				string(asKnownFc): {givenFc},
			}
			return retMap, []fcPair{}, nil
		} else {
			verRet := ver.verTrueEqualFactAndCheckFnReq(ast.NewEqualFact(knownFc, givenFc), FinalRoundNoMsg().CopyAndReqOkToTrue())
			if verRet.IsErr() {
				return nil, []fcPair{}, fmt.Errorf(verRet.String())
			}
			if verRet.IsUnknown() {
				return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
			}
			return nil, []fcPair{}, nil
		}
	case *ast.FnObj:
		switch asGivenFc := givenFc.(type) {
		case ast.Atom:
			return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
		case *ast.FnObj:
			if ast.IsSetBuilder(asKnownFc) && ast.IsSetBuilder(asGivenFc) {
				return ver.matchFcsByTheyAreAllSetBuilders(asKnownFc, asGivenFc, freeVars, specFactName)
			}

			retMap := map[string][]ast.Obj{}
			retFcPairs := []fcPair{}

			if len(asKnownFc.Params) != len(asGivenFc.Params) {
				return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
			}

			headMatchedMap, headMatchedFcPairs, err := ver.matchFcInSpecFactInKnownForallFactAndGivenFc_ReturnFreeParamFcMapAndUnmatchedFcPairs(asKnownFc.FnHead, asGivenFc.FnHead, freeVars, specFactName)
			if err != nil {
				return nil, []fcPair{}, err
			}
			retMap, retFcPairs = ver.mergeSingleMatchedMapAndUnMatchedFcPairs(headMatchedMap, headMatchedFcPairs, retMap, retFcPairs)

			paramsMatchedMap, paramsMatchedFcPairs, err := ver.matchFcsInKnownSpecFactAndGivenFc_ReturnSliceOfFreeParamFcMapAndSliceOfUnmatchedFcPairs(asKnownFc.Params, asGivenFc.Params, freeVars, specFactName)
			if err != nil {
				return nil, []fcPair{}, err
			}
			retMap, retFcPairs = ver.mergeMultipleMatchedMapAndUnMatchedFcPairs(paramsMatchedMap, paramsMatchedFcPairs, retMap, retFcPairs)

			return retMap, retFcPairs, nil
		}
	}

	return nil, []fcPair{}, nil
}

// 非常重要：返回uniFact下面的某个specFact里的所有的param推出来的 free param 和 给定obj的对应关系，以及所有的没有匹配上的fc的pair们组成的slice
func (ver *Verifier) matchFcsInKnownSpecFactAndGivenFc_ReturnSliceOfFreeParamFcMapAndSliceOfUnmatchedFcPairs(knownFcs []ast.Obj, givenFcs []ast.Obj, freeVars map[string]struct{}, specFactName string) ([]map[string][]ast.Obj, [][]fcPair, error) {
	if len(knownFcs) != len(givenFcs) {
		return nil, [][]fcPair{}, fmt.Errorf("required parameters number of fact %s is %d, get %d", specFactName, len(knownFcs), len(givenFcs))
	}

	matchedMaps := []map[string][]ast.Obj{}
	unmatchedFcPairs := [][]fcPair{}
	for i := range knownFcs {
		freeParamToConcreteObjMatchedMap, unmatchedFcPair, err := ver.matchFcInSpecFactInKnownForallFactAndGivenFc_ReturnFreeParamFcMapAndUnmatchedFcPairs(knownFcs[i], givenFcs[i], freeVars, specFactName)
		if err != nil {
			return nil, [][]fcPair{}, err
		}
		matchedMaps = append(matchedMaps, freeParamToConcreteObjMatchedMap)
		unmatchedFcPairs = append(unmatchedFcPairs, unmatchedFcPair)
	}
	return matchedMaps, unmatchedFcPairs, nil
}

func (ver *Verifier) mergeMultipleMatchedMapAndUnMatchedFcPairs(matchedMaps []map[string][]ast.Obj, matchedFcPairs [][]fcPair, putTo map[string][]ast.Obj, putToFcPairs []fcPair) (map[string][]ast.Obj, []fcPair) {
	for _, matchedMap := range matchedMaps {
		for freeVar, instVars := range matchedMap {
			if _, ok := putTo[freeVar]; ok {
				putTo[freeVar] = append(putTo[freeVar], instVars...)
			} else {
				putTo[freeVar] = instVars
			}
		}
	}
	for _, matchedFcPairs := range matchedFcPairs {
		putToFcPairs = append(putToFcPairs, matchedFcPairs...)
	}
	return putTo, putToFcPairs
}

func (ver *Verifier) mergeSingleMatchedMapAndUnMatchedFcPairs(matchedMap map[string][]ast.Obj, matchedFcPairs []fcPair, putTo map[string][]ast.Obj, putToFcPairs []fcPair) (map[string][]ast.Obj, []fcPair) {
	for freeVar, instVars := range matchedMap {
		if _, ok := putTo[freeVar]; ok {
			putTo[freeVar] = append(putTo[freeVar], instVars...)
		} else {
			putTo[freeVar] = instVars
		}
	}
	putToFcPairs = append(putToFcPairs, matchedFcPairs...)
	return putTo, putToFcPairs
}

func (ver *Verifier) matchFcsByTheyAreAllSetBuilders(knownFc *ast.FnObj, givenFc *ast.FnObj, freeVars map[string]struct{}, specFactName string) (map[string][]ast.Obj, []fcPair, error) {
	// Normalize both set builders by instantiating their bound param with the same fresh atom,
	// then verify their definitions align (same parent set and facts). All involved facts must be the same.
	var instKnownStruct, instGivenStruct *ast.SetBuilderStruct

	knownStruct, err := knownFc.ToSetBuilderStruct()
	if err != nil {
		return nil, []fcPair{}, err
	}
	givenStruct, err := givenFc.ToSetBuilderStruct()
	if err != nil {
		return nil, []fcPair{}, err
	}

	// 对应 两个 set builder obj 里的 fact。二者涉及到的specFact但凡有一个名字没对上，那我们就认为这两个obj完全不一样
	if len(knownStruct.Facts) != len(givenStruct.Facts) {
		return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
	}

	for i := range knownStruct.Facts {
		kf := knownStruct.Facts[i]
		gf := givenStruct.Facts[i]

		if kf.PropName.String() != gf.PropName.String() {
			return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
		}

		if len(kf.Params) != len(gf.Params) {
			return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
		}
	}

	// set builder 里的参数不一样，不一定代表不同的set builder
	if knownFc.Params[0].String() != givenFc.Params[1].String() {
		randomParam := ver.Env.GenerateUndeclaredRandomName()

		instKnownStruct, err = knownStruct.ReplaceParamWithNewParam(randomParam)
		if err != nil {
			return nil, []fcPair{}, err
		}
		instGivenStruct, err = givenStruct.ReplaceParamWithNewParam(randomParam)
		if err != nil {
			return nil, []fcPair{}, err
		}

	} else {
		instKnownStruct = knownStruct
		instGivenStruct = givenStruct
	}

	parentSetMatchedMap, parentSetMatchedFcPairs, err := ver.matchFcInSpecFactInKnownForallFactAndGivenFc_ReturnFreeParamFcMapAndUnmatchedFcPairs(instKnownStruct.ParentSet, instGivenStruct.ParentSet, freeVars, specFactName)
	if err != nil {
		return nil, []fcPair{}, err
	}

	// 把 parent 里得到的 freeVar 和 obj 的对应关系；以及从facts里得到的对应关系，返回
	retMap := map[string][]ast.Obj{}
	for freeVar, instVars := range parentSetMatchedMap {
		if retMap[freeVar] == nil {
			retMap[freeVar] = append([]ast.Obj{}, instVars...)
		} else {
			retMap[freeVar] = append(retMap[freeVar], instVars...)
		}
	}

	// 对应 parent 和 facts 的时候，但凡有一个地方没对应上，我们就认为这两个obj完全不一样
	if len(parentSetMatchedFcPairs) > 0 {
		return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
	}

	for i := range instKnownStruct.Facts {
		freeParamObjMatchMap, unMatchedFcPairs, err := ver.matchFcsInKnownSpecFactAndGivenFc_ReturnSliceOfFreeParamFcMapAndSliceOfUnmatchedFcPairs(instKnownStruct.Facts[i].Params, instGivenStruct.Facts[i].Params, freeVars, specFactName)
		if err != nil {
			return nil, []fcPair{}, err
		}

		for _, factMatchedMap := range unMatchedFcPairs {
			if len(factMatchedMap) > 0 {
				return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
			}
		}

		for _, factMatchedMap := range freeParamObjMatchMap {
			for freeVar, instVars := range factMatchedMap {
				if retMap[freeVar] == nil {
					retMap[freeVar] = append([]ast.Obj{}, instVars...)
				} else {
					retMap[freeVar] = append(retMap[freeVar], instVars...)
				}
			}
		}

	}

	return retMap, []fcPair{}, nil
}
