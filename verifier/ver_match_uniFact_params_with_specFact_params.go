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
	env "golitex/environment"
)

func (ver *Verifier) matchUniFactParamsWithSpecFactParams(knownSpecFactInUniFact *env.KnownSpecFact_InUniFact, specFact *ast.SpecFactStmt) (bool, map[string]ast.Fc, error) {
	knownFcs := knownSpecFactInUniFact.SpecFact.Params
	givenFcs := specFact.Params
	freeVars := knownSpecFactInUniFact.UniFact.Params
	freeVarsMap := map[string]struct{}{}
	for _, freeVar := range freeVars {
		freeVarsMap[freeVar] = struct{}{}
	}

	matchedMaps, unmatchedFcPairs, err := ver.matchFcsInKnownSpecFactAndGivenFc(knownFcs, givenFcs, freeVarsMap, string(specFact.PropName))
	if err != nil {
		return false, nil, err
	}
	matchedMap, unMatchedFcPairs := ver.mergeMultipleMatchedMapAndUnMatchedFcPairs(matchedMaps, unmatchedFcPairs, map[string][]ast.Fc{}, []fcPair{})

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
			ok, err := ver.verTrueEqualFact(ast.NewEqualFact(firstVar, instVars[j]), FinalRoundNoMsg, false)
			if err != nil {
				return false, nil, err
			}
			if !ok {
				return false, nil, nil
			}
		}
	}

	freeVarToInstVar := map[string]ast.Fc{}
	for freeVar, instVars := range matchedMap {
		freeVarToInstVar[freeVar] = instVars[0]
	}

	// 把实例化了的没被匹配的fcPair拿出来，检查是否是equal
	for _, fcPair := range unMatchedFcPairs {
		instKnownFreeVar, err := fcPair.knownFc.Instantiate(freeVarToInstVar)
		if err != nil {
			return false, nil, err
		}
		ok, err := ver.verTrueEqualFact(ast.NewEqualFact(instKnownFreeVar, fcPair.givenFc), FinalRoundNoMsg, false)
		if err != nil {
			return false, nil, err
		}
		if !ok {
			return false, nil, nil
		}
	}

	return true, freeVarToInstVar, nil
}

type fcPair struct {
	knownFc ast.Fc
	givenFc ast.Fc
}

// return map{freeVar: instVar}, unMatched fcPairs, matched?, err
func (ver *Verifier) matchFcInKnownSpecFactAndGivenFc(knownFc ast.Fc, givenFc ast.Fc, freeVars map[string]struct{}, specFactName string) (map[string][]ast.Fc, []fcPair, error) {
	switch asKnownFc := knownFc.(type) {
	case ast.FcAtom:
		if _, ok := freeVars[string(asKnownFc)]; ok {
			retMap := map[string][]ast.Fc{
				string(asKnownFc): {givenFc},
			}
			return retMap, []fcPair{}, nil
		} else {
			ok, err := ver.verTrueEqualFact(ast.NewEqualFact(knownFc, givenFc), FinalRoundNoMsg, false)
			if err != nil {
				return nil, []fcPair{}, err
			}
			if !ok {
				return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
			}
			return nil, []fcPair{}, nil
		}
	case *ast.FcFn:
		switch asGivenFc := givenFc.(type) {
		case ast.FcAtom:
			return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
		case *ast.FcFn:
			retMap := map[string][]ast.Fc{}
			retFcPairs := []fcPair{}

			if len(asKnownFc.Params) != len(asGivenFc.Params) {
				return nil, []fcPair{{knownFc: knownFc, givenFc: givenFc}}, nil
			}

			headMatchedMap, headMatchedFcPairs, err := ver.matchFcInKnownSpecFactAndGivenFc(asKnownFc.FnHead, asGivenFc.FnHead, freeVars, specFactName)
			if err != nil {
				return nil, []fcPair{}, err
			}
			retMap, retFcPairs = ver.mergeSingleMatchedMapAndUnMatchedFcPairs(headMatchedMap, headMatchedFcPairs, retMap, retFcPairs)

			paramsMatchedMap, paramsMatchedFcPairs, err := ver.matchFcsInKnownSpecFactAndGivenFc(asKnownFc.Params, asGivenFc.Params, freeVars, specFactName)
			if err != nil {
				return nil, []fcPair{}, err
			}
			retMap, retFcPairs = ver.mergeMultipleMatchedMapAndUnMatchedFcPairs(paramsMatchedMap, paramsMatchedFcPairs, retMap, retFcPairs)
			return retMap, retFcPairs, nil
		}
	}

	return nil, []fcPair{}, nil
}

func (ver *Verifier) matchFcsInKnownSpecFactAndGivenFc(knownFcs []ast.Fc, givenFcs []ast.Fc, freeVars map[string]struct{}, specFactName string) ([]map[string][]ast.Fc, [][]fcPair, error) {
	if len(knownFcs) != len(givenFcs) {
		return nil, [][]fcPair{}, fmt.Errorf("required parameters number of fact %s is %d, get %d", specFactName, len(knownFcs), len(givenFcs))
	}

	matchedMaps := []map[string][]ast.Fc{}
	unmatchedFcPairs := [][]fcPair{}
	for i := range knownFcs {
		matchedMap, matchedFcPairs, err := ver.matchFcInKnownSpecFactAndGivenFc(knownFcs[i], givenFcs[i], freeVars, specFactName)
		if err != nil {
			return nil, [][]fcPair{}, err
		}
		matchedMaps = append(matchedMaps, matchedMap)
		unmatchedFcPairs = append(unmatchedFcPairs, matchedFcPairs)
	}
	return matchedMaps, unmatchedFcPairs, nil
}

func (ver *Verifier) mergeMultipleMatchedMapAndUnMatchedFcPairs(matchedMaps []map[string][]ast.Fc, matchedFcPairs [][]fcPair, putTo map[string][]ast.Fc, putToFcPairs []fcPair) (map[string][]ast.Fc, []fcPair) {
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

func (ver *Verifier) mergeSingleMatchedMapAndUnMatchedFcPairs(matchedMap map[string][]ast.Fc, matchedFcPairs []fcPair, putTo map[string][]ast.Fc, putToFcPairs []fcPair) (map[string][]ast.Fc, []fcPair) {
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
