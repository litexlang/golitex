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
	ast "golitex/ast"
	env "golitex/environment"
)

func (ver *Verifier) matchUniFactParamsWithSpecFactParams(knownSpecFactInUniFact *env.KnownSpecFact_InUniFact, specFact *ast.SpecFactStmt) (bool, error) {
	_ = knownSpecFactInUniFact
	_ = specFact

	return false, nil
}

type fcPair struct {
	knownFc ast.Fc
	givenFc ast.Fc
}

// return map{freeVar: instVar}, unMatched fcPairs, matched?, err
func (ver *Verifier) matchFcInKnownSpecFactAndGivenFc(knownFc ast.Fc, givenFc ast.Fc, freeVars map[string]struct{}) (map[string][]ast.Fc, []fcPair, error) {
	switch asKnownFc := knownFc.(type) {
	case ast.FcAtom:
		if _, ok := freeVars[string(asKnownFc)]; ok {
			retMap := map[string][]ast.Fc{
				string(asKnownFc): {givenFc},
			}
			return retMap, []fcPair{}, nil
		} else {
			ok, err := ver.VerFactStmt(ast.NewEqualFact(knownFc, givenFc), FinalRoundNoMsg)
			if err != nil {
				return nil, []fcPair{}, err
			}
			if !ok {
				return nil, []fcPair{fcPair{knownFc: knownFc, givenFc: givenFc}}, nil
			}
			return nil, []fcPair{}, nil
		}
	case *ast.FcFn:
		switch asGivenFc := givenFc.(type) {
		case ast.FcAtom:
			return nil, []fcPair{fcPair{knownFc: knownFc, givenFc: givenFc}}, nil
		case *ast.FcFn:
			retMap := map[string][]ast.Fc{}
			retFcPairs := []fcPair{}

			if len(asKnownFc.Params) != len(asGivenFc.Params) {
				return nil, []fcPair{fcPair{knownFc: knownFc, givenFc: givenFc}}, nil
			}

			headMatchedMap, headMatchedFcPairs, err := ver.matchFcInKnownSpecFactAndGivenFc(asKnownFc.FnHead, asGivenFc.FnHead, freeVars)
			if err != nil {
				return nil, []fcPair{}, err
			}
			retMap, retFcPairs = ver.mergeSingleMatchedMapAndUnMatchedFcPairs(headMatchedMap, headMatchedFcPairs, retMap, retFcPairs)

			paramsMatchedMap, paramsMatchedFcPairs, err := ver.matchFcsInKnownSpecFactAndGivenFc(asKnownFc.Params, asGivenFc.Params, freeVars)
			if err != nil {
				return nil, []fcPair{}, err
			}
			retMap, retFcPairs = ver.mergeMultipleMatchedMapAndUnMatchedFcPairs(paramsMatchedMap, paramsMatchedFcPairs, retMap, retFcPairs)
			return retMap, retFcPairs, nil
		}
	}

	return nil, []fcPair{}, nil
}

func (ver *Verifier) matchFcsInKnownSpecFactAndGivenFc(knownFcs []ast.Fc, givenFcs []ast.Fc, freeVars map[string]struct{}) ([]map[string][]ast.Fc, [][]fcPair, error) {
	matchedMaps := []map[string][]ast.Fc{}
	unmatchedFcPairs := [][]fcPair{}
	for i := range knownFcs {
		matchedMap, matchedFcPairs, err := ver.matchFcInKnownSpecFactAndGivenFc(knownFcs[i], givenFcs[i], freeVars)
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
