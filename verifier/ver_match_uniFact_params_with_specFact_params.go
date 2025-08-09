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
func (ver *Verifier) matchFcInKnownSpecFactAndGivenFc(knownFc ast.Fc, givenFc ast.Fc, freeVars map[string]struct{}) (map[string]ast.Fc, []fcPair, bool, error) {
	switch asKnownFc := knownFc.(type) {
	case ast.FcAtom:
		if _, ok := freeVars[string(asKnownFc)]; ok {
			retMap := map[string]ast.Fc{
				string(asKnownFc): givenFc,
			}
			return retMap, []fcPair{}, true, nil
		} else {
			ok, err := ver.VerFactStmt(ast.NewEqualFact(knownFc, givenFc), FinalRoundNoMsg)
			if err != nil {
				return nil, []fcPair{}, false, err
			}
			if !ok {
				return nil, []fcPair{fcPair{knownFc: knownFc, givenFc: givenFc}}, false, nil
			}
			return nil, []fcPair{}, true, nil
		}
	case *ast.FcFn:
		switch asGivenFc := givenFc.(type) {
		case ast.FcAtom:
			return nil, []fcPair{fcPair{knownFc: knownFc, givenFc: givenFc}}, false, nil
		case *ast.FcFn:
			retMap := map[string]ast.Fc{}
			headMatchedMap, headMatchedFcPairs, headMatched, err := ver.matchFcInKnownSpecFactAndGivenFc(asKnownFc.FnHead, asGivenFc.FnHead, freeVars)
			if err != nil {
				return nil, []fcPair{}, false, err
			}
			panic("")
		}
	}

	return false, nil
}
