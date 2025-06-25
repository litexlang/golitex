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
	cmp "golitex/cmp"
	env "golitex/environment"
)

// REMARK: 2025.6.4 这个文件很本质，需要未来检查一下里面逻辑有没有问题

// match 函数不需要传入state: 没有any, spec 之分，也不需要打印
func (ver *Verifier) matchStoredUniSpecWithSpec_preventDifferentVarsMatchTheSameFreeVar(knownFact env.KnownSpecFact_InUniFact, stmt *ast.SpecFactStmt) (map[string][]ast.Fc, bool, error) { // 之所以是map[string][]ast.Fc而不是 map[string]ast.Fc, 因为可能用户输入的是字面量相同，实际意义一样的obj
	if len(stmt.Params) != len(knownFact.SpecFact.Params) {
		return nil, false, nil
	}

	retMap := map[string][]ast.Fc{}

	for i, uniParam := range knownFact.SpecFact.Params {
		// matchMap, matched, err := ver.match_FcInFactUnderUniFact_WithConFc(uniParam, stmt.Params[i], knownFact.UniFact.Params)
		matchMap, matched, err := ver.match_FcInFactUnderUniFact_WithConFc(uniParam, stmt.Params[i], knownFact)
		if err != nil {
			return nil, false, err
		}
		if !matched {
			return nil, false, nil
		}
		mergeMatchMaps(matchMap, retMap)
	}

	return retMap, true, nil
}

func isFcAtomInForallParamSet(fcAtom ast.FcAtom, knownFact env.KnownSpecFact_InUniFact) bool {
	for _, param := range knownFact.UniFact.Params {
		// if fcAtom.PkgName == glob.EmptyPkg && param == fcAtom.Name {
		if param == fcAtom.Name {
			return true
		}
	}
	return false
}

// paramInFactUnderUniFact 可能是自由的，可能是固定的，反正它来自一个forall下面的某个specFact
func (ver *Verifier) match_FcInFactUnderUniFact_WithConFc(fcInFactUnderUniFact ast.Fc, conFc ast.Fc, knownFact env.KnownSpecFact_InUniFact) (map[string][]ast.Fc, bool, error) {
	if leftAsAtom, ok := fcInFactUnderUniFact.(ast.FcAtom); ok {
		if isFcAtomInForallParamSet(leftAsAtom, knownFact) {
			return map[string][]ast.Fc{leftAsAtom.Name: {conFc}}, true, nil
		} else {
			ok, _, err := cmp.Cmp_ByBIR(fcInFactUnderUniFact, conFc)
			if err != nil {
				return nil, false, err
			}
			if ok {
				return make(map[string][]ast.Fc), true, nil
			}

			return ver.match_FcAtomInFactUnderUniFact_ConFc(leftAsAtom, conFc, knownFact)
		}
	} else {
		return ver.match_FcFnInFactUnderUniFact_ConFc(fcInFactUnderUniFact.(*ast.FcFn), conFc, knownFact)
	}

	// 注意到，如果传入的不是fn，而是atom，那大概率是不能match上的。只有一种例外:
	// know forall x A: $p(x *(3-2)); $p(1*1) 这时候 3 -2 要能和1对上。而 uniFunc 的对应关系，只是让自由变量去对应，不包括builtinFc的match
	// 同时，也不能直接去CmpFcRule，因为如果输入的变量的字面量刚好是存着的自由变量的字面量，那恰好相等了，这是不行的。只能是BuiltinFc 之间相等
	// 为了处理这种情况，引入下面这段代码
	// ok, err := cmp.BuiltinFcEqualRule(fcInFactUnderUniFact, conFc)
	// if err != nil {
	// 	return nil, false, err
	// }
	// if ok {
	// 	return make(map[string][]ast.Fc), true, nil
	// }

	// // Safe type switching
	// switch param := fcInFactUnderUniFact.(type) {
	// case ast.FcAtom:
	// 	// return ver.match_FcAtomInFactUnderUniFact_ConFc(param, conFc, uniFactUniParams)
	// 	return ver.match_FcAtomInFactUnderUniFact_ConFc(param, conFc)
	// case *ast.FcFn:
	// 	// return ver.match_FcFnInFactUnderUniFact_ConFc(param, conFc, uniFactUniParams)
	// 	return ver.match_FcFnInFactUnderUniFact_ConFc(param, conFc)
	// default:
	// 	return nil, false, fmt.Errorf("unexpected type %T for parameter %v", param, fcInFactUnderUniFact.String())
	// }
}

// func (ver *Verifier) match_FcAtomInFactUnderUniFact_ConFc(fcAtomInFactUnderUniFact ast.FcAtom, conFc ast.Fc, uniParams []string) (map[string][]ast.Fc, bool, error) {
func (ver *Verifier) match_FcAtomInFactUnderUniFact_ConFc(fcAtomInFactUnderUniFact ast.FcAtom, conFc ast.Fc, knownFact env.KnownSpecFact_InUniFact) (map[string][]ast.Fc, bool, error) {
	retMap := make(map[string][]ast.Fc)

	if isFcAtomInForallParamSet(fcAtomInFactUnderUniFact, knownFact) {
		retMap[fcAtomInFactUnderUniFact.Name] = []ast.Fc{conFc}
		return retMap, true, nil
	}

	// ok, err := ver.iterateOverKnownSpecEqualFactsAndCheck(fcAtomInFactUnderUniFact, conFc)
	// ok, err := ver.makeFcEqualFactAndVerify(fcAtomInFactUnderUniFact, conFc, SpecNoMsg)
	ok, err := ver.fcEqualSpec(fcAtomInFactUnderUniFact, conFc, FinalRoundNoMsg)
	if err != nil {
		return nil, false, err
	}
	if ok {
		return retMap, true, nil
	}

	return nil, false, nil
}

// func (ver *Verifier) match_FcFnInFactUnderUniFact_ConFc(fcFnUnFactUnderUniFact *ast.FcFn, conFc ast.Fc, uniParams []string) (map[string][]ast.Fc, bool, error) {
func (ver *Verifier) match_FcFnInFactUnderUniFact_ConFc(fcFnUnFactUnderUniFact *ast.FcFn, conFc ast.Fc, knownFact env.KnownSpecFact_InUniFact) (map[string][]ast.Fc, bool, error) {
	retMap := map[string][]ast.Fc{}

	conParamAsFcFn, ok := conFc.(*ast.FcFn)
	if !ok {
		return nil, false, nil
	}

	// match head
	// matchMap, ok, err := ver.match_FcInFactUnderUniFact_WithConFc(fcFnUnFactUnderUniFact.FnHead, conParamAsFcFn.FnHead, uniParams)
	matchMap, ok, err := ver.match_FcInFactUnderUniFact_WithConFc(fcFnUnFactUnderUniFact.FnHead, conParamAsFcFn.FnHead, knownFact)
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}
	mergeMatchMaps(matchMap, retMap)

	if len(conParamAsFcFn.Params) != len(fcFnUnFactUnderUniFact.Params) {
		return nil, false, nil //? 不清楚应该报错还是说直接返回不对，应该是返回不对
	}

	for i, uniPipe := range fcFnUnFactUnderUniFact.Params {
		// matchMap, ok, err := ver.match_FcInFactUnderUniFact_WithConFc(param, conParamAsFcFn.ParamSegs[i][j], uniParams)
		matchMap, ok, err := ver.match_FcInFactUnderUniFact_WithConFc(uniPipe, conParamAsFcFn.Params[i], knownFact)
		if err != nil {
			return nil, false, err
		}
		if !ok {
			return nil, false, nil
		}
		mergeMatchMaps(matchMap, retMap)
	}

	return retMap, true, nil
}

func mergeMatchMaps(from map[string][]ast.Fc, to map[string][]ast.Fc) {
	for key, value := range from {
		if _, ok := (to)[key]; ok {
			(to)[key] = append((to)[key], value...)
		} else {
			(to)[key] = value
		}
	}
}
