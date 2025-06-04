// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Contact the development team: <litexlang@outlook.com>
// Visit litexlang.org and https://github.com/litexlang/golitex for more info.

package litex_verifier

import (
	ast "golitex/ast"
	cmp "golitex/cmp"
	env "golitex/environment"
	glob "golitex/glob"
	"strings"
)

// REMARK: 2025.6.4 这个文件很本质，需要未来检查一下里面逻辑有没有问题

// match 函数不需要传入state: 没有any, spec 之分，也不需要打印
func (ver *Verifier) matchStoredUniSpecWithSpec_preventDifferentVarsMatchTheSameFreeVar(knownFact env.KnownSpecFact_InUniSpecFact, stmt *ast.SpecFactStmt) (map[string][]ast.Fc, bool, error) { // 之所以是map[string][]ast.Fc而不是 map[string]ast.Fc, 因为可能用户输入的是字面量相同，实际意义一样的obj
	if len(stmt.Params) != len(knownFact.SpecFact.Params) {
		return nil, false, nil
	}

	retMap := map[string][]ast.Fc{}

	for i, uniParam := range knownFact.SpecFact.Params {
		// matchMap, matched, err := ver.match_FcInFactUnderUniFact_WithConFc(uniParam, stmt.Params[i], knownFact.UniFact.Params)
		matchMap, matched, err := ver.match_FcInFactUnderUniFact_WithConFc(uniParam, stmt.Params[i])
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

// paramInFactUnderUniFact 可能是自由的，可能是固定的，反正它来自一个forall下面的某个specFact
func (ver *Verifier) match_FcInFactUnderUniFact_WithConFc(fcInFactUnderUniFact ast.Fc, conFc ast.Fc) (map[string][]ast.Fc, bool, error) {
	if leftAsAtom, ok := fcInFactUnderUniFact.(*ast.FcAtom); ok {
		if strings.HasPrefix(leftAsAtom.Name, glob.UniParamPrefix) {
			return map[string][]ast.Fc{leftAsAtom.Name: {conFc}}, true, nil
		} else {
			ok, err := cmp.BuiltinFcEqualRule(fcInFactUnderUniFact, conFc)
			if err != nil {
				return nil, false, err
			}
			if ok {
				return make(map[string][]ast.Fc), true, nil
			}

			return ver.match_FcAtomInFactUnderUniFact_ConFc(leftAsAtom, conFc)
		}
	} else {
		return ver.match_FcFnInFactUnderUniFact_ConFc(fcInFactUnderUniFact.(*ast.FcFn), conFc)
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
	// case *ast.FcAtom:
	// 	// return ver.match_FcAtomInFactUnderUniFact_ConFc(param, conFc, uniFactUniParams)
	// 	return ver.match_FcAtomInFactUnderUniFact_ConFc(param, conFc)
	// case *ast.FcFn:
	// 	// return ver.match_FcFnInFactUnderUniFact_ConFc(param, conFc, uniFactUniParams)
	// 	return ver.match_FcFnInFactUnderUniFact_ConFc(param, conFc)
	// default:
	// 	return nil, false, fmt.Errorf("unexpected type %T for parameter %v", param, fcInFactUnderUniFact.String())
	// }
}

// func (ver *Verifier) match_FcAtomInFactUnderUniFact_ConFc(fcAtomInFactUnderUniFact *ast.FcAtom, conFc ast.Fc, uniParams []string) (map[string][]ast.Fc, bool, error) {
func (ver *Verifier) match_FcAtomInFactUnderUniFact_ConFc(fcAtomInFactUnderUniFact *ast.FcAtom, conFc ast.Fc) (map[string][]ast.Fc, bool, error) {
	retMap := make(map[string][]ast.Fc)

	// 不利用查prefix的方式来确定涉及到的param是不是 uni
	// if matchStr, ok := isUniParam(fcAtomInFactUnderUniFact, uniParams); ok {
	// 	retMap[matchStr] = []ast.Fc{conFc}
	// 	return retMap, true, nil
	// }

	// 利用查prefix的方式来确定涉及到的param是不是 uni
	if uniParamStr, ok := fcAtomInFactUnderUniFact.NameIsUniParam_PkgNameEmpty(); ok {
		retMap[uniParamStr] = []ast.Fc{conFc}
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
func (ver *Verifier) match_FcFnInFactUnderUniFact_ConFc(fcFnUnFactUnderUniFact *ast.FcFn, conFc ast.Fc) (map[string][]ast.Fc, bool, error) {
	retMap := map[string][]ast.Fc{}

	conParamAsFcFn, ok := conFc.(*ast.FcFn)
	if !ok {
		return nil, false, nil
	}

	// match head
	// matchMap, ok, err := ver.match_FcInFactUnderUniFact_WithConFc(fcFnUnFactUnderUniFact.FnHead, conParamAsFcFn.FnHead, uniParams)
	matchMap, ok, err := ver.match_FcInFactUnderUniFact_WithConFc(fcFnUnFactUnderUniFact.FnHead, conParamAsFcFn.FnHead)
	if err != nil {
		return nil, false, err
	}
	if !ok {
		return nil, false, nil
	}
	mergeMatchMaps(matchMap, retMap)

	if len(conParamAsFcFn.ParamSegs) != len(fcFnUnFactUnderUniFact.ParamSegs) {
		return nil, false, nil //? 不清楚应该报错还是说直接返回不对，应该是返回不对
	}

	for i, uniPipe := range fcFnUnFactUnderUniFact.ParamSegs {
		// matchMap, ok, err := ver.match_FcInFactUnderUniFact_WithConFc(param, conParamAsFcFn.ParamSegs[i][j], uniParams)
		matchMap, ok, err := ver.match_FcInFactUnderUniFact_WithConFc(uniPipe, conParamAsFcFn.ParamSegs[i])
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
