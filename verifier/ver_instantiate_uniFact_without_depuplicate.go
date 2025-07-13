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

// 在用uniFact来验证specFact时，这个已知的uniFact 可能形如 forall a x: $p(a,x)。然后我代入的x刚好是a。于是整个forall被instantiate成 forall a a: $p(a,a)。然后我要验证这个 forall a a: $p(a,a) 我发现a已经在外面定义go了，于是把它替换成了乱码ABCD, 然后变成验证 forall ABCD ABCD: $p(ABCD,ABCD)。总之就错了。避免这个的办法是，让knownUniFact先把param先随机化啦，然后再代入
func (ver *Verifier) instantiateUniFactWithoutDuplicate(oldStmt *ast.UniFactStmt) (*ast.UniFactStmt, map[string]ast.Fc, error) {
	paramMap, paramMapStrToStr := processUniFactParamsDuplicateDeclared(ver.env, oldStmt.Params)

	return useRandomParamToReplaceOriginalParam(oldStmt, paramMap, paramMapStrToStr)
}

func useRandomParamToReplaceOriginalParam(oldStmt *ast.UniFactStmt, paramMap map[string]ast.Fc, paramMapStrToStr map[string]string) (*ast.UniFactStmt, map[string]ast.Fc, error) {
	if len(paramMap) == 0 {
		return oldStmt, nil, nil
	}

	instantiatedOldStmt, err := ast.InstantiateUniFact(oldStmt, paramMap)
	if err != nil {
		return nil, nil, err
	}

	newParams := []string{}
	for _, param := range oldStmt.Params {
		if newParam, ok := paramMapStrToStr[param]; ok {
			newParams = append(newParams, newParam)
		} else {
			newParams = append(newParams, param)
		}
	}

	newStmtPtr := ast.NewUniFact(newParams, instantiatedOldStmt.ParamSets, instantiatedOldStmt.DomFacts, instantiatedOldStmt.ThenFacts)

	return newStmtPtr, paramMap, nil
}

func processUniFactParamsDuplicateDeclared(env *env.Env, params []string) (map[string]ast.Fc, map[string]string) {
	paramMap := make(map[string]ast.Fc)
	paramMapStrToStr := make(map[string]string)
	for _, param := range params {
		for {
			newParam := param
			if env.IsAtomDeclared(ast.FcAtom(newParam), map[string]struct{}{}) {
				newParam = generateUndeclaredRandomName(env)
				if !env.IsAtomDeclared(ast.FcAtom(newParam), map[string]struct{}{}) {
					paramMap[param] = ast.FcAtom(newParam)
					paramMapStrToStr[param] = newParam
					break
				}
			} else {
				break
			}
		}
	}
	return paramMap, paramMapStrToStr
}

func processUniFactParamsDuplicateDeclared_notInGivenMap(env *env.Env, params []string, notInMap map[string]string) (map[string]ast.Fc, map[string]string) {
	paramMap := make(map[string]ast.Fc)
	paramMapStrToStr := make(map[string]string)
	for _, param := range params {
		for {
			newParam := param
			_, inNotOnMap := notInMap[newParam]
			if env.IsAtomDeclared(ast.FcAtom(newParam), map[string]struct{}{}) || inNotOnMap {
				newParam = generateUndeclaredRandomName(env)

				_, inNotOnMap = notInMap[newParam]
				if !env.IsAtomDeclared(ast.FcAtom(newParam), map[string]struct{}{}) && !inNotOnMap {
					paramMap[param] = ast.FcAtom(newParam)
					paramMapStrToStr[param] = newParam
					break
				}
			} else {
				break
			}
		}
	}
	return paramMap, paramMapStrToStr
}

func (ver *Verifier) preprocessKnownUniFactParams(knownUniFact *env.KnownSpecFact_InUniFact) (env.KnownSpecFact_InUniFact, map[string]string, error) {
	paramMap, paramMapStrToStr := processUniFactParamsDuplicateDeclared(ver.env, knownUniFact.UniFact.Params)

	for _, domFact := range knownUniFact.UniFact.DomFacts {
		curParamMap, curParamMapStrToStr := map[string]ast.Fc{}, map[string]string{}
		switch asStmt := domFact.(type) {
		case *ast.UniFactStmt:
			curParamMap, curParamMapStrToStr = processUniFactParamsDuplicateDeclared_notInGivenMap(ver.env, asStmt.Params, paramMapStrToStr)
			// newDomFact, _, err := useRandomParamToReplaceOriginalParam(asStmt, curParamMap, curParamMapStrToStr)
			// if err != nil {
			// 	return env.KnownSpecFact_InUniFact{}, nil, err
			// }
			// newDomFacts = append(newDomFacts, newDomFact)
		case *ast.UniFactWithIffStmt:
			panic("not implemented")
			// curParamMap, curParamMapStrToStr = processUniFactParamsDuplicateDeclared_notInGivenMap(ver.env, asStmt.UniFact.Params, paramMapStrToStr)
			// newDomFact, _, err := useRandomParamToReplaceOriginalParam(asStmt.UniFact, curParamMap, curParamMapStrToStr)
			// if err != nil {
			// 	return env.KnownSpecFact_InUniFact{}, nil, err
			// }
			// newDomFacts = append(newDomFacts, newDomFact)
		default:
			// newDomFacts = append(newDomFacts, domFact)
			continue
		}

	}
	// TODO
	// 这里会instantiate整个uniFact，其实then里面没必要ins
	newStmtPtr, paramMap, err := useRandomParamToReplaceOriginalParam(knownUniFact.UniFact, paramMap, paramMapStrToStr)
	if err != nil {
		return env.KnownSpecFact_InUniFact{}, nil, err
	}

	newSpecFactStmt, err := knownUniFact.SpecFact.Instantiate(paramMap)
	if err != nil {
		return env.KnownSpecFact_InUniFact{}, nil, err
	}

	return env.MakeKnownSpecFact_InUniFact(newSpecFactStmt.(*ast.SpecFactStmt), newStmtPtr), paramMapStrToStr, nil
}
