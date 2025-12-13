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

package litex_executor

import (
	"errors"
	ast "golitex/ast"
	env "golitex/environment"
	glob "golitex/glob"
	"maps"
)

// 在用uniFact来验证specFact时，这个已知的uniFact 可能形如 forall a x: $p(a,x)。然后我代入的x刚好是a。于是整个forall被instantiate成 forall a a: $p(a,a)。然后我要验证这个 forall a a: $p(a,a) 我发现a已经在外面定义go了，于是把它替换成了乱码ABCD, 然后变成验证 forall ABCD ABCD: $p(ABCD,ABCD)。总之就错了。避免这个的办法是，让knownUniFact先把param先随机化啦，然后再代入
func (ver *Verifier) instantiateUniFactWithoutDuplicate(oldStmt *ast.UniFactStmt) (*ast.UniFactStmt, map[string]ast.Obj, error) {
	paramMap, paramMapStrToStr := processUniFactParamsDuplicateDeclared(ver.Env, oldStmt.Params)

	return useRandomParamToReplaceOriginalParamInUniFact(oldStmt, paramMap, paramMapStrToStr)
}

func useRandomParamToReplaceOriginalParamInUniFactWithIff(oldStmt *ast.UniFactWithIffStmt, paramMap map[string]ast.Obj, paramMapStrToStr map[string]string) (*ast.UniFactWithIffStmt, map[string]ast.Obj, error) {
	if len(paramMap) == 0 {
		return oldStmt, nil, nil
	}

	instantiatedOldStmt, err := oldStmt.InstantiateFact(paramMap)
	if err != nil {
		return nil, nil, err
	}
	instantiatedOldStmtAsUniFactIff, ok := instantiatedOldStmt.(*ast.UniFactWithIffStmt)
	if !ok {
		return nil, nil, errors.New("instantiatedOldStmt is not a UniFactWithIffStmt")
	}

	newParams := []string{}
	for _, param := range instantiatedOldStmtAsUniFactIff.UniFact.Params {
		if newParam, ok := paramMapStrToStr[param]; ok {
			newParams = append(newParams, newParam)
		} else {
			newParams = append(newParams, param)
		}
	}

	newStmtPtr := ast.NewUniFactWithIff(ast.NewUniFact(newParams, instantiatedOldStmtAsUniFactIff.UniFact.ParamSets, instantiatedOldStmtAsUniFactIff.UniFact.DomFacts, instantiatedOldStmtAsUniFactIff.UniFact.ThenFacts, instantiatedOldStmtAsUniFactIff.UniFact.Line), instantiatedOldStmtAsUniFactIff.IffFacts, instantiatedOldStmtAsUniFactIff.UniFact.Line)

	return newStmtPtr, paramMap, nil
}

func useRandomParamToReplaceOriginalParamInUniFact(oldStmt *ast.UniFactStmt, paramMap map[string]ast.Obj, paramMapStrToStr map[string]string) (*ast.UniFactStmt, map[string]ast.Obj, error) {
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

	newStmtPtr := ast.NewUniFact(newParams, instantiatedOldStmt.ParamSets, instantiatedOldStmt.DomFacts, instantiatedOldStmt.ThenFacts, instantiatedOldStmt.Line)

	return newStmtPtr, paramMap, nil
}

func processUniFactParamsDuplicateDeclared(env *env.Env, params []string) (map[string]ast.Obj, map[string]string) {
	paramMap := make(map[string]ast.Obj)
	paramMapStrToStr := make(map[string]string)
	for _, param := range params {
		for {
			newParam := param
			ret := env.IsNameDefinedOrBuiltin(newParam, map[string]struct{}{})
			if ret.IsTrue() {
				newParam = env.GenerateUndeclaredRandomName()
				ret = env.IsNameDefinedOrBuiltin(newParam, map[string]struct{}{})
				if ret.IsErr() {
					paramMap[param] = ast.Atom(newParam)
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

func processUniFactParamsDuplicateDeclared_notInGivenMap(env *env.Env, params []string, notInMap map[string]string) (map[string]ast.Obj, map[string]string) {
	paramMap := make(map[string]ast.Obj)
	paramMapStrToStr := make(map[string]string)
	for _, param := range params {
		for {
			newParam := param
			_, inNotOnMap := notInMap[newParam]
			ret := env.IsNameDefinedOrBuiltin(newParam, map[string]struct{}{})
			if ret.IsTrue() || inNotOnMap {
				newParam = env.GenerateUndeclaredRandomName()

				_, inNotOnMap = notInMap[newParam]
				ret = env.IsNameDefinedOrBuiltin(newParam, map[string]struct{}{})
				if ret.IsErr() && !inNotOnMap {
					paramMap[param] = ast.Atom(newParam)
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

func (ver *Verifier) preprocessUniFactParamsWithoutThenFacts_OrStmt(knownUniFact *ast.UniFactStmt, orStmt *ast.OrStmt) (*uniFactWithoutThenFacts, map[string]ast.Obj, map[string]string, *ast.OrStmt, error) {
	uniFactWithoutThen, paramMap, paramMapStrToStr, err := ver.preprocessUniFactParamsWithoutThenFacts(knownUniFact)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	instantiatedOrStmt, err := orStmt.InstantiateFact(paramMap)
	if err != nil {
		return nil, nil, nil, nil, err
	}

	return uniFactWithoutThen, paramMap, paramMapStrToStr, instantiatedOrStmt.(*ast.OrStmt), nil
}

func (ver *Verifier) preprocessUniFactParamsWithoutThenFacts(knownUniFact *ast.UniFactStmt) (*uniFactWithoutThenFacts, map[string]ast.Obj, map[string]string, error) {
	paramMap, paramMapStrToStr := processUniFactParamsDuplicateDeclared(ver.Env, knownUniFact.Params)

	domFacts_paramRandomized := []ast.FactStmt{}

	for _, domFact := range knownUniFact.DomFacts {
		switch asStmt := domFact.(type) {
		case *ast.UniFactStmt:
			copiedParamMap, copiedMapStrToStr := maps.Clone(paramMap), maps.Clone(paramMapStrToStr)

			curParamMap, curParamMapStrToStr := processUniFactParamsDuplicateDeclared_notInGivenMap(ver.Env, asStmt.Params, copiedMapStrToStr)

			copiedParamMap = glob.MergeMap(curParamMap, copiedParamMap)
			copiedMapStrToStr = glob.MergeMap(curParamMapStrToStr, copiedMapStrToStr)

			newDomFact, _, err := useRandomParamToReplaceOriginalParamInUniFact(asStmt, copiedParamMap, copiedMapStrToStr)
			if err != nil {
				return nil, nil, nil, err
			}
			domFacts_paramRandomized = append(domFacts_paramRandomized, newDomFact)
		case *ast.UniFactWithIffStmt:
			copiedParamMap, copiedMapStrToStr := maps.Clone(paramMap), maps.Clone(paramMapStrToStr)

			curParamMap, curParamMapStrToStr := processUniFactParamsDuplicateDeclared_notInGivenMap(ver.Env, asStmt.UniFact.Params, copiedMapStrToStr)

			copiedParamMap = glob.MergeMap(curParamMap, copiedParamMap)
			copiedMapStrToStr = glob.MergeMap(curParamMapStrToStr, copiedMapStrToStr)

			newDomFact, _, err := useRandomParamToReplaceOriginalParamInUniFactWithIff(asStmt, copiedParamMap, copiedMapStrToStr)
			if err != nil {
				return nil, nil, nil, err
			}
			domFacts_paramRandomized = append(domFacts_paramRandomized, newDomFact)
		default:
			domFacts_paramRandomized = append(domFacts_paramRandomized, domFact)
			continue
		}

	}

	newParams := []string{}
	for _, param := range knownUniFact.Params {
		if newParam, ok := paramMapStrToStr[param]; ok {
			newParams = append(newParams, newParam)
		} else {
			newParams = append(newParams, param)
		}
	}

	newParamSets := []ast.Obj{}
	for _, paramSet := range knownUniFact.ParamSets {
		inst, err := paramSet.Instantiate(paramMap)
		if err != nil {
			return nil, nil, nil, err
		}
		newParamSets = append(newParamSets, inst)
	}

	newDomFacts := []ast.FactStmt{}
	for _, domFact := range domFacts_paramRandomized {
		inst, err := domFact.InstantiateFact(paramMap)
		if err != nil {
			return nil, nil, nil, err
		}
		newDomFacts = append(newDomFacts, inst)
	}

	newUniFactWithoutThen := newUniFactWithoutThenFacts(newParams, newParamSets, newDomFacts)

	return newUniFactWithoutThen, paramMap, paramMapStrToStr, nil
}

type uniFactWithoutThenFacts struct {
	Params    []string
	ParamSets []ast.Obj
	DomFacts  []ast.FactStmt
}

func newUniFactWithoutThenFacts(params []string, paramSets []ast.Obj, domFacts []ast.FactStmt) *uniFactWithoutThenFacts {
	return &uniFactWithoutThenFacts{
		Params:    params,
		ParamSets: paramSets,
		DomFacts:  domFacts,
	}
}

func instantiateUniFactWithoutThenFacts(u *uniFactWithoutThenFacts, paramMap map[string]ast.Obj) (*uniFactWithoutThenFacts, error) {
	instantiatedParamSets := []ast.Obj{}
	for _, paramSet := range u.ParamSets {
		instantiatedParamSet, err := paramSet.Instantiate(paramMap)
		if err != nil {
			return nil, err
		}
		instantiatedParamSets = append(instantiatedParamSets, instantiatedParamSet)
	}

	instantiatedDomFacts := []ast.FactStmt{}
	for _, domFact := range u.DomFacts {
		instantiatedDomFact, err := domFact.InstantiateFact(paramMap)
		if err != nil {
			return nil, err
		}
		instantiatedDomFacts = append(instantiatedDomFacts, instantiatedDomFact)
	}

	return newUniFactWithoutThenFacts(u.Params, instantiatedParamSets, instantiatedDomFacts), nil
}

func (u *uniFactWithoutThenFacts) ParamInParamSetFacts(paramMap map[string]ast.Obj) []*ast.SpecFactStmt {
	paramSetFacts := make([]*ast.SpecFactStmt, len(u.Params))
	for i, param := range u.Params {
		paramSetFacts[i] = ast.NewInFactWithParamObj(paramMap[param], u.ParamSets[i], glob.BuiltinLine)
	}
	return paramSetFacts
}
