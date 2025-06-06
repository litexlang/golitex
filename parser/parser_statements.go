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

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
)

func (tb *tokenBlock) TopStmt() (*ast.TopStmt, error) {
	pub := false
	if tb.header.is(glob.KeywordPub) {
		tb.header.skip("")
		pub = true
	}

	if tb.header.is(glob.KeywordImport) {
		_, err := tb.importStmt()
		if err != nil {
			return nil, err
		}
		return nil, nil
	}

	ret, err := tb.Stmt()
	if err != nil {
		return nil, err
	}

	return ast.NewTopStmt(ret, pub), nil
}

func (tb *tokenBlock) Stmt() (ast.Stmt, error) {
	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	var ret ast.Stmt
	switch cur {
	case glob.KeywordProp:
		ret, err = tb.defPropStmt()
	case glob.KeywordExistProp:
		ret, err = tb.defExistPropStmt()
	case glob.KeywordFn:
		ret, err = tb.defFnStmt()
	case glob.KeywordObj:
		ret, err = tb.defObjStmt()
	case glob.KeywordHave:
		ret, err = tb.defHaveStmt()
	case glob.KeywordClaim:
		ret, err = tb.claimStmt()
	case glob.KeywordProve:
		ret, err = tb.proveClaimStmt()
	case glob.KeywordKnow:
		{
			if tb.TokenAtHeaderIndexIs(1, glob.KeywordProp) {
				ret, err = tb.knowPropStmt()
			} else if tb.TokenAtHeaderIndexIs(1, glob.KeywordExistProp) {
				ret, err = tb.knowExistPropStmt()
			} else if tb.TokenAtHeaderIndexIs(1, glob.KeywordSuppose) {
				ret, err = tb.knowSupposeStmt()
			} else {
				ret, err = tb.knowFactStmt()
			}
		}
	case glob.KeywordSet:
		ret, err = tb.setDefStmt()
	case glob.KeywordSuppose:
		ret, err = tb.supposePropMatchStmt()
	case glob.KeywordWith:
		ret, err = tb.withPropMatchStmt()
	case glob.KeywordProveInEachCase:
		ret, err = tb.proveInEachCaseStmt()
	default:
		ret, err = tb.factStmt(UniFactDepth0)
	}

	if err != nil {
		return nil, err
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of block")
	}

	return ret, nil
}

func (tb *tokenBlock) factStmt(uniFactDepth uniFactEnum) (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordForall) {
		return tb.uniFactStmt(uniFactDepth)
	} else if tb.header.is(glob.KeywordOr) {
		return tb.orStmt()
	} else {
		return tb.specFactStmt()
	}
}

func (tb *tokenBlock) orStmt() (*ast.OrStmt, error) {
	orFacts := []ast.SpecFactStmt{}
	isOr := tb.header.isAndSkip(glob.KeywordOr)
	if !isOr {
		return nil, fmt.Errorf("expect 'or'")
	}

	err := tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	for _, factToParse := range tb.body {
		fact, err := factToParse.specFactStmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		orFacts = append(orFacts, *fact)
	}

	return ast.NewOrStmt(orFacts), nil
}

func (tb *tokenBlock) SpecFactOrOrStmt() (ast.LogicOrSpec_Stmt, error) {
	if tb.header.is(glob.KeywordOr) {
		return tb.orStmt()
	} else {
		return tb.specFactStmt()
	}
}

func (tb *tokenBlock) specFactStmt() (*ast.SpecFactStmt, error) {
	isTrue := true
	if tb.header.is(glob.KeywordNot) {
		tb.header.skip("")
		isTrue = !isTrue
	}

	if tb.header.is(glob.KeywordExist) {
		return tb.existFactStmt(isTrue)
	}

	if tb.header.is(glob.FuncFactPrefix) {
		ret, err := tb.pureFuncSpecFact()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		if isTrue {
			return ret, nil
		} else {
			return ret.ReverseTrue(), nil
		}
	} else {
		ret, err := tb.relaFactStmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		if isTrue {
			return ret, nil
		} else {
			return ret.ReverseTrue(), nil
		}
	}
}

func (tb *tokenBlock) uniFactStmt(uniFactDepth uniFactEnum) (*ast.UniFactStmt, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	params, setParams, paramInSetsFacts, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(uniFactDepth.addDepth(), glob.KeywordThen)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFacts) == 0 {
		iffFacts = ast.EmptyIffFacts
	}

	return ast.NewUniFactStmtWithSetReqInDom(params, setParams, domainFacts, thenFacts, iffFacts, paramInSetsFacts), nil
}

func (tb *tokenBlock) bodyFacts(uniFactDepth uniFactEnum) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for _, f := range tb.body {
		fact, err := f.factStmt(uniFactDepth)
		if err != nil {
			return nil, err
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (tb *tokenBlock) defPropStmt() (*ast.DefPropStmt, error) {
	err := tb.header.skip(glob.KeywordProp)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	declHeader, err := tb.defHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if !tb.header.is(glob.KeySymbolColon) {
		return ast.NewDefPropStmt(*declHeader, nil, nil), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domFacts, _, iffFacts, err := tb.uniFactBodyFacts(UniFactDepth1, glob.KeywordIff)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFacts) == 0 {
		iffFacts = ast.EmptyIffFacts
	}

	return ast.NewDefPropStmt(*declHeader, domFacts, iffFacts), nil
}

func (tb *tokenBlock) defFnStmt() (*ast.DefFnStmt, error) {
	err := tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	decl, err := tb.defHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	retType, err := tb.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip("")
		domFacts, thenFacts, _, err = tb.uniFactBodyFacts(UniFactDepth1, glob.KeywordThen)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	}

	retInSetsFacts := ast.Param_ParamSet_ToInFact(decl.Name, retType)

	return ast.NewDefFnStmt(*decl, domFacts, thenFacts, retInSetsFacts), nil
}

func (tb *tokenBlock) defObjStmt() (*ast.DefObjStmt, error) {
	err := tb.header.skip(glob.KeywordObj)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	objNames := []string{}
	objSets := []ast.Fc{}

	for !tb.header.is(glob.KeySymbolColon) && !tb.header.ExceedEnd() {
		objName, err := tb.header.next()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		objNames = append(objNames, objName)

		tp, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		objSets = append(objSets, tp)

		tb.header.skipIfIs(glob.KeySymbolComma)
	}

	if len(objNames) == 0 {
		return nil, fmt.Errorf("expect at least one object")
	}

	facts := []ast.FactStmt{}

	if !tb.header.ExceedEnd() && tb.header.is(glob.KeySymbolColon) {
		tb.header.skip("")
		facts, err = tb.bodyFacts(UniFactDepth0)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	} else if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	paramInSetsFacts := make([]ast.FactStmt, len(objSets))
	for i, objSet := range objSets {
		paramInSetsFacts[i] = ast.Param_ParamSet_ToInFact(objNames[i], objSet)
	}

	return ast.NewDefObjStmt(objNames, objSets, facts, paramInSetsFacts), nil
}

func (tb *tokenBlock) claimStmt() (*ast.ClaimStmt, error) {
	tb.header.skip(glob.KeywordClaim)
	err := error(nil)

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	toCheck, err := tb.body[0].claimToCheckFact()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	proof := &[]ast.Stmt{}

	isProve := true
	if tb.body[1].header.is(glob.KeywordProveByContradiction) {
		isProve = false
	} else if !tb.body[1].header.is(glob.KeywordProve) {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}
	tb.body[1].header.skip("")

	err = tb.body[1].header.testAndSkip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	for _, block := range tb.body[1].body {
		curStmt, err := block.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		*proof = append(*proof, curStmt)
	}

	return ast.NewClaimProveStmt(isProve, toCheck, *proof), nil
}

func (tb *tokenBlock) proveClaimStmt() (*ast.ClaimStmt, error) {
	tb.header.skip(glob.KeywordProve)
	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	innerStmtArr := []ast.Stmt{}
	for _, innerStmt := range tb.body {
		curStmt, err := innerStmt.Stmt()
		if err != nil {
			return nil, err
		}
		innerStmtArr = append(innerStmtArr, curStmt)
	}
	return ast.NewClaimProveStmt(true, ast.ClaimStmtEmptyToCheck, innerStmtArr), nil
}

func (tb *tokenBlock) knowFactStmt() (*ast.KnowFactStmt, error) {
	tb.header.skip(glob.KeywordKnow)

	if !tb.header.is(glob.KeySymbolColon) {

		facts := []ast.FactStmt{}
		fact, err := tb.factStmt(UniFactDepth0)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return ast.NewKnowStmt(facts), nil
	}

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	facts, err := tb.bodyFacts(UniFactDepth0)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewKnowStmt(facts), nil
}

// relaFact 只支持2个参数的关系
func (tb *tokenBlock) relaFactStmt() (*ast.SpecFactStmt, error) {
	var ret *ast.SpecFactStmt

	fc, err := tb.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// add prefix to fc
	// fc, err = ast.AddUniPrefixToFc(fc)
	// if err != nil {
	// 	return nil, &tokenBlockErr{err, *tb}
	// }

	if tb.header.strAtCurIndexPlus(0) == glob.KeywordIs {
		return tb.header.isExpr(fc)
	}

	opt, err := tb.header.next()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if opt == glob.RelaPropNamePrefix {
		propName, err := tb.header.rawFcAtom()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		var propNamePtr ast.Fc = propName

		// propNamePtr, err = ast.AddUniPrefixToFc(propNamePtr)
		// if err != nil {
		// 	return nil, &tokenBlockErr{err, *tb}
		// }
		propNameAsAtomPtr, ok := propNamePtr.(*ast.FcAtom)
		if !ok {
			return nil, fmt.Errorf("expect prop name")
		}
		propName = propNameAsAtomPtr

		fc2, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		// fc2, err = ast.AddUniPrefixToFc(fc2)
		// if err != nil {
		// 	return nil, &tokenBlockErr{err, *tb}
		// }

		params := []ast.Fc{fc, fc2}

		ret = ast.NewSpecFactStmt(ast.TruePure, *propName, params)
	} else if !glob.IsBuiltinInfixRelaPropSymbol(opt) {
		return nil, fmt.Errorf("expect relation prop")
	} else {
		fc2, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		// add prefix to fc2
		// fc2, err = ast.AddUniPrefixToFc(fc2)
		// if err != nil {
		// 	return nil, &tokenBlockErr{err, *tb}
		// }

		// 必须到底了
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

		params := []ast.Fc{fc, fc2}

		ret = ast.NewSpecFactStmt(ast.TruePure, *ast.NewFcAtomWithName(opt), params)
	}

	// 这里加入语法糖：!= 等价于 not =，好处是我 = 有 commutative的性质，我不用额外处理 != 了
	if ret.NameIs(glob.KeySymbolNotEqual) {
		ret.TypeEnum = ast.FalsePure
		ret.PropName = *ast.NewFcAtom(glob.EmptyPkg, glob.KeySymbolEqual)
	}

	return ret, nil
}

func (tb *tokenBlock) defHeader() (*ast.DefHeader, error) {
	name, err := tb.header.next()
	if err != nil {
		return nil, err
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, err
	}

	params, setParams, paramInSetsFacts, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, err
	}

	if len(paramInSetsFacts) != len(params) {
		tb.addMessage(glob.WarningMsg("there are %d params, but only %d of them are given with requirements in sets", len(params), len(paramInSetsFacts)))
	}

	return ast.NewDefHeader(name, params, setParams, paramInSetsFacts), nil
}

func (tb *tokenBlock) defExistPropStmt() (*ast.DefExistPropStmt, error) {
	err := tb.header.skip(glob.KeywordExistProp)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	existParams := []string{}
	existParamSets := []ast.Fc{}

	for !tb.header.is(glob.KeywordSt) {
		param, err := tb.header.next()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		existParams = append(existParams, param)

		paramSet, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		existParamSets = append(existParamSets, paramSet)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	if len(existParams) == 0 {
		return nil, fmt.Errorf("expect at least one parameter")
	}

	err = tb.header.skip(glob.KeywordSt)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// nameDepthMap := ast.NameDepthMap{}
	// for _, existParam := range existParams {
	// 	nameDepthMap[existParam] = 1
	// }

	def, err := tb.defExistPropStmtBody()

	// add prefix to existParams
	// for i := range existParams {
	// 	existParams[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, existParams[i])
	// }

	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	existParamInSetsFacts := make([]ast.FactStmt, len(existParamSets))
	for i, existParamSet := range existParamSets {
		existParamInSetsFacts[i] = ast.Param_ParamSet_ToInFact(existParams[i], existParamSet)
	}

	return ast.NewDefExistPropStmt(def, existParams, existParamInSetsFacts), nil
}

// 本质上这个设计是有问题的。exist把 sep 这个奇怪的东西混进param 来了
func (tb *tokenBlock) existFactStmt(isTrue bool) (*ast.SpecFactStmt, error) {
	err := tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// if tb.header.is(glob.FuncFactPrefix) {
	// 	pureSpecFact, err := tb.pureFuncSpecFact(nameDepthMap)
	// 	if err != nil {
	// 		return nil, &tokenBlockErr{err, *tb}
	// 	}

	// 	if isTrue {
	// 		return ast.NewSpecFactStmt(ast.TrueExist, pureSpecFact.PropName, pureSpecFact.Params), nil
	// 	} else {
	// 		return ast.NewSpecFactStmt(ast.FalseExist, pureSpecFact.PropName, pureSpecFact.Params), nil
	// 	}
	// } else {
	existParams := []ast.Fc{}

	for !tb.header.is(glob.KeywordSt) {
		param, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		existParams = append(existParams, param)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeywordSt)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// add prefix to existParams
	// for i := range existParams {
	// 	existParams[i], err = ast.AddUniPrefixToFc(existParams[i])
	// 	if err != nil {
	// 		return nil, &tokenBlockErr{err, *tb}
	// 	}
	// }

	pureSpecFact, err := tb.pureFuncSpecFact()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	factParams := []ast.Fc{}
	factParams = append(factParams, existParams...)
	factParams = append(factParams, ast.BuiltinExist_St_FactExistParamPropParmSepAtom)
	factParams = append(factParams, pureSpecFact.Params...)

	if isTrue {
		return ast.NewSpecFactStmt(ast.TrueExist_St, pureSpecFact.PropName, factParams), nil
	} else {
		return ast.NewSpecFactStmt(ast.FalseExist_St, pureSpecFact.PropName, factParams), nil
	}
	// }
}

func (tb *tokenBlock) pureFuncSpecFact() (*ast.SpecFactStmt, error) {
	if tb.header.is(glob.FuncFactPrefix) {
		tb.header.skip(glob.FuncFactPrefix)
	}

	propName, err := tb.header.rawFcAtom()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// propName = *ast.AddUniPrefixToFcAtom(&propName, nameDepthMap)
	// prefixedPropName, err := ast.AddUniPrefixToFcAtom(propName)
	// if err != nil {
	// 	return nil, &tokenBlockErr{err, *tb}
	// }
	// propName = prefixedPropName

	params := []ast.Fc{}
	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			param, err := tb.header.rawFc()
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}

			// add prefix to param
			// param, err = ast.AddUniPrefixToFc(param)
			// if err != nil {
			// 	return nil, &tokenBlockErr{err, *tb}
			// }

			params = append(params, param)

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				continue
			}

			if tb.header.is(glob.KeySymbolRightBrace) {
				break
			}

			return nil, fmt.Errorf("expected ',' or '%s' but got '%s'", glob.KeySymbolRightBrace, tb.header.strAtCurIndexPlus(0))
		}
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	ret := ast.NewSpecFactStmt(ast.TruePure, *propName, params)

	return ret, nil
}

func (tb *tokenBlock) defHaveStmt() (*ast.HaveStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	objNames := []string{}

	// there is at least one object name
	for {
		objName, err := tb.header.next()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		objNames = append(objNames, objName)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
			continue
		}
		if tb.header.is(glob.KeywordSt) {
			break
		}
		return nil, fmt.Errorf("expect '%s' or '%s' but got '%s'", glob.KeywordSt, glob.KeySymbolComma, tb.header.strAtCurIndexPlus(0))
	}

	err = tb.header.skip(glob.KeywordSt)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	fact, err := tb.specFactStmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewHaveStmt(objNames, *fact), nil
}

func (tb *tokenBlock) bodyBlockFacts(uniFactDepth uniFactEnum, parseBodyFactNum int) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}

	if uniFactDepth.allowMoreDepth() {
		for i := range parseBodyFactNum {
			stmt := tb.body[i]
			fact, err := stmt.factStmt(uniFactDepth) // no longer allow further uniFact
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}
			facts = append(facts, fact)
		}
	} else {
		for i := range parseBodyFactNum {
			stmt := tb.body[i]
			fact, err := stmt.SpecFactOrOrStmt()
			if err != nil {
				if tb.body[i].CurrentTokenIs(glob.KeywordForall) {
					return nil, fmt.Errorf("expect specific fact: at most 2 layers of universal quantifier is allowed")
				} else {
					return nil, &tokenBlockErr{err, *tb}
				}
			}
			facts = append(facts, fact)
		}
	}

	return facts, nil
}

func (tb *tokenBlock) defExistPropStmtBody() (*ast.DefExistPropStmtBody, error) {
	declHeader, err := tb.defHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// merge nameDepthMap and nameDepthMap2
	// for key := range existParamDepthMap {
	// 	nameDepthMap[key] = existParamDepthMap[key]
	// }

	if !tb.header.is(glob.KeySymbolColon) {
		return ast.NewExistPropDef(*declHeader, []ast.FactStmt{}, []ast.LogicOrSpec_Stmt{}), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	var domFacts []ast.FactStmt
	var iffFactsAsFactStatements []ast.FactStmt

	domFacts, _, iffFactsAsFactStatements, err = tb.uniFactBodyFacts(UniFactDepth1, glob.KeywordIff)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFactsAsFactStatements) == 0 {
		return nil, fmt.Errorf("expect 'iff' section in proposition definition has at least one fact")
	}

	iffFactsAsLogicExprOrSpecFacts := make([]ast.LogicOrSpec_Stmt, len(iffFactsAsFactStatements))

	for i, fact := range iffFactsAsFactStatements {
		if specFact, ok := fact.(*ast.SpecFactStmt); ok {
			iffFactsAsLogicExprOrSpecFacts[i] = specFact
		} else if logicExprOrSpecFact, ok := fact.(ast.LogicOrSpec_Stmt); ok {
			iffFactsAsLogicExprOrSpecFacts[i] = logicExprOrSpecFact
		} else {
			return nil, fmt.Errorf("expect spec fact or logic expr or spec fact in iff section, but got: %v", fact)
		}
	}

	return ast.NewExistPropDef(*declHeader, domFacts, iffFactsAsLogicExprOrSpecFacts), nil
}

func (tb *tokenBlock) setDefStmt() (*ast.SetDefSetBuilderStmt, error) {
	err := tb.header.skip(glob.KeywordSet)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	setName, err := tb.header.next()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if tb.header.ExceedEnd() {
		return ast.NewSetDefSetBuilderStmt(setName, ast.EmptyParentSet, []ast.FactStmt{}), nil
	}

	var parentSet ast.Fc = nil
	if !tb.header.is(glob.KeySymbolColon) {
		parentSet, err = tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	facts, err := tb.bodyBlockFacts(UniFactDepth0, len(tb.body))
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewSetDefSetBuilderStmt(setName, parentSet, facts), nil

}

func (tb *tokenBlock) claimToCheckFact() (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordForall) {
		return tb.uniFactStmt_WithoutUniPrefix_InClaimStmt()
	} else {
		return tb.specFactStmt()
	}
}

// claim 因为实在太难instantiate了(要让所有的stmt都添加instantiate这个方法，太难了)，所以不能让用户随便命名forall里的参数了，用户只能用不存在的参数名
func (tb *tokenBlock) uniFactStmt_WithoutUniPrefix_InClaimStmt() (*ast.UniFactStmt, error) {
	// 不能直接用 uniFact  parse 因为我不能让 body 的 fact 里的 涉及forall param list的时候，我不加 prefix，我只有在 runtime 来加
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	params, setParams, paramInSetsFacts, err := tb.uniFactHeadWithoutUniPrefix(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(UniFactDepth0, glob.KeywordThen)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFacts) == 0 {
		iffFacts = ast.EmptyIffFacts
	} else {
		return nil, fmt.Errorf("universal fact in claim statement should not have iff facts")
	}

	return ast.NewUniFactStmtWithSetReqInDom(params, setParams, domainFacts, thenFacts, iffFacts, paramInSetsFacts), nil
}

func (tb *tokenBlock) uniFactBodyFacts(uniFactDepth uniFactEnum, defaultSectionName string) ([]ast.FactStmt, []ast.FactStmt, []ast.FactStmt, error) {
	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}
	iffFacts := []ast.FactStmt{}
	err := error(nil)

	if len(tb.body) == 0 {
		return nil, nil, nil, fmt.Errorf("%v expect body", tb.header)
	}

	eachSectionStartWithKw := false
	curToken, err := tb.body[0].header.currentToken()
	if err != nil {
		return nil, nil, nil, err
	}

	if curToken == glob.KeywordDom || curToken == glob.KeywordThen || curToken == glob.KeywordIff {
		eachSectionStartWithKw = true
	}

	if eachSectionStartWithKw {
		for _, stmt := range tb.body {
			kw, err := stmt.header.skipAndSkipColonAndAchieveEnd()
			if err != nil {
				return nil, nil, nil, err
			}
			facts, err := stmt.bodyBlockFacts(uniFactDepth, len(stmt.body))
			if err != nil {
				return nil, nil, nil, err
			}
			switch kw {
			case glob.KeywordDom:
				domFacts = append(domFacts, facts...)
			case glob.KeywordThen:
				thenFacts = append(thenFacts, facts...)
			case glob.KeywordIff:
				iffFacts = append(iffFacts, facts...)
			default:
				return nil, nil, nil, fmt.Errorf("expect keyword in uni fact body, but got: %s", kw)
			}
		}
	} else if tb.body[len(tb.body)-1].header.is(glob.KeywordThen) {
		domFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body)-1)
		if err != nil {
			return nil, nil, nil, err
		}

		err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
		if err != nil {
			return nil, nil, nil, err
		}
		thenFacts, err = tb.body[len(tb.body)-1].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-1].body))
		if err != nil {
			return nil, nil, nil, err
		}
	} else if tb.body[len(tb.body)-1].header.is(glob.KeywordIff) {
		thenFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body)-1)
		if err != nil {
			return nil, nil, nil, err
		}

		err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordIff)
		if err != nil {
			return nil, nil, nil, err
		}
		iffFacts, err = tb.body[len(tb.body)-1].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-1].body))
		if err != nil {
			return nil, nil, nil, err
		}
	} else {
		if defaultSectionName == glob.KeywordThen {
			thenFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body))
			if err != nil {
				return nil, nil, nil, err
			}
		} else if defaultSectionName == glob.KeywordIff {
			iffFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body))
			if err != nil {
				return nil, nil, nil, err
			}
		} else {
			return nil, nil, nil, fmt.Errorf("%s is not expected here", defaultSectionName)
		}
	}

	return domFacts, thenFacts, iffFacts, nil
}

func (tb *tokenBlock) supposePropMatchStmt() (*ast.SupposeStmt, error) {
	err := tb.header.skip(glob.KeywordSuppose)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	fact, err := tb.pureFuncSpecFact()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	body := []ast.Stmt{}
	for _, stmt := range tb.body {
		curStmt, err := stmt.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		// TODO 暂时只能全是fact
		body = append(body, curStmt)
	}

	return ast.NewWhenPropMatchStmt(*fact, body), nil
}

func (tb *tokenBlock) withPropMatchStmt() (*ast.WithPropMatchStmt, error) {
	err := tb.header.skip(glob.KeywordWith)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	fact, err := tb.pureFuncSpecFact()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	body := []ast.Stmt{}
	for _, stmt := range tb.body {
		curStmt, err := stmt.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		body = append(body, curStmt)
	}

	return ast.NewWithPropMatchStmt(*fact, body), nil
}

func (tb *tokenBlock) knowPropStmt() (*ast.KnowPropStmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	prop, err := tb.defPropStmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewKnowPropStmt(*prop), nil
}

func (tb *tokenBlock) proveInEachCaseStmt() (*ast.ProveInEachCaseStmt, error) {
	err := tb.header.skipKwAndColon_ExceedEnd(glob.KeywordProveInEachCase)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	orFact, err := tb.body[0].orStmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	thenFacts := []ast.FactStmt{}
	err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	for _, stmt := range tb.body[1].body {
		curStmt, err := stmt.factStmt(UniFactDepth0)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		thenFacts = append(thenFacts, curStmt)
	}

	proofs := [][]ast.Stmt{}
	for i := 2; i < len(tb.body); i++ {
		proof := []ast.Stmt{}

		err = tb.body[i].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		for _, stmt := range tb.body[i].body {
			curStmt, err := stmt.Stmt()
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}
			proof = append(proof, curStmt)
		}
		proofs = append(proofs, proof)
	}

	if len(proofs) != len(orFact.Facts) {
		return nil, &tokenBlockErr{fmt.Errorf("prove in each case: expect %d proofs, but got %d. expect the number of proofs to be the same as the number of facts in the or fact", len(orFact.Facts), len(proofs)), *tb}
	}

	return ast.NewProveInEachCaseStmt(*orFact, thenFacts, proofs), nil
}

// func (tb *tokenBlock) proveOrStmt() (*ast.ProveOrStmt, error) {
// 	err := tb.header.skip(glob.KeywordProveOr)
// 	if err != nil {
// 		return nil, &tokenBlockErr{err, *tb}
// 	}

// 	indexes := map[int]struct{}{}
// 	for {
// 		curToken, err := tb.header.getAndSkip("")
// 		if err != nil {
// 			return nil, &tokenBlockErr{err, *tb}
// 		}
// 		// to int
// 		curIndex, err := strconv.Atoi(curToken)
// 		if err != nil {
// 			return nil, &tokenBlockErr{err, *tb}
// 		}
// 		indexes[curIndex] = struct{}{}
// 		if tb.header.is(glob.KeySymbolComma) {
// 			tb.header.skip(glob.KeySymbolComma)
// 			continue
// 		}
// 		if tb.header.is(glob.KeySymbolColon) {
// 			break
// 		}
// 		return nil, fmt.Errorf("expect '%s' or '%s' but got '%s'", glob.KeySymbolColon, glob.KeySymbolComma, tb.header.strAtCurIndexPlus(0))
// 	}

// 	err = tb.header.skip(glob.KeySymbolColon)
// 	if err != nil {
// 		return nil, &tokenBlockErr{err, *tb}
// 	}

// 	// orFact, err := tb.body[0].logicExprStmt(ast.NameDepthMap{})
// 	orFact, err := tb.body[0].orStmt(ast.NameDepthMap{})
// 	if err != nil {
// 		return nil, &tokenBlockErr{err, *tb}
// 	}

// 	// if !orFact.IsOr {
// 	// 	return nil, &tokenBlockErr{fmt.Errorf("prove or: expect or fact, but got: %s", orFact.String()), *tb}
// 	// }

// 	err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
// 	if err != nil {
// 		return nil, &tokenBlockErr{err, *tb}
// 	}

// 	proofs := []ast.Stmt{}
// 	for _, stmt := range tb.body[1].body {
// 		curStmt, err := stmt.Stmt()
// 		if err != nil {
// 			return nil, &tokenBlockErr{err, *tb}
// 		}
// 		proofs = append(proofs, curStmt)
// 	}

// 	for index := range indexes {
// 		if index < 0 || index >= len(orFact.Facts) {
// 			return nil, &tokenBlockErr{fmt.Errorf("prove or: index out of range: %d", index), *tb}
// 		}
// 	}

// 	return ast.NewProveOrStmt(indexes, *orFact, proofs), nil
// }

func (tb *tokenBlock) knowExistPropStmt() (*ast.KnowExistPropStmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	existProp, err := tb.defExistPropStmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewKnowExistPropStmt(*existProp), nil
}

func (tb *tokenBlock) uniFactHeadWithoutUniPrefix(endWith string) ([]string, []ast.Fc, []ast.FactStmt, error) {
	paramName := []string{}
	paramInSetsFacts := []ast.FactStmt{}
	setParams := []ast.Fc{}

	for !tb.header.is(endWith) {
		objName, err := tb.header.next()
		if err != nil {
			return nil, nil, nil, err
		}

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
			continue
		} else if tb.header.is(endWith) {
			break
		} else {
			tp, err := tb.header.rawFc()
			if err != nil {
				return nil, nil, nil, err
			}

			paramName = append(paramName, objName)
			paramInSetsFacts = append(paramInSetsFacts, ast.Param_ParamSet_ToInFact(objName, tp))
			setParams = append(setParams, tp)

			tb.header.skipIfIs(glob.KeySymbolComma)
		}
	}

	if tb.header.isAndSkip(endWith) {
		return paramName, setParams, paramInSetsFacts, nil
	} else {
		return nil, nil, nil, fmt.Errorf("expected '%s' but got '%s'", endWith, tb.header.strAtCurIndexPlus(0))
	}
}

func (tb *tokenBlock) param_paramSet_paramInSetFacts(endWith string) ([]string, []ast.Fc, []ast.FactStmt, error) {
	params := []string{}
	paramInSetsFacts := []ast.FactStmt{}
	setParams := []ast.Fc{}

	if !tb.header.is(endWith) {
		for {
			param, err := tb.header.next()
			if err != nil {
				return nil, nil, nil, err
			}

			params = append(params, param)

			setParam, err := tb.header.rawFc()
			if err != nil {
				return nil, nil, nil, err
			}

			setParams = append(setParams, setParam)
			paramInSetsFacts = append(paramInSetsFacts, ast.Param_ParamSet_ToInFact(param, setParam))

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				continue
			}

			if tb.header.is(endWith) {
				break
			}

			return nil, nil, nil, fmt.Errorf("expected ',' or '%s' but got '%s'", endWith, tb.header.strAtCurIndexPlus(0))
		}
	}

	err := tb.header.skip(endWith)
	if err != nil {
		return nil, nil, nil, err
	}

	return params, setParams, paramInSetsFacts, nil
}

func (tb *tokenBlock) importStmt() (ast.Stmt, error) {
	// import 是个很重的语句，本质上一旦import了，里面的所有的事实，所有的定理，所有引入的变量，都被放到当前环境里了。在load新的包的过程中，新的包的parser会收到现在的包的parserEnv的影响。
	return nil, nil
}

func (tb *tokenBlock) knowSupposeStmt() (*ast.KnowSupposeStmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	supposeStmt, err := tb.supposePropMatchStmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewKnowSupposeStmt(*supposeStmt), nil
}
