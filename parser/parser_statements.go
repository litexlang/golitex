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

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"strings"
)

func (tb *tokenBlock) TopStmt() (ast.Stmt, error) {
	// if tb.header.is(glob.KeywordPub) {
	// 	return tb.pubStmt()
	// } else {
	// 	return tb.stmt()
	// }
	return tb.stmt()

}

func (tb *tokenBlock) stmt() (ast.Stmt, error) {
	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	var ret ast.Stmt
	switch cur {
	case glob.KeywordImport:
		ret, err = tb.importStmt()
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
		ret, err = tb.proveStmt()
	case glob.KeywordKnow:
		{
			if tb.TokenAtHeaderIndexIs(1, glob.KeywordProp) {
				ret, err = tb.knowPropStmt()
			} else if tb.TokenAtHeaderIndexIs(1, glob.KeywordExistProp) {
				ret, err = tb.knowExistPropStmt()
			} else {
				ret, err = tb.knowFactStmt()
			}
		}
	case glob.KeywordSuppose:
		ret, err = tb.supposePropMatchStmt()
	case glob.KeywordWith:
		ret, err = tb.withPropMatchStmt()
	case glob.KeywordProveInEachCase:
		ret, err = tb.proveInEachCaseStmt()
	case glob.KeywordFnTemplate:
		ret, err = tb.defFnTemplateStmt()
	case glob.KeywordImportGlobally:
		ret, err = tb.importGloballyStmt()
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
		return tb.uniFactInterface(uniFactDepth)
	} else if tb.header.is(glob.KeywordOr) {
		return tb.orStmt()
	} else if tb.header.is(glob.KeywordEnum) {
		return tb.enumStmt()
	} else {
		return tb.specFactStmt()
	}
}

func (tb *tokenBlock) enumStmt() (*ast.EnumStmt, error) {
	err := tb.header.skip(glob.KeywordEnum)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	setName, err := tb.header.RawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// skip colon and get end
	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil || !tb.header.ExceedEnd() {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(tb.body) != 1 {
		return nil, fmt.Errorf("syntax error: expect a list of objects to be enumerated")
	}

	enumFcs := []ast.Fc{}
	for {
		fc, err := tb.body[0].header.RawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		enumFcs = append(enumFcs, fc)
		tb.body[0].header.skipIfIs(glob.KeySymbolComma)
		if tb.body[0].header.ExceedEnd() {
			break
		}
	}

	return ast.NewEnumStmt(setName, enumFcs), nil
}

func (tb *tokenBlock) orStmt() (*ast.OrStmt, error) {
	orFacts := []*ast.SpecFactStmt{}
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
		orFacts = append(orFacts, fact)
	}

	return ast.NewOrStmt(orFacts), nil
}

func (tb *tokenBlock) SpecFactOrOrStmt() (ast.OrStmt_SpecStmt, error) {
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

func (tb *tokenBlock) uniFactInterface(uniFactDepth uniFactEnum) (ast.UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	params, setParams, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(uniFactDepth.addDepth(), glob.KeywordThen)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFacts) == 0 {
		return ast.NewUniFact(params, setParams, domainFacts, thenFacts), nil
	} else {
		ret := ast.NewUniFactWithIff(ast.NewUniFact(params, setParams, domainFacts, thenFacts), iffFacts)

		if len(thenFacts) == 0 {
			return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeywordThen, ret.String())
		}

		return ret, nil
	}

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

	declHeader, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if !tb.header.is(glob.KeySymbolColon) {
		return ast.NewDefPropStmt(declHeader, nil, nil), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domFacts, iffFacts, err := tb.dom_IffOrThen_Body(glob.KeywordIff)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// iff, dom 里不能出现和被定义的prop同名的prop，否则用def做验证的时候会出问题
	for _, fact := range iffFacts {
		if factAsSpecFact, ok := fact.(*ast.SpecFactStmt); ok {
			if string(factAsSpecFact.PropName) == declHeader.Name {
				return nil, fmt.Errorf("iff or dom fact cannot be the same as the prop being defined")
			}
		}
	}

	for _, fact := range domFacts {
		if factAsSpecFact, ok := fact.(*ast.SpecFactStmt); ok {
			if string(factAsSpecFact.PropName) == declHeader.Name {
				return nil, fmt.Errorf("iff or dom fact cannot be the same as the prop being defined")
			}
		}
	}

	return ast.NewDefPropStmt(declHeader, domFacts, iffFacts), nil
}

func (tb *tokenBlock) FnTemplateStmt(keyword string) (*ast.FnTemplateStmt, error) {
	err := tb.header.skip(keyword)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	decl, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	retSet, err := tb.header.RawFc()
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

	return ast.NewFnTemplateStmt(decl, domFacts, thenFacts, retSet), nil
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
		objNames = append(objNames, addPkgNameToString(objName))

		tp, err := tb.header.RawFc()
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
		paramInSetsFacts[i] = ast.NewInFact(objNames[i], objSet)
	}

	return ast.NewDefObjStmt(objNames, objSets, facts), nil
}

func (tb *tokenBlock) claimStmt() (ast.ClaimInterface, error) {
	err := tb.header.skip(glob.KeywordClaim)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	toCheck, err := tb.body[0].factStmt(UniFactDepth0)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	proof := []ast.Stmt{}

	isProve := true
	if tb.body[1].header.is(glob.KeywordProveByContradiction) {
		isProve = false
		err := tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProveByContradiction)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	} else if tb.body[1].header.is(glob.KeywordProve) {
		err := tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	} else {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}

	for _, block := range tb.body[1].body {
		curStmt, err := block.stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		proof = append(proof, curStmt)
	}

	if isProve {
		return ast.NewClaimStmt(toCheck, proof), nil
	} else {
		if _, ok := toCheck.(ast.OrStmt_SpecStmt); !ok {
			return nil, fmt.Errorf("fact in claim prove by contradiction must be allowed reversible")
		}

		return ast.NewClaimProveByContradictionStmt(*ast.NewClaimStmt(toCheck, proof)), nil
	}
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

	fc, err := tb.header.RawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	opt, err := tb.header.next()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if opt == glob.FuncFactPrefix {
		propName, err := tb.header.rawFcAtom()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		if tb.header.ExceedEnd() {
			ret = ast.NewSpecFactStmt(ast.TruePure, propName, []ast.Fc{fc})
		} else {
			fc2, err := tb.header.RawFc()
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}

			params := []ast.Fc{fc, fc2}

			ret = ast.NewSpecFactStmt(ast.TruePure, propName, params)
		}
	} else if !glob.IsBuiltinInfixRelaPropSymbol(opt) {
		return nil, fmt.Errorf("expect relation prop")
	} else {
		fc2, err := tb.header.RawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		// 必须到底了
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

		params := []ast.Fc{fc, fc2}

		ret = ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(opt), params)
	}

	// 这里加入语法糖：!= 等价于 not =，好处是我 = 有 commutative的性质，我不用额外处理 != 了
	if ret.NameIs(glob.KeySymbolNotEqual) {
		ret.TypeEnum = ast.FalsePure
		// ret.PropName = *ast.NewFcAtom(glob.EmptyPkg, glob.KeySymbolEqual)
		ret.PropName = ast.FcAtom(glob.KeySymbolEqual)
	}

	return ret, nil
}

func (tb *tokenBlock) defHeaderWithoutParsingColonAtEnd() (*ast.DefHeader, error) {
	name, err := tb.header.next()
	if err != nil {
		return nil, err
	}
	name = addPkgNameToString(name)

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, err
	}

	params, setParams, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, err
	}

	return ast.NewDefHeader(name, params, setParams), nil
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

		existParams = append(existParams, addPkgNameToString(param))

		paramSet, err := tb.header.RawFc()
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

	def, err := tb.defExistPropStmtBody()

	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewDefExistPropStmt(def, existParams, existParamSets), nil
}

// 本质上这个设计是有问题的。exist把 sep 这个奇怪的东西混进param 来了
func (tb *tokenBlock) existFactStmt(isTrue bool) (*ast.SpecFactStmt, error) {
	err := tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	existParams := []ast.Fc{}

	for !tb.header.is(glob.KeywordSt) {
		param, err := tb.header.RawFc()
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

	pureSpecFact, err := tb.pureFuncSpecFact()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	factParams := ast.MakeExistFactParamsSlice(existParams, pureSpecFact.Params)

	if isTrue {
		return ast.NewSpecFactStmt(ast.TrueExist_St, pureSpecFact.PropName, factParams), nil
	} else {
		return ast.NewSpecFactStmt(ast.FalseExist_St, pureSpecFact.PropName, factParams), nil
	}
}

func (tb *tokenBlock) pureFuncSpecFact() (*ast.SpecFactStmt, error) {
	if tb.header.is(glob.FuncFactPrefix) {
		tb.header.skip(glob.FuncFactPrefix)
	}

	propName, err := tb.header.rawFcAtom()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	params := []ast.Fc{}
	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			param, err := tb.header.RawFc()
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}

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

	ret := ast.NewSpecFactStmt(ast.TruePure, propName, params)

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
		objNames = append(objNames, addPkgNameToString(objName))
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
	declHeader, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if !tb.header.is(glob.KeySymbolColon) {
		return ast.NewExistPropDef(declHeader, []ast.FactStmt{}, []ast.FactStmt{}), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domFacts, iffFactsAsFactStatements, err := tb.dom_IffOrThen_Body(glob.KeywordIff)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFactsAsFactStatements) == 0 {
		return nil, fmt.Errorf("expect 'iff' section in proposition definition has at least one fact")
	}

	return ast.NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements), nil
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
		curStmt, err := stmt.stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		// TODO 暂时只能全是fact
		body = append(body, curStmt)
	}

	return ast.NewWhenPropMatchStmt(*fact, body), nil
}

func (tb *tokenBlock) withPropMatchStmt() (*ast.WithStmt, error) {
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
		curStmt, err := stmt.stmt()
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
			curStmt, err := stmt.stmt()
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

func (tb *tokenBlock) param_paramSet_paramInSetFacts(endWith string) ([]string, []ast.Fc, error) {
	params := []string{}
	setParams := []ast.Fc{}

	if !tb.header.is(endWith) {
		for {
			param, err := tb.header.next()
			if err != nil {
				return nil, nil, err
			}

			params = append(params, addPkgNameToString(param))

			setParam, err := tb.header.RawFc()
			if err != nil {
				return nil, nil, err
			}

			setParams = append(setParams, setParam)

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				continue
			}

			if tb.header.is(endWith) {
				break
			}

			return nil, nil, fmt.Errorf("expected ',' or '%s' but got '%s'", endWith, tb.header.strAtCurIndexPlus(0))
		}
	}

	err := tb.header.skip(endWith)
	if err != nil {
		return nil, nil, err
	}

	// params 不能重复
	for i := range params {
		for j := i + 1; j < len(params); j++ {
			if params[i] == params[j] {
				return nil, nil, fmt.Errorf("parameters cannot be repeated, get duplicate parameter: %s", params[i])
			}
		}
	}

	// nth parameter set should not include 0 to n-1th parameter inside
	for i, setParam := range setParams {
		atomsInSetParam := ast.GetAtomsInFc(setParam)
		for j := i; j < len(params); j++ {
			for _, atom := range atomsInSetParam {
				if ast.IsFcAtomEqualToGivenString(atom, params[j]) {
					return nil, nil, fmt.Errorf("the set %s of the parameter if index %d cannot include any parameters from the index %d to the last one (found parameter %s)", setParam.String(), i, j, params[j])
				}
			}
		}
	}

	return params, setParams, nil
}

func (tb *tokenBlock) importStmt() (ast.ImportStmtInterface, error) {
	err := tb.header.skip(glob.KeywordImport)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	importPath := ""
	importPath, err = tb.getStringInDoubleQuotes()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if tb.header.is(glob.KeywordAs) {
		asPkgName := ""
		tb.header.skip(glob.KeywordAs)
		asPkgName, err = tb.header.next()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		return ast.NewImportStmt(importPath, asPkgName), nil
	} else {
		return ast.NewImportFileStmt(importPath), nil
	}

}

func (tb *tokenBlock) getStringInDoubleQuotes() (string, error) {
	if !tb.header.is(glob.KeySymbolDoubleQuote) {
		return "", fmt.Errorf("expected double quote but got '%s'", tb.header.strAtCurIndexPlus(0))
	}

	tb.header.skip(glob.KeySymbolDoubleQuote)

	builder := strings.Builder{}

	for !tb.header.is(glob.KeySymbolDoubleQuote) {
		curToken, err := tb.header.next()
		if err != nil {
			return "", err
		}
		builder.WriteString(curToken)
	}

	tb.header.skip(glob.KeySymbolDoubleQuote)

	return builder.String(), nil
}

// func (tb *tokenBlock) pubStmt() (*ast.PubStmt, error) {
// 	err := tb.header.skipKwAndColon_ExceedEnd(glob.KeywordPub)
// 	if err != nil {
// 		return nil, &tokenBlockErr{err, *tb}
// 	}

// 	stmts := []ast.Stmt{}
// 	for _, stmt := range tb.body {
// 		curStmt, err := stmt.stmt()
// 		if err != nil {
// 			return nil, &tokenBlockErr{err, *tb}
// 		}
// 		stmts = append(stmts, curStmt)
// 	}

// 	return ast.NewPubStmt(stmts), nil
// }

func (tb *tokenBlock) proveStmt() (*ast.ProveStmt, error) {
	err := tb.header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	proof := []ast.Stmt{}
	for _, stmt := range tb.body {
		curStmt, err := stmt.stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		proof = append(proof, curStmt)
	}

	return ast.NewProveStmt(proof), nil
}

// called by exist_prop and prop def
func (tb *tokenBlock) dom_IffOrThen_Body(sectionName string) ([]ast.FactStmt, []ast.FactStmt, error) {
	var err error
	domFacts, sectionFacts := []ast.FactStmt{}, []ast.FactStmt{}
	if len(tb.body) == 0 {
		return domFacts, sectionFacts, nil
	}

	if tb.body[0].header.is(glob.KeywordDom) {
		domFacts, err = tb.body[0].parseFactBodyWithHeaderNameAndUniFactDepth(glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}

		if len(tb.body) == 1 {
			return domFacts, sectionFacts, nil
		} else if len(tb.body) == 2 {
			sectionFacts, err = tb.body[1].parseFactBodyWithHeaderNameAndUniFactDepth(sectionName, UniFactDepth1)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *tb}
			}
			return domFacts, sectionFacts, nil
		} else {
			return nil, nil, &tokenBlockErr{fmt.Errorf("expect 1 or 2 body facts, but got %d", len(tb.body)), *tb}
		}
	} else {
		// 如果body下面直接是 iff 那在这里讨论了
		if tb.body[len(tb.body)-1].header.is(sectionName) {
			for i := range len(tb.body) - 1 {
				curStmt, err := tb.body[i].factStmt(UniFactDepth1)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				domFacts = append(domFacts, curStmt)
			}
			sectionFacts, err = tb.body[len(tb.body)-1].parseFactBodyWithHeaderNameAndUniFactDepth(sectionName, UniFactDepth1)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *tb}
			}
			return domFacts, sectionFacts, nil
		} else {
			for _, stmt := range tb.body {
				curStmt, err := stmt.factStmt(UniFactDepth1)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				sectionFacts = append(sectionFacts, curStmt)
			}
			return domFacts, sectionFacts, nil
		}
	}

}

func (tb *tokenBlock) parseFactBodyWithHeaderNameAndUniFactDepth(headerName string, uniFactDepth uniFactEnum) ([]ast.FactStmt, error) {
	err := tb.header.skipKwAndColon_ExceedEnd(headerName)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	facts := []ast.FactStmt{}
	for _, stmt := range tb.body {
		curStmt, err := stmt.factStmt(uniFactDepth)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		facts = append(facts, curStmt)
	}
	return facts, nil
}

func (tb *tokenBlock) defFnTemplateStmt() (*ast.DefFnTemplateStmt, error) {
	fnTemplateStmt, err := tb.FnTemplateStmt(glob.KeywordFnTemplate)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewFnTemplateDefStmt(fnTemplateStmt), nil
}

func (tb *tokenBlock) defFnStmt() (*ast.DefFnStmt, error) {
	fnTemplateStmt, err := tb.FnTemplateStmt(glob.KeywordFn)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewDefFnStmt(fnTemplateStmt), nil
}

func (tb *tokenBlock) importGloballyStmt() (*ast.ImportGloballyStmt, error) {
	err := tb.header.skip(glob.KeywordImportGlobally)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	path, err := tb.getStringInDoubleQuotes()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewImportGloballyStmt(path), nil
}
