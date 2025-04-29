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
	ast "golitex/litex_ast"
	glob "golitex/litex_global"
	"strings"
)

func (tb *tokenBlock) TopStmt() (*ast.TopStmt, error) {
	pub := false
	if tb.header.is(glob.KeywordPub) {
		tb.header.skip()
		pub = true
	}

	ret, err := tb.Stmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
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
	case glob.KeywordInterface:
		ret, err = tb.defInterfaceStmt()
	case glob.KeywordType:
		ret, err = tb.defTypeStmt()
	case glob.KeywordProp:
		ret, err = tb.defConPropStmt(glob.KeywordProp, ast.NameDepthMap{})
	case glob.KeywordExistProp:
		ret, err = tb.defConExistPropStmt()
	case glob.KeywordFn:
		ret, err = tb.defConFnStmt()
	case glob.KeywordObj:
		ret, err = tb.defObjStmt()
	case glob.KeywordExistObj:
		ret, err = tb.defExistObjStmt()
	case glob.KeywordClaim:
		ret, err = tb.claimStmt()
	case glob.KeywordProve:
		ret, err = tb.proveClaimStmt()
	case glob.KeywordProveByContradiction:
		ret, err = tb.proveClaimStmt()
	case glob.KeywordKnow:
		ret, err = tb.knowStmt()
	case glob.KeywordAxiom:
		ret, err = tb.axiomStmt()
	case glob.KeywordThm:
		ret, err = tb.thmStmt()
	case glob.KeywordSet:
		ret, err = tb.setDefStmt()
	default:
		ret, err = tb.factStmt(ast.NameDepthMap{}, UniFactDepth0)
	}

	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if !tb.header.ExceedEnd() {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ret, nil
}

func (tb *tokenBlock) factStmt(nameDepthMap ast.NameDepthMap, curAllowUniFactEnum AllowUniFactEnum) (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordForall) {
		return tb.uniFactStmt(nameDepthMap, curAllowUniFactEnum)
	} else if tb.header.is(glob.KeywordWhen) {
		return tb.condFactStmt(nameDepthMap, curAllowUniFactEnum)
	} else if tb.header.is(glob.KeywordAnd) || tb.header.is(glob.KeywordOr) {
		return tb.logicExprStmt(nameDepthMap)
	}

	return tb.specFactStmt(nameDepthMap)
}

func (tb *tokenBlock) logicExprStmt(nameDepthMap ast.NameDepthMap) (*ast.LogicExprStmt, error) {
	isOr := tb.header.isAndSkip(glob.KeywordOr)
	if !isOr {
		err := tb.header.skip(glob.KeywordAnd)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	}

	err := tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	facts := []ast.LogicExprOrSpecFactStmt{}
	for _, factToParse := range tb.body {
		fact, err := factToParse.logicExprOrSpecFactStmt(nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		facts = append(facts, fact)
	}

	// 用很呆的方式保证只能是 logical expression 或者 specFact
	for _, fact := range facts {
		if _, ok := fact.(*ast.SpecFactStmt); ok {
			continue
		}

		if _, ok := fact.(*ast.LogicExprStmt); ok {
			continue
		}

		return nil, fmt.Errorf("expect logical expression or specFact")
	}

	if len(facts) > glob.FactMaxNumInLogicExpr {
		return nil, fmt.Errorf("logic expr has too many facts: %d, expect no more than %d", len(facts), glob.FactMaxNumInLogicExpr)
	}

	return ast.NewOrAndFact(isOr, facts), nil
}

func (tb *tokenBlock) logicExprOrSpecFactStmt(nameDepthMap ast.NameDepthMap) (ast.LogicExprOrSpecFactStmt, error) {
	if tb.header.is(glob.KeywordOr) || tb.header.is(glob.KeywordAnd) {
		return tb.logicExprStmt(nameDepthMap)
	}

	return tb.specFactStmt(nameDepthMap)
}

func (tb *tokenBlock) specFactStmt(nameDepthMap ast.NameDepthMap) (*ast.SpecFactStmt, error) {
	isTrue := true
	if tb.header.is(glob.KeywordNot) {
		tb.header.skip()
		isTrue = !isTrue
	}

	if tb.header.is(glob.KeywordExist) {
		return tb.existFactStmt(nameDepthMap, isTrue)
	}

	if tb.header.is(glob.FuncFactPrefix) {
		ret, err := tb.pureFuncSpecFact(nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		if isTrue {
			return ret, nil
		} else {
			return ret.ReverseIsTrue(), nil
		}
	} else {
		ret, err := tb.relaFactStmt(nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		if isTrue {
			return ret, nil
		} else {
			return ret.ReverseIsTrue(), nil
		}
	}
}

func (tb *tokenBlock) uniFactStmt(nameDepthMap ast.NameDepthMap, curAllowUniFactEnum AllowUniFactEnum) (*ast.ConUniFactStmt, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	params, paramTypes, err := tb.header.paramSliceInDeclHeadAndSkipEnd(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	newUniParams := ast.NameDepthMap{}
	for key := range nameDepthMap {
		newUniParams[key] = nameDepthMap[key]
	}

	for i := range params {
		prefixNum, declared := nameDepthMap[params[i]]
		if !declared {
			newUniParams[params[i]] = 1
			params[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, params[i])
		} else {
			newUniParams[params[i]] = prefixNum + 1
			params[i] = strings.Repeat(glob.UniParamPrefix, prefixNum+1) + params[i]
		}
	}

	domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(newUniParams, curAllowUniFactEnum.addDepth())
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFacts) == 0 {
		iffFacts = ast.EmptyIffFacts
	}

	return ast.NewConUniFactStmt(params, paramTypes, domainFacts, thenFacts, iffFacts), nil
}

func (tb *tokenBlock) bodyFacts(nameDepthMap ast.NameDepthMap, curAllowUniFactEnum AllowUniFactEnum) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for _, f := range tb.body {
		fact, err := f.factStmt(nameDepthMap, curAllowUniFactEnum)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (tb *tokenBlock) thenBlockSpecFacts(nameDepthMap ast.NameDepthMap) ([]*ast.SpecFactStmt, error) {
	facts := []*ast.SpecFactStmt{}
	tb.header.skip() // skip "then"
	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	for _, curStmt := range tb.body {
		fact, err := curStmt.specFactStmt(nameDepthMap)
		if err != nil {
			return nil, thenFactMustSpecMsg(&curStmt, err)
		}

		facts = append(facts, fact)
	}

	return facts, nil
}

func (tb *tokenBlock) defConPropStmt(prefix string, existParamDepthMap ast.NameDepthMap) (*ast.DefConPropStmt, error) {
	if prefix != "" {
		err := tb.header.skip(prefix)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	}

	declHeader, nameDepthMap, err := tb.conDefHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// merge nameDepthMap and nameDepthMap2
	for key := range existParamDepthMap {
		nameDepthMap[key] = existParamDepthMap[key]
	}

	if !tb.header.is(glob.KeySymbolColon) {
		return ast.NewDefConPropStmt(*declHeader, nil, nil), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domFacts, iffFacts, err := tb.bodyFactSectionFactSection(glob.KeywordIff, nameDepthMap, UniFactDepth0)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFacts) == 0 {
		return nil, fmt.Errorf("expect 'iff' section in proposition definition has at least one fact")
	}

	return ast.NewDefConPropStmt(*declHeader, domFacts, iffFacts), nil
}

func (tb *tokenBlock) defConFnStmt() (*ast.DefConFnStmt, error) {
	err := tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	decl, nameDepthMap, err := tb.conDefHeader()
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
		tb.header.skip()
		domFacts, thenFacts, err = tb.bodyFactSectionFactSection(glob.KeywordThen, nameDepthMap, UniFactDepth0)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	}

	return ast.NewDefConFnStmt(*decl, retType, domFacts, thenFacts), nil
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

	facts := []ast.FactStmt{}

	if !tb.header.ExceedEnd() && tb.header.is(glob.KeySymbolColon) {
		tb.header.skip()
		facts, err = tb.bodyFacts(ast.NameDepthMap{}, UniFactDepth0)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	} else if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	return ast.NewDefObjStmt(objNames, objSets, facts), nil
}

func (tb *tokenBlock) claimStmt() (*ast.ClaimStmt, error) {
	tb.header.skip(glob.KeywordClaim)
	err := error(nil)

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
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
	tb.body[1].header.skip()

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
	isProve := true

	if tb.header.is(glob.KeywordProveByContradiction) {
		isProve = false
		tb.header.skip(glob.KeywordProveByContradiction)
	} else if tb.header.is(glob.KeywordProve) {
		tb.header.skip(glob.KeywordProve)
	} else {
		return nil, fmt.Errorf("expect prove or prove_by_contradiction")
	}
	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	innerStmtArr := []ast.Stmt{}
	for _, innerStmt := range tb.body {
		curStmt, err := innerStmt.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		innerStmtArr = append(innerStmtArr, curStmt)
	}
	return ast.NewClaimProveStmt(isProve, ast.ClaimStmtEmptyToCheck, innerStmtArr), nil
}

func (tb *tokenBlock) knowStmt() (*ast.KnowStmt, error) {
	tb.header.skip(glob.KeywordKnow)

	if !tb.header.is(glob.KeySymbolColon) {
		facts := []ast.FactStmt{}
		fact, err := tb.factStmt(ast.NameDepthMap{}, UniFactDepth0)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return ast.NewKnowStmt(facts), nil
	}

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	facts, err := tb.bodyFacts(ast.NameDepthMap{}, UniFactDepth0)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewKnowStmt(facts), nil
}

// relaFact 只支持2个参数的关系
func (tb *tokenBlock) relaFactStmt(nameDepthMap ast.NameDepthMap) (*ast.SpecFactStmt, error) {
	fc, err := tb.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// add prefix to fc
	fc, err = ast.AddUniPrefixToFc(fc, nameDepthMap)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

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
		var propNamePtr ast.Fc = &propName

		propNamePtr, err = ast.AddUniPrefixToFc(propNamePtr, nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		propNameAsAtomPtr, ok := propNamePtr.(*ast.FcAtom)
		if !ok {
			return nil, fmt.Errorf("expect prop name")
		}
		propName = *propNameAsAtomPtr

		fc2, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		fc2, err = ast.AddUniPrefixToFc(fc2, nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		params := []ast.Fc{fc, fc2}

		return ast.NewSpecFactStmt(ast.TrueAtom, propName, params), nil
	} else if !glob.IsBuiltinInfixRelaProp(opt) {
		return nil, fmt.Errorf("expect relation prop")
	} else {
		fc2, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		// add prefix to fc2
		fc2, err = ast.AddUniPrefixToFc(fc2, nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		// 必须到底了
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

		params := []ast.Fc{fc, fc2}

		return ast.NewSpecFactStmt(ast.TrueAtom, ast.FcAtom{Name: opt}, params), nil
	}

}

func (tb *tokenBlock) axiomStmt() (*ast.AxiomStmt, error) {
	tb.header.skip(glob.KeywordAxiom)
	decl, err := tb.defConPropStmt(glob.KeywordProp, ast.NameDepthMap{})
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewAxiomStmt(decl), nil
}

func (tb *tokenBlock) thmStmt() (*ast.ThmStmt, error) {
	err := tb.header.skip(glob.KeywordThm)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	if len(tb.body) != 2 {
		return nil, fmt.Errorf("expect two statements in thm")
	}

	decl, err := tb.body[0].defConPropStmt(glob.KeywordProp, ast.NameDepthMap{})
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	facts, err := tb.body[1].proveBlock()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewThmStmt(decl, facts), nil
}

func (tb *tokenBlock) proveBlock() ([]ast.Stmt, error) {
	tb.header.skip(glob.KeywordProve)
	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	innerStmtArr := []ast.Stmt{}
	for _, innerStmt := range tb.body {
		curStmt, err := innerStmt.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		innerStmtArr = append(innerStmtArr, curStmt)
	}

	return innerStmtArr, nil
}

func (tb *tokenBlock) condFactStmt(nameDepthMap ast.NameDepthMap, curAllowUniFactEnum AllowUniFactEnum) (*ast.CondFactStmt, error) {
	err := tb.header.skip(glob.KeywordWhen)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	condFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}

	for i := 0; i < len(tb.body)-1; i++ {
		fact, err := tb.body[i].factStmt(nameDepthMap, curAllowUniFactEnum.addDepth())
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		condFacts = append(condFacts, fact)
	}

	err = tb.body[len(tb.body)-1].header.skip(glob.KeywordThen)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	err = tb.body[len(tb.body)-1].header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	for i := len(tb.body[len(tb.body)-1].body) - 1; i >= 0; i-- {
		fact, err := tb.body[len(tb.body)-1].body[i].specFactStmt(nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		thenFacts = append(thenFacts, fact)
	}

	return ast.NewCondFactStmt(condFacts, thenFacts), nil
}

func (tb *tokenBlock) defInterfaceStmt() (*ast.DefInterfaceStmt, error) {
	panic("")
}

func (tb *tokenBlock) defTypeStmt() (*ast.DefTypeStmt, error) {
	panic("")
}

func (tb *tokenBlock) conDefHeader() (*ast.ConDefHeader, ast.NameDepthMap, error) {
	name, err := tb.header.next()
	if err != nil {
		return nil, nil, &tokenBlockErr{err, *tb}
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, nil, &tokenBlockErr{err, *tb}
	}

	params := []string{}
	typeParams := []ast.Fc{}
	nameDepthMap := ast.NameDepthMap{}

	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.next()
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}

		_, declared := nameDepthMap[param]
		if declared {
			return nil, nil, fmt.Errorf("duplicate parameter %s", param)
		}
		nameDepthMap[param] = 1

		typeParam, err := tb.header.rawFc()
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}

		typeParams = append(typeParams, typeParam)
		param = fmt.Sprintf("%s%s", glob.UniParamPrefix, param)
		params = append(params, param)

		tb.header.skipIfIs(glob.KeySymbolComma)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewConDefHeader(name, params, typeParams), nameDepthMap, nil
}

func (tb *tokenBlock) bodyFactSectionSpecFactSection(kw string, nameDepthMap ast.NameDepthMap, curAllowUniFactEnum AllowUniFactEnum) ([]ast.FactStmt, []*ast.SpecFactStmt, error) {
	section1Facts := []ast.FactStmt{}
	section2SpecFacts := []*ast.SpecFactStmt{}
	err := error(nil)

	if len(tb.body) == 0 {
		return nil, nil, fmt.Errorf("%v expect body", tb.header)
	}

	if tb.body[0].header.is(glob.KeywordDom) {
		err = tb.body[0].header.skip(glob.KeywordDom)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}
		err = tb.body[0].header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}

		if curAllowUniFactEnum.allowMoreDepth() {
			for i := 0; i < len(tb.body[0].body); i++ {
				curStmt, err := tb.body[0].body[i].factStmt(nameDepthMap, curAllowUniFactEnum.addDepth())
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		} else {
			for i := 0; i < len(tb.body[0].body); i++ {
				curStmt, err := tb.body[0].body[i].specFactStmt(nameDepthMap)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		}

		if len(tb.body) == 1 {
			return section1Facts, section2SpecFacts, nil
		}
		if !tb.body[1].header.is(kw) {
			for i := 1; i < len(tb.body); i++ {
				curStmt, err := tb.body[i].specFactStmt(nameDepthMap)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section2SpecFacts = append(section2SpecFacts, curStmt)
			}
			return section1Facts, section2SpecFacts, nil
		} else {
			err = tb.body[1].header.skip(kw)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *tb}
			}
			err = tb.body[1].header.skip(glob.KeySymbolColon)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *tb}
			}
			for i := 0; i < len(tb.body[1].body); i++ {
				curStmt, err := tb.body[1].body[i].specFactStmt(nameDepthMap)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section2SpecFacts = append(section2SpecFacts, curStmt)
			}
			return section1Facts, section2SpecFacts, nil
		}
	}

	if tb.body[len(tb.body)-1].header.is(kw) {
		if curAllowUniFactEnum.allowMoreDepth() {
			for i := range len(tb.body) - 1 {
				curStmt, err := tb.body[i].factStmt(nameDepthMap, curAllowUniFactEnum.addDepth())
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		} else {
			for i := range len(tb.body) - 1 {
				curStmt, err := tb.body[i].specFactStmt(nameDepthMap)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		}
		section2SpecFacts, err = tb.body[len(tb.body)-1].thenBlockSpecFacts(nameDepthMap)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}
	} else {
		for i := range tb.body {
			curStmt, err := tb.body[i].specFactStmt(nameDepthMap)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *tb}
			}
			section2SpecFacts = append(section2SpecFacts, curStmt)
		}
	}

	return section1Facts, section2SpecFacts, nil
}

func (tb *tokenBlock) defConExistPropStmt() (*ast.DefConExistPropStmt, error) {
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

	err = tb.header.skip(glob.KeywordSt)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	nameDepthMap := ast.NameDepthMap{}
	for _, existParam := range existParams {
		nameDepthMap[existParam] = 1
	}

	def, err := tb.defConPropWithSpecIffFacts("", nameDepthMap)

	// add prefix to existParams
	for i := range existParams {
		existParams[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, existParams[i])
	}

	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewDefConExistPropStmt(def, existParams, existParamSets), nil
}

func (tb *tokenBlock) existFactStmt(nameDepthMap ast.NameDepthMap, isTrue bool) (*ast.SpecFactStmt, error) {
	err := tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if tb.header.is(glob.FuncFactPrefix) {
		pureSpecFact, err := tb.pureFuncSpecFact(nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		if isTrue {
			return ast.NewSpecFactStmt(ast.TrueExist, pureSpecFact.PropName, pureSpecFact.Params), nil
		} else {
			return ast.NewSpecFactStmt(ast.FalseExist, pureSpecFact.PropName, pureSpecFact.Params), nil
		}
	} else {
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
		for i := range existParams {
			existParams[i], err = ast.AddUniPrefixToFc(existParams[i], nameDepthMap)
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}
		}

		pureSpecFact, err := tb.pureFuncSpecFact(nameDepthMap)
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
	}
}

func (tb *tokenBlock) pureFuncSpecFact(nameDepthMap ast.NameDepthMap) (*ast.SpecFactStmt, error) {
	ok := tb.header.isAndSkip(glob.FuncFactPrefix)
	if !ok {
		return nil, fmt.Errorf("pure func spec fact must start with %s", glob.FuncFactPrefix)
	}

	propName, err := tb.header.rawFcAtom()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	propName = *ast.AddUniPrefixToFcAtom(&propName, nameDepthMap)

	params := []ast.Fc{}
	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		// add prefix to param
		param, err = ast.AddUniPrefixToFc(param, nameDepthMap)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		params = append(params, param)
		tb.header.skipIfIs(glob.KeySymbolComma)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewSpecFactStmt(ast.TrueAtom, propName, params), nil
}

func (tb *tokenBlock) defExistObjStmt() (*ast.ExistObjDefStmt, error) {
	err := tb.header.skip(glob.KeywordExistObj)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	objNames := []string{}

	for !tb.header.is(glob.FuncFactPrefix) {
		objName, err := tb.header.next()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		objNames = append(objNames, objName)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	fact, err := tb.specFactStmt(ast.NameDepthMap{})
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewExistObjDefStmt(objNames, *fact), nil
}

func (tb *tokenBlock) bodyFactSectionFactSection(kw string, nameDepthMap ast.NameDepthMap, curAllowUniFactEnum AllowUniFactEnum) ([]ast.FactStmt, []ast.FactStmt, error) {
	section1Facts := []ast.FactStmt{}
	section2Facts := []ast.FactStmt{}
	err := error(nil)

	if len(tb.body) == 0 {
		return nil, nil, fmt.Errorf("%v expect body", tb.header)
	}

	if tb.body[0].header.is(glob.KeywordDom) {
		err = tb.body[0].header.skipKwAndColon(glob.KeywordDom)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}

		section1Facts, err = tb.body[0].bodyBlockFacts(nameDepthMap, curAllowUniFactEnum.addDepth(), len(tb.body[0].body))
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}

		if len(tb.body) == 1 {
			return section1Facts, section2Facts, nil
		}

		err = tb.body[1].header.skipKwAndColon(kw)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}
		section2Facts, err = tb.body[1].bodyBlockFacts(nameDepthMap, curAllowUniFactEnum.addDepth(), len(tb.body[1].body))
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}
		return section1Facts, section2Facts, nil
	}

	if tb.body[len(tb.body)-1].header.is(kw) {
		section1Facts, err = tb.bodyBlockFacts(nameDepthMap, curAllowUniFactEnum.addDepth(), len(tb.body)-1)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}

		err = tb.body[len(tb.body)-1].header.skipKwAndColon(kw)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}
		section2Facts, err = tb.body[len(tb.body)-1].bodyBlockFacts(nameDepthMap, curAllowUniFactEnum.addDepth(), len(tb.body[len(tb.body)-1].body))
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}
	} else {
		section2Facts, err = tb.bodyBlockFacts(nameDepthMap, curAllowUniFactEnum, len(tb.body))
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}
	}

	return section1Facts, section2Facts, nil
}

func (tb *tokenBlock) bodyBlockFacts(nameDepthMap ast.NameDepthMap, curAllowUniFactEnum AllowUniFactEnum, parseBodyFactNum int) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}

	if curAllowUniFactEnum.allowMoreDepth() {
		for i := 0; i < parseBodyFactNum; i++ {
			stmt := tb.body[i]
			fact, err := stmt.factStmt(nameDepthMap, curAllowUniFactEnum) // no longer allow further uniFact
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}
			facts = append(facts, fact)
		}
	} else {
		for i := 0; i < parseBodyFactNum; i++ {
			stmt := tb.body[i]
			fact, err := stmt.specFactStmt(nameDepthMap)
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}
			facts = append(facts, fact)
		}
	}

	return facts, nil
}

func (tb *tokenBlock) defConPropWithSpecIffFacts(prefix string, existParamDepthMap ast.NameDepthMap) (*ast.ExistPropDef, error) {
	if prefix != "" {
		err := tb.header.skip(prefix)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	}

	declHeader, nameDepthMap, err := tb.conDefHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	// merge nameDepthMap and nameDepthMap2
	for key := range existParamDepthMap {
		nameDepthMap[key] = existParamDepthMap[key]
	}

	if !tb.header.is(glob.KeySymbolColon) {
		return ast.NewExistPropDef(*declHeader, []ast.FactStmt{}, []*ast.SpecFactStmt{}), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domFacts, iffFacts, err := tb.bodyFactSectionSpecFactSection(glob.KeywordIff, nameDepthMap, UniFactDepth1)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFacts) == 0 {
		return nil, fmt.Errorf("expect 'iff' section in proposition definition has at least one fact")
	}

	return ast.NewExistPropDef(*declHeader, domFacts, iffFacts), nil
}

func (tb *tokenBlock) setDefStmt() (ast.SetDefStmt, error) {
	err := tb.header.skip(glob.KeywordSet)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	setName, err := tb.header.next()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if tb.header.is(glob.KeySymbolLeftCurly) {
		err = tb.header.skip(glob.KeySymbolLeftCurly)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		elems := []ast.Fc{}
		for !tb.header.is(glob.KeySymbolRightCurly) {
			elem, err := tb.header.rawFc()
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}
			elems = append(elems, elem)
		}

		err = tb.header.skip(glob.KeySymbolRightCurly)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		return ast.NewDefSetEnumtmt(setName, elems), nil
	} else {
		parentSet, err := tb.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		facts, err := tb.bodyBlockFacts(ast.NameDepthMap{}, UniFactDepth0, len(tb.body))
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}

		return ast.NewSetDefSetBuilderStmt(setName, parentSet, facts), nil
	}
}

func (tb *tokenBlock) claimToCheckFact() (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordForall) {
		return tb.uniFactStmtInClaim()
	} else {
		return tb.specFactStmt(ast.NameDepthMap{})
	}
}

// claim 因为实在太难instantiate了(要让所有的stmt都添加instantiate这个方法，太难了)，所以不能让用户随便命名forall里的参数了，用户只能用不存在的参数名
func (tb *tokenBlock) uniFactStmtInClaim() (ast.UniFactStmt, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	params, paramTypes, err := tb.header.paramSliceInDeclHeadAndSkipEnd(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(ast.NameDepthMap{}, UniFactDepth1)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(iffFacts) == 0 {
		iffFacts = ast.EmptyIffFacts
	} else {
		return nil, fmt.Errorf("universal fact in claim statement should not have iff facts")
	}

	return ast.NewConUniFactStmt(params, paramTypes, domainFacts, thenFacts, iffFacts), nil
}

func (tb *tokenBlock) uniFactBodyFacts(nameDepthMap ast.NameDepthMap, curAllowUniFactEnum AllowUniFactEnum) ([]ast.FactStmt, []ast.FactStmt, []ast.FactStmt, error) {
	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}
	iffFacts := []ast.FactStmt{}
	err := error(nil)

	if len(tb.body) == 0 {
		return nil, nil, nil, fmt.Errorf("%v expect body", tb.header)
	}

	eachSectionStartWithKw := tb.body[0].header.is(glob.KeywordDom) || tb.body[0].header.is(glob.KeywordThen) || tb.body[0].header.is(glob.KeywordIff)

	if eachSectionStartWithKw {
		for _, stmt := range tb.body {
			kw, err := stmt.header.skipAndSkipColonAndAchieveEnd()
			if err != nil {
				return nil, nil, nil, &tokenBlockErr{err, *tb}
			}
			facts, err := stmt.bodyBlockFacts(nameDepthMap, curAllowUniFactEnum, len(stmt.body))
			if err != nil {
				return nil, nil, nil, &tokenBlockErr{err, *tb}
			}
			switch kw {
			case glob.KeywordDom:
				domFacts = append(domFacts, facts...)
			case glob.KeywordThen:
				thenFacts = append(thenFacts, facts...)
			case glob.KeywordIff:
				iffFacts = append(iffFacts, facts...)
			}
		}
	} else if tb.body[len(tb.body)-1].header.is(glob.KeywordThen) {
		domFacts, err = tb.bodyBlockFacts(nameDepthMap, curAllowUniFactEnum.addDepth(), len(tb.body)-1)
		if err != nil {
			return nil, nil, nil, &tokenBlockErr{err, *tb}
		}

		err = tb.body[len(tb.body)-1].header.skipKwAndColon(glob.KeywordThen)
		if err != nil {
			return nil, nil, nil, &tokenBlockErr{err, *tb}
		}
		thenFacts, err = tb.body[len(tb.body)-1].bodyBlockFacts(nameDepthMap, curAllowUniFactEnum.addDepth(), len(tb.body[len(tb.body)-1].body))
		if err != nil {
			return nil, nil, nil, &tokenBlockErr{err, *tb}
		}
	} else {
		thenFacts, err = tb.bodyBlockFacts(nameDepthMap, curAllowUniFactEnum, len(tb.body))
		if err != nil {
			return nil, nil, nil, &tokenBlockErr{err, *tb}
		}
	}

	return domFacts, thenFacts, iffFacts, nil
}
