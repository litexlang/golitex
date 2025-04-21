// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen (malloc_realloc_calloc@outlook.com)
// Visit litexlang.org and https://github.com/litexlang/golitex for more information.

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
		ret, err = tb.defConPropStmt()
	case glob.KeywordExistProp:
		ret, err = tb.defConExistPropStmt(ast.NameDepthMap{}, true)
	case glob.KeywordFn:
		ret, err = tb.defConFnStmt()
	case glob.KeywordObj:
		ret, err = tb.defObjStmt()
	case glob.KeywordClaim:
		ret, err = tb.claimStmt()
	case glob.KeywordProve:
		ret, err = tb.proveClaimStmt()
	case glob.KeywordProveByContradiction:
		ret, err = tb.proveClaimStmt()
	case glob.KeywordKnow:
		ret, err = tb.knowStmt()
	case glob.KeywordHave:
		ret, err = tb.haveStmt()
	case glob.KeywordAxiom:
		ret, err = tb.axiomStmt()
	case glob.KeywordThm:
		ret, err = tb.thmStmt()
	default:
		ret, err = tb.factStmt(ast.NameDepthMap{}, true)
	}

	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if !tb.header.ExceedEnd() {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ret, nil
}

func (tb *tokenBlock) factStmt(nameDepths ast.NameDepthMap, allowUniFactInUniDom bool) (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordForall) {
		return tb.uniFactStmt(nameDepths, allowUniFactInUniDom)
	} else if tb.header.is(glob.KeywordWhen) {
		return tb.condFactStmt(nameDepths)
	}
	// else if tb.header.is(glob.KeywordExist) {
	// 	return tb.ExistFactStmt(nameDepths)
	// }
	return tb.specFactStmt(nameDepths)
}

func (tb *tokenBlock) specFactStmt(nameDepths ast.NameDepthMap) (*ast.SpecFactStmt, error) {
	isTrue := true
	if tb.header.is(glob.KeywordNot) {
		tb.header.skip(glob.KeywordNot)
		isTrue = false
	}

	ok, err := tb.isSpecFactNotRelaFact()
	if err != nil {
		return nil, err
	}
	if !ok {
		return tb.relaFactStmt(nameDepths)
	}

	propName, err := tb.header.rawFcAtom()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	propName = *ast.AddUniPrefixToFcAtom(&propName, nameDepths)

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

		param, err = ast.AddUniPrefixToFc(param, nameDepths)
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

	return ast.NewSpecFactStmt(isTrue, propName, params), nil
}

// func (tb *tokenBlock) ExistFactStmt(nameDepths ast.NameDepthMap) (*ast.ExistFactStmt, error) {
// 	err := tb.header.skip(glob.KeywordExist)
// 	if err != nil {
// 		return nil, &tokenBlockErr{err, *tb}
// 	}

// 	existFc := []ast.Fc{}
// 	for !tb.header.ExceedEnd() {
// 		fc, err := tb.header.rawFc()
// 		if err != nil {
// 			return nil, &tokenBlockErr{err, *tb}
// 		}
// 		fc, err = ast.AddUniPrefixToFc(fc, nameDepths)
// 		if err != nil {
// 			return nil, &tokenBlockErr{err, *tb}
// 		}
// 		existFc = append(existFc, fc)

// 		if !tb.header.isAndSkip(glob.KeySymbolComma) {
// 			break
// 		}
// 	}

// 	specFact, err := tb.specFactStmt(nameDepths)
// 	if err != nil {
// 		return nil, &tokenBlockErr{err, *tb}
// 	}

// 	return ast.NewExistFactStmt(specFact, existFc), nil
// }

func (tb *tokenBlock) uniFactStmt(nameDepths ast.NameDepthMap, allowUniFactInUniDom bool) (ast.UniFactStmt, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	typeParams := []string{}
	typeInterfaces := []*ast.FcAtom{}

	if tb.header.is(glob.KeySymbolLess) {
		tb.header.next()
		typeParams, typeInterfaces, err = tb.header.typeListInDeclsAndSkipEnd(glob.KeySymbolGreater)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	}

	params, paramTypes, err := tb.header.paramSliceInDeclHeadAndSkipEnd(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	newUniParams := ast.NameDepthMap{}
	for key := range nameDepths {
		newUniParams[key] = nameDepths[key]
	}

	for i := range params {
		prefixNum, declared := nameDepths[params[i]]
		if !declared {
			newUniParams[params[i]] = 1
			params[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, params[i])
		} else {
			newUniParams[params[i]] = prefixNum + 1
			params[i] = strings.Repeat(glob.UniParamPrefix, prefixNum+1) + params[i]
		}
	}

	domainFacts, thenFacts, err := tb.bodyFactSectionSpecFactSection(glob.KeywordThen, newUniParams, allowUniFactInUniDom)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if len(typeParams) > 0 {
		return ast.NewGenericUniStmt(typeParams, typeInterfaces, params, paramTypes, domainFacts, thenFacts), nil
	} else {
		return ast.NewUniFactStmt(params, paramTypes, domainFacts, thenFacts), nil
	}
}

func (tb *tokenBlock) bodyFacts(nameDepths ast.NameDepthMap) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for _, f := range tb.body {
		fact, err := f.factStmt(nameDepths, true)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (tb *tokenBlock) thenBlockSpecFacts(nameDepths ast.NameDepthMap) ([]*ast.SpecFactStmt, error) {
	facts := []*ast.SpecFactStmt{}
	tb.header.skip() // skip "then"
	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	for _, curStmt := range tb.body {
		fact, err := curStmt.specFactStmt(nameDepths)
		if err != nil {
			return nil, thenFactMustSpecMsg(&curStmt, err)
		}

		facts = append(facts, fact)
	}

	return facts, nil
}

func (tb *tokenBlock) defConPropStmt() (*ast.DefConPropStmt, error) {
	err := tb.header.skip(glob.KeywordProp)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	declHeader, nameDepths, err := tb.conDefHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	if !tb.header.is(glob.KeySymbolColon) {
		return ast.NewDefConPropStmt(*declHeader, nil, nil), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domFacts, iffFacts, err := tb.bodyFactSectionSpecFactSection(glob.KeywordIff, nameDepths, true)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewDefConPropStmt(*declHeader, domFacts, iffFacts), nil
}

func (tb *tokenBlock) defConFnStmt() (*ast.DefConFnStmt, error) {
	err := tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	decl, nameDepths, err := tb.conDefHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	retType, err := tb.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip()
		domFacts, thenFacts, err = tb.bodyFactSectionSpecFactSection(glob.KeywordThen, nameDepths, true)
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
		facts, err = tb.bodyFacts(ast.NameDepthMap{})
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
	} else if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	return ast.NewDefObjStmt(objNames, objSets, facts), nil
}

func (tb *tokenBlock) claimStmt() (*ast.ClaimProveStmt, error) {
	tb.header.skip(glob.KeywordClaim)
	err := error(nil)

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	toCheck := &[]ast.FactStmt{}
	proof := &[]ast.Stmt{}

	for i := 0; i < len(tb.body)-1; i++ {
		if !tb.header.is(glob.KeywordProve) && !tb.header.is(glob.KeywordProveByContradiction) {
			fact, err := tb.body[i].factStmt(ast.NameDepthMap{}, true)
			if err != nil {
				return nil, &tokenBlockErr{err, *tb}
			}
			*toCheck = append(*toCheck, fact)
		}
	}

	isProve := true
	if tb.body[len(tb.body)-1].header.is(glob.KeywordProveByContradiction) {
		isProve = false
		// prove_by_contradiction 时不能超过1个checkFact
		if len(*toCheck) > 1 {
			return nil, fmt.Errorf("%v expect only one checkFact", glob.KeywordProveByContradiction)
		}
	} else if !tb.body[len(tb.body)-1].header.is(glob.KeywordProve) {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}
	tb.body[len(tb.body)-1].header.skip()

	err = tb.body[len(tb.body)-1].header.testAndSkip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	for _, block := range tb.body[len(tb.body)-1].body {
		curStmt, err := block.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		*proof = append(*proof, curStmt)
	}

	return ast.NewClaimProveStmt(isProve, *toCheck, *proof), nil
}

func (tb *tokenBlock) proveClaimStmt() (*ast.ClaimProveStmt, error) {
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
	return ast.NewClaimProveStmt(isProve, []ast.FactStmt{}, innerStmtArr), nil
}

func (tb *tokenBlock) knowStmt() (*ast.KnowStmt, error) {
	tb.header.skip(glob.KeywordKnow)

	if !tb.header.is(glob.KeySymbolColon) {
		facts := []ast.FactStmt{}
		fact, err := tb.factStmt(ast.NameDepthMap{}, true)
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return ast.NewKnowStmt(facts), nil
	}

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	facts, err := tb.bodyFacts(ast.NameDepthMap{})
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewKnowStmt(facts), nil
}

func (tb *tokenBlock) haveStmt() (*ast.HaveStmt, error) {
	tb.header.skip(glob.KeywordHave)

	haveObjNames := []string{}

	for !tb.header.ExceedEnd() {
		objName, err := tb.header.next()
		if err != nil {
			return nil, &tokenBlockErr{err, *tb}
		}
		haveObjNames = append(haveObjNames, objName)

		if !tb.header.isAndSkip(glob.KeySymbolComma) {
			break
		}
	}

	propStmt, err := tb.specFactStmt(ast.NameDepthMap{})
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewHaveStmt(*propStmt, haveObjNames), nil
}

// relaFact 只支持2个参数的关系
func (tb *tokenBlock) relaFactStmt(nameDepths ast.NameDepthMap) (*ast.SpecFactStmt, error) {
	fc, err := tb.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	fc, err = ast.AddUniPrefixToFc(fc, nameDepths)
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

	// 我认为没必要一定是内置的符号，可以是用户自定义的
	// if !glob.IsKeySymbolRelaProp(opt) {
	// 	return nil, &parseTimeErr{err, *tb}
	// }

	fc2, err := tb.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}
	fc2, err = ast.AddUniPrefixToFc(fc2, nameDepths)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	params := []ast.Fc{fc, fc2}

	return ast.NewSpecFactStmt(true, ast.FcAtom{Value: opt}, params), nil
}

func (tb *tokenBlock) axiomStmt() (*ast.AxiomStmt, error) {
	tb.header.skip(glob.KeywordAxiom)
	decl, err := tb.defConPropStmt()
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

	decl, err := tb.body[0].defConPropStmt()
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

func (tb *tokenBlock) condFactStmt(nameDepths ast.NameDepthMap) (*ast.CondFactStmt, error) {
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
	thenFacts := []*ast.SpecFactStmt{}

	for i := 0; i < len(tb.body)-1; i++ {
		fact, err := tb.body[i].factStmt(nameDepths, true)
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
		fact, err := tb.body[len(tb.body)-1].body[i].specFactStmt(nameDepths)
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
	nameDepths := ast.NameDepthMap{}

	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.next()
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}

		_, declared := nameDepths[param]
		if declared {
			return nil, nil, fmt.Errorf("duplicate parameter %s", param)
		}
		nameDepths[param] = 1

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

	return ast.NewConDefHeader(name, params, typeParams), nameDepths, nil
}

func (tb *tokenBlock) bodyFactSectionSpecFactSection(kw string, nameDepths ast.NameDepthMap, allowUniFactInUniDom bool) ([]ast.FactStmt, []*ast.SpecFactStmt, error) {
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

		if allowUniFactInUniDom {
			for i := 0; i < len(tb.body[0].body); i++ {
				curStmt, err := tb.body[0].body[i].factStmt(nameDepths, true)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		} else {
			for i := 0; i < len(tb.body[0].body); i++ {
				curStmt, err := tb.body[0].body[i].specFactStmt(nameDepths)
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
				curStmt, err := tb.body[i].specFactStmt(nameDepths)
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
				curStmt, err := tb.body[1].body[i].specFactStmt(nameDepths)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section2SpecFacts = append(section2SpecFacts, curStmt)
			}
			return section1Facts, section2SpecFacts, nil
		}
	}

	if tb.body[len(tb.body)-1].header.is(kw) {
		if allowUniFactInUniDom {
			for i := 0; i < len(tb.body)-1; i++ {
				curStmt, err := tb.body[i].factStmt(nameDepths, true)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		} else {
			for i := 0; i < len(tb.body)-1; i++ {
				curStmt, err := tb.body[i].specFactStmt(nameDepths)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *tb}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		}
		section2SpecFacts, err = tb.body[len(tb.body)-1].thenBlockSpecFacts(nameDepths)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *tb}
		}
	} else {
		for i := 0; i < len(tb.body); i++ {
			curStmt, err := tb.body[i].specFactStmt(nameDepths)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *tb}
			}
			section2SpecFacts = append(section2SpecFacts, curStmt)
		}
	}

	return section1Facts, section2SpecFacts, nil
}

// * 我这里可以以这样的逻辑去实现这个函数，本质原因是specFact被当做rawFc去parse是不会报错的
func (b *tokenBlock) isSpecFactNotRelaFact() (bool, error) {
	curIndex := b.header.index
	defer b.setHeaderIndex(curIndex)

	_, err := b.header.rawFc()
	if err != nil {
		return false, err
	}

	if b.header.ExceedEnd() {
		return true, nil
	}
	return false, nil
}

func (tb *tokenBlock) defConExistPropStmt(nameDepths ast.NameDepthMap, allowUniFactInUniDom bool) (*ast.DefConExistPropStmt, error) {
	err := tb.header.skip(glob.KeywordExistProp)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	params, paramTypes, err := tb.header.paramSliceInDeclHeadAndSkipEnd(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	newUniParams := ast.NameDepthMap{}
	for key := range nameDepths {
		newUniParams[key] = nameDepths[key]
	}

	for i := range params {
		prefixNum, declared := nameDepths[params[i]]
		if !declared {
			newUniParams[params[i]] = 1
			params[i] = fmt.Sprintf("%s%s", glob.UniParamPrefix, params[i])
		} else {
			newUniParams[params[i]] = prefixNum + 1
			params[i] = strings.Repeat(glob.UniParamPrefix, prefixNum+1) + params[i]
		}
	}

	domainFacts, thenFacts, err := tb.bodyFactSectionSpecFactSection(glob.KeywordThen, newUniParams, allowUniFactInUniDom)
	if err != nil {
		return nil, &tokenBlockErr{err, *tb}
	}

	return ast.NewDefConExistPropStmt(params, paramTypes, domainFacts, thenFacts), nil
}
