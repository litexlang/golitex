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

func (stmt *tokenBlock) TopStmt() (*ast.TopStmt, error) {
	pub := false
	if stmt.header.is(glob.KeywordPub) {
		stmt.header.skip()
		pub = true
	}

	ret, err := stmt.Stmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewTopStmt(ret, pub), nil
}

func (stmt *tokenBlock) Stmt() (ast.Stmt, error) {
	cur, err := stmt.header.currentToken()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	var ret ast.Stmt
	switch cur {
	case glob.KeywordInterface:
		ret, err = stmt.defInterfaceStmt()
	case glob.KeywordType:
		ret, err = stmt.defTypeStmt()
	case glob.KeywordProp:
		ret, err = stmt.defConPropStmt()
	case glob.KeywordExistProp:
		ret, err = stmt.defConExistPropStmt()
	case glob.KeywordFn:
		ret, err = stmt.defConFnStmt()
	case glob.KeywordObj:
		ret, err = stmt.defObjStmt()
	case glob.KeywordClaim:
		ret, err = stmt.claimStmt()
	case glob.KeywordProve:
		ret, err = stmt.proveClaimStmt()
	case glob.KeywordProveByContradiction:
		ret, err = stmt.proveClaimStmt()
	case glob.KeywordKnow:
		ret, err = stmt.knowStmt()
	case glob.KeywordHave:
		ret, err = stmt.haveStmt()
	case glob.KeywordAxiom:
		ret, err = stmt.axiomStmt()
	case glob.KeywordThm:
		ret, err = stmt.thmStmt()
	default:
		ret, err = stmt.factStmt(ast.NameDepthMap{}, true)
	}

	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	if !stmt.header.ExceedEnd() {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ret, nil
}

func (stmt *tokenBlock) factStmt(nameDepths ast.NameDepthMap, allowUniFactInUniDom bool) (ast.FactStmt, error) {
	if stmt.header.is(glob.KeywordForall) {
		return stmt.uniFactStmt(nameDepths, allowUniFactInUniDom)
	} else if stmt.header.is(glob.KeywordWhen) {
		return stmt.condFactStmt(nameDepths)
	}
	return stmt.specFactStmt(nameDepths)
}

func (stmt *tokenBlock) specFactStmt(nameDepths ast.NameDepthMap) (*ast.SpecFactStmt, error) {
	isTrue := true
	if stmt.header.is(glob.KeywordNot) {
		stmt.header.skip(glob.KeywordNot)
		isTrue = false
	}

	ok, err := stmt.isSpecFactNotRelaFact()
	if err != nil {
		return nil, err
	}
	if !ok {
		return stmt.relaFactStmt(nameDepths)
	}

	propName, err := stmt.header.rawFcAtom()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}
	propName = *ast.AddUniPrefixToFcAtom(&propName, nameDepths)

	params := []ast.Fc{}
	err = stmt.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	for !stmt.header.is(glob.KeySymbolRightBrace) {
		param, err := stmt.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}

		param, err = ast.AddUniPrefixToFc(param, nameDepths)
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}

		params = append(params, param)
		if stmt.header.is(glob.KeySymbolComma) {
			stmt.header.next()
		}
	}

	err = stmt.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewSpecFactStmt(isTrue, propName, params), nil
}

func (stmt *tokenBlock) uniFactStmt(nameDepths ast.NameDepthMap, allowUniFactInUniDom bool) (ast.UniFactStmt, error) {
	err := stmt.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	typeParams := []string{}
	typeInterfaces := []*ast.FcAtom{}

	if stmt.header.is(glob.KeySymbolLess) {
		stmt.header.next()
		typeParams, typeInterfaces, err = stmt.header.typeListInDeclsAndSkipEnd(glob.KeySymbolGreater)
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
	}

	params, paramTypes, err := stmt.header.paramSliceInDeclHeadAndSkipEnd(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
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

	domainFacts, thenFacts, err := stmt.bodyFactSectionSpecFactSection(glob.KeywordThen, newUniParams, allowUniFactInUniDom)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	if len(typeParams) > 0 {
		return ast.NewGenericUniStmt(typeParams, typeInterfaces, params, paramTypes, domainFacts, thenFacts), nil
	} else {
		return ast.NewUniFactStmt(params, paramTypes, domainFacts, thenFacts), nil
	}
}

func (stmt *tokenBlock) bodyFacts(nameDepths ast.NameDepthMap) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for _, f := range stmt.body {
		fact, err := f.factStmt(nameDepths, true)
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *tokenBlock) thenBlockSpecFacts(nameDepths ast.NameDepthMap) ([]*ast.SpecFactStmt, error) {
	facts := []*ast.SpecFactStmt{}
	stmt.header.skip() // skip "then"
	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	for _, curStmt := range stmt.body {
		fact, err := curStmt.specFactStmt(nameDepths)
		if err != nil {
			return nil, thenFactMustSpecMsg(&curStmt, err)
		}

		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *tokenBlock) blockHeaderBodyFacts(kw string, nameDepths ast.NameDepthMap) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	stmt.header.skip(kw)
	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	for _, curStmt := range stmt.body {
		fact, err := curStmt.factStmt(nameDepths, true)
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (stmt *tokenBlock) defConPropStmt() (*ast.DefConPropStmt, error) {
	err := stmt.header.skip(glob.KeywordProp)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	declHeader, nameDepths, err := stmt.conDefHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	if !stmt.header.is(glob.KeySymbolColon) {
		return ast.NewDefConPropStmt(*declHeader, nil, nil), nil
	}

	err = stmt.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	domFacts, iffFacts, err := stmt.bodyFactSectionSpecFactSection(glob.KeywordIff, nameDepths, true)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewDefConPropStmt(*declHeader, domFacts, iffFacts), nil
}

func (stmt *tokenBlock) bodyTwoFactSections(kw string, nameDepths ast.NameDepthMap) ([]ast.FactStmt, []ast.FactStmt, error) {
	section1Facts := []ast.FactStmt{}
	section2Facts := []ast.FactStmt{}
	err := error(nil)

	if stmt.body[len(stmt.body)-1].header.is(kw) {
		for i := 0; i < len(stmt.body)-1; i++ {
			curStmt, err := stmt.body[i].factStmt(nameDepths, true)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *stmt}
			}
			section1Facts = append(section1Facts, curStmt)
		}
		section2Facts, err = stmt.body[len(stmt.body)-1].blockHeaderBodyFacts(kw, nameDepths)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.body); i++ {
			curStmt, err := stmt.body[i].factStmt(nameDepths, true)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *stmt}
			}
			section2Facts = append(section2Facts, curStmt)
		}
	}

	return section1Facts, section2Facts, nil
}

func (stmt *tokenBlock) defConFnStmt() (*ast.DefConFnStmt, error) {
	err := stmt.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	decl, nameDepths, err := stmt.conDefHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	retType, err := stmt.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	if stmt.header.is(glob.KeySymbolColon) {
		stmt.header.skip()
		domFacts, thenFacts, err = stmt.bodyFactSectionSpecFactSection(glob.KeywordThen, nameDepths, true)
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
	}

	return ast.NewDefConFnStmt(*decl, retType, domFacts, thenFacts), nil
}

func (stmt *tokenBlock) defObjStmt() (*ast.DefObjStmt, error) {
	err := stmt.header.skip(glob.KeywordObj)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	objNames := []string{}
	objSets := []ast.Fc{}

	for !stmt.header.is(glob.KeySymbolColon) && !stmt.header.ExceedEnd() {
		decl, err := stmt.header.next()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		if stmt.header.is(glob.KeySymbolComma) {
			err = stmt.header.skip(glob.KeySymbolColon)
			if err != nil {
				return nil, &tokenBlockErr{err, *stmt}
			}
		}
		objNames = append(objNames, decl)
		tp, err := stmt.header.rawFc()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		objSets = append(objSets, tp)
	}

	facts := []ast.FactStmt{}

	if !stmt.header.ExceedEnd() && stmt.header.is(glob.KeySymbolColon) {
		stmt.header.skip()
		facts, err = stmt.bodyFacts(ast.NameDepthMap{})
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
	} else if !stmt.header.ExceedEnd() {
		return nil, fmt.Errorf("expect ':' or end of block")
	}

	return ast.NewDefObjStmt(objNames, objSets, facts), nil
}

func (stmt *tokenBlock) claimStmt() (*ast.ClaimProveStmt, error) {
	stmt.header.skip(glob.KeywordClaim)
	err := error(nil)

	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	toCheck := &[]ast.FactStmt{}
	proof := &[]ast.Stmt{}

	for i := 0; i < len(stmt.body)-1; i++ {
		if !stmt.header.is(glob.KeywordProve) && !stmt.header.is(glob.KeywordProveByContradiction) {
			fact, err := stmt.body[i].factStmt(ast.NameDepthMap{}, true)
			if err != nil {
				return nil, &tokenBlockErr{err, *stmt}
			}
			*toCheck = append(*toCheck, fact)
		}
	}

	isProve := true
	if stmt.body[len(stmt.body)-1].header.is(glob.KeywordProveByContradiction) {
		isProve = false
	} else if !stmt.body[len(stmt.body)-1].header.is(glob.KeywordProve) {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}
	stmt.body[len(stmt.body)-1].header.skip()

	err = stmt.body[len(stmt.body)-1].header.testAndSkip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	for _, block := range stmt.body[len(stmt.body)-1].body {
		curStmt, err := block.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		*proof = append(*proof, curStmt)
	}

	return ast.NewClaimProveStmt(isProve, *toCheck, *proof), nil
}

func (stmt *tokenBlock) proveClaimStmt() (*ast.ClaimProveStmt, error) {
	isProve := true

	if stmt.header.is(glob.KeywordProveByContradiction) {
		isProve = false
		stmt.header.skip(glob.KeywordProveByContradiction)
	} else if stmt.header.is(glob.KeywordProve) {
		stmt.header.skip(glob.KeywordProve)
	} else {
		return nil, fmt.Errorf("expect prove or prove_by_contradiction")
	}
	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	innerStmtArr := []ast.Stmt{}
	for _, innerStmt := range stmt.body {
		curStmt, err := innerStmt.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		innerStmtArr = append(innerStmtArr, curStmt)
	}
	return ast.NewClaimProveStmt(isProve, []ast.FactStmt{}, innerStmtArr), nil
}

func (stmt *tokenBlock) knowStmt() (*ast.KnowStmt, error) {
	stmt.header.skip(glob.KeywordKnow)

	if !stmt.header.is(glob.KeySymbolColon) {
		facts := []ast.FactStmt{}
		fact, err := stmt.factStmt(ast.NameDepthMap{}, true)
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return ast.NewKnowStmt(facts), nil
	}

	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	facts, err := stmt.bodyFacts(ast.NameDepthMap{})
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewKnowStmt(facts), nil
}

func (stmt *tokenBlock) defConExistPropStmt() (*ast.DefConExistPropStmt, error) {
	err := stmt.header.skip(glob.KeywordExistProp)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	decl, nameDepths, err := stmt.conDefHeader()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	existObjOrFn := []string{}
	existObjOrFnTypes := []*ast.FcAtom{}

	for !stmt.header.is(glob.KeySymbolColon) && !stmt.header.ExceedEnd() {
		decl, err := stmt.header.next()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		tp, err := stmt.header.rawFcAtom()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		existObjOrFn = append(existObjOrFn, decl)
		existObjOrFnTypes = append(existObjOrFnTypes, &tp)
		if stmt.header.is(glob.KeySymbolComma) {
			stmt.header.skip()
		}
	}

	err = stmt.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	domFacts, thenFacts, err := stmt.bodyTwoFactSections(glob.KeywordIff, nameDepths)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewDefConExistPropStmt(*decl, existObjOrFn, existObjOrFnTypes, domFacts, thenFacts), nil
}

func (stmt *tokenBlock) haveStmt() (*ast.HaveStmt, error) {
	stmt.header.skip(glob.KeywordHave)
	propStmt, err := stmt.specFactStmt(ast.NameDepthMap{})
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	if !stmt.header.is(glob.KeySymbolColon) {
		return nil, fmt.Errorf("expected ':'")
	}

	if len(stmt.body) != 1 {
		return nil, fmt.Errorf("expect one string in members")
	}

	members, err := stmt.body[0].header.stringSliceUntilEnd()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewHaveStmt(*propStmt, members), nil
}

// relaFact 只支持2个参数的关系
func (stmt *tokenBlock) relaFactStmt(nameDepths ast.NameDepthMap) (*ast.SpecFactStmt, error) {
	fc, err := stmt.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}
	fc, err = ast.AddUniPrefixToFc(fc, nameDepths)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	if stmt.header.strAtCurIndexPlus(0) == glob.KeywordIs {
		return stmt.header.isExpr(fc)
	}

	opt, err := stmt.header.next()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	// 我认为没必要一定是内置的符号，可以是用户自定义的
	// if !glob.IsKeySymbolRelaProp(opt) {
	// 	return nil, &parseTimeErr{err, *stmt}
	// }

	fc2, err := stmt.header.rawFc()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}
	fc2, err = ast.AddUniPrefixToFc(fc2, nameDepths)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	params := []ast.Fc{fc, fc2}

	return ast.NewSpecFactStmt(true, ast.FcAtom{Value: opt}, params), nil
}

func (stmt *tokenBlock) axiomStmt() (*ast.AxiomStmt, error) {
	stmt.header.skip(glob.KeywordAxiom)
	decl, err := stmt.defPropExistStmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewAxiomStmt(decl), nil
}

func (stmt *tokenBlock) thmStmt() (*ast.ThmStmt, error) {
	err := stmt.header.skip(glob.KeywordThm)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}
	err = stmt.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}
	if !stmt.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	if len(stmt.body) != 2 {
		return nil, fmt.Errorf("expect two statements in thm")
	}

	decl, err := stmt.body[0].defPropExistStmt()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	facts, err := stmt.body[1].proveBlock()
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewThmStmt(decl, facts), nil
}

func (stmt *tokenBlock) proveBlock() ([]ast.Stmt, error) {
	stmt.header.skip(glob.KeywordProve)
	if err := stmt.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	innerStmtArr := []ast.Stmt{}
	for _, innerStmt := range stmt.body {
		curStmt, err := innerStmt.Stmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		innerStmtArr = append(innerStmtArr, curStmt)
	}

	return innerStmtArr, nil
}

func (stmt *tokenBlock) condFactStmt(nameDepths ast.NameDepthMap) (*ast.CondFactStmt, error) {
	err := stmt.header.skip(glob.KeywordWhen)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}
	err = stmt.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}
	if !stmt.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	condFacts := []ast.FactStmt{}
	thenFacts := []*ast.SpecFactStmt{}

	for i := 0; i < len(stmt.body)-1; i++ {
		fact, err := stmt.body[i].factStmt(nameDepths, true)
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		condFacts = append(condFacts, fact)
	}

	err = stmt.body[len(stmt.body)-1].header.skip(glob.KeywordThen)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}
	err = stmt.body[len(stmt.body)-1].header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, &tokenBlockErr{err, *stmt}
	}

	for i := len(stmt.body[len(stmt.body)-1].body) - 1; i >= 0; i-- {
		fact, err := stmt.body[len(stmt.body)-1].body[i].specFactStmt(nameDepths)
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		thenFacts = append(thenFacts, fact)
	}

	return ast.NewCondFactStmt(condFacts, thenFacts), nil
}

func (stmt *tokenBlock) defInterfaceStmt() (*ast.DefInterfaceStmt, error) {
	panic("")
}

func (stmt *tokenBlock) defTypeStmt() (*ast.DefTypeStmt, error) {
	panic("")
}

func (stmt *tokenBlock) conDefHeader() (*ast.ConDefHeader, ast.NameDepthMap, error) {
	name, err := stmt.header.next()
	if err != nil {
		return nil, nil, &tokenBlockErr{err, *stmt}
	}

	err = stmt.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, nil, &tokenBlockErr{err, *stmt}
	}

	params := []string{}
	typeParams := []ast.Fc{}
	nameDepths := ast.NameDepthMap{}

	for !stmt.header.is(glob.KeySymbolRightBrace) {
		param, err := stmt.header.next()
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *stmt}
		}

		_, declared := nameDepths[param]
		if declared {
			return nil, nil, fmt.Errorf("duplicate parameter %s", param)
		}
		nameDepths[param] = 1

		typeParam, err := stmt.header.rawFc()
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *stmt}
		}

		typeParams = append(typeParams, typeParam)
		param = fmt.Sprintf("%s%s", glob.UniParamPrefix, param)
		params = append(params, param)

		if stmt.header.is(glob.KeySymbolComma) {
			stmt.header.skip()
		}
	}

	err = stmt.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, nil, &tokenBlockErr{err, *stmt}
	}

	return ast.NewConDefHeader(name, params, typeParams), nameDepths, nil
}

func (stmt *tokenBlock) bodyFactSectionSpecFactSection(kw string, nameDepths ast.NameDepthMap, allowUniFactInUniDom bool) ([]ast.FactStmt, []*ast.SpecFactStmt, error) {
	section1Facts := []ast.FactStmt{}
	section2SpecFacts := []*ast.SpecFactStmt{}
	err := error(nil)

	if len(stmt.body) == 0 {
		return nil, nil, fmt.Errorf("%v expect body", stmt.header)
	}

	if stmt.body[0].header.is(glob.KeywordDom) {
		err = stmt.body[0].header.skip(glob.KeywordDom)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *stmt}
		}
		err = stmt.body[0].header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *stmt}
		}

		if allowUniFactInUniDom {
			for i := 0; i < len(stmt.body[0].body); i++ {
				curStmt, err := stmt.body[0].body[i].factStmt(nameDepths, true)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *stmt}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		} else {
			for i := 0; i < len(stmt.body[0].body); i++ {
				curStmt, err := stmt.body[0].body[i].specFactStmt(nameDepths)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *stmt}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		}

		if len(stmt.body) == 1 {
			return section1Facts, section2SpecFacts, nil
		}
		if !stmt.body[1].header.is(kw) {
			for i := 1; i < len(stmt.body); i++ {
				curStmt, err := stmt.body[i].specFactStmt(nameDepths)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *stmt}
				}
				section2SpecFacts = append(section2SpecFacts, curStmt)
			}
			return section1Facts, section2SpecFacts, nil
		} else {
			err = stmt.body[1].header.skip(kw)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *stmt}
			}
			err = stmt.body[1].header.skip(glob.KeySymbolColon)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *stmt}
			}
			for i := 0; i < len(stmt.body[1].body); i++ {
				curStmt, err := stmt.body[1].body[i].specFactStmt(nameDepths)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *stmt}
				}
				section2SpecFacts = append(section2SpecFacts, curStmt)
			}
			return section1Facts, section2SpecFacts, nil
		}
	}

	if stmt.body[len(stmt.body)-1].header.is(kw) {
		if allowUniFactInUniDom {
			for i := 0; i < len(stmt.body)-1; i++ {
				curStmt, err := stmt.body[i].factStmt(nameDepths, true)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *stmt}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		} else {
			for i := 0; i < len(stmt.body)-1; i++ {
				curStmt, err := stmt.body[i].specFactStmt(nameDepths)
				if err != nil {
					return nil, nil, &tokenBlockErr{err, *stmt}
				}
				section1Facts = append(section1Facts, curStmt)
			}
		}
		section2SpecFacts, err = stmt.body[len(stmt.body)-1].thenBlockSpecFacts(nameDepths)
		if err != nil {
			return nil, nil, &tokenBlockErr{err, *stmt}
		}
	} else {
		for i := 0; i < len(stmt.body); i++ {
			curStmt, err := stmt.body[i].specFactStmt(nameDepths)
			if err != nil {
				return nil, nil, &tokenBlockErr{err, *stmt}
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

func (stmt *tokenBlock) defPropExistStmt() (ast.DefPropStmt, error) {
	if stmt.header.is(glob.KeywordProp) {
		prop, err := stmt.defConPropStmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		return prop, nil
	} else if stmt.header.is(glob.KeywordExistProp) {
		exist, err := stmt.defConExistPropStmt()
		if err != nil {
			return nil, &tokenBlockErr{err, *stmt}
		}
		return exist, nil
	}

	return nil, fmt.Errorf(`expected keyword "prop" or "exist"`)
}
