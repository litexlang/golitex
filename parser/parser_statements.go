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

package litex_parser

import (
	"fmt"
	ast "golitex/ast"
	glob "golitex/glob"
	"slices"
	"strconv"
	"strings"
)

func (p *Parser) Stmt(tb *tokenBlock) (ast.Stmt, error) {
	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	var ret ast.Stmt
	switch cur {
	case glob.KeywordProp:
		ret, err = p.defPropStmt(tb)
	case glob.KeywordExistProp:
		ret, err = p.defExistPropStmt(tb, glob.KeywordExistProp)
	case glob.KeywordFn:
		ret, err = p.defFnStmt(tb, true)
	case glob.KeywordLet:
		if tb.header.strAtCurIndexPlus(1) == glob.KeywordFn {
			tb.header.skip(glob.KeywordLet)
			ret, err = p.defFnStmt(tb, true)
		} else {
			ret, err = p.defObjStmt(tb)
		}
	case glob.KeywordHave:
		if tb.header.strAtCurIndexPlus(1) == glob.KeywordSet {
			if tb.header.strAtCurIndexPlus(2) == glob.KeywordFn {
				ret, err = p.haveSetFnStmt(tb)
			} else {
				ret, err = p.haveSetStmt(tb)
			}
		} else if tb.header.strAtCurIndexPlus(1) == glob.KeywordFn {
			if tb.header.strAtCurIndexPlus(2) == glob.KeySymbolColon {
				ret, err = p.haveFnStmt(tb)
				// } else if tb.header.strAtCurIndexPlus(4) == glob.KeywordLift {
				// 	
 	ret, err = p.haveFnLiftStmt(tb)
			} else {
				ret, err = p.haveFnEqualStmt(tb)
			}
		} else if slices.Contains(tb.header.slice, glob.KeywordSt) {
			ret, err = p.haveObjStStmt(tb)
		} else if tb.header.strAtCurIndexPlus(1) == glob.KeywordCart {
			// Check for "have objName cart(...) = ..." pattern
			ret, err = p.haveObjFromCartSetStmt(tb)
		} else if slices.Contains(tb.header.slice, glob.KeySymbolEqual) {
			ret, err = p.haveObjEqualStmt(tb)
		} else {
			ret, err = p.haveObjInNonEmptySetStmt(tb)
		}
	case glob.KeywordClaim:
		ret, err = p.claimStmt(tb)
	case glob.KeywordProve:
		ret, err = p.proveStmt(tb)
	case glob.KeywordKnow:
		{
			if tb.TokenAtHeaderIndexIs(1, glob.KeySymbolAt) {
				if tb.TokenAtHeaderIndexIs(2, glob.KeywordExist) {
					ret, err = p.knowExistPropStmt(tb)
				} else {
					ret, err = p.knowPropStmt(tb)
				}
			} else {
				ret, err = p.knowFactStmt(tb)
			}
		}
	case glob.KeywordProveInEachCase:
		ret, err = p.proveInEachCaseStmt(tb)
	case glob.KeywordProveCaseByCase:
		ret, err = p.proveCaseByCaseStmt(tb)
	case glob.KeywordProveByEnum:
		ret, err = p.proveByEnum(tb)
	case glob.KeySymbolAt:
		ret, err = p.namedUniFactStmt(tb)
	case glob.KeywordFnTemplate:
		ret, err = p.fnTemplateStmt(tb)
	case glob.KeywordClear:
		ret, err = p.clearStmt(tb)
	case glob.KeywordProveByInduction:
		ret, err = p.proveByInductionStmt(tb)
	// case glob.KeywordProveInRangeSet:
	// 	
 	ret, err = p.proveInRangeSetStmt(tb)
	case glob.KeywordProveInRange:
		ret, err = p.proveInRangeStmt(tb)
	case glob.KeywordProveIsTransitiveProp:
		ret, err = p.proveIsTransitivePropStmt(tb)
	case glob.KeywordProveIsCommutativeProp:
		ret, err = p.proveCommutativePropStmt(tb)
	case glob.KeywordAlgo:
		ret, err = p.algoDefStmt(tb)
	case glob.KeywordEval:
		ret, err = p.evalStmt(tb)
	case glob.KeywordProveAlgo:
		ret, err = p.defProveAlgoStmt(tb)
	case glob.KeywordBy:
		ret, err = p.byStmt(tb)
	case glob.KeywordProveByContradiction:
		ret, err = p.proveByContradictionStmt(tb)
	case glob.KeywordPrint:
		ret, err = p.printStmt(tb)
	case glob.KeywordHelp:
		ret, err = p.helpStmt(tb)
	case glob.KeywordDoNothing:
		ret, err = p.doNothingStmt(tb)
	case glob.KeywordImport:
		ret, err = p.importDirStmt(tb)
	case glob.KeywordHaveCartWithDim:
		ret, err = p.haveCartWithDimStmt(tb)
	default:
		ret, err = p.factsStmt(tb)
	}

	if err != nil {
		return nil, err
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of block")
	}

	return ret, nil
}

func (p *Parser) factStmt(tb *tokenBlock, uniFactDepth uniFactEnum) (ast.FactStmt, error) {
	if !tb.EndWith(glob.KeySymbolColon) {
		return tb.inlineFactThenSkipStmtTerminatorUntilEndSignals([]string{})
	}

	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	switch cur {
	case glob.KeywordForall:
		if tb.GetEnd() == glob.KeySymbolColon {
			uniFact, err := p.uniFactInterface(tb, uniFactDepth)
			if err != nil {
				return nil, err
			}
			return uniFact.(ast.FactStmt), nil
		} else {
			uniFact, err := p.inlineUniInterfaceSkipTerminator(tb, []string{})
			if err != nil {
				return nil, err
			}
			return uniFact.(ast.FactStmt), nil
		}
	case glob.KeywordOr:
		return p.orStmt(tb)
	case glob.KeySymbolEqual:
		return p.equalsFactStmt(tb)
	default:
		return p.fact(tb)
	}

}

func (p *Parser) orStmt(tb *tokenBlock) (*ast.OrStmt, error) {
	if tb.GetEnd() != glob.KeySymbolColon {
		return tb.inlineOrFact()
	}

	orFacts := []*ast.SpecFactStmt{}
	isOr := tb.header.isAndSkip(glob.KeywordOr)
	if !isOr {
		return nil, fmt.Errorf("expect 'or'")
	}

	err := tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for _, factToParse := range tb.body {
		fact, err := p.specFactStmt_ExceedEnd(&factToParse)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		orFacts = append(orFacts, fact)
	}

	return ast.NewOrStmt(orFacts, tb.line), nil
}

func (p *Parser) SpecFactOrOrStmt(tb *tokenBlock) (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordOr) {
		return p.orStmt(tb)
	} else if tb.header.is(glob.KeySymbolEqual) {
		return p.equalsFactStmt(tb)
	} else {
		return p.specFactStmt(tb)
	}
}

func (p *Parser) specFactStmt_ExceedEnd(tb *tokenBlock) (*ast.SpecFactStmt, error) {

	ret, err := p.specFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ret, nil
}

func (p *Parser) specFactStmt(tb *tokenBlock) (*ast.SpecFactStmt, error) {
	stmt, err := p.specFactStmt_OrOneLineEqualsFact(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	switch astStmt := stmt.(type) {
	case *ast.SpecFactStmt:
		return astStmt, nil
	default:
		return nil, fmt.Errorf("expect specific fact, get %s", astStmt.String())
	}
}

func (p *Parser) specFactStmt_OrOneLineEqualsFact(tb *tokenBlock) (ast.FactStmt, error) {
	isTrue := true
	if tb.header.is(glob.KeywordNot) {
		tb.header.skip("")
		isTrue = !isTrue
	}

	if tb.header.is(glob.KeywordExist) {
		return p.existFactStmt(tb, isTrue)
	}

	ret, err := p.specFactWithoutExist_WithoutNot(tb)

	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if isTrue {
		return ret, nil
	} else {
		return ret.ReverseTrue(), nil
	}

}

func (p *Parser) specFactWithoutExist_WithoutNot(tb *tokenBlock) (*ast.SpecFactStmt, error) {
	stmt, err := p.specFactWithoutExist_WithoutNot_Or_EqualsFact(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	switch astStmt := stmt.(type) {
	case *ast.SpecFactStmt:
		return astStmt, nil
	default:
		return nil, fmt.Errorf("expect specific fact, get %s", astStmt.String())
	}
}

func (p *Parser) specFactWithoutExist_WithoutNot_Or_EqualsFact(tb *tokenBlock) (ast.FactStmt, error) {
	if tb.header.is(glob.FuncFactPrefix) {
		ret, err := p.pureFuncSpecFact(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		} else {
		ret, err := p.relaFactStmt_orRelaEquals(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
	}
}
}

func (p *Parser) uniFactInterface(tb *tokenBlock, uniFactDepth uniFactEnum) (ast.UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	params, setParams, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolColon, false)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// domainFacts, thenFacts, iffFacts, err := p.uniFactBodyFacts(tb, uniFactDepth.addDepth(), glob.KeywordThen)
	domainFacts, thenFacts, iffFacts, err := p.uniFactBodyFacts(tb, uniFactDepth.addDepth(), glob.KeySymbolRightArrow)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(iffFacts) == 0 {
		if len(thenFacts) == 0 {
			return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeySymbolRightArrow, ast.NewUniFact(params, setParams, domainFacts, thenFacts, tb.line))
		}

		return ast.NewUniFact(params, setParams, domainFacts, thenFacts, tb.line), nil
	} else {
		ret := ast.NewUniFactWithIff(ast.NewUniFact(params, setParams, domainFacts, thenFacts, tb.line), iffFacts, tb.line)

		if len(thenFacts) == 0 {
			// return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeywordThen, ret)
			return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeySymbolRightArrow, ret)
		}

		return ret, nil
	}

}

func (p *Parser) bodyFacts(tb *tokenBlock, uniFactDepth uniFactEnum) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for _, f := range tb.body {
		fact, err := p.factStmt(&f, uniFactDepth)
		if err != nil {
			return nil, err
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

func (p *Parser) defPropStmt(tb *tokenBlock) (*ast.DefPropStmt, error) {
	body, err := p.defPropStmtWithoutSelfReferCheck(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = NoSelfReferenceInPropDef(string(body.DefHeader.Name), append(append(body.DomFacts, body.IffFacts...), body.ThenFacts...))
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
}
func (p *Parser) defPropStmtWithoutSelfReferCheck(tb *tokenBlock) (*ast.DefPropStmt, error) {
	err := tb.header.skip(glob.KeywordProp)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	declHeader, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.is(glob.KeySymbolColon) {
		if tb.header.ExceedEnd() {
			return ast.NewDefPropStmt(declHeader, nil, nil, []ast.FactStmt{}, tb.line), nil
		} else if tb.header.is(glob.KeySymbolEquivalent) {
			err = tb.header.skip(glob.KeySymbolEquivalent)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			unitFacts, err := tb.inlineFacts_checkUniDepth1([]string{})
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			return ast.NewDefPropStmt(declHeader, []ast.FactStmt{}, unitFacts, []ast.FactStmt{}, tb.line), nil
		} else {
			return nil, fmt.Errorf("expect ':' or end of block")
		}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.ExceedEnd() {
		// domFacts, iffFacts, err := p.dom_and_section(tb, glob.KeywordIff, glob.KeywordThen)
		// domFacts, iffFacts, err := p.dom_and_section(tb, glob.KeywordIff, glob.KeySymbolEqualLarger)
		domFacts, iffFacts, err := p.dom_and_section(tb, glob.KeySymbolEquivalent, glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		// iff, dom 里不能出现和被定义的prop同名的prop，否则用def做验证的时候会出问题
		for _, fact := range iffFacts {
			if factAsSpecFact, ok := fact.(*ast.SpecFactStmt); ok {
				if string(factAsSpecFact.PropName) == string(declHeader.Name) {
					return nil, fmt.Errorf("iff or dom fact cannot be the same as the prop being defined")
				}
			}
		}

		for _, fact := range domFacts {
			if factAsSpecFact, ok := fact.(*ast.SpecFactStmt); ok {
				if string(factAsSpecFact.PropName) == string(declHeader.Name) {
					return nil, fmt.Errorf("iff or dom fact cannot be the same as the prop being defined")
				}
			}
		}

		return ast.NewDefPropStmt(declHeader, domFacts, iffFacts, []ast.FactStmt{}, tb.line), nil
	} else {
		domFacts, iffFacts, err := tb.bodyOfInlineDomAndThen(glob.KeySymbolEquivalent, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return ast.NewDefPropStmt(declHeader, domFacts, iffFacts, []ast.FactStmt{}, tb.line), nil
	}

}

func (p *Parser) defObjStmt(tb *tokenBlock) (*ast.DefLetStmt, error) {
	err := tb.header.skip("")
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	objNames, objSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolColon, true)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(objNames) == 0 {
		return nil, fmt.Errorf("expect at least one object")
	}

	if tb.header.ExceedEnd() && len(tb.body) == 0 {
		return ast.NewDefLetStmt(objNames, objSets, []ast.FactStmt{}, tb.line), nil
	} else if tb.header.ExceedEnd() && len(tb.body) != 0 {

			facts, err := p.bodyFacts(tb, UniFactDepth0)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		} else {
		facts, err := tb.inlineFacts_checkUniDepth0([]string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		err = checkFactsUniDepth0(facts)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
}

func (p *Parser) claimStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordClaim)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.is(glob.KeySymbolColon) {
		return p.claimNamedUniFactInline(tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.body[0].header.is(glob.KeySymbolAt) {
		if tb.body[0].header.strAtCurIndexPlus(1) == glob.KeywordExist {
			return p.claimExistPropStmt(tb)
		} else {
			return p.claimPropStmt(tb)
		}
	}

	if len(tb.body) != 2 {
		return nil, fmt.Errorf("expect 2 body blocks after claim")
	}
		
		toCheck, err := p.factStmt(&tb.body[0], UniFactDepth0)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
	proof := []ast.Stmt{}

	isProve := true

	if tb.body[1].header.is(glob.KeywordProveByContradiction) {
		isProve = false
		err := tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProveByContradiction)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
	} else if tb.body[1].header.is(glob.KeywordProve) {
		err := tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
	} else {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction' after claim")
	}
	
	for _, block := range tb.body[1].body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proof = append(proof, curStmt)
	}

	if asUniFactWithIffStmt, ok := toCheck.(*ast.UniFactWithIffStmt); ok {
		if !isProve {
			return nil, fmt.Errorf("prove_by_contradiction is not supported for iff statement")
		} else {
			err := tb.body[2].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			proof2 := []ast.Stmt{}
			
			for _, block := range tb.body[2].body {
				curStmt, err := p.Stmt(&block)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				proof2 = append(proof2, curStmt)
			}

			if len(proof2) == 0 || len(proof) == 0 {
				return nil, fmt.Errorf("expect proof after claim")
			}

			return ast.NewClaimIffStmt(asUniFactWithIffStmt, proof, proof2, tb.line), nil
		}
	}

	if len(proof) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	if isProve {
		return ast.NewClaimProveStmt(toCheck, proof, tb.line), nil
	} else {
		return ast.NewClaimProveByContradictionStmt(ast.NewClaimProveStmt(toCheck, proof, tb.line), tb.line), nil
	}
}

func (p *Parser) knowFactStmt(tb *tokenBlock) (*ast.KnowFactStmt, error) {
	tb.header.skip(glob.KeywordKnow)

	if !tb.header.is(glob.KeySymbolColon) {
		var facts ast.FactStmtSlice = ast.FactStmtSlice{}
		var err error
		facts, err = tb.inlineFacts_checkUniDepth0([]string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		err = checkFactsUniDepth0(facts)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}		

		return ast.NewKnowFactStmt(facts, tb.line), nil
	}

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	var err error
	var facts ast.FactStmtSlice = ast.FactStmtSlice{}
	
	facts, err = p.bodyFacts(tb, UniFactDepth0)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return ast.NewKnowFactStmt(facts, tb.line), nil
}

// relaFact 只支持2个参数的关系
func (p *Parser) relaFactStmt_orRelaEquals(tb *tokenBlock) (ast.FactStmt, error) {
	var ret *ast.SpecFactStmt
	
	obj, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	opt, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if opt == glob.FuncFactPrefix {
		propName, err := p.notNumberAtom(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if tb.header.ExceedEnd() {
			ret = ast.NewSpecFactStmt(ast.TruePure, propName, []ast.Obj{obj}, tb.line)
		} else {
			obj2, err := p.Obj(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			params := []ast.Obj{obj, obj2}

			ret = ast.NewSpecFactStmt(ast.TruePure, propName, params, tb.line)
		}
	} else if !glob.IsBuiltinInfixRelaPropSymbol(opt) {
		return nil, fmt.Errorf("expect relation prop")
	} else {
		obj2, err := p.Obj(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		params := []ast.Obj{obj, obj2}

		if opt != glob.KeySymbolEqual {
			ret = ast.NewSpecFactStmt(ast.TruePure, ast.Atom(opt), params, tb.line)
		} else {
			// 循环地看下面一位是不是 = ，直到不是
			if tb.header.is(glob.KeySymbolEqual) {
				return tb.relaEqualsFactStmt(obj, obj2)
			} else {
				ret = ast.NewSpecFactStmt(ast.TruePure, ast.Atom(opt), params, tb.line)
			}
		}
	}

	// 这里加入语法糖：!= 等价于 not =，好处是我 = 有 commutative的性质，我不用额外处理 != 了
	if ret.NameIs(glob.KeySymbolNotEqual) {
		ret.TypeEnum = ast.FalsePure
		// ret.PropName = *ast.NewFcAtom(glob.EmptyPkg, glob.KeySymbolEqual)
		ret.PropName = ast.Atom(glob.KeySymbolEqual)
	}

	return ret, nil
}

func (p *Parser) defHeaderWithoutParsingColonAtEnd(tb *tokenBlock) (*ast.DefHeader, error) {
	name, err := tb.header.next()
	if err != nil {
		return nil, err
	}
	// name = addPkgNameToString(name)

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, err
	}

	params, setParams, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolRightBrace, false)
	if err != nil {
		return nil, err
	}

	return ast.NewDefHeader(ast.Atom(name), params, setParams), nil
}

func (p *Parser) defExistPropStmt(tb *tokenBlock, head string) (*ast.DefExistPropStmt, error) {
	body, err := p.defExistPropStmtBodyWithoutSelfReferCheck(tb, head)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = NoSelfReferenceInPropDef(string(body.DefBody.DefHeader.Name), append(append(body.DefBody.DomFacts, body.DefBody.IffFacts...), body.DefBody.ThenFacts...))
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return body, nil
}

func (p *Parser) defExistPropStmtBodyWithoutSelfReferCheck(tb *tokenBlock, head string) (*ast.DefExistPropStmt, error) {
	var err error

	err = tb.header.skip(head)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	existParams, existParamSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeywordSt, false)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(existParams) == 0 {
		return nil, fmt.Errorf("expect at least one parameter in exist prop definition")
	}

	def, err := p.defExistPropStmtBody(tb)

	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

// 本质上这个设计是有问题的。exist把 sep 这个奇怪的东西混进param 来了
func (p *Parser) existFactStmt(tb *tokenBlock, isTrue bool) (*ast.SpecFactStmt, error) {
	err := tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	existParams := []ast.Obj{}

	for !tb.header.is(glob.KeywordSt) {
		param, err := p.Obj(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		existParams = append(existParams, param)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeywordSt)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	pureSpecFact, err := p.specFactWithoutExist_WithoutNot(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	factParams := ast.MakeExistFactParamsSlice(existParams, pureSpecFact.Params)

	if isTrue {
		return ast.NewSpecFactStmt(ast.TrueExist_St, pureSpecFact.PropName, factParams, tb.line), nil
	} else {
		return ast.NewSpecFactStmt(ast.FalseExist_St, pureSpecFact.PropName, factParams, tb.line), nil
	}
}

func (p *Parser) pureFuncSpecFact(tb *tokenBlock) (*ast.SpecFactStmt, error) {
	if tb.header.is(glob.FuncFactPrefix) {
		tb.header.skip(glob.FuncFactPrefix)
	}
	
	propName, err := p.notNumberAtom(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	params := []ast.Obj{}
	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			param, err := p.Obj(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
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
		return nil, parserErrAtTb(err, tb)
	}

	ret := ast.NewSpecFactStmt(ast.TruePure, propName, params, tb.line)

	return ret, nil
}

func (p *Parser) haveObjStStmt(tb *tokenBlock) (*ast.HaveObjStStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	objNames := []string{}

	// there is at least one object name
	for {
		objName, err := tb.header.next()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		// objNames = append(objNames, addPkgNameToString(objName))
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
		return nil, parserErrAtTb(err, tb)
	}

	pureSpecFact, err := p.specFactWithoutExist_WithoutNot(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	factParams := ast.MakeExistFactParamsSlice(existParams, pureSpecFact.Params)

	if isTrue {
		return ast.NewSpecFactStmt(ast.TrueExist_St, pureSpecFact.PropName, factParams, tb.line), nil
	} else {
		return ast.NewSpecFactStmt(ast.FalseExist_St, pureSpecFact.PropName, factParams, tb.line), nil
	}
}

func (p *Parser) bodyBlockFacts(tb *tokenBlock, uniFactDepth uniFactEnum, parseBodyFactNum int) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}

	if uniFactDepth.allowMoreDepth() {
		
		for i := range parseBodyFactNum {
			stmt := tb.body[i]
			fact, err := p.factStmt(&stmt, uniFactDepth) // no longer allow further uniFact
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			facts = append(facts, fact)
		}
	} else {
		for i := range parseBodyFactNum {
			stmt := tb.body[i]
			fact, err := p.SpecFactOrOrStmt(&stmt)
			if err != nil {
				if tb.body[i].header.is(glob.KeywordForall) {
					return nil, fmt.Errorf("expect specific fact: at most 2 layers of universal quantifier is allowed")
				} else {
					return nil, parserErrAtTb(err, tb)
				}
			}
			facts = append(facts, fact)
		}
	}

	return facts, nil
}

func (p *Parser) defExistPropStmtBody(tb *tokenBlock) (*ast.DefExistPropStmtBody, error) {
	declHeader, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.ExceedEnd() {
		return ast.NewExistPropDef(declHeader, []ast.FactStmt{}, []ast.FactStmt{}, []ast.FactStmt{}, tb.line), nil
	}

	if tb.header.is(glob.KeySymbolEquivalent) {
		err = tb.header.skip(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		unitFacts, err := tb.inlineFacts_checkUniDepth1([]string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return ast.NewExistPropDef(declHeader, []ast.FactStmt{}, unitFacts, []ast.FactStmt{}, tb.line), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.ExceedEnd() {

		// domFacts, iffFactsAsFactStatements, err := p.dom_and_section(tb, glob.KeywordIff, glob.KeywordThen)
		// domFacts, iffFactsAsFactStatements, err := p.dom_and_section(tb, glob.KeywordIff, glob.KeySymbolEqualLarger)
		domFacts, iffFactsAsFactStatements, err := p.dom_and_section(tb, glob.KeySymbolEquivalent, glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if len(iffFactsAsFactStatements) == 0 {
			return nil, fmt.Errorf("expect 'iff' section in proposition definition has at least one fact")
		}

		return ast.NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements, []ast.FactStmt{}, tb.line), nil
	} else {
		domFacts, iffFactsAsFactStatements, err := tb.bodyOfInlineDomAndThen(glob.KeySymbolEquivalent, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return ast.NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements, []ast.FactStmt{}, tb.line), nil
	}
}

func (p *Parser) uniFactBodyFacts(tb *tokenBlock, uniFactDepth uniFactEnum, defaultSectionName string) ([]ast.FactStmt, []ast.FactStmt, []ast.FactStmt, error) {
	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}
	iffFacts := []ast.FactStmt{}
	err := error(nil)

	if len(tb.body) == 0 {
		return nil, nil, nil, fmt.Errorf("%s expect body", tb.header.String())
	}

	eachSectionStartWithKw := false
	curToken, err := tb.body[0].header.currentToken()
	if err != nil {
		return nil, nil, nil, err
	}

	// if curToken == glob.KeywordDom || curToken == glob.KeywordThen || curToken == glob.KeywordIff {
	// if curToken == glob.KeywordDom || curToken == glob.KeySymbolEqualLarger || curToken == glob.KeywordIff {
	if curToken == glob.KeywordDom || curToken == glob.KeySymbolRightArrow || curToken == glob.KeySymbolEquivalent {
		eachSectionStartWithKw = true
	}

	if eachSectionStartWithKw {
		for _, stmt := range tb.body {
			kw, err := stmt.header.skipAndSkipColonAndAchieveEnd()
			if err != nil {
				return nil, nil, nil, err
			}
			facts, err := p.bodyBlockFacts(&stmt, uniFactDepth, len(stmt.body))
			if err != nil {
				return nil, nil, nil, err
			}
			switch kw {
			case glob.KeywordDom:
				domFacts = append(domFacts, facts...)
			// case glob.KeywordThen:
			case glob.KeySymbolRightArrow:
				thenFacts = append(thenFacts, facts...)
			// case glob.KeywordIff:
			case glob.KeySymbolEquivalent:
				iffFacts = append(iffFacts, facts...)
			default:
				return nil, nil, nil, fmt.Errorf("expect keyword in uni fact body, but got: %s", kw)
			}
		}
		// } else if tb.body[len(tb.body)-1].header.is(glob.KeywordThen) {
	} else if tb.body[len(tb.body)-1].header.is(glob.KeySymbolRightArrow) {
		domFacts, err = p.bodyBlockFacts(tb, uniFactDepth, len(tb.body)-1)
		if err != nil {
			return nil, nil, nil, err
		}

		// err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, nil, nil, err
		}
		thenFacts, err = tb.body[len(tb.body)-1].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-1].body))
		if err != nil {
			return nil, nil, nil, err
		}
		// } else if tb.body[len(tb.body)-1].header.is(glob.KeywordIff) {
	} else if tb.body[len(tb.body)-1].header.is(glob.KeySymbolEquivalent) {
		if len(tb.body) <= 1 {
			return nil, nil, nil, fmt.Errorf("expect at least 2 body blocks")
		}

		if tb.body[0].header.is(glob.KeywordDom) {
			err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeywordDom)
			if err != nil {
				return nil, nil, nil, err
			}
			domFacts, err = tb.body[0].bodyBlockFacts(uniFactDepth, len(tb.body[0].body))
			if err != nil {
				return nil, nil, nil, err
			}

			if len(tb.body) <= 2 {
				return nil, nil, nil, fmt.Errorf("expect at least 2 body blocks")
			}

			err = tb.body[len(tb.body)-2].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
			if err != nil {
				return nil, nil, nil, err
			}
			thenFacts, err = tb.body[len(tb.body)-2].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-2].body))
			if err != nil {
				return nil, nil, nil, err
			}

		} else if tb.body[0].header.is(glob.KeySymbolRightArrow) {
			err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
			if err != nil {
				return nil, nil, nil, err
			}
			thenFacts, err = tb.body[0].bodyBlockFacts(uniFactDepth, len(tb.body[0].body))
			if err != nil {
				return nil, nil, nil, err
			}
		} else {
			if tb.body[len(tb.body)-2].header.is(glob.KeySymbolRightArrow) {

				domFacts, err = p.bodyBlockFacts(tb, uniFactDepth, len(tb.body)-2)
				if err != nil {
					return nil, nil, nil, err
				}

				// body[len(tb.body)-2] is =>:
				err = tb.body[len(tb.body)-2].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
				if err != nil {
					return nil, nil, nil, err
				}
				thenFacts, err = tb.body[len(tb.body)-2].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-2].body))
				if err != nil {
					return nil, nil, nil, err
				}
			} else {
				// 全部是 then
				thenFacts, err = p.bodyBlockFacts(tb, uniFactDepth, len(tb.body)-1)
				if err != nil {
					return nil, nil, nil, err
				}
			}

		}

		// thenFacts, err = p.bodyBlockFacts(tb, uniFactDepth, len(tb.body)-1)
		// if err != nil {
		// 	return nil, nil, nil, err
		// }

		// err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordIff)
		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, nil, nil, err
		}
		iffFacts, err = tb.body[len(tb.body)-1].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-1].body))
		if err != nil {
			return nil, nil, nil, err
		}
	} else {
		// if defaultSectionName == glob.KeywordThen {
		if defaultSectionName == glob.KeySymbolRightArrow {
			thenFacts, err = p.bodyBlockFacts(tb, uniFactDepth, len(tb.body))
			if err != nil {
				return nil, nil, nil, err
			}
			// } else if defaultSectionName == glob.KeywordIff {
		} else if defaultSectionName == glob.KeySymbolEquivalent {
			iffFacts, err = p.bodyBlockFacts(tb, uniFactDepth, len(tb.body))
			if err != nil {
				return nil, nil, nil, err
			}
		} else {
			return nil, nil, nil, fmt.Errorf("%s is not expected here", defaultSectionName)
		}
	}

	return domFacts, thenFacts, iffFacts, nil
}

func (p *Parser) knowPropStmt(tb *tokenBlock) (*ast.KnowPropStmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	namedUniFact, err := p.namedUniFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

func (p *Parser) proveInEachCaseStmt(tb *tokenBlock) (*ast.ProveInEachCaseStmt, error) {
	err := tb.header.skip(glob.KeywordProveInEachCase)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.is(glob.KeySymbolColon) {
		err := tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

		orFact, err := tb.body[0].orStmt()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		thenFacts := []ast.FactStmt{}
		// err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
		err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		
		for _, stmt := range tb.body[1].body {
			curStmt, err := p.factStmt(&stmt, UniFactDepth0)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			thenFacts = append(thenFacts, curStmt)
		}

		proofs := []ast.StmtSlice{}
		for i := 2; i < len(tb.body); i++ {
			proof := ast.StmtSlice{}

			err = tb.body[i].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			
			for _, stmt := range tb.body[i].body {
				curStmt, err := p.Stmt(&stmt)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				proof = append(proof, curStmt)
			}
			proofs = append(proofs, proof)
		}

		if len(proofs) != len(orFact.Facts) {
			return nil, parserErrAtTb(fmt.Errorf("prove in each case: expect %d proofs, but got %d. expect the number of proofs to be the same as the number of facts in the or fact", len(orFact.Facts), len(proofs)), tb)
		}

		return ast.NewProveInEachCaseStmt(orFact, thenFacts, proofs, tb.line), nil
	} else {
		orFact, err := tb.inlineOrFact()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		thenFacts := []ast.FactStmt{}
		for !tb.header.is(glob.KeySymbolColon) {
			fact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals([]string{glob.KeySymbolColon})
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			thenFacts = append(thenFacts, fact)
		}

		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		proofs := []ast.StmtSlice{}
		for i := range len(tb.body) {
			proof := ast.StmtSlice{}

			err = tb.body[i].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			
			for _, stmt := range tb.body[i].body {
				curStmt, err := p.Stmt(&stmt)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				proof = append(proof, curStmt)
			}
			proofs = append(proofs, proof)
		}

		if len(proofs) != len(orFact.Facts) {
			return nil, parserErrAtTb(fmt.Errorf("prove in each case: expect %d proofs, but got %d. expect the number of proofs to be the same as the number of facts in the or fact", len(orFact.Facts), len(proofs)), tb)
		}

		return ast.NewProveInEachCaseStmt(orFact, thenFacts, proofs, tb.line), nil
	}
}

func (p *Parser) proveCaseByCaseStmt(tb *tokenBlock) (*ast.ProveCaseByCaseStmt, error) {
	err := tb.header.skipKwAndColonCheckEOL(glob.KeywordProveCaseByCase)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	caseFacts := []*ast.SpecFactStmt{}
	thenFacts := ast.FactStmtSlice{}
	proofs := []ast.StmtSlice{}
	hasEncounteredCase := false

	for _, block := range tb.body {
		if block.header.is(glob.KeywordCase) {
			hasEncounteredCase = true

			// Skip "case" keyword
			err := block.header.skip(glob.KeywordCase)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			// Parse the specFact (condition)
			curStmt, err := p.specFactStmt(&block)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			// Skip the colon after specFact
			err = block.header.skip(glob.KeySymbolColon)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			caseFacts = append(caseFacts, curStmt)

			// Parse proof statements in the case block body
			proof := ast.StmtSlice{}
			
			for _, stmt := range block.body {
				curStmt, err := p.Stmt(&stmt)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				proof = append(proof, curStmt)
			}
			proofs = append(proofs, proof)
		} else {
			// This is a thenFacts block
			if hasEncounteredCase {
				return nil, parserErrAtTb(fmt.Errorf("prove_case_by_case: thenFacts can only appear before case blocks"), tb)
			}

			// Parse thenFacts (could be =>: section or inline facts)
			if block.header.is(glob.KeySymbolRightArrow) {
				err = block.header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}

				for _, stmt := range block.body {

    		curStmt, err := p.factStmt(&stmt, UniFactDepth0)
		if err != nil {
						return nil, parserErrAtTb(err, tb)
					}
     
				}
			} else {
				// Parse inline fact

					curStmt, err := p.factStmt(&block, UniFactDepth0)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
			}
		}
	}

	if len(caseFacts) == 0 {
		return nil, parserErrAtTb(fmt.Errorf("prove_case_by_case: at least one case block is required"), tb)
	}

	// Verify that the number of proofs matches the number of cases
	if len(proofs) != len(caseFacts) {
		return nil, parserErrAtTb(fmt.Errorf("prove_case_by_case: expect %d proofs, but got %d. expect the number of proofs to be the same as the number of case facts", len(caseFacts), len(proofs)), tb)
	}

	return ast.NewProveCaseByCaseStmt(caseFacts, thenFacts, proofs, tb.line), nil
}

func (p *Parser) param_paramSet_paramInSetFacts(tb *tokenBlock, endWith string, allowExceedEnd bool) ([]string, []ast.Obj, error) {
	params := []string{}
	setParams := []ast.Obj{}
	paramWithoutSetCount := 0

	if !tb.header.is(endWith) {
		for {
			param, err := tb.header.next()
			if err != nil {
				return nil, nil, err
			}

			// params = append(params, addPkgNameToString(param))
			params = append(params, param)

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				paramWithoutSetCount++
				continue
			}

			setParam, err := p.Obj(tb)
			if err != nil {
				return nil, nil, err
			}

			if paramWithoutSetCount == 0 {
				setParams = append(setParams, setParam)
			} else {
				for range paramWithoutSetCount + 1 {
					setParams = append(setParams, setParam)
				}
				paramWithoutSetCount = 0
			}

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				continue
			}

			if tb.header.is(endWith) || (allowExceedEnd && tb.header.ExceedEnd()) {
				break
			}

			return nil, nil, fmt.Errorf("expected ',' or '%s' but got '%s'", endWith, tb.header.strAtCurIndexPlus(0))
		}
	}

	if !allowExceedEnd || !tb.header.ExceedEnd() {
		err := tb.header.skip(endWith)
		if err != nil {
			return nil, nil, err
		}
	}

	// params 不能重复
	for i := range params {
		for j := i + 1; j < len(params); j++ {
			if params[i] == params[j] {
				return nil, nil, fmt.Errorf("parameters cannot be repeated, get duplicate parameter: %s", params[i])
			}
		}
	}

	// nth parameter set should not include nth to last parameter inside
	for i, setParam := range setParams {
		atomsInSetParam := ast.GetAtomsInObj(setParam)
		atomsInSetParamAsStr := make([]string, len(atomsInSetParam))
		for i, atom := range atomsInSetParam {
			atomsInSetParamAsStr[i] = string(atom)
		}

		for j := i; j < len(params); j++ {
			if slices.Contains(atomsInSetParamAsStr, params[j]) {
				return nil, nil, fmt.Errorf("the set %s of the parameter if index %d cannot include any parameters from the index %d to the last one (found parameter %s)", setParam, i, j, params[j])
			}
		}
	}

	return params, setParams, nil
}

func (p *Parser) getStringInDoubleQuotes(tb *tokenBlock) (string, error) {
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

func (p *Parser) proveStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordProve)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(tb.body) == 0 {
		return nil, fmt.Errorf("expect proof")
	}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip(glob.KeySymbolColon)
		proof := []ast.Stmt{}
		for _, stmt := range tb.body {

  		curStmt, err := p.Stmt(&stmt)
		if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
   
		}

		return ast.NewProveStmt(proof, tb.line), nil
	} else {
		factToCheck, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals([]string{glob.KeySymbolColon})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		proofs := []ast.Stmt{}
		for _, stmt := range tb.body {

  		curStmt, err := p.Stmt(&stmt)
		if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
   
		}

		return ast.NewClaimProveStmt(factToCheck, proofs, tb.line), nil
	}
}

// called by exist_prop and prop def

func (p *Parser) parseFactBodyWithHeaderNameAndUniFactDepth(tb *tokenBlock, headerName string, uniFactDepth uniFactEnum) ([]ast.FactStmt, error) {
	err := tb.header.skipKwAndColonCheckEOL(headerName)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	facts := []ast.FactStmt{}
	for _, stmt := range tb.body {
		curStmt, err := p.factStmt(&stmt, uniFactDepth)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		facts = append(facts, curStmt)
	}
	return facts, nil
}

// 要保证 fn 里的params 和 fn 里面的 uniFact 的params 是不一样的，否则可能出现严重的问题
func (p *Parser) defFnStmt(tb *tokenBlock, skipFn bool) (*ast.DefFnStmt, error) {
	if skipFn {
		err := tb.header.skip(glob.KeywordFn)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
	}

	decl, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
	
	retSet, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
	if asAtom, ok := retSet.(ast.Atom); ok {
		if string(asAtom) == glob.KeySymbolColon {
			return nil, fmt.Errorf(": is not allowed in return set")
		}
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip("")
		if tb.header.ExceedEnd() {
			domFacts, thenFacts, err = p.dom_and_section(tb, glob.KeySymbolRightArrow, glob.KeySymbolEquivalent)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
		} else {
			domFacts, err = tb.inlineFacts_untilWord_or_exceedEnd_notSkipWord(glob.KeySymbolRightArrow, []string{})
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			if !tb.header.is(glob.KeySymbolRightArrow) {
				return ast.NewDefFnStmt(string(decl.Name), ast.NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts, tb.line), tb.line), nil
			}

			err = tb.header.skip(glob.KeySymbolRightArrow)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			thenFacts, err = tb.inlineFacts_untilEndOfInline([]string{})
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
		}
	} else if tb.header.is(glob.KeySymbolRightArrow) {
		err = tb.header.skip(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		unitFacts, err := tb.inlineFacts_checkUniDepth1([]string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		thenFacts = append(thenFacts, unitFacts...)
	}

	return ast.NewDefFnStmt(string(decl.Name), ast.NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts, tb.line), tb.line), nil
}

func (p *Parser) claimPropStmt(tb *tokenBlock) (*ast.ClaimPropStmt, error) {
	namedUniFact, err := tb.body[0].namedUniFactStmt()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.body[1].header.is(glob.KeywordProve) {
		err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	} else if tb.body[1].header.is(glob.KeywordProveByContradiction) {
		panic("prove_by_contradiction is not supported for prop statement")
	} else {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}

	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	proofs := []ast.Stmt{}
	for _, stmt := range tb.body[1].body {

 		curStmt, err := p.Stmt(&stmt)
	if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
  
	}

	if len(proofs) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	// return ast.NewClaimPropStmt(ast.NewDefPropStmt(declHeader, []ast.FactStmt{}, iffFacts, thenFacts), proofs, isProve), nil
	return ast.NewClaimPropStmt(ast.NewDefPropStmt(namedUniFact.DefPropStmt.DefHeader, namedUniFact.DefPropStmt.DomFacts, namedUniFact.DefPropStmt.IffFacts, namedUniFact.DefPropStmt.ThenFacts, tb.line), proofs, tb.line), nil
}

func (p *Parser) claimExistPropStmt(tb *tokenBlock) (*ast.ClaimExistPropStmt, error) {
	if len(tb.body) != 3 {
		return nil, fmt.Errorf("expect 3 body blocks")
	}

	existProp, err := tb.body[0].atExistPropDefStmt()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	proofs := []ast.Stmt{}
	for _, stmt := range tb.body[1].body {

 		curStmt, err := p.Stmt(&stmt)
	if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
  
	}

	err = tb.body[2].header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	haveObj := []ast.Obj{}
	for !tb.body[2].header.ExceedEnd() {
		
		curObj, err := p.Obj(&tb.body[2])
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		haveObj = append(haveObj, curObj)
	}

	if len(proofs) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	return ast.NewClaimExistPropStmt(existProp, proofs, haveObj, tb.line), nil
}

func (p *Parser) dom_and_section(tb *tokenBlock, kw string, kw_should_not_exist_in_body string) ([]ast.FactStmt, []ast.FactStmt, error) {
	if len(tb.body) == 0 {
		return nil, nil, fmt.Errorf("expect dom or section")
	}

	var err error
	domFacts, sectionFacts := []ast.FactStmt{}, []ast.FactStmt{}

	if tb.body[len(tb.body)-1].header.is(kw_should_not_exist_in_body) {
		return nil, nil, fmt.Errorf("%s section is not allowed to be the last section", kw_should_not_exist_in_body)
	}

	// there are 5 cases: 1. no dom, just section 2. dom and section without dom specification 3. dom and section with both specification 4. just dom 5. just section
	if !tb.body[0].header.is(glob.KeywordDom) && !tb.body[len(tb.body)-1].header.is(kw) {
		for _, stmt := range tb.body {

  		curStmt, err := p.factStmt(&stmt, UniFactDepth1)
		if err != nil {
				return nil, nil, parserErrAtTb(err, tb)
			}
   
		}
		return domFacts, sectionFacts, nil
	} else if !tb.body[0].header.is(glob.KeywordDom) && tb.body[len(tb.body)-1].header.is(kw) {
		for i := range len(tb.body) - 1 {

  		curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
		if err != nil {
				return nil, nil, parserErrAtTb(err, tb)
			}
   
		}
		sectionFacts, err = tb.body[len(tb.body)-1].parseFactBodyWithHeaderNameAndUniFactDepth(kw, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		} else if len(tb.body) == 2 && tb.body[0].header.is(glob.KeywordDom) && tb.body[1].header.is(kw) {
		domFacts, err = tb.body[0].parseFactBodyWithHeaderNameAndUniFactDepth(glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		}
		sectionFacts, err = tb.body[1].parseFactBodyWithHeaderNameAndUniFactDepth(kw, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		} else if len(tb.body) == 1 && tb.body[0].header.is(glob.KeywordDom) {
		domFacts, err = tb.body[0].parseFactBodyWithHeaderNameAndUniFactDepth(glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		} else if len(tb.body) == 1 && tb.body[0].header.is(kw) {
		sectionFacts, err = tb.body[0].parseFactBodyWithHeaderNameAndUniFactDepth(kw, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		} else {
		return nil, nil, fmt.Errorf("expect dom section and %s section", kw)
	}
}

func (p *Parser) intentionalSetBody(tb *tokenBlock) (string, ast.Obj, []*ast.SpecFactStmt, error) {
	err := tb.header.skip(glob.KeySymbolLeftCurly)
	if err != nil {
		return "", nil, nil, parserErrAtTb(err, tb)
	}

	param, err := tb.header.next()
	if err != nil {
		return "", nil, nil, parserErrAtTb(err, tb)
	}
	
	parentSet, err := p.Obj(tb)
	if err != nil {
		return "", nil, nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return "", nil, nil, parserErrAtTb(err, tb)
	}

	proofs := []*ast.SpecFactStmt{}
	for !tb.header.is(glob.KeySymbolRightCurly) {
		curStmt, err := p.specFactStmt(tb)
		if err != nil {
			return "", nil, nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
		tb.header.skipIfIs(glob.KeySymbolComma)
	}

	err = tb.header.skip(glob.KeySymbolRightCurly)
	if err != nil {
		return "", nil, nil, parserErrAtTb(err, tb)
	}

func (p *Parser) fact(tb *tokenBlock) (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordNot) {
		return p.specFactStmt(tb)
	}

	if tb.header.is(glob.KeywordExist) {
		return p.existFactStmt(tb, true)
	}

	if tb.header.is(glob.FuncFactPrefix) {
		ret, err := p.pureFuncSpecFact(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		} else {
		ret, err := p.relaFact_intensionalSetFact_enumStmt_equals(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
}

func (p *Parser) relaFact_intensionalSetFact_enumStmt_equals(tb *tokenBlock) (ast.FactStmt, error) {
	var ret *ast.SpecFactStmt
	
	obj, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	opt, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if opt == glob.FuncFactPrefix {
		propName, err := tb.notNumberAtom()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if tb.header.ExceedEnd() {
			ret = ast.NewSpecFactStmt(ast.TruePure, propName, []ast.Obj{obj}, tb.line)
		} else {
			
			obj2, err := p.Obj(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			params := []ast.Obj{obj, obj2}

			ret = ast.NewSpecFactStmt(ast.TruePure, propName, params, tb.line)
		}
		// } else if opt == glob.KeySymbolEqual && tb.header.is(glob.KeySymbolLeftCurly) {
		// 	return tb.enumStmt_or_intensionalSetStmt_or_DomOf(obj)
	} else if glob.IsBuiltinInfixRelaPropSymbol(opt) {
		
		obj2, err := p.Obj(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if opt == glob.KeySymbolEqual {
			// 循环地看下面一位是不是 = ，直到不是
			if tb.header.is(glob.KeySymbolEqual) {
				return tb.relaEqualsFactStmt(obj, obj2)
			}
		}

		// 必须到底了
		if !tb.header.ExceedEnd() {
			// or 的情况
			if tb.header.is(glob.KeywordOr) {
				return tb.inlineOrFactWithFirstFact(ret)
			}

			return nil, fmt.Errorf("expect end of line")
		}

		params := []ast.Obj{obj, obj2}

		ret = ast.NewSpecFactStmt(ast.TruePure, ast.Atom(opt), params, tb.line)
	} else {
		return nil, fmt.Errorf("expect relation prop")
	}

	// 这里加入语法糖：!= 等价于 not =，好处是我 = 有 commutative的性质，我不用额外处理 != 了
	if ret.NameIs(glob.KeySymbolNotEqual) {
		ret.TypeEnum = ast.FalsePure
		ret.PropName = ast.Atom(glob.KeySymbolEqual)
	}

	return ret, nil
}

// func (p *Parser) enumStmt_or_intensionalSetStmt_or_DomOf(tb *tokenBlock, obj ast.Obj) (ast.FactStmt, error) {
// 	// if tb.header.is(glob.KeySymbolLeftCurly) {
// 	// 	return tb.enumFactualStmt(obj)
// 	// } else {
// 	// 	return tb.intensionalSetFactualStmt(obj)
// 	// }

// 	err := tb.header.skip(glob.KeySymbolLeftCurly)
// 	if err != nil {
// 		return nil, fmt.Errorf("")
// 	}

// 	if tb.header.is(glob.KeySymbolRightCurly) {
// 		err = tb.header.skip(glob.KeySymbolRightCurly)
// 		if err != nil {
// 			return nil, fmt.Errorf("")
// 		}

// 		return ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, ast.MakeEnumSetObj([]ast.Obj{})}, tb.line), nil
// 	}

// 	leftmost, err := p.Obj(tb)
// 		return nil, fmt.Errorf("")
// 	}

// 	if tb.header.is(glob.KeySymbolComma) || tb.header.is(glob.KeySymbolRightCurly) {
// 		enumItems := []ast.Obj{leftmost}
// 		tb.header.skipIfIs(glob.KeySymbolComma) // 不能是 err = tb.header.skip(glob.KeySymbolComma) 因为这样会跳过 right curly
// 		for !tb.header.is(glob.KeySymbolRightCurly) {
// 			curItem, err := p.Obj(tb)
// 				return nil, fmt.Errorf("")
// 			}
// 			enumItems = append(enumItems, curItem)
// 			tb.header.skipIfIs(glob.KeySymbolComma)
// 		}

// 		err = tb.header.skip(glob.KeySymbolRightCurly)
// 		if err != nil {
// 			return nil, fmt.Errorf("")
// 		}

// 		return ast.NewSpecFactStmt(ast.TruePure, ast.Atom(glob.KeySymbolEqual), []ast.Obj{obj, ast.MakeEnumSetObj(enumItems)}, tb.line), nil
// 	} else {
// 		if _, ok := leftmost.(ast.Atom); !ok {
// 			return nil, fmt.Errorf("expect obj atom")
// 		} else {
// 			if glob.IsValidUserDefinedNameWithoutPkgName(string(leftmost.(ast.Atom))) != nil {
// 				return nil, fmt.Errorf("expect obj atom without pkg name")
// 			}
// 		}

// 		parentSet, err := p.Obj(tb)
// 			return nil, parserErrAtTb(err, tb)
// 		}

// 		err = tb.header.skip(glob.KeySymbolColon)
// 		if err != nil {
// 			return nil, parserErrAtTb(err, tb)
// 		}

// 		proofs := []*ast.SpecFactStmt{}
// 		for !tb.header.is(glob.KeySymbolRightCurly) {
// 			curStmt, err := p.specFactStmt(tb)
// 			if err != nil {
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			proofs = append(proofs, curStmt)
// 			tb.header.skipIfIs(glob.KeySymbolComma)
// 		}

// 		err = tb.header.skip(glob.KeySymbolRightCurly)
// 		if err != nil {
// 			return nil, fmt.Errorf("")
// 		}

// 		return ast.NewIntensionalSetStmt(obj, string(leftmost.(ast.Atom)), parentSet, proofs, tb.line), nil
// 	}
// }

func (p *Parser) proveByEnum(tb *tokenBlock) (*ast.ProveByEnumStmt, error) {
	err := tb.header.skip(glob.KeywordProveByEnum)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// param paramSet pairs
	params, paramSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolRightBrace, false)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Use the new parseDomThenProve function to handle all three cases:
	// 1. dom:, =>:, prove: (all three sections)
	// 2. =>:, prove: (no dom section)
	// 3. =>: (only then section, no dom and no prove)
	domFacts, thenFacts, proofs, err := parseDomThenProve(tb.body)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	uniFact := ast.NewUniFact(params, paramSets, domFacts, thenFacts, tb.line)
	return ast.NewProveByEnumStmt(uniFact, proofs, tb.line), nil
}

func (p *Parser) bodyOfKnowProp(tb *tokenBlock) ([]ast.FactStmt, []ast.FactStmt, error) {
	var err error
	iffFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}

	// if tb.body[len(tb.body)-1].header.is(glob.KeywordThen) {
	if tb.body[len(tb.body)-1].header.is(glob.KeySymbolRightArrow) {
		for i := range len(tb.body) - 1 {
			iffFact, err := p.factStmt(&tb.body[i], UniFactDepth1)
			if err != nil {
				return nil, nil, parserErrAtTb(err, tb)
			}
			iffFacts = append(iffFacts, iffFact)
		}

		// err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		}

		for _, stmt := range tb.body[len(tb.body)-1].body {
			curStmt, err := p.factStmt(&stmt, UniFactDepth1)
			if err != nil {
				return nil, nil, parserErrAtTb(err, tb)
			}
			thenFacts = append(thenFacts, curStmt)
		}

		return iffFacts, thenFacts, nil
	} else {
		for i := range len(tb.body) {
			thenFact, err := p.factStmt(&tb.body[i], UniFactDepth1)
			if err != nil {
				return nil, nil, parserErrAtTb(err, tb)
			}
			thenFacts = append(thenFacts, thenFact)
		}

		return iffFacts, thenFacts, nil
	}
}

func (p *Parser) haveObjInNonEmptySetStmt(tb *tokenBlock) (*ast.HaveObjInNonEmptySetStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	objNames, objSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolColon, true)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(objNames) == 0 {
		return nil, fmt.Errorf("expect at least one object")
	}

	return ast.NewHaveObjInNonEmptySetStmt(objNames, objSets, tb.line), nil
}

func (p *Parser) haveSetStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeywordSet)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	haveSetName, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// err = tb.header.skip(glob.KeySymbolColonEqual)
	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Check if next token is "cart"
	if tb.header.is(glob.KeywordCart) {
		// Parse cart(...)
  
		rightObj, err := p.Obj(tb)
	if err != nil {
   return nil, parserErrAtTb(err, tb)
  }

		cartObj, ok := rightObj.(*ast.FnObj)
		if !ok {
			return nil, fmt.Errorf("expected cart to be FnObj")
		}

		if !ast.IsFn_WithHeadName(rightObj, glob.KeywordCart) {
			return nil, fmt.Errorf("expected cart function call")
		}

		// Check end of line
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

		return ast.NewHaveCartSetStmt(haveSetName, cartObj, tb.line), nil
	}
	
	obj, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if ast.IsEnumSetObj(obj) {
		return ast.NewHaveEnumSetStmt(haveSetName, obj.(*ast.FnObj), tb.line), nil
	} else if ast.IsIntensionalSetObj(obj) {
		param, parentSet, facts, err := GetParamParentSetFactsFromIntensionalSet(obj.(*ast.FnObj))
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		} else {
		return nil, fmt.Errorf("expect enum set or intensional set")
	}
}

func (p *Parser) haveSetFnStmt(tb *tokenBlock) (ast.Stmt, error) {
	tb.header.skip(glob.KeywordHave)
	tb.header.skip(glob.KeywordSet)
	tb.header.skip(glob.KeywordFn)

	declHeader, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// err = tb.header.skip(glob.KeySymbolColonEqual)
	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	param, parentSet, proofs, err := p.intentionalSetBody(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

func (p *Parser) haveCartWithDimStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordHaveCartWithDim)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	name, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
	
	cartDim, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	param, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Parse body: forall statements and optional case-by-case structure
	facts := []ast.FactStmt{}

	// 第一个 block 形如 =>: ... 这样的
	err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for _, stmt := range tb.body[0].body {

 		curStmt, err := p.factStmt(&stmt, UniFactDepth0)
	if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
  
	}

	// 分类：如果下面body[1]是case开头的，那就说明是case-by-case结构；否则是普通结构
	if len(tb.body) != 3 {
		return nil, fmt.Errorf("expect 3 blocks of %s when not defining case-by-case, but got %d", glob.KeywordHaveCartWithDim, len(tb.body))
	}

	proofs := []ast.Stmt{}
	err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for _, stmt := range tb.body[1].body {

 		curStmt, err := p.Stmt(&stmt)
	if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
  
	}

	// 最后一行是 =
	err = tb.body[len(tb.body)-1].header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
 
	equalTo, err := p.Obj(&tb.body[2])
	if err != nil {
  return nil, parserErrAtTb(err, tb)
 }

func (p *Parser) namedUniFactStmt(tb *tokenBlock) (*ast.NamedUniFactStmt, error) {
	var err error
	err = tb.header.skip(glob.KeySymbolAt)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	declHeader, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.ExceedEnd() {
		iffFacts, thenFacts, err := p.bodyOfKnowProp(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}, iffFacts, thenFacts, tb.line), tb.line), nil
	} else {
		iffFact, err := tb.inlineDomFactInUniFactInterface([]string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		thenFact, err := tb.thenFacts_SkipEnd_Semicolon_or_EOL([]string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}, iffFact, thenFact, tb.line), tb.line), nil
	}
}

// TODO: 让 forall 里也能有它
func (p *Parser) equalsFactStmt(tb *tokenBlock) (*ast.EqualsFactStmt, error) {
	tb.header.skip(glob.KeySymbolEqual)

	if tb.header.is(glob.KeySymbolColon) {
		err := tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if tb.header.ExceedEnd() {
			params := make(ast.ObjSlice, 0, len(tb.body))
			for _, param := range tb.body {
    
				param, err := p.Obj(&param)
		if err != nil {
     return nil, parserErrAtTb(err, tb)
    }
				params = append(params, param)
			}

			if len(params) < 2 {
				return nil, fmt.Errorf("expect at least two params")
			}

			return ast.NewEqualsFactStmt(params, tb.line), nil
		} else {
			params := []ast.Obj{}
			for {
				
				curObj, err := p.Obj(tb)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				params = append(params, curObj)

				if tb.header.is(glob.KeySymbolComma) {
					tb.header.skip(glob.KeySymbolComma)
					continue
				}

				if tb.header.ExceedEnd() {
					break
				}
			}

			return ast.NewEqualsFactStmt(params, tb.line), nil
		}
	} else {
		err := tb.header.skip(glob.KeySymbolLeftBrace)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		params := []ast.Obj{}
		for {
   
			curObj, err := p.Obj(tb)
	if err != nil {
    return nil, parserErrAtTb(err, tb)
   }
			params = append(params, curObj)

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				continue
			}

			if tb.header.is(glob.KeySymbolRightBrace) {
				tb.header.skip(glob.KeySymbolRightBrace)
				break
			}
		}

		return ast.NewEqualsFactStmt(params, tb.line), nil
	}
}

func (p *Parser) knowExistPropStmt(tb *tokenBlock) (*ast.KnowExistPropStmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	existProp, err := p.atExistPropDefStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

// func (p *Parser) latexStmt(tb *tokenBlock) (ast.Stmt, error) {
// 	comment := tb.header.strAtCurIndexPlus(1)
// 	tb.header.skip("")
// 	tb.header.skip("")

// 	return ast.NewLatexStmt(comment, tb.line), nil
// }

func (p *Parser) fnTemplateStmt(tb *tokenBlock) (ast.Stmt, error) {
	tb.header.skipNext()
	defHeader, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	if len(tb.body) == 1 {
		fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := tb.body[0].fnInFnTemplateStmt()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		newFnTStruct := ast.NewFnTStruct(fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, tb.body[0].line)

		return ast.NewFnTemplateStmt(defHeader, []ast.FactStmt{}, newFnTStruct, tb.line), nil
	} else if len(tb.body) >= 2 {
		if tb.body[0].header.is(glob.KeywordDom) {
			err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeywordDom)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			templateDomFacts, err := tb.body[0].bodyFacts(UniFactDepth1)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := tb.body[1].fnInFnTemplateStmt()
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			newFnTStruct := ast.NewFnTStruct(fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, tb.body[1].line)

			return ast.NewFnTemplateStmt(defHeader, templateDomFacts, newFnTStruct, tb.line), nil
		} else {
			templateDomFacts := []ast.FactStmt{}
			for i := range len(tb.body) - 1 {

   		curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
		if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
    
			}

			fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := tb.body[len(tb.body)-1].fnInFnTemplateStmt()
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			newFnTStruct := ast.NewFnTStruct(fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, tb.body[len(tb.body)-1].line)

			return ast.NewFnTemplateStmt(defHeader, templateDomFacts, newFnTStruct, tb.line), nil
		}
	} else {
		return nil, fmt.Errorf("expect one or two body blocks")
	}

}

func (p *Parser) fnInFnTemplateStmt(tb *tokenBlock) ([]string, []ast.Obj, ast.Obj, []ast.FactStmt, []ast.FactStmt, error) {
	var err error

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, nil, nil, nil, nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, nil, nil, nil, nil, parserErrAtTb(err, tb)
	}

	fnParams, fnParamSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolRightBrace, false)
	if err != nil {
		return nil, nil, nil, nil, nil, parserErrAtTb(err, tb)
	}
 
	fnRetSet, err := p.Obj(tb)
		if err != nil {
			return nil, nil, nil, nil, nil, parserErrAtTb(err, tb)
		}

	if tb.header.ExceedEnd() {
		return fnParams, fnParamSets, fnRetSet, []ast.FactStmt{}, []ast.FactStmt{}, nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, nil, nil, nil, nil, parserErrAtTb(err, tb)
	}

	// domFacts, thenFacts, err := p.dom_and_section(tb, glob.KeywordThen, glob.KeywordIff)
	// domFacts, thenFacts, err := p.dom_and_section(tb, glob.KeySymbolEqualLarger, glob.KeywordIff)
	domFacts, thenFacts, err := p.dom_and_section(tb, glob.KeySymbolRightArrow, glob.KeySymbolEquivalent)
	if err != nil {
		return nil, nil, nil, nil, nil, parserErrAtTb(err, tb)
	}

func (p *Parser) clearStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordClear)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ast.NewClearStmt(tb.line), nil
}

func (p *Parser) doNothingStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordDoNothing)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ast.NewDoNothingStmt(tb.line), nil
}

func (p *Parser) factsStmt(tb *tokenBlock) (ast.Stmt, error) {
	if tb.GetEnd() != glob.KeySymbolColon { // 因为可能是 forall : 这样的
		facts, err := tb.inlineFacts_checkUniDepth0([]string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if len(facts) == 1 {
			return facts[0], nil
		}

		return ast.NewInlineFactsStmt(facts, tb.line), nil
	} else {
		return p.factStmt(tb, UniFactDepth0)
	}
}

func (p *Parser) claimNamedUniFactInline(tb *tokenBlock) (ast.Stmt, error) {
	var err error
	var namedUniFact *ast.NamedUniFactStmt

	if tb.header.is(glob.KeySymbolAt) {
		// 有点小问题，最好必须要规定是named inline
		namedUniFact, err = p.namedUniFactStmt(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
	}

	if tb.header.is(glob.KeySymbolColon) {
		err := tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

	} else {
		// return ast.NewClaimProveStmt(fact, []ast.Stmt{}, tb.line), nil
		return nil, fmt.Errorf("expect proof after claim")
	}

	proof := []ast.Stmt{}
	for _, block := range tb.body {

 		curStmt, err := p.Stmt(&block)
		
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proof = append(proof, curStmt)
	}

	if len(proof) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	return ast.NewClaimPropStmt(namedUniFact.DefPropStmt, proof, tb.line), nil
}

func (p *Parser) proveByInductionStmt(tb *tokenBlock) (*ast.ProveByInductionStmt, error) {
	err := tb.header.skip(glob.KeywordProveByInduction)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	fact, err := p.specFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	param, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.is(glob.KeySymbolComma) {
		err = tb.header.skip(glob.KeySymbolRightBrace)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		} else {
		err = tb.header.skip(glob.KeySymbolComma)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
  
		start, err := p.Obj(tb)
	if err != nil {
   return nil, parserErrAtTb(err, tb)
  }

		err = tb.header.skip(glob.KeySymbolRightBrace)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
}

func (p *Parser) haveObjFromCartSetStmt(tb *tokenBlock) (*ast.HaveObjFromCartSetStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Parse object name
	objName, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Parse cart(...)
 
	cartSetObj, err := p.Obj(tb)
	if err != nil {
  return nil, parserErrAtTb(err, tb)
 }

	cartSet, ok := cartSetObj.(*ast.FnObj)
	if !ok {
		return nil, parserErrAtTb(fmt.Errorf("expected cart to be FnObj"), tb)
	}

	if !ast.IsFn_WithHeadName(cartSetObj, glob.KeywordCart) {
		return nil, parserErrAtTb(fmt.Errorf("expected cart function call"), tb)
	}

	// Parse = ...
	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
 
	equalTo, err := p.Obj(tb)
	if err != nil {
  return nil, parserErrAtTb(err, tb)
 }

	// Check end of line
	if !tb.header.ExceedEnd() {
		return nil, parserErrAtTb(fmt.Errorf("expect end of line"), tb)
	}

	return ast.NewHaveObjFromCartSetStmt(objName, cartSet, equalTo, tb.line), nil
}

func (p *Parser) haveObjEqualStmt(tb *tokenBlock) (*ast.HaveObjEqualStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	objectEqualTos := []ast.Obj{}

	objectNames, setSlice, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolEqual, false)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for !tb.header.ExceedEnd() {
		objectEqualTo, err := p.Obj(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		objectEqualTos = append(objectEqualTos, objectEqualTo)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	if len(objectEqualTos) != len(setSlice) {
		return nil, fmt.Errorf("number of objects and sets do not match")
	}

	return ast.NewHaveObjEqualStmt(objectNames, objectEqualTos, setSlice, tb.line), nil
}

func (p *Parser) haveFnEqualStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	defHeader, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
 
	retSet, err := p.Obj(tb)
	if err != nil {
  return nil, parserErrAtTb(err, tb)
 }

	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.is(glob.KeySymbolColon) {
  
		equalTo, err := p.Obj(tb)
	if err != nil {
   return nil, parserErrAtTb(err, tb)
  }

		return ast.NewHaveFnEqualStmt(defHeader, retSet, equalTo, tb.line), nil
	} else {
		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		caseByCaseFacts := []*ast.SpecFactStmt{}
		caseByCaseEqualTo := []ast.Obj{}
		for _, block := range tb.body {
			err := block.header.skip(glob.KeywordCase)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			curStmt, err := p.specFactStmt(&block)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			err = block.header.skip(glob.KeySymbolColon)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
   
			obj, err := p.Obj(&block)
	if err != nil {
    return nil, parserErrAtTb(err, tb)
   }
			caseByCaseEqualTo = append(caseByCaseEqualTo, obj)
			caseByCaseFacts = append(caseByCaseFacts, curStmt)
		}

		return &ast.HaveFnEqualCaseByCaseStmt{
			DefHeader:         defHeader,
			RetSet:            retSet,
			CaseByCaseFacts:   caseByCaseFacts,
			CaseByCaseEqualTo: caseByCaseEqualTo,
			Line:              tb.line,
		}, nil
	}
}

// func (p *Parser) haveFnLiftStmt(tb *tokenBlock) (*ast.HaveFnLiftStmt, error) {
// 	err := tb.header.skip(glob.KeywordHave)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeywordFn)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	fnName, err := tb.header.next()
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolEqual)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeywordLift)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolLeftBrace)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	opt, err := p.Obj(tb)
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolComma)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	domainOfEachParamOfGivenFn := []ast.Obj{}
// 	for !tb.header.is(glob.KeySymbolRightBrace) {

// 		curDomain, err := p.Obj(tb)
// 			return nil, parserErrAtTb(err, tb)
// 		}

// 		domainOfEachParamOfGivenFn = append(domainOfEachParamOfGivenFn, curDomain)

// 		done, err := tb.expectAndSkipCommaOr(glob.KeySymbolRightBrace)
// 		if err != nil {
// 			return nil, err
// 		}
// 		if done {
// 			break
// 		}
// 	}

// 	err = tb.header.skip(glob.KeySymbolRightBrace)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	return ast.NewHaveFnLiftStmt(fnName, opt, domainOfEachParamOfGivenFn, tb.line), nil
// }

func (p *Parser) haveFnStmt(tb *tokenBlock) (ast.Stmt, error) {
	var err error

	err = tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(tb.body) < 1 {
		return nil, fmt.Errorf("expect at least 1 body block")
	}

	defFnStmt, err := tb.body[0].defFnStmt(false)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Check if it's prove or case-by-case
	if len(tb.body) >= 2 && tb.body[1].header.is(glob.KeywordProve) {
		if len(tb.body) != 3 {
			return nil, fmt.Errorf("expect 3 body blocks for have fn with prove")
		}
		err = tb.body[1].header.skip(glob.KeywordProve)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		proof := []ast.Stmt{}
		for _, block := range tb.body[1].body {

  		curStmt, err := p.Stmt(&block)
			
				return nil, parserErrAtTb(err, tb)
			}
			proof = append(proof, curStmt)
		}

		err = tb.body[2].header.skip(glob.KeySymbolEqual)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		haveObjSatisfyFn, err := p.Obj(&tb.body[2])
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		} else if len(tb.body) >= 2 && tb.body[1].header.is(glob.KeywordCase) {
		// Case-by-case structure: body[0] is defFnStmt, body[1..n] are case/equal pairs
		if (len(tb.body)-1)%2 != 0 {
			return nil, fmt.Errorf("expect even number of body blocks after defFnStmt for case-by-case (got %d)", len(tb.body)-1)
		}

		cases := []*ast.SpecFactStmt{}
		proofs := []ast.StmtSlice{}
		EqualTo := []ast.Obj{}
		for i := 1; i < len(tb.body); i++ {
			if (i-1)%2 == 0 {
				// Case block
				err := tb.body[i].header.skip(glob.KeywordCase)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				curStmt, err := tb.body[i].specFactStmt()
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				cases = append(cases, curStmt)
				err = tb.body[i].header.skip(glob.KeySymbolColon)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				curProof := ast.StmtSlice{}
				for _, block := range tb.body[i].body {

    		curStmt, err := p.Stmt(&block)
					
						return nil, parserErrAtTb(err, tb)
					}
					curProof = append(curProof, curStmt)
				}
				proofs = append(proofs, curProof)
			} else {
				// Equal block
				err := tb.body[i].header.skip(glob.KeySymbolEqual)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				curHaveObj, err := p.Obj(&tb.body[i])
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				EqualTo = append(EqualTo, curHaveObj)
			}
		}

		return ast.NewHaveFnCaseByCaseStmt(defFnStmt, cases, proofs, EqualTo, tb.line), nil
	} else {
		return nil, fmt.Errorf("expect 'prove:' or 'case' after defFnStmt in have fn statement")
	}
}

func (p *Parser) relaEqualsFactStmt(tb *tokenBlock, obj, fc2 ast.Obj) (*ast.EqualsFactStmt, error) {
	equalsItem := []ast.Obj{obj, fc2}
	for tb.header.is(glob.KeySymbolEqual) {
		tb.header.skip(glob.KeySymbolEqual)
  
		obj3, err := p.Obj(tb)
	if err != nil {
   return nil, parserErrAtTb(err, tb)
  }
		equalsItem = append(equalsItem, obj3)
	}
	return ast.NewEqualsFactStmt(equalsItem, tb.line), nil
}

// func (p *Parser) markdownStmt(tb *tokenBlock) (ast.Stmt, error) {
// 	comment := tb.header.strAtCurIndexPlus(1)
// 	tb.header.skip("")
// 	tb.header.skip("")

// 	return ast.NewMarkdownStmt(comment, tb.line), nil
// }

func (p *Parser) atExistPropDefStmt(tb *tokenBlock) (*ast.DefExistPropStmt, error) {
	err := tb.header.skip(glob.KeySymbolAt)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	existParams, existParamSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeywordSt, false)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	header, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	iffFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}
	if tb.body[len(tb.body)-1].header.is(glob.KeySymbolRightArrow) {
		for i := range len(tb.body) - 1 {
			block := tb.body[i]

  		curStmt, err := p.factStmt(&block, UniFactDepth1)
		if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
   
		}

		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		for i := range tb.body[len(tb.body)-1].body {
			curStmt, err := tb.body[len(tb.body)-1].body[i].factStmt(UniFactDepth1)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			thenFacts = append(thenFacts, curStmt)
		}
	} else {
		for i := range len(tb.body) {

  		curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
		if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
   
	}

	return ast.NewDefExistPropStmt(ast.NewExistPropDef(header, []ast.FactStmt{}, iffFacts, thenFacts, tb.line), existParams, existParamSets, tb.line), nil
}

// Example:
// prove_in_range(a, 1, 3):
//
//	a > 0
//
// prove_in_range(a, 1, 3):
//
//	dom:
//	    ...
//	=>:
//	    ...
//	prove:
//	    ...
//
// prove_in_range(a, 1, 3):
//
//	dom:
//	    ...
//	=>:
//	    ...
//
// prove_in_range(a, 1, 3):
//
//	...
//	prove:
//	    ...
func (p *Parser) proveInRangeStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordProveInRange)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	param, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
 
	start, err := p.Obj(tb)
	if err != nil {
  return nil, parserErrAtTb(err, tb)
 }

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
 
	end, err := p.Obj(tb)
	if err != nil {
  return nil, parserErrAtTb(err, tb)
 }

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}
	proofs := []ast.Stmt{}

	// Parse body sections: dom, =>, prove
	if len(tb.body) == 0 {
		// Empty body, all remain empty
	} else if tb.body[0].header.is(glob.KeywordDom) {
		// First section is dom: must be dom, =>, (optional) prove
		if len(tb.body) < 2 || len(tb.body) > 3 {
			return nil, parserErrAtTb(fmt.Errorf("when dom is first, body must have 2 or 3 sections (dom, =>, [prove])"), tb)
		}

		// Parse dom section
		err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeywordDom)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		for _, stmt := range tb.body[0].body {

  		curStmt, err := p.factStmt(&stmt, UniFactDepth1)
		if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
   
		}

		// Parse => section
		if !tb.body[1].header.is(glob.KeySymbolRightArrow) {
			return nil, parserErrAtTb(fmt.Errorf("second section must be => when dom is first"), tb)
		}
		err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		for _, stmt := range tb.body[1].body {

  		curStmt, err := p.factStmt(&stmt, UniFactDepth1)
		if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
   
		}

		// Parse optional prove section
		if len(tb.body) == 3 {
			if !tb.body[2].header.is(glob.KeywordProve) {
				return nil, parserErrAtTb(fmt.Errorf("third section must be prove when dom is first"), tb)
			}
			err = tb.body[2].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			for _, stmt := range tb.body[2].body {

   		curStmt, err := p.Stmt(&stmt)
		if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
    
			}
		}
		// If len(tb.body) == 2, prove remains nil
	} else {
		// First section is not dom
		// Check if last section is prove
		lastIdx := len(tb.body) - 1
		hasProve := tb.body[lastIdx].header.is(glob.KeywordProve)

		if hasProve {
			// All sections before prove are then
			for i := 0; i < lastIdx; i++ {
				if !tb.body[i].header.is(glob.KeySymbolRightArrow) {
					return nil, parserErrAtTb(fmt.Errorf("when dom is not first, all sections before prove must be =>"), tb)
				}
				err = tb.body[i].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				for _, stmt := range tb.body[i].body {

    		curStmt, err := p.factStmt(&stmt, UniFactDepth1)
		if err != nil {
						return nil, parserErrAtTb(err, tb)
					}
     
				}
			}

			// Parse prove section
			err = tb.body[lastIdx].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			for _, stmt := range tb.body[lastIdx].body {

   		curStmt, err := p.Stmt(&stmt)
		if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
    
			}
		} else {
			// No prove section, all are direct fact statements (thenFacts)
			for i := range len(tb.body) {
				// Check if it's a => section or a direct fact statement
				if tb.body[i].header.is(glob.KeySymbolRightArrow) {
					// It's a => section
					err = tb.body[i].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
					if err != nil {
						return nil, parserErrAtTb(err, tb)
					}
					for _, stmt := range tb.body[i].body {
						curStmt, err := p.factStmt(&stmt, UniFactDepth1)
						if err != nil {
							return nil, parserErrAtTb(err, tb)
						}
						thenFacts = append(thenFacts, curStmt)
					}
				} else {
					// It's a direct fact statement (no => needed)
					curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
					if err != nil {
						return nil, parserErrAtTb(err, tb)
					}
					thenFacts = append(thenFacts, curStmt)
				}
			}
			// prove remains nil, dom remains empty
		}
	}

	return ast.NewProveInRangeStmt(param, start, end, domFacts, thenFacts, proofs, tb.line), nil
}

// parse prove_in_range_set(start, end, x S): then_fact prove:
// func (p *Parser) proveInRangeSetStmt(tb *tokenBlock) (ast.Stmt, error) {
// 	err := tb.header.skip(glob.KeywordProveInRangeSet)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolLeftBrace)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	startAsInt, err := p.skipInt(tb)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolComma)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	endAsInt, err := p.skipInt(tb)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolComma)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	param, err := tb.header.next()
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	paramSet, err := p.Obj(tb)
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolRightBrace)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolColon)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	if tb.body[len(tb.body)-1].header.is(glob.KeywordProve) {
// 		thenFacts := []ast.FactStmt{}
// 		for i := range len(tb.body) - 1 {

// 			curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			thenFacts = append(thenFacts, curStmt)
// 		}

// 		proofs := []ast.Stmt{}
// 		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
// 		if err != nil {
// 			return nil, parserErrAtTb(err, tb)
// 		}

// 		for _, stmt := range tb.body[len(tb.body)-1].body {

// 			curStmt, err := p.Stmt(&stmt)
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			proofs = append(proofs, curStmt)
// 		}

// 		return ast.NewProveInRangeSetStmt(startAsInt, endAsInt, param, paramSet, thenFacts, proofs, tb.line), nil
// 	} else {
// 		thenFacts := []ast.FactStmt{}
// 		for i := range len(tb.body) {

// 			curStmt, err := p.factStmt(&tb.body[i], UniFactDepth0)
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			thenFacts = append(thenFacts, curStmt)
// 		}

// 		return ast.NewProveInRangeSetStmt(startAsInt, endAsInt, param, paramSet, thenFacts, nil, tb.line), nil
// 	}
// }

func (p *Parser) skipInt(tb *tokenBlock) (int64, error) {
	intStr, err := tb.header.next()
	if err != nil {
		return 0, err
	}

// parseDomThenProve parses a body structure that can have three types of sections:
// 1. dom:, =>:, prove: (all three sections present)
// 2. =>:, prove: (no dom section)
// 3. (only then section, no dom and no prove)
//
// It returns (domFacts, thenFacts, proofs, error)
// - domFacts: facts in the dom: section (can be empty)
// - thenFacts: facts in the =>: section (can be empty)
// - proofs: statements in the prove: section (can be empty)
func parseDomThenProve(body []tokenBlock) ([]ast.FactStmt, []ast.FactStmt, []ast.Stmt, error) {
	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}
	proofs := []ast.Stmt{}

	if len(body) == 0 {
		// Empty body, all remain empty
		return domFacts, thenFacts, proofs, nil
	}

	// Case 1: First section is dom: (must be dom, =>, [prove])
	if body[0].header.is(glob.KeywordDom) {
		if len(body) < 2 || len(body) > 3 {
			return nil, nil, nil, fmt.Errorf("when dom is first, body must have 2 or 3 sections (dom, =>, [prove]), got %d sections", len(body))
		}

		// Parse dom section
		err := body[0].header.skipKwAndColonCheckEOL(glob.KeywordDom)
		if err != nil {
			return nil, nil, nil, err
		}
		for _, stmt := range body[0].body {

  		curStmt, err := p.factStmt(&stmt, UniFactDepth1)
		if err != nil {
				return nil, nil, nil, err
			}
   
		}

		// Parse => section
		if !body[1].header.is(glob.KeySymbolRightArrow) {
			return nil, nil, nil, fmt.Errorf("second section must be => when dom is first")
		}
		err = body[1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, nil, nil, err
		}
		for _, stmt := range body[1].body {

  		curStmt, err := p.factStmt(&stmt, UniFactDepth1)
		if err != nil {
				return nil, nil, nil, err
			}
   
		}

		// Parse optional prove section
		if len(body) == 3 {
			if !body[2].header.is(glob.KeywordProve) {
				return nil, nil, nil, fmt.Errorf("third section must be prove when dom is first")
			}
			err = body[2].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, nil, nil, err
			}
			for _, stmt := range body[2].body {

   		curStmt, err := p.Stmt(&stmt)
		if err != nil {
					return nil, nil, nil, err
				}
    
			}
		}
		// If len(body) == 2, prove remains empty
		return domFacts, thenFacts, proofs, nil
	}

	// Case 2 : First section is not dom
	// Check if last section is prove
	lastIdx := len(body) - 1
	hasProve := body[lastIdx].header.is(glob.KeywordProve)

	if hasProve {
		// Case 2: =>:, prove: (no dom section)
		// All sections before prove are =>
		for i := 0; i < lastIdx; i++ {
			if !body[i].header.is(glob.KeySymbolRightArrow) {
				return nil, nil, nil, fmt.Errorf("when dom is not first, all sections before prove must be =>, but section %d is not", i)
			}
			err := body[i].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
			if err != nil {
				return nil, nil, nil, err
			}
			for _, stmt := range body[i].body {

   		curStmt, err := p.factStmt(&stmt, UniFactDepth1)
		if err != nil {
					return nil, nil, nil, err
				}
    
			}
		}

		// Parse prove section
		err := body[lastIdx].header.skipKwAndColonCheckEOL(glob.KeywordProve)
		if err != nil {
			return nil, nil, nil, err
		}
		for _, stmt := range body[lastIdx].body {

  		curStmt, err := p.Stmt(&stmt)
		if err != nil {
				return nil, nil, nil, err
			}
   
		}
		return domFacts, thenFacts, proofs, nil
	} else {
		// Case 3: Only then section (no dom and no prove)
		// Parse all body blocks directly as fact statements, no need to check for =>
		for i := range len(body) {
			// Check if it's a => section or a direct fact statement
			if body[i].header.is(glob.KeySymbolRightArrow) {
				// It's a => section, skip the => marker
				err := body[i].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
				if err != nil {
					return nil, nil, nil, err
				}
				for _, stmt := range body[i].body {

    		curStmt, err := p.factStmt(&stmt, UniFactDepth1)
		if err != nil {
						return nil, nil, nil, err
					}
     
			} else {
				// It's a direct fact statement (no => needed)
				curStmt, err := body[i].factStmt(UniFactDepth1)
				if err != nil {
					return nil, nil, nil, err
				}
				thenFacts = append(thenFacts, curStmt)
			}
		}
		// dom and prove remain empty
		return domFacts, thenFacts, proofs, nil
	}
}

// func parseDomThenOfProveByEnum(tbSlice []tokenBlock) ([]ast.FactStmt, []ast.FactStmt, error) {
// 	domFacts := []ast.FactStmt{}
// 	thenFacts := []ast.FactStmt{}

// 	if tbSlice[len(tbSlice)-1].header.is(glob.KeySymbolRightArrow) {
// 		for i := range len(tbSlice) - 1 {
// 			curStmt, err := tbSlice[i].factStmt(UniFactDepth1)
// 			if err != nil {
// 				return nil, nil, parserErrAtTb(err, &tbSlice[i])
// 			}
// 			domFacts = append(domFacts, curStmt)
// 		}

// 		err := tbSlice[len(tbSlice)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
// 		if err != nil {
// 			return nil, nil, parserErrAtTb(err, &tbSlice[len(tbSlice)-1])
// 		}

// 		for i := range len(tbSlice[len(tbSlice)-1].body) {
// 			curStmt, err := tbSlice[len(tbSlice)-1].body[i].factStmt(UniFactDepth1)
// 			if err != nil {
// 				return nil, nil, parserErrAtTb(err, &tbSlice[len(tbSlice)-1])
// 			}
// 			thenFacts = append(thenFacts, curStmt)
// 		}
// 	} else {
// 		for i := range len(tbSlice) {
// 			curStmt, err := tbSlice[i].factStmt(UniFactDepth1)
// 			if err != nil {
// 				return nil, nil, parserErrAtTb(err, &tbSlice[i])
// 			}
// 			thenFacts = append(thenFacts, curStmt)
// 		}
// 	}

// 	return domFacts, thenFacts, nil
// }

func (p *Parser) proveIsTransitivePropStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordProveIsTransitiveProp)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
 
	prop, err := p.Obj(tb)
	if err != nil {
  return nil, parserErrAtTb(err, tb)
 }
	propAtom, ok := prop.(ast.Atom)
	if !ok {
		return nil, parserErrAtTb(fmt.Errorf("expect obj atom, but got %T", prop), tb)
	}

	if tb.header.skip(glob.KeySymbolComma) != nil {
		return nil, parserErrAtTb(err, tb)
	}

	params := []string{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.next()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		params = append(params, param)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	if len(params) != 3 {
		return nil, parserErrAtTb(fmt.Errorf("expect 3 params, but got %d", len(params)), tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	proofs := []ast.Stmt{}
	for _, block := range tb.body {

 		curStmt, err := p.Stmt(&block)
		
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
	}
	return ast.NewProveIsTransitivePropStmt(propAtom, params, proofs, tb.line), nil

}

func (p *Parser) proveCommutativePropStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordProveIsCommutativeProp)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	specFact, err := p.specFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(specFact.Params) != 2 {
		return nil, parserErrAtTb(fmt.Errorf("expect 2 params, but got %d", len(specFact.Params)), tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(tb.body) != 2 {
		return nil, parserErrAtTb(fmt.Errorf("expect 2 body blocks, but got %d", len(tb.body)), tb)
	}

	proofs := []ast.Stmt{}
	err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for _, block := range tb.body[0].body {

 		curStmt, err := p.Stmt(&block)
		
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	proofsRightToLeft := []ast.Stmt{}
	err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for _, block := range tb.body[1].body {

 		curStmt, err := p.Stmt(&block)
		
			return nil, parserErrAtTb(err, tb)
		}
		proofsRightToLeft = append(proofsRightToLeft, curStmt)
	}

	return ast.NewProveIsCommutativePropStmt(specFact, proofs, proofsRightToLeft, tb.line), nil

}

func (p *Parser) algoDefStmt(tb *tokenBlock) (*ast.DefAlgoStmt, error) {
	err := tb.header.skip(glob.KeywordAlgo)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	funcName, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	params := []string{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.next()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		params = append(params, param)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	stmts := []ast.AlgoStmt{}
	for _, block := range tb.body {
		curStmt, err := p.algoStmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		stmts = append(stmts, curStmt)
	}

	return ast.NewAlgoDefStmt(funcName, params, stmts, tb.line), nil
}

func (p *Parser) evalStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordEval)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
 
	fcsToEval, err := p.Obj(tb)
	if err != nil {
  return nil, parserErrAtTb(err, tb)
 }

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

func (p *Parser) defProveAlgoStmt(tb *tokenBlock) (*ast.DefProveAlgoStmt, error) {
	err := tb.header.skip(glob.KeywordProveAlgo)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	funcName, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	params := []string{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.next()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		params = append(params, param)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	stmts := []ast.ProveAlgoStmt{}
	for _, block := range tb.body {
		curStmt, err := p.proveAlgoStmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		stmts = append(stmts, curStmt)
	}
	return ast.NewDefProveAlgoStmt(funcName, params, stmts, tb.line), nil
}

func (p *Parser) byStmt(tb *tokenBlock) (*ast.ByStmt, error) {
	err := tb.header.skip(glob.KeywordBy)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	proveAlgoName, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	proveAlgoParams := []ast.Obj{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := p.Obj(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proveAlgoParams = append(proveAlgoParams, param)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// by statement no longer has then facts - facts are returned from prove_algo
	return ast.NewByStmt(proveAlgoName, proveAlgoParams, tb.line), nil
}

func (p *Parser) proveByContradictionStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordProveByContradiction)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	toCheck, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals([]string{glob.KeySymbolColon})
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	proofs := []ast.Stmt{}
	for _, block := range tb.body {

 		curStmt, err := p.Stmt(&block)
		
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
	}
	return ast.NewClaimProveByContradictionStmt(ast.NewClaimProveStmt(toCheck, proofs, tb.line), tb.line), nil
}

// printStmt prints a string to the console
func (p *Parser) printStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordPrint)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	isFString := false
	if tb.header.is("f") {
		isFString = true
		tb.header.skip("f")
	}

	value, err := p.getStringInDoubleQuotes(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

func (p *Parser) helpStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordHelp)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	keyword, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

func (p *Parser) importDirStmt(tb *tokenBlock) (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordImport)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Parse the path in double quotes
	path, err := p.getStringInDoubleQuotes(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Check if path ends with .lit - if so, it's an ImportFileStmt
	if strings.HasSuffix(path, glob.LitexFileSuffix) {
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}
		return ast.NewImportFileStmt(path, tb.line), nil
	}

	// Otherwise, it's an ImportDirStmt
	// Check if there's an "as" keyword followed by a package name
	var asPkgName string
	if tb.header.is(glob.KeywordAs) {
		tb.header.skip(glob.KeywordAs)
		asPkgName, err = tb.header.next()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
	} else {
		// If no "as" keyword, use the path as the package name
		// Extract the last component of the path as the default package name
		pathParts := strings.Split(path, "/")
		asPkgName = pathParts[len(pathParts)-1]
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ast.NewImportStmt(path, asPkgName, tb.line), nil
}
