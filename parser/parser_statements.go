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
	"path/filepath"
	"slices"
	"strings"
)

func (tb *tokenBlock) Stmt() (ast.Stmt, error) {
	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, tbErr(err, tb)
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
		ret, err = tb.defFnStmt(true)
	case glob.KeywordLet:
		ret, err = tb.defObjStmt()
	case glob.KeywordHave:
		if tb.header.strAtCurIndexPlus(1) == glob.KeywordSet {
			if tb.header.strAtCurIndexPlus(2) == glob.KeywordFn {
				ret, err = tb.haveSetFnStmt()
			} else {
				if slices.Contains(tb.header.slice, glob.KeywordSetDefinedByReplacement) {
					ret, err = tb.haveSetDefinedByReplacementStmt()
				} else {
					ret, err = tb.haveSetStmt()
				}
			}
		} else if tb.header.strAtCurIndexPlus(1) == glob.KeywordFn {
			if tb.header.strAtCurIndexPlus(2) == glob.KeySymbolColon {
				ret, err = tb.claimHaveFnStmt()
			} else if tb.header.strAtCurIndexPlus(4) == glob.KeywordLift {
				ret, err = tb.haveFnLiftStmt()
			} else {
				ret, err = tb.haveFnEqualStmt()
			}
		} else if slices.Contains(tb.header.slice, glob.KeywordSt) {
			ret, err = tb.haveObjStStmt()
		} else if slices.Contains(tb.header.slice, glob.KeySymbolEqual) {
			ret, err = tb.haveObjEqualStmt()
		} else {
			ret, err = tb.haveObjInNonEmptySetStmt()
		}
	case glob.KeywordClaim:
		ret, err = tb.claimStmt()
	case glob.KeywordProve:
		ret, err = tb.proveStmt()
	case glob.KeywordKnow:
		{
			if tb.TokenAtHeaderIndexIs(1, glob.KeySymbolAt) {
				if tb.TokenAtHeaderIndexIs(2, glob.KeywordExist) {
					ret, err = tb.knowExistPropStmt()
				} else {
					ret, err = tb.knowPropStmt()
				}
			} else {
				ret, err = tb.knowFactStmt()
			}
		}
	case glob.KeywordProveInEachCase:
		ret, err = tb.proveInEachCaseStmt()
	case glob.KeywordProveOverFiniteSet:
		ret, err = tb.proveOverFiniteSetStmt()
	case glob.KeySymbolAt:
		ret, err = tb.namedUniFactStmt()
	case glob.CommentSig:
		ret, err = tb.commentStmt()
	case glob.KeywordFnTemplate:
		ret, err = tb.fnTemplateStmt()
	case glob.KeywordClear:
		ret, err = tb.clearStmt()
	case glob.KeywordProveByInduction:
		ret, err = tb.proveByInductionStmt()
	default:
		ret, err = tb.factsStmt()
	}

	if err != nil {
		return nil, err
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of block")
	}

	return ret, nil
}

type uniFactHeaderEnum int8

const (
	uniFactHeaderEnumForall uniFactHeaderEnum = iota
	uniFactHeaderEnumIf
	uniFactHeaderEnumIfAndForall
)

func (tb *tokenBlock) factStmt(uniFactDepth uniFactEnum) (ast.FactStmt, error) {
	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	switch cur {
	case glob.KeywordForall:
		if tb.GetEnd() == glob.KeySymbolColon {
			return tb.uniFactInterface(uniFactDepth)
		} else {
			return tb.inlineUniInterface()
		}
	case glob.KeywordOr:
		return tb.orStmt()
	case glob.KeySymbolEqual:
		return tb.equalsFactStmt()
	case glob.KeywordIf:
		if tb.GetEnd() == glob.KeySymbolColon {
			return tb.ifStmt(uniFactDepth)
		} else {
			return tb.inlineIfInterface()
		}
	default:
		return tb.fact()
	}

}

func (tb *tokenBlock) enumFactualStmt(setName ast.Fc) (*ast.EnumStmt, error) {
	// skip colon and get end
	err := tb.header.skip(glob.KeySymbolLeftCurly)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	enumFcs := []ast.Fc{}
	for !tb.CurrentTokenIs(glob.KeySymbolRightCurly) {
		fc, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		enumFcs = append(enumFcs, fc)
		tb.header.skipIfIs(glob.KeySymbolComma)
	}
	err = tb.header.skip(glob.KeySymbolRightCurly)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewEnumStmt(setName, enumFcs), nil
}

func (tb *tokenBlock) orStmt() (*ast.OrStmt, error) {
	if tb.GetEnd() != glob.KeySymbolColon {
		return tb.inlineOrStmt()
	}

	orFacts := []*ast.SpecFactStmt{}
	isOr := tb.header.isAndSkip(glob.KeywordOr)
	if !isOr {
		return nil, fmt.Errorf("expect 'or'")
	}

	err := tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	for _, factToParse := range tb.body {
		fact, err := factToParse.specFactStmt_ExceedEnd()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		orFacts = append(orFacts, fact)
	}

	return ast.NewOrStmt(orFacts), nil
}

func (tb *tokenBlock) SpecFactOrOrStmt() (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordOr) {
		return tb.orStmt()
	} else if tb.header.is(glob.KeySymbolEqual) {
		return tb.equalsFactStmt()
	} else {
		return tb.specFactStmt()
	}
}

func (tb *tokenBlock) specFactStmt_ExceedEnd() (*ast.SpecFactStmt, error) {
	ret, err := tb.specFactStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ret, nil
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

	ret, err := tb.ordinarySpecFact()

	if err != nil {
		return nil, tbErr(err, tb)
	}

	if isTrue {
		return ret, nil
	} else {
		return ret.ReverseTrue(), nil
	}

}

func (tb *tokenBlock) ordinarySpecFact() (*ast.SpecFactStmt, error) {
	if tb.header.is(glob.FuncFactPrefix) {
		ret, err := tb.pureFuncSpecFact()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ret, nil
	} else {
		ret, err := tb.relaFactStmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ret, nil
	}
}

func (tb *tokenBlock) uniFactInterface(uniFactDepth uniFactEnum) (ast.UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	params, setParams, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolColon, false)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(uniFactDepth.addDepth(), glob.KeywordThen)
	domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(uniFactDepth.addDepth(), glob.KeySymbolEqualLarger)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if len(iffFacts) == 0 {
		return ast.NewUniFact(params, setParams, domainFacts, thenFacts), nil
	} else {
		ret := ast.NewUniFactWithIff(ast.NewUniFact(params, setParams, domainFacts, thenFacts), iffFacts)

		if len(thenFacts) == 0 {
			// return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeywordThen, ret)
			return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeySymbolEqualLarger, ret)
		}

		return ret, nil
	}

}

func (tb *tokenBlock) ifStmt(uniFactDepth uniFactEnum) (ast.UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordIf)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(uniFactDepth.addDepth(), glob.KeySymbolEqualLarger)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if len(iffFacts) == 0 {
		return ast.NewUniFact([]string{}, []ast.Fc{}, domainFacts, thenFacts), nil
	} else {
		ret := ast.NewUniFactWithIff(ast.NewUniFact([]string{}, []ast.Fc{}, domainFacts, thenFacts), iffFacts)

		if len(thenFacts) == 0 {
			// return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeywordThen, ret)
			return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeySymbolEqualLarger, ret)
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
		return nil, tbErr(err, tb)
	}

	declHeader, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if !tb.header.is(glob.KeySymbolColon) {
		if tb.header.ExceedEnd() {
			return ast.NewDefPropStmt(declHeader, nil, nil, []ast.FactStmt{}), nil
		} else if tb.header.is(glob.KeySymbolEquivalent) {
			err = tb.header.skip(glob.KeySymbolEquivalent)
			if err != nil {
				return nil, tbErr(err, tb)
			}
			unitFacts, err := tb.inlineFacts_checkUniDepth1()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			return ast.NewDefPropStmt(declHeader, []ast.FactStmt{}, unitFacts, []ast.FactStmt{}), nil
		} else {
			return nil, fmt.Errorf("expect ':' or end of block")
		}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.header.ExceedEnd() {
		// domFacts, iffFacts, err := tb.dom_and_section(glob.KeywordIff, glob.KeywordThen)
		// domFacts, iffFacts, err := tb.dom_and_section(glob.KeywordIff, glob.KeySymbolEqualLarger)
		domFacts, iffFacts, err := tb.dom_and_section(glob.KeySymbolEquivalent, glob.KeySymbolEqualLarger)
		if err != nil {
			return nil, tbErr(err, tb)
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

		return ast.NewDefPropStmt(declHeader, domFacts, iffFacts, []ast.FactStmt{}), nil
	} else {
		domFacts, iffFacts, err := tb.bodyOfInlineDomAndThen(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewDefPropStmt(declHeader, domFacts, iffFacts, []ast.FactStmt{}), nil
	}

}

func (tb *tokenBlock) defObjStmt() (*ast.DefObjStmt, error) {
	err := tb.header.skip("")
	if err != nil {
		return nil, tbErr(err, tb)
	}

	objNames, objSets, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolColon, true)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if len(objNames) == 0 {
		return nil, fmt.Errorf("expect at least one object")
	}

	if tb.header.ExceedEnd() && len(tb.body) == 0 {
		return ast.NewDefObjStmt(objNames, objSets, []ast.FactStmt{}), nil
	} else if tb.header.ExceedEnd() && len(tb.body) != 0 {
		facts, err := tb.bodyFacts(UniFactDepth0)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ast.NewDefObjStmt(objNames, objSets, facts), nil
	} else {
		facts, err := tb.inlineFacts_checkUniDepth0()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		err = checkFactsUniDepth0(facts)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewDefObjStmt(objNames, objSets, facts), nil
	}
}

func (tb *tokenBlock) claimStmt() (ast.ClaimInterface, error) {
	err := tb.header.skip(glob.KeywordClaim)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if !tb.header.is(glob.KeySymbolColon) {
		return tb.claimStmtInline()
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.body[0].header.is(glob.KeySymbolAt) {
		return tb.claimPropStmt()
	} else if tb.body[0].header.is(glob.KeywordExistProp) {
		return tb.claimExistPropStmt()
	}

	toCheck, err := tb.body[0].factStmt(UniFactDepth0)
	if err != nil {
		return nil, tbErr(err, tb)
	}
	proof := []ast.Stmt{}

	isProve := true

	if len(tb.body) != 2 {
		if len(tb.body) != 1 {
			return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction' after claim")
		} else {
			return ast.NewClaimProveStmt(toCheck, []ast.Stmt{}), nil
		}
	}

	if tb.body[1].header.is(glob.KeywordProveByContradiction) {
		isProve = false
		err := tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProveByContradiction)
		if err != nil {
			return nil, tbErr(err, tb)
		}
	} else if tb.body[1].header.is(glob.KeywordProve) {
		err := tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
		if err != nil {
			return nil, tbErr(err, tb)
		}
	} else {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction' after claim")
	}

	for _, block := range tb.body[1].body {
		curStmt, err := block.Stmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		proof = append(proof, curStmt)
	}

	if isProve {
		return ast.NewClaimProveStmt(toCheck, proof), nil
	} else {
		return ast.NewClaimProveByContradictionStmt(*ast.NewClaimProveStmt(toCheck, proof)), nil
	}
}

func (tb *tokenBlock) knowFactStmt() (*ast.KnowFactStmt, error) {
	tb.header.skip(glob.KeywordKnow)

	if !tb.header.is(glob.KeySymbolColon) {
		var facts ast.FactStmtSlice = ast.FactStmtSlice{}
		var err error
		facts, err = tb.inlineFacts_checkUniDepth0()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		err = checkFactsUniDepth0(facts)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ast.NewKnowStmt(facts.ToCanBeKnownStmtSlice()), nil
	}

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, tbErr(err, tb)
	}

	var err error
	var facts ast.FactStmtSlice = ast.FactStmtSlice{}
	facts, err = tb.bodyFacts(UniFactDepth0)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewKnowStmt(facts.ToCanBeKnownStmtSlice()), nil
}

// relaFact 只支持2个参数的关系
func (tb *tokenBlock) relaFactStmt() (*ast.SpecFactStmt, error) {
	var ret *ast.SpecFactStmt

	fc, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	opt, err := tb.header.next()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if opt == glob.FuncFactPrefix {
		propName, err := tb.rawFcAtom()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if tb.header.ExceedEnd() {
			ret = ast.NewSpecFactStmt(ast.TruePure, propName, []ast.Fc{fc})
		} else {
			fc2, err := tb.RawFc()
			if err != nil {
				return nil, tbErr(err, tb)
			}

			params := []ast.Fc{fc, fc2}

			ret = ast.NewSpecFactStmt(ast.TruePure, propName, params)
		}
	} else if !glob.IsBuiltinInfixRelaPropSymbol(opt) {
		return nil, fmt.Errorf("expect relation prop")
	} else {
		fc2, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
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

	params, setParams, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolRightBrace, false)
	if err != nil {
		return nil, err
	}

	return ast.NewDefHeader(ast.FcAtom(name), params, setParams), nil
}

func (tb *tokenBlock) defExistPropStmt() (*ast.DefExistPropStmt, error) {
	var err error

	err = tb.header.skip(glob.KeywordExistProp)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	existParams, existParamSets, err := tb.param_paramSet_paramInSetFacts(glob.KeywordSt, false)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if len(existParams) == 0 {
		return nil, fmt.Errorf("expect at least one parameter in exist prop definition")
	}

	def, err := tb.defExistPropStmtBody()

	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewDefExistPropStmt(def, existParams, existParamSets), nil
}

// 本质上这个设计是有问题的。exist把 sep 这个奇怪的东西混进param 来了
func (tb *tokenBlock) existFactStmt(isTrue bool) (*ast.SpecFactStmt, error) {
	err := tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	existParams := []ast.Fc{}

	for !tb.header.is(glob.KeywordSt) {
		param, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		existParams = append(existParams, param)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeywordSt)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	pureSpecFact, err := tb.ordinarySpecFact()
	if err != nil {
		return nil, tbErr(err, tb)
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

	propName, err := tb.rawFcAtom()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	params := []ast.Fc{}
	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			param, err := tb.RawFc()
			if err != nil {
				return nil, tbErr(err, tb)
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
		return nil, tbErr(err, tb)
	}

	ret := ast.NewSpecFactStmt(ast.TruePure, propName, params)

	return ret, nil
}

func (tb *tokenBlock) haveObjStStmt() (*ast.HaveObjStStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	objNames := []string{}

	// there is at least one object name
	for {
		objName, err := tb.header.next()
		if err != nil {
			return nil, tbErr(err, tb)
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
		return nil, tbErr(err, tb)
	}

	fact, err := tb.specFactStmt()
	if err != nil {
		return nil, tbErr(err, tb)
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
				return nil, tbErr(err, tb)
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
					return nil, tbErr(err, tb)
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
		return nil, tbErr(err, tb)
	}

	if tb.header.ExceedEnd() {
		return ast.NewExistPropDef(declHeader, []ast.FactStmt{}, []ast.FactStmt{}), nil
	}

	if tb.header.is(glob.KeySymbolEquivalent) {
		err = tb.header.skip(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		unitFacts, err := tb.inlineFacts_checkUniDepth1()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ast.NewExistPropDef(declHeader, []ast.FactStmt{}, unitFacts), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.header.ExceedEnd() {

		// domFacts, iffFactsAsFactStatements, err := tb.dom_and_section(glob.KeywordIff, glob.KeywordThen)
		// domFacts, iffFactsAsFactStatements, err := tb.dom_and_section(glob.KeywordIff, glob.KeySymbolEqualLarger)
		domFacts, iffFactsAsFactStatements, err := tb.dom_and_section(glob.KeySymbolEquivalent, glob.KeySymbolEqualLarger)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if len(iffFactsAsFactStatements) == 0 {
			return nil, fmt.Errorf("expect 'iff' section in proposition definition has at least one fact")
		}

		return ast.NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements), nil
	} else {
		domFacts, iffFactsAsFactStatements, err := tb.bodyOfInlineDomAndThen(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements), nil
	}
}

func (tb *tokenBlock) uniFactBodyFacts(uniFactDepth uniFactEnum, defaultSectionName string) ([]ast.FactStmt, []ast.FactStmt, []ast.FactStmt, error) {
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
	if curToken == glob.KeywordDom || curToken == glob.KeySymbolEqualLarger || curToken == glob.KeySymbolEquivalent {
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
			// case glob.KeywordThen:
			case glob.KeySymbolEqualLarger:
				thenFacts = append(thenFacts, facts...)
			// case glob.KeywordIff:
			case glob.KeySymbolEquivalent:
				iffFacts = append(iffFacts, facts...)
			default:
				return nil, nil, nil, fmt.Errorf("expect keyword in uni fact body, but got: %s", kw)
			}
		}
		// } else if tb.body[len(tb.body)-1].header.is(glob.KeywordThen) {
	} else if tb.body[len(tb.body)-1].header.is(glob.KeySymbolEqualLarger) {
		domFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body)-1)
		if err != nil {
			return nil, nil, nil, err
		}

		// err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
		err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeySymbolEqualLarger)
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
			err = tb.body[0].header.skipKwAndColon_ExceedEnd(glob.KeywordDom)
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

			err = tb.body[len(tb.body)-2].header.skipKwAndColon_ExceedEnd(glob.KeySymbolEqualLarger)
			if err != nil {
				return nil, nil, nil, err
			}
			thenFacts, err = tb.body[len(tb.body)-2].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-2].body))
			if err != nil {
				return nil, nil, nil, err
			}

		} else if tb.body[0].header.is(glob.KeySymbolEqualLarger) {
			err = tb.body[0].header.skipKwAndColon_ExceedEnd(glob.KeySymbolEqualLarger)
			if err != nil {
				return nil, nil, nil, err
			}
			thenFacts, err = tb.body[0].bodyBlockFacts(uniFactDepth, len(tb.body[0].body))
			if err != nil {
				return nil, nil, nil, err
			}
		} else {
			if tb.body[len(tb.body)-2].header.is(glob.KeySymbolEqualLarger) {

				domFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body)-2)
				if err != nil {
					return nil, nil, nil, err
				}

				// body[len(tb.body)-2] is =>:
				err = tb.body[len(tb.body)-2].header.skipKwAndColon_ExceedEnd(glob.KeySymbolEqualLarger)
				if err != nil {
					return nil, nil, nil, err
				}
				thenFacts, err = tb.body[len(tb.body)-2].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-2].body))
				if err != nil {
					return nil, nil, nil, err
				}
			} else {
				// 全部是 then
				thenFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body)-1)
				if err != nil {
					return nil, nil, nil, err
				}
			}

		}

		// thenFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body)-1)
		// if err != nil {
		// 	return nil, nil, nil, err
		// }

		// err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordIff)
		err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, nil, nil, err
		}
		iffFacts, err = tb.body[len(tb.body)-1].bodyBlockFacts(uniFactDepth, len(tb.body[len(tb.body)-1].body))
		if err != nil {
			return nil, nil, nil, err
		}
	} else {
		// if defaultSectionName == glob.KeywordThen {
		if defaultSectionName == glob.KeySymbolEqualLarger {
			thenFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body))
			if err != nil {
				return nil, nil, nil, err
			}
			// } else if defaultSectionName == glob.KeywordIff {
		} else if defaultSectionName == glob.KeySymbolEquivalent {
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

// func (tb *tokenBlock) supposePropMatchStmt() (*ast.SupposeStmt, error) {
// 	err := tb.header.skip(glob.KeywordSuppose)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	fact, err := tb.pureFuncSpecFact()
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolColon)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	body := []ast.Stmt{}
// 	for _, stmt := range tb.body {
// 		curStmt, err := stmt.stmt()
// 		if err != nil {
// 			return nil, tbErr(err, tb)
// 		}

// 		// TODO 暂时只能全是fact
// 		body = append(body, curStmt)
// 	}

// 	return ast.NewWhenPropMatchStmt(*fact, body), nil
// }

// func (tb *tokenBlock) withPropMatchStmt() (*ast.WithStmt, error) {
// 	err := tb.header.skip(glob.KeywordWith)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	fact, err := tb.pureFuncSpecFact()
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolColon)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	body := []ast.Stmt{}
// 	for _, stmt := range tb.body {
// 		curStmt, err := stmt.stmt()
// 		if err != nil {
// 			return nil, tbErr(err, tb)
// 		}
// 		body = append(body, curStmt)
// 	}

// 	return ast.NewWithPropMatchStmt(*fact, body), nil
// }

func (tb *tokenBlock) knowPropStmt() (*ast.KnowPropStmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	namedUniFact, err := tb.namedUniFactStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewKnowPropStmt(namedUniFact.DefPropStmt), nil
}

func (tb *tokenBlock) proveInEachCaseStmt() (*ast.ProveInEachCaseStmt, error) {
	err := tb.header.skipKwAndColon_ExceedEnd(glob.KeywordProveInEachCase)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	orFact, err := tb.body[0].orStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	thenFacts := []ast.FactStmt{}
	// err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
	err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeySymbolEqualLarger)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	for _, stmt := range tb.body[1].body {
		curStmt, err := stmt.factStmt(UniFactDepth0)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		thenFacts = append(thenFacts, curStmt)
	}

	proofs := []ast.StmtSlice{}
	for i := 2; i < len(tb.body); i++ {
		proof := ast.StmtSlice{}

		err = tb.body[i].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		for _, stmt := range tb.body[i].body {
			curStmt, err := stmt.Stmt()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			proof = append(proof, curStmt)
		}
		proofs = append(proofs, proof)
	}

	if len(proofs) != len(orFact.Facts) {
		return nil, tbErr(fmt.Errorf("prove in each case: expect %d proofs, but got %d. expect the number of proofs to be the same as the number of facts in the or fact", len(orFact.Facts), len(proofs)), tb)
	}

	return ast.NewProveInEachCaseStmt(*orFact, thenFacts, proofs), nil
}

func (tb *tokenBlock) param_paramSet_paramInSetFacts(endWith string, allowExceedEnd bool) ([]string, []ast.Fc, error) {
	params := []string{}
	setParams := []ast.Fc{}
	paramWithoutSetCount := 0

	if !tb.header.is(endWith) {
		for {
			param, err := tb.header.next()
			if err != nil {
				return nil, nil, err
			}

			params = append(params, addPkgNameToString(param))

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				paramWithoutSetCount++
				continue
			}

			setParam, err := tb.RawFc()
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
		atomsInSetParam := ast.GetAtomsInFc(setParam)
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

func (tb *tokenBlock) importStmt() (ast.ImportStmtInterface, error) {
	err := tb.header.skip(glob.KeywordImport)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	importPath := ""
	importPath, err = tb.getStringInDoubleQuotes()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.header.is(glob.KeywordAs) {
		asPkgName := ""
		tb.header.skip(glob.KeywordAs)
		asPkgName, err = tb.header.next()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ast.NewImportStmt(importPath, asPkgName), nil
	} else {
		if strings.HasSuffix(importPath, ".lix") {
			return ast.NewImportFileStmt(importPath), nil
		} else {
			// 得到 path 的最后一位，默认是 repo 的 repo 名
			lastPart := filepath.Base(importPath)
			return ast.NewImportStmt(importPath, lastPart), nil
		}
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
// 		return nil, tbErr(err, tb)
// 	}

// 	stmts := []ast.Stmt{}
// 	for _, stmt := range tb.body {
// 		curStmt, err := stmt.stmt()
// 		if err != nil {
// 			return nil, tbErr(err, tb)
// 		}
// 		stmts = append(stmts, curStmt)
// 	}

// 	return ast.NewPubStmt(stmts), nil
// }

func (tb *tokenBlock) proveStmt() (*ast.ProveStmt, error) {
	err := tb.header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if len(tb.body) == 0 {
		return nil, fmt.Errorf("expect proof")
	}

	proof := []ast.Stmt{}
	for _, stmt := range tb.body {
		curStmt, err := stmt.Stmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		proof = append(proof, curStmt)
	}

	return ast.NewProveStmt(proof), nil
}

// called by exist_prop and prop def

func (tb *tokenBlock) parseFactBodyWithHeaderNameAndUniFactDepth(headerName string, uniFactDepth uniFactEnum) ([]ast.FactStmt, error) {
	err := tb.header.skipKwAndColon_ExceedEnd(headerName)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	facts := []ast.FactStmt{}
	for _, stmt := range tb.body {
		curStmt, err := stmt.factStmt(uniFactDepth)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, curStmt)
	}
	return facts, nil
}

// 要保证 fn 里的params 和 fn 里面的 uniFact 的params 是不一样的，否则可能出现严重的问题
func (tb *tokenBlock) defFnStmt(skipFn bool) (*ast.DefFnStmt, error) {
	if skipFn {
		err := tb.header.skip(glob.KeywordFn)
		if err != nil {
			return nil, tbErr(err, tb)
		}
	}

	decl, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	retSet, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}
	if asAtom, ok := retSet.(ast.FcAtom); ok {
		if string(asAtom) == glob.KeySymbolColon {
			return nil, fmt.Errorf(": is not allowed in return set")
		}
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip("")
		if tb.header.ExceedEnd() {
			// domFacts, thenFacts, err = tb.dom_and_section(glob.KeywordThen, glob.KeywordIff)
			// domFacts, thenFacts, err = tb.dom_and_section(glob.KeySymbolEqualLarger, glob.KeywordIff)
			domFacts, thenFacts, err = tb.dom_and_section(glob.KeySymbolEqualLarger, glob.KeySymbolEquivalent)
			if err != nil {
				return nil, tbErr(err, tb)
			}
		} else {
			domFacts, err = tb.inlineFacts_untilWord_or_exceedEnd_notSkipWord(glob.KeySymbolEqualLarger)
			if err != nil {
				return nil, tbErr(err, tb)
			}

			if !tb.header.is(glob.KeySymbolEqualLarger) {
				return ast.NewDefFnStmt(string(decl.Name), ast.NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts)), nil
			}

			err = tb.header.skip(glob.KeySymbolEqualLarger)
			if err != nil {
				return nil, tbErr(err, tb)
			}

			thenFacts, err = tb.inlineFacts_untilEndOfInline()
			if err != nil {
				return nil, tbErr(err, tb)
			}
		}
	} else if tb.header.is(glob.KeySymbolEqualLarger) {
		err = tb.header.skip(glob.KeySymbolEqualLarger)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		unitFacts, err := tb.inlineFacts_checkUniDepth1()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		thenFacts = append(thenFacts, unitFacts...)
	}

	return ast.NewDefFnStmt(string(decl.Name), ast.NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts)), nil
}

func (tb *tokenBlock) claimPropStmt() (*ast.ClaimPropStmt, error) {
	// declHeader, err := tb.body[0].headerOfAtProp()
	// if err != nil {
	// 	return nil, tbErr(err, tb)
	// }

	// iffFacts, thenFacts, err := tb.body[0].bodyOfKnowProp()
	// if err != nil {
	// 	return nil, tbErr(err, tb)
	// }

	namedUniFact, err := tb.body[0].namedUniFactStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	isProve := false
	if tb.body[1].header.is(glob.KeywordProve) {
		isProve = true
		err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
	} else if tb.body[1].header.is(glob.KeywordProveByContradiction) {
		err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProveByContradiction)
	} else {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}

	if err != nil {
		return nil, tbErr(err, tb)
	}

	proofs := []ast.Stmt{}
	for _, stmt := range tb.body[1].body {
		curStmt, err := stmt.Stmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	// return ast.NewClaimPropStmt(ast.NewDefPropStmt(declHeader, []ast.FactStmt{}, iffFacts, thenFacts), proofs, isProve), nil
	return ast.NewClaimPropStmt(ast.NewDefPropStmt(&namedUniFact.DefPropStmt.DefHeader, namedUniFact.DefPropStmt.DomFacts, namedUniFact.DefPropStmt.IffFacts, namedUniFact.DefPropStmt.ThenFacts), proofs, isProve), nil
}

func (tb *tokenBlock) claimExistPropStmt() (*ast.ClaimExistPropStmt, error) {
	existProp, err := tb.body[0].defExistPropStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	proofs := []ast.Stmt{}
	if tb.body[1].header.is(glob.KeywordProve) {
		err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		for _, stmt := range tb.body[1].body {
			curStmt, err := stmt.Stmt()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			proofs = append(proofs, curStmt)
		}
	} else {
		return nil, fmt.Errorf("expect 'prove'")
	}

	return ast.NewClaimExistPropStmt(existProp, proofs), nil
}

// func (tb *tokenBlock) proveByMathInductionStmt() (*ast.ProveByMathInductionStmt, error) {
// 	var err error
// 	var paramIndex int = 0
// 	var start int = 0

// 	err = tb.header.skip(glob.KeywordProveByMathInduction)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolLeftBrace)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	fact, err := tb.specFactStmt()
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	if tb.header.is(glob.KeySymbolComma) {
// 		tb.header.skip(glob.KeySymbolComma)
// 		paramIndexAsStr, err := tb.header.next()
// 		if err != nil {
// 			return nil, tbErr(err, tb)
// 		}

// 		paramIndex, err = strconv.Atoi(paramIndexAsStr)
// 		if err != nil {
// 			return nil, tbErr(err, tb)
// 		}

// 		if tb.header.is(glob.KeySymbolComma) {
// 			tb.header.skip(glob.KeySymbolComma)
// 			startAsStr, err := tb.header.next()
// 			if err != nil {
// 				return nil, tbErr(err, tb)
// 			}
// 			start, err = strconv.Atoi(startAsStr)
// 			if err != nil {
// 				return nil, tbErr(err, tb)
// 			}
// 		}
// 	}

// 	err = tb.header.skip(glob.KeySymbolRightBrace)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	// 第ParamIndex个参数必须是atom

// 	return ast.NewProveByMathInductionStmt(fact, paramIndex, start), nil
// }

func (tb *tokenBlock) dom_and_section(kw string, kw_should_not_exist_in_body string) ([]ast.FactStmt, []ast.FactStmt, error) {
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
			curStmt, err := stmt.factStmt(UniFactDepth1)
			if err != nil {
				return nil, nil, tbErr(err, tb)
			}
			sectionFacts = append(sectionFacts, curStmt)
		}
		return domFacts, sectionFacts, nil
	} else if !tb.body[0].header.is(glob.KeywordDom) && tb.body[len(tb.body)-1].header.is(kw) {
		for i := range len(tb.body) - 1 {
			curStmt, err := tb.body[i].factStmt(UniFactDepth1)
			if err != nil {
				return nil, nil, tbErr(err, tb)
			}
			domFacts = append(domFacts, curStmt)
		}
		sectionFacts, err = tb.body[len(tb.body)-1].parseFactBodyWithHeaderNameAndUniFactDepth(kw, UniFactDepth1)
		if err != nil {
			return nil, nil, tbErr(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else if len(tb.body) == 2 && tb.body[0].header.is(glob.KeywordDom) && tb.body[1].header.is(kw) {
		domFacts, err = tb.body[0].parseFactBodyWithHeaderNameAndUniFactDepth(glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, tbErr(err, tb)
		}
		sectionFacts, err = tb.body[1].parseFactBodyWithHeaderNameAndUniFactDepth(kw, UniFactDepth1)
		if err != nil {
			return nil, nil, tbErr(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else if len(tb.body) == 1 && tb.body[0].header.is(glob.KeywordDom) {
		domFacts, err = tb.body[0].parseFactBodyWithHeaderNameAndUniFactDepth(glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, tbErr(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else if len(tb.body) == 1 && tb.body[0].header.is(kw) {
		sectionFacts, err = tb.body[0].parseFactBodyWithHeaderNameAndUniFactDepth(kw, UniFactDepth1)
		if err != nil {
			return nil, nil, tbErr(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else {
		return nil, nil, fmt.Errorf("expect dom section and %s section", kw)
	}
}

func (tb *tokenBlock) intentionalSetBody() (string, ast.Fc, []*ast.SpecFactStmt, error) {
	param, err := tb.header.next()
	if err != nil {
		return "", nil, nil, tbErr(err, tb)
	}

	parentSet, err := tb.RawFc()
	if err != nil {
		return "", nil, nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return "", nil, nil, tbErr(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return "", nil, nil, fmt.Errorf("expect end of line")
	}

	proofs := []*ast.SpecFactStmt{}
	for _, stmt := range tb.body {
		curStmt, err := stmt.specFactStmt()
		if err != nil {
			return "", nil, nil, tbErr(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	return param, parentSet, proofs, nil
}

func (tb *tokenBlock) intensionalSetFactualStmt(curSet ast.Fc) (*ast.IntensionalSetStmt, error) {
	param, parentSet, proofs, err := tb.intentionalSetBody()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewIntensionalSetStmt(curSet, param, parentSet, proofs), nil
}

func (tb *tokenBlock) fact() (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordNot) {
		return tb.specFactStmt()
	}

	if tb.header.is(glob.KeywordExist) {
		return tb.existFactStmt(true)
	}

	if tb.header.is(glob.FuncFactPrefix) {
		ret, err := tb.pureFuncSpecFact()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ret, nil
	} else {
		ret, err := tb.relaFact_intensionalSetFact_enumStmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ret, nil
	}
}

func (tb *tokenBlock) relaFact_intensionalSetFact_enumStmt() (ast.FactStmt, error) {
	var ret *ast.SpecFactStmt

	fc, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	opt, err := tb.header.next()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if opt == glob.FuncFactPrefix {
		propName, err := tb.rawFcAtom()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if tb.header.ExceedEnd() {
			ret = ast.NewSpecFactStmt(ast.TruePure, propName, []ast.Fc{fc})
		} else {
			fc2, err := tb.RawFc()
			if err != nil {
				return nil, tbErr(err, tb)
			}

			params := []ast.Fc{fc, fc2}

			ret = ast.NewSpecFactStmt(ast.TruePure, propName, params)
		}
	} else if opt == glob.KeySymbolColonEqual {
		return tb.enumStmt_or_intensionalSetStmt_or_DomOf(fc)
	} else if glob.IsBuiltinInfixRelaPropSymbol(opt) {
		fc2, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		// 必须到底了
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

		params := []ast.Fc{fc, fc2}

		ret = ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(opt), params)
	} else {
		return nil, fmt.Errorf("expect relation prop")
	}

	// 这里加入语法糖：!= 等价于 not =，好处是我 = 有 commutative的性质，我不用额外处理 != 了
	if ret.NameIs(glob.KeySymbolNotEqual) {
		ret.TypeEnum = ast.FalsePure
		ret.PropName = ast.FcAtom(glob.KeySymbolEqual)
	}

	return ret, nil
}

func (tb *tokenBlock) enumStmt_or_intensionalSetStmt_or_DomOf(fc ast.Fc) (ast.EnumSet_IntensionalSet_EqualDom, error) {
	if tb.header.is(glob.KeySymbolLeftCurly) {
		return tb.enumFactualStmt(fc)
	} else {
		return tb.intensionalSetFactualStmt(fc)
	}
}

func (tb *tokenBlock) proveOverFiniteSetStmt() (*ast.ProveOverFiniteSetStmt, error) {
	err := tb.header.skipKwAndColon_ExceedEnd(glob.KeywordProveOverFiniteSet)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	var uniFact ast.UniFactInterface
	if tb.body[0].GetEnd() == glob.KeySymbolColon {
		uniFact, err = tb.body[0].uniFactInterface(UniFactDepth0)
		if err != nil {
			return nil, tbErr(err, tb)
		}
	} else {
		// uniFact, err = tb.body[0].inlineUniFact()
		uniFact, err = tb.body[0].inlineUniInterface()
		if err != nil {
			return nil, tbErr(err, tb)
		}
	}

	uniFactAsUniFactStmt, ok := uniFact.(*ast.UniFactStmt)
	if !ok {
		return nil, fmt.Errorf("expect universal fact without iff")
	}

	if len(uniFactAsUniFactStmt.DomFacts) != 0 {
		// 必须全部是 reversible 的domFact 否则就报错。因为 在执行的时候，如果dom是真的，那就检查；如果dom是否的，那就跳过这次检查；不允许是unknown
		for _, domFact := range uniFactAsUniFactStmt.DomFacts {
			_, ok := domFact.(ast.Spec_OrFact)
			if !ok {
				return nil, fmt.Errorf("dom facts of universal fact must be reversible")
			}
		}
	}

	if len(tb.body) == 1 {
		return ast.NewProveOverFiniteSetStmt(uniFactAsUniFactStmt, []ast.StmtSlice{}), nil
	}

	err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	proofs := []ast.StmtSlice{}
	for i := 1; i < len(tb.body); i++ {
		curProof := ast.StmtSlice{}
		for _, stmt := range tb.body[i].body {
			curStmt, err := stmt.Stmt()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			curProof = append(curProof, curStmt)
		}
		proofs = append(proofs, curProof)
	}

	return ast.NewProveOverFiniteSetStmt(uniFactAsUniFactStmt, proofs), nil
}

func (tb *tokenBlock) bodyOfKnowProp() ([]ast.FactStmt, []ast.FactStmt, error) {
	var err error
	iffFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}

	// if tb.body[len(tb.body)-1].header.is(glob.KeywordThen) {
	if tb.body[len(tb.body)-1].header.is(glob.KeySymbolEqualLarger) {
		for i := range len(tb.body) - 1 {
			iffFact, err := tb.body[i].factStmt(UniFactDepth1)
			if err != nil {
				return nil, nil, tbErr(err, tb)
			}
			iffFacts = append(iffFacts, iffFact)
		}

		// err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
		err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeySymbolEqualLarger)
		if err != nil {
			return nil, nil, tbErr(err, tb)
		}

		for _, stmt := range tb.body[len(tb.body)-1].body {
			curStmt, err := stmt.factStmt(UniFactDepth1)
			if err != nil {
				return nil, nil, tbErr(err, tb)
			}
			thenFacts = append(thenFacts, curStmt)
		}

		return iffFacts, thenFacts, nil
	} else {
		for i := range len(tb.body) {
			thenFact, err := tb.body[i].factStmt(UniFactDepth1)
			if err != nil {
				return nil, nil, tbErr(err, tb)
			}
			thenFacts = append(thenFacts, thenFact)
		}

		return iffFacts, thenFacts, nil
	}
}

// func (tb *tokenBlock) headerOfAtProp() (*ast.DefHeader, error) {
// 	var err error
// 	err = tb.header.skip(glob.KeySymbolAt)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	declHeader, err := tb.defHeaderWithoutParsingColonAtEnd()
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolColon)
// 	if err != nil {
// 		return nil, tbErr(err, tb)
// 	}

// 	if !tb.header.ExceedEnd() {
// 		return nil, fmt.Errorf("expect end of @ body, but got '%s'", tb.header.strAtCurIndexPlus(0))
// 	}

// 	return declHeader, nil
// }

func (tb *tokenBlock) haveObjInNonEmptySetStmt() (*ast.HaveObjInNonEmptySetStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	objNames, objSets, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolColon, true)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if len(objNames) == 0 {
		return nil, fmt.Errorf("expect at least one object")
	}

	return ast.NewHaveObjInNonEmptySetStmt(objNames, objSets), nil
}

func (tb *tokenBlock) haveSetStmt() (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeywordSet)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	haveSetName, err := tb.header.next()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColonEqual)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	fact, err := tb.enumStmt_or_intensionalSetStmt_or_DomOf(ast.FcAtom(haveSetName))
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewHaveSetStmt(fact), nil
}

func (tb *tokenBlock) haveSetFnStmt() (ast.Stmt, error) {
	tb.header.skip(glob.KeywordHave)
	tb.header.skip(glob.KeywordSet)
	tb.header.skip(glob.KeywordFn)

	declHeader, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColonEqual)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	param, parentSet, proofs, err := tb.intentionalSetBody()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewHaveSetFnStmt(declHeader, param, parentSet, proofs), nil
}

func (tb *tokenBlock) haveSetDefinedByReplacementStmt() (ast.Stmt, error) {
	tb.header.skip(glob.KeywordHave)
	tb.header.skip(glob.KeywordSet)

	setName, err := tb.header.next()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeywordSetDefinedByReplacement)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	domSet, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	rangeSet, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	propName, err := tb.rawFcAtom()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// exceed end
	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ast.NewHaveSetDefinedByReplacementStmt(setName, domSet, rangeSet, propName), nil
}

func (tb *tokenBlock) namedUniFactStmt() (*ast.NamedUniFactStmt, error) {
	var err error
	err = tb.header.skip(glob.KeySymbolAt)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	declHeader, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.header.ExceedEnd() {
		iffFacts, thenFacts, err := tb.bodyOfKnowProp()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewNamedUniFactStmt(ast.NewDefPropStmt(declHeader, []ast.FactStmt{}, iffFacts, thenFacts)), nil
	} else {
		iffFact, err := tb.domFactInUniFactInterface()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		thenFact, err := tb.thenFacts_SkipEnd_Semicolon_or_EOL()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewNamedUniFactStmt(ast.NewDefPropStmt(declHeader, []ast.FactStmt{}, iffFact, thenFact)), nil
	}
}

// TODO: 让 forall 里也能有它
func (tb *tokenBlock) equalsFactStmt() (*ast.EqualsFactStmt, error) {
	tb.header.skip(glob.KeySymbolEqual)

	if tb.header.is(glob.KeySymbolColon) {
		err := tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if tb.header.ExceedEnd() {
			params := make(ast.FcSlice, 0, len(tb.body))
			for _, param := range tb.body {
				param, err := param.RawFc()
				if err != nil {
					return nil, tbErr(err, tb)
				}
				params = append(params, param)
			}

			if len(params) < 2 {
				return nil, fmt.Errorf("expect at least two params")
			}

			return ast.NewEqualsFactStmt(params), nil
		} else {
			params := []ast.Fc{}
			for {
				curFc, err := tb.RawFc()
				if err != nil {
					return nil, tbErr(err, tb)
				}
				params = append(params, curFc)

				if tb.header.is(glob.KeySymbolComma) {
					tb.header.skip(glob.KeySymbolComma)
					continue
				}

				if tb.header.ExceedEnd() {
					break
				}
			}

			return ast.NewEqualsFactStmt(params), nil
		}
	} else {
		err := tb.header.skip(glob.KeySymbolLeftBrace)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		params := []ast.Fc{}
		for {
			curFc, err := tb.RawFc()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			params = append(params, curFc)

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
				continue
			}

			if tb.header.is(glob.KeySymbolRightBrace) {
				tb.header.skip(glob.KeySymbolRightBrace)
				break
			}
		}

		return ast.NewEqualsFactStmt(params), nil
	}
}

func (tb *tokenBlock) knowExistPropStmt() (*ast.KnowExistPropStmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolAt)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	existParams, existParamSets, err := tb.param_paramSet_paramInSetFacts(glob.KeywordSt, false)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if len(existParams) == 0 {
		return nil, fmt.Errorf("expect at least one parameter in exist prop definition")
	}

	def, err := tb.defExistPropStmtBody()

	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewKnowExistPropStmt(*ast.NewDefExistPropStmt(def, existParams, existParamSets)), nil
}

func (tb *tokenBlock) commentStmt() (ast.Stmt, error) {
	comment := tb.header.strAtCurIndexPlus(1)
	tb.header.skip(glob.CommentSig)
	tb.header.skip("")

	return ast.NewCommentStmt(comment), nil
}

func (tb *tokenBlock) fnTemplateStmt() (ast.Stmt, error) {
	tb.header.skipNext()
	defHeader, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	if len(tb.body) == 1 {
		fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := tb.body[0].fnInFnTemplateStmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewFnTemplateStmt(defHeader, []ast.FactStmt{}, fnParams, fnParamSets, fnRetSet, domFacts, thenFacts), nil
	} else if len(tb.body) >= 2 {
		if tb.body[0].header.is(glob.KeywordDom) {
			err = tb.body[0].header.skipKwAndColon_ExceedEnd(glob.KeywordDom)
			if err != nil {
				return nil, tbErr(err, tb)
			}

			templateDomFacts, err := tb.body[0].bodyFacts(UniFactDepth1)
			if err != nil {
				return nil, tbErr(err, tb)
			}

			fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := tb.body[1].fnInFnTemplateStmt()
			if err != nil {
				return nil, tbErr(err, tb)
			}

			return ast.NewFnTemplateStmt(defHeader, templateDomFacts, fnParams, fnParamSets, fnRetSet, domFacts, thenFacts), nil
		} else {
			templateDomFacts := []ast.FactStmt{}
			for i := range len(tb.body) - 1 {
				curStmt, err := tb.body[i].factStmt(UniFactDepth1)
				if err != nil {
					return nil, tbErr(err, tb)
				}
				templateDomFacts = append(templateDomFacts, curStmt)
			}

			fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := tb.body[len(tb.body)-1].fnInFnTemplateStmt()
			if err != nil {
				return nil, tbErr(err, tb)
			}

			return ast.NewFnTemplateStmt(defHeader, templateDomFacts, fnParams, fnParamSets, fnRetSet, domFacts, thenFacts), nil
		}
	} else {
		return nil, fmt.Errorf("expect one or two body blocks")
	}

}

func (tb *tokenBlock) fnInFnTemplateStmt() ([]string, []ast.Fc, ast.Fc, []ast.FactStmt, []ast.FactStmt, error) {
	var err error

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, nil, nil, nil, nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, nil, nil, nil, nil, tbErr(err, tb)
	}

	fnParams, fnParamSets, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolRightBrace, false)
	if err != nil {
		return nil, nil, nil, nil, nil, tbErr(err, tb)
	}

	fnRetSet, err := tb.RawFc()
	if err != nil {
		return nil, nil, nil, nil, nil, tbErr(err, tb)
	}

	if tb.header.ExceedEnd() {
		return fnParams, fnParamSets, fnRetSet, []ast.FactStmt{}, []ast.FactStmt{}, nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, nil, nil, nil, nil, tbErr(err, tb)
	}

	// domFacts, thenFacts, err := tb.dom_and_section(glob.KeywordThen, glob.KeywordIff)
	// domFacts, thenFacts, err := tb.dom_and_section(glob.KeySymbolEqualLarger, glob.KeywordIff)
	domFacts, thenFacts, err := tb.dom_and_section(glob.KeySymbolEqualLarger, glob.KeySymbolEquivalent)
	if err != nil {
		return nil, nil, nil, nil, nil, tbErr(err, tb)
	}

	return fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, nil
}

func (tb *tokenBlock) clearStmt() (ast.Stmt, error) {
	err := tb.header.skip(glob.KeywordClear)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ast.NewClearStmt(), nil
}

func (tb *tokenBlock) factsStmt() (ast.Stmt, error) {
	if tb.GetEnd() != glob.KeySymbolColon { // 因为可能是 forall : 这样的
		facts, err := tb.inlineFacts_checkUniDepth0()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if len(facts) == 1 {
			return facts[0], nil
		}

		return ast.NewInlineFactsStmt(facts), nil
	} else {
		return tb.factStmt(UniFactDepth0)
	}
}

func (tb *tokenBlock) claimStmtInline() (ast.ClaimInterface, error) {
	var fact ast.FactStmt
	var err error
	var namedUniFact *ast.NamedUniFactStmt

	if tb.header.is(glob.KeySymbolAt) {
		// 有点小问题，最好必须要规定是named inline
		namedUniFact, err = tb.namedUniFactStmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
	} else {
		fact, err = tb.inlineFact()
		if err != nil {
			return nil, tbErr(err, tb)
		}
	}

	isProve := true
	if tb.header.is(glob.KeySymbolColon) {
		err := tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

	} else if tb.header.is(glob.KeywordProveByContradiction) {
		err := tb.header.skipKwAndColon_ExceedEnd(glob.KeywordProveByContradiction)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		isProve = false
	} else if tb.header.is(glob.KeywordProve) {
		err := tb.header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
		if err != nil {
			return nil, tbErr(err, tb)
		}
	} else {
		return ast.NewClaimProveStmt(fact, []ast.Stmt{}), nil
	}

	proof := []ast.Stmt{}
	for _, block := range tb.body {
		curStmt, err := block.Stmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		proof = append(proof, curStmt)
	}

	if namedUniFact != nil {
		return ast.NewClaimPropStmt(&namedUniFact.DefPropStmt, proof, isProve), nil
	} else if isProve {
		return ast.NewClaimProveStmt(fact, proof), nil
	} else {
		return ast.NewClaimProveByContradictionStmt(*ast.NewClaimProveStmt(fact, proof)), nil
	}
}

func (tb *tokenBlock) proveByInductionStmt() (*ast.ProveByInductionStmt, error) {
	err := tb.header.skip(glob.KeywordProveByInduction)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	fact, err := tb.specFactStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	param, err := tb.header.next()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if !tb.header.is(glob.KeySymbolComma) {
		err = tb.header.skip(glob.KeySymbolRightBrace)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		return ast.NewProveByInductionStmt(fact, param, ast.FcAtom("1")), nil
	} else {
		err = tb.header.skip(glob.KeySymbolComma)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		start, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolRightBrace)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewProveByInductionStmt(fact, param, start), nil
	}
}

func (tb *tokenBlock) haveObjEqualStmt() (*ast.HaveObjEqualStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	objectNames := []string{}
	objectEqualTos := []ast.Fc{}
	setSlice := []ast.Fc{}

	for !tb.header.is(glob.KeySymbolEqual) {
		objectName, err := tb.header.next()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		objectNames = append(objectNames, objectName)

		set, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		setSlice = append(setSlice, set)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	for !tb.header.ExceedEnd() {
		objectEqualTo, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		objectEqualTos = append(objectEqualTos, objectEqualTo)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	if len(objectEqualTos) != len(setSlice) {
		return nil, fmt.Errorf("number of objects and sets do not match")
	}

	return ast.NewHaveObjEqualStmt(objectNames, objectEqualTos, setSlice), nil
}

func (tb *tokenBlock) haveFnEqualStmt() (*ast.HaveFnEqualStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	defHeader, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	retSet, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	equalTo, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewHaveFnEqualStmt(defHeader, retSet, equalTo), nil
}

func (tb *tokenBlock) haveFnLiftStmt() (*ast.HaveFnLiftStmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	fnName, err := tb.header.next()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeywordLift)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	opt, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	domainOfEachParamOfGivenFn := []ast.Fc{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		curDomain, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}

		domainOfEachParamOfGivenFn = append(domainOfEachParamOfGivenFn, curDomain)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewHaveFnLiftStmt(fnName, opt, domainOfEachParamOfGivenFn), nil
}

func (tb *tokenBlock) claimHaveFnStmt() (*ast.HaveFnStmt, error) {
	var err error

	if len(tb.body) != 3 {
		return nil, fmt.Errorf("expect 3 body blocks")
	}

	err = tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	defFnStmt, err := tb.body[0].defFnStmt(false)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.body[1].header.skip(glob.KeywordProve)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	proof := []ast.Stmt{}
	for _, block := range tb.body[1].body {
		curStmt, err := block.Stmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		proof = append(proof, curStmt)
	}

	err = tb.body[2].header.skip(glob.KeywordHave)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	haveObjSatisfyFn, err := tb.body[2].RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewClaimHaveFnStmt(defFnStmt, proof, haveObjSatisfyFn), nil
}
