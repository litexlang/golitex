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
	"path/filepath"
	"slices"
	"strconv"
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
		ret, err = tb.defFnStmt()
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
		} else if slices.Contains(tb.header.slice, glob.KeywordSt) {
			ret, err = tb.haveObjStStmt()
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
	case glob.KeywordProveByMathInduction:
		ret, err = tb.proveByMathInductionStmt()
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

	if tb.header.ExceedEnd() {
		for _, factToParse := range tb.body {
			fact, err := factToParse.specFactStmt()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			orFacts = append(orFacts, fact)
		}

	} else {
		for {
			fact, err := tb.specFactStmt()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			orFacts = append(orFacts, fact)

			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
			} else if tb.header.ExceedEnd() {
				break
			} else {
				return nil, fmt.Errorf("expect ',' or end of line")
			}
		}
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
			return nil, tbErr(err, tb)
		}
		if isTrue {
			return ret, nil
		} else {
			return ret.ReverseTrue(), nil
		}
	} else {
		ret, err := tb.relaFactStmt()
		if err != nil {
			return nil, tbErr(err, tb)
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
		return nil, tbErr(err, tb)
	}

	params, setParams, err := tb.param_paramSet_paramInSetFacts(glob.KeySymbolColon, false)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(uniFactDepth.addDepth(), glob.KeywordThen)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if len(iffFacts) == 0 {
		return ast.NewUniFact(params, setParams, domainFacts, thenFacts), nil
	} else {
		ret := ast.NewUniFactWithIff(ast.NewUniFact(params, setParams, domainFacts, thenFacts), iffFacts)

		if len(thenFacts) == 0 {
			return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeywordThen, ret)
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
			unitFacts, err := tb.inlineFacts_untilEndOfInline()
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
		domFacts, iffFacts, err := tb.dom_and_section(glob.KeywordIff, glob.KeywordThen)
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
		// facts, err := tb.inlineFacts_untilEOL()
		// if err != nil {
		// 	return nil, tbErr(err, tb)
		// }
		// return ast.NewDefObjStmt(objNames, objSets, facts), nil
		facts, err := tb.inlineFacts_untilEndOfInline()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		err = checkFactsUniDepth(facts)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewDefObjStmt(objNames, objSets, facts), nil
	}

	// if len(objSets) > 0 {
	// 	tb.header.skip("")
	// 	facts, err = tb.bodyFacts(UniFactDepth0)
	// 	if err != nil {
	// 		return nil, tbErr(err, tb)
	// 	}
	// } else if !tb.header.ExceedEnd() {
	// 	return nil, fmt.Errorf("expect ':' or end of block")
	// }

}

func (tb *tokenBlock) claimStmt() (ast.ClaimInterface, error) {
	err := tb.header.skip(glob.KeywordClaim)
	if err != nil {
		return nil, tbErr(err, tb)
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
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction' after claim")
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
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
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
		facts := ast.FactStmtSlice{}
		fact, err := tb.factStmt(UniFactDepth0)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, fact) // 之所以不能用,让know后面同一行里能有很多很多事实，是因为forall-fact是会换行的
		return ast.NewKnowStmt(facts.ToCanBeKnownStmtSlice()), nil

	}

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, tbErr(err, tb)
	}

	var err error
	var facts ast.FactStmtSlice = ast.FactStmtSlice{}
	if tb.header.ExceedEnd() {
		facts, err = tb.bodyFacts(UniFactDepth0)
		if err != nil {
			return nil, tbErr(err, tb)
		}
	} else {
		facts, err = tb.inlineFacts_untilEndOfInline()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		err = checkFactsUniDepth(facts)
		if err != nil {
			return nil, tbErr(err, tb)
		}
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

	pureSpecFact, err := tb.pureFuncSpecFact()
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
		unitFacts, err := tb.inlineFacts_untilEndOfInline()
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

		domFacts, iffFactsAsFactStatements, err := tb.dom_and_section(glob.KeywordIff, glob.KeywordThen)
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

	// declHeader, err := tb.headerOfAtProp()
	// if err != nil {
	// 	return nil, tbErr(err, tb)
	// }

	// iffFacts, thenFacts, err := tb.bodyOfKnowProp()
	// if err != nil {
	// 	return nil, tbErr(err, tb)
	// }

	// return ast.NewKnowPropStmt(*ast.NewDefPropStmt(declHeader, []ast.FactStmt{}, iffFacts, thenFacts)), nil

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
	err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
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

func (tb *tokenBlock) defFnStmt() (*ast.DefFnStmt, error) {
	err := tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	decl, err := tb.defHeaderWithoutParsingColonAtEnd()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	retSet, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	domFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip("")
		if tb.header.ExceedEnd() {
			domFacts, thenFacts, err = tb.dom_and_section(glob.KeywordThen, glob.KeywordIff)
			if err != nil {
				return nil, tbErr(err, tb)
			}
		} else {
			domFacts, thenFacts, err = tb.bodyOfInlineDomAndThen(glob.KeySymbolEqualLarger)
			if err != nil {
				return nil, tbErr(err, tb)
			}
		}
	} else if tb.header.is(glob.KeySymbolEqualLarger) {
		err = tb.header.skip(glob.KeySymbolEqualLarger)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		unitFacts, err := tb.inlineFacts_untilEndOfInline()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		thenFacts = append(thenFacts, unitFacts...)
	}

	return ast.NewDefFnStmt(string(decl.Name), ast.NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts)), nil
}

func (tb *tokenBlock) claimPropStmt() (*ast.ClaimPropStmt, error) {
	declHeader, err := tb.body[0].headerOfAtProp()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	iffFacts, thenFacts, err := tb.body[0].bodyOfKnowProp()
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

	return ast.NewClaimPropStmt(ast.NewDefPropStmt(declHeader, []ast.FactStmt{}, iffFacts, thenFacts), proofs, isProve), nil
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

func (tb *tokenBlock) proveByMathInductionStmt() (*ast.ProveByMathInductionStmt, error) {
	var err error
	var paramIndex int = 0
	var start int = 0

	err = tb.header.skip(glob.KeywordProveByMathInduction)
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

	if tb.header.is(glob.KeySymbolComma) {
		tb.header.skip(glob.KeySymbolComma)
		paramIndexAsStr, err := tb.header.next()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		paramIndex, err = strconv.Atoi(paramIndexAsStr)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
			startAsStr, err := tb.header.next()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			start, err = strconv.Atoi(startAsStr)
			if err != nil {
				return nil, tbErr(err, tb)
			}
		}
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// 第ParamIndex个参数必须是atom

	return ast.NewProveByMathInductionStmt(fact, paramIndex, start), nil
}

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
		return nil, fmt.Errorf("%s expect universal fact without dom facts", glob.KeywordProveOverFiniteSet)
	}

	if len(tb.body) == 1 {
		return ast.NewProveOverFiniteSetStmt(uniFactAsUniFactStmt, []ast.Stmt{}), nil
	}

	err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordProve)
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

	return ast.NewProveOverFiniteSetStmt(uniFactAsUniFactStmt, proofs), nil
}

func (tb *tokenBlock) bodyOfKnowProp() ([]ast.FactStmt, []ast.FactStmt, error) {
	var err error
	iffFacts := []ast.FactStmt{}
	thenFacts := []ast.FactStmt{}

	if tb.body[len(tb.body)-1].header.is(glob.KeywordThen) {
		for i := range len(tb.body) - 1 {
			iffFact, err := tb.body[i].factStmt(UniFactDepth1)
			if err != nil {
				return nil, nil, tbErr(err, tb)
			}
			iffFacts = append(iffFacts, iffFact)
		}

		err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
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

func (tb *tokenBlock) headerOfAtProp() (*ast.DefHeader, error) {
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

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of @ body, but got '%s'", tb.header.strAtCurIndexPlus(0))
	}

	return declHeader, nil
}

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
		// iffFacts, thenFacts, err := tb.bodyOfInlineDomAndThen(glob.KeySymbolEqualLarger)
		// if err != nil {
		// 	return nil, tbErr(err, tb)
		// }

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
	} else if len(tb.body) == 2 {
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

	domFacts, thenFacts, err := tb.dom_and_section(glob.KeywordThen, glob.KeywordIff)
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
	if tb.GetEnd() != glob.KeySymbolColon {
		facts, err := tb.inlineFacts_untilEndOfInline()
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
