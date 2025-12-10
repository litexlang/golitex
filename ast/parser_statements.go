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

package litex_ast

import (
	"fmt"
	"strings"

	glob "golitex/glob"
	"slices"
)

func (p *TbParser) Stmt(tb *tokenBlock) (Stmt, error) {
	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	var ret Stmt
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
			ret, err = p.haveSetStmt(tb)
		} else if tb.header.strAtCurIndexPlus(1) == glob.KeywordFn {
			if tb.header.strAtCurIndexPlus(2) == glob.KeySymbolColon {
				ret, err = p.haveFnStmt(tb)
				// } else if tb.header.strAtCurIndexPlus(4) == glob.KeywordLift {
				// 	ret, err = tb.haveFnLiftStmt()
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

func (p *TbParser) defPropStmt(tb *tokenBlock) (Stmt, error) {
	body, err := p.defPropStmtWithoutSelfReferCheck(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = NoSelfReferenceInPropDef(string(body.DefHeader.Name), append(append(body.DomFacts, body.IffFacts...), body.ThenFacts...))
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return body, nil
}

func (p *TbParser) defPropStmtWithoutSelfReferCheck(tb *tokenBlock) (*DefPropStmt, error) {
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
			return NewDefPropStmt(declHeader, nil, nil, []FactStmt{}, tb.line), nil
		} else if tb.header.is(glob.KeySymbolEquivalent) {
			err = tb.header.skip(glob.KeySymbolEquivalent)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			unitFacts, err := p.inlineFacts_checkUniDepth1(tb, []string{})
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			return NewDefPropStmt(declHeader, []FactStmt{}, unitFacts, []FactStmt{}, tb.line), nil
		} else {
			return nil, fmt.Errorf("expect ':' or end of block")
		}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.ExceedEnd() {
		// domFacts, iffFacts, err := tb.dom_and_section(glob.KeywordIff, glob.KeywordThen)
		// domFacts, iffFacts, err := tb.dom_and_section(glob.KeywordIff, glob.KeySymbolEqualLarger)
		domFacts, iffFacts, err := p.dom_and_section(tb, glob.KeySymbolEquivalent, glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		// iff, dom 里不能出现和被定义的prop同名的prop，否则用def做验证的时候会出问题
		for _, fact := range iffFacts {
			if factAsSpecFact, ok := fact.(*SpecFactStmt); ok {
				if string(factAsSpecFact.PropName) == string(declHeader.Name) {
					return nil, fmt.Errorf("iff or dom fact cannot be the same as the prop being defined")
				}
			}
		}

		for _, fact := range domFacts {
			if factAsSpecFact, ok := fact.(*SpecFactStmt); ok {
				if string(factAsSpecFact.PropName) == string(declHeader.Name) {
					return nil, fmt.Errorf("iff or dom fact cannot be the same as the prop being defined")
				}
			}
		}

		return NewDefPropStmt(declHeader, domFacts, iffFacts, []FactStmt{}, tb.line), nil
	} else {
		domFacts, iffFacts, err := p.bodyOfInlineDomAndThen(tb, glob.KeySymbolEquivalent, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		return NewDefPropStmt(declHeader, domFacts, iffFacts, []FactStmt{}, tb.line), nil
	}
}

func (p *TbParser) defExistPropStmt(tb *tokenBlock, keyword string) (Stmt, error) {
	body, err := p.defExistPropStmtBodyWithoutSelfReferCheck(tb, keyword)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = NoSelfReferenceInPropDef(string(body.DefBody.DefHeader.Name), append(append(body.DefBody.DomFacts, body.DefBody.IffFacts...), body.DefBody.ThenFacts...))
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return body, nil
}

func (p *TbParser) defExistPropStmtBodyWithoutSelfReferCheck(tb *tokenBlock, head string) (*DefExistPropStmt, error) {
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

	return NewDefExistPropStmt(def, existParams, existParamSets, tb.line), nil
}

func (p *TbParser) defFnStmt(tb *tokenBlock, skipFn bool) (Stmt, error) {
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
	if asAtom, ok := retSet.(Atom); ok {
		if string(asAtom) == glob.KeySymbolColon {
			return nil, fmt.Errorf(": is not allowed in return set")
		}
	}

	domFacts := []FactStmt{}
	thenFacts := []FactStmt{}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip("")
		if tb.header.ExceedEnd() {
			domFacts, thenFacts, err = p.dom_and_section(tb, glob.KeySymbolRightArrow, glob.KeySymbolEquivalent)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
		} else {
			domFacts, err = p.inlineFacts_untilWord_or_exceedEnd_notSkipWord(tb, glob.KeySymbolRightArrow, []string{})
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			if !tb.header.is(glob.KeySymbolRightArrow) {
				return NewDefFnStmt(string(decl.Name), NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts, tb.line), tb.line), nil
			}

			err = tb.header.skip(glob.KeySymbolRightArrow)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			thenFacts, err = p.inlineFacts_untilEndOfInline(tb, []string{})
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
		}
	} else if tb.header.is(glob.KeySymbolRightArrow) {
		err = tb.header.skip(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		unitFacts, err := p.inlineFacts_checkUniDepth1(tb, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		thenFacts = append(thenFacts, unitFacts...)
	}

	return NewDefFnStmt(string(decl.Name), NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts, tb.line), tb.line), nil
}

func (p *TbParser) defObjStmt(tb *tokenBlock) (Stmt, error) {
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
		return NewDefLetStmt(objNames, objSets, []FactStmt{}, tb.line), nil
	} else if tb.header.ExceedEnd() && len(tb.body) != 0 {
		facts, err := p.bodyFacts(tb, UniFactDepth0)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return NewDefLetStmt(objNames, objSets, facts, tb.line), nil
	} else {
		facts, err := p.inlineFacts_checkUniDepth0(tb, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		err = checkFactsUniDepth0(facts)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		return NewDefLetStmt(objNames, objSets, facts, tb.line), nil
	}
}

func (p *TbParser) haveSetStmt(tb *tokenBlock) (Stmt, error) {
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

		cartObj, ok := rightObj.(*FnObj)
		if !ok {
			return nil, fmt.Errorf("expected cart to be FnObj")
		}

		if !IsFn_WithHeadName(rightObj, glob.KeywordCart) {
			return nil, fmt.Errorf("expected cart function call")
		}

		// Check end of line
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

		return NewHaveCartSetStmt(haveSetName, cartObj, tb.line), nil
	}

	obj, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if IsEnumSetObj(obj) {
		return NewHaveEnumSetStmt(haveSetName, obj.(*FnObj), tb.line), nil
	} else if IsIntensionalSetObj(obj) {
		param, parentSet, facts, err := GetParamParentSetFactsFromIntensionalSetObj(obj.(*FnObj))
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return NewHaveIntensionalSetStmt(param, parentSet, facts, tb.line), nil
	} else {
		return nil, fmt.Errorf("expect enum set or intensional set")
	}
}

func (p *TbParser) haveFnStmt(tb *tokenBlock) (Stmt, error) {
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

	defFnStmt, err := p.defFnStmt(&tb.body[0], false)
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

		proof := []Stmt{}
		for _, block := range tb.body[1].body {
			curStmt, err := p.Stmt(&block)
			if err != nil {
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
		}

		return NewClaimHaveFnStmt(defFnStmt.(*DefFnStmt), proof, haveObjSatisfyFn, tb.line), nil
	} else if len(tb.body) >= 2 && tb.body[1].header.is(glob.KeywordCase) {
		// Case-by-case structure: body[0] is defFnStmt, body[1..n] are case/equal pairs
		if (len(tb.body)-1)%2 != 0 {
			return nil, fmt.Errorf("expect even number of body blocks after defFnStmt for case-by-case (got %d)", len(tb.body)-1)
		}

		cases := []*SpecFactStmt{}
		proofs := []StmtSlice{}
		EqualTo := []Obj{}
		for i := 1; i < len(tb.body); i++ {
			if (i-1)%2 == 0 {
				// Case block
				err := tb.body[i].header.skip(glob.KeywordCase)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				curStmt, err := p.specFactStmt(&tb.body[i])
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				cases = append(cases, curStmt)
				err = tb.body[i].header.skip(glob.KeySymbolColon)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				curProof := StmtSlice{}
				for _, block := range tb.body[i].body {
					curStmt, err := p.Stmt(&block)
					if err != nil {
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

		return NewHaveFnCaseByCaseStmt(defFnStmt.(*DefFnStmt), cases, proofs, EqualTo, tb.line), nil
	} else {
		return nil, fmt.Errorf("expect 'prove:' or 'case' after defFnStmt in have fn statement")
	}
}

func (p *TbParser) haveFnEqualStmt(tb *tokenBlock) (Stmt, error) {
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

		return NewHaveFnEqualStmt(defHeader, retSet, equalTo, tb.line), nil
	} else {
		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		caseByCaseFacts := []*SpecFactStmt{}
		caseByCaseEqualTo := []Obj{}
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

		return &HaveFnEqualCaseByCaseStmt{
			DefHeader:         defHeader,
			RetSet:            retSet,
			CaseByCaseFacts:   caseByCaseFacts,
			CaseByCaseEqualTo: caseByCaseEqualTo,
			Line:              tb.line,
		}, nil
	}
}

func (p *TbParser) haveObjStStmt(tb *tokenBlock) (Stmt, error) {
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

	fact, err := p.specFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return NewHaveStmt(objNames, fact, tb.line), nil
}

func (p *TbParser) bodyBlockFacts(tb *tokenBlock, uniFactDepth uniFactEnum, parseBodyFactNum int) ([]FactStmt, error) {
	facts := []FactStmt{}

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

func (p *TbParser) defExistPropStmtBody(tb *tokenBlock) (*DefExistPropStmtBody, error) {
	declHeader, err := p.defHeaderWithoutParsingColonAtEnd(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.ExceedEnd() {
		return NewExistPropDef(declHeader, []FactStmt{}, []FactStmt{}, []FactStmt{}, tb.line), nil
	}

	if tb.header.is(glob.KeySymbolEquivalent) {
		err = tb.header.skip(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		unitFacts, err := p.inlineFacts_checkUniDepth1(tb, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return NewExistPropDef(declHeader, []FactStmt{}, unitFacts, []FactStmt{}, tb.line), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.ExceedEnd() {

		// domFacts, iffFactsAsFactStatements, err := tb.dom_and_section(glob.KeywordIff, glob.KeywordThen)
		// domFacts, iffFactsAsFactStatements, err := tb.dom_and_section(glob.KeywordIff, glob.KeySymbolEqualLarger)
		domFacts, iffFactsAsFactStatements, err := p.dom_and_section(tb, glob.KeySymbolEquivalent, glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if len(iffFactsAsFactStatements) == 0 {
			return nil, fmt.Errorf("expect 'iff' section in proposition definition has at least one fact")
		}

		return NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements, []FactStmt{}, tb.line), nil
	} else {
		domFacts, iffFactsAsFactStatements, err := p.bodyOfInlineDomAndThen(tb, glob.KeySymbolEquivalent, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		return NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements, []FactStmt{}, tb.line), nil
	}
}

func (p *TbParser) haveObjFromCartSetStmt(tb *tokenBlock) (Stmt, error) {
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

	cartSet, ok := cartSetObj.(*FnObj)
	if !ok {
		return nil, parserErrAtTb(fmt.Errorf("expected cart to be FnObj"), tb)
	}

	if !IsFn_WithHeadName(cartSetObj, glob.KeywordCart) {
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

	return NewHaveObjFromCartSetStmt(objName, cartSet, equalTo, tb.line), nil
}

func (p *TbParser) haveObjEqualStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	objectEqualTos := []Obj{}

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

	return NewHaveObjEqualStmt(objectNames, objectEqualTos, setSlice, tb.line), nil
}

func (p *TbParser) haveObjInNonEmptySetStmt(tb *tokenBlock) (Stmt, error) {
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

	return NewHaveObjInNonEmptySetStmt(objNames, objSets, tb.line), nil
}

func (p *TbParser) claimStmt(tb *tokenBlock) (Stmt, error) {
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
	proof := []Stmt{}

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

	if asUniFactWithIffStmt, ok := toCheck.(*UniFactWithIffStmt); ok {
		if !isProve {
			return nil, fmt.Errorf("prove_by_contradiction is not supported for iff statement")
		} else {
			err := tb.body[2].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			proof2 := []Stmt{}
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

			return NewClaimIffStmt(asUniFactWithIffStmt, proof, proof2, tb.line), nil
		}
	}

	if len(proof) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	if isProve {
		return NewClaimProveStmt(toCheck, proof, tb.line), nil
	} else {
		return NewClaimProveByContradictionStmt(NewClaimProveStmt(toCheck, proof, tb.line), tb.line), nil
	}
}

func (p *TbParser) proveStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProve)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(tb.body) == 0 {
		return nil, fmt.Errorf("expect proof")
	}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip(glob.KeySymbolColon)
		proof := []Stmt{}
		for _, stmt := range tb.body {
			curStmt, err := p.Stmt(&stmt)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			proof = append(proof, curStmt)
		}

		return NewProveStmt(proof, tb.line), nil
	} else {
		factToCheck, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, []string{glob.KeySymbolColon})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		proofs := []Stmt{}
		for _, stmt := range tb.body {
			curStmt, err := p.Stmt(&stmt)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			proofs = append(proofs, curStmt)
		}

		return NewClaimProveStmt(factToCheck, proofs, tb.line), nil
	}
}

func (p *TbParser) knowExistPropStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	existProp, err := p.atExistPropDefStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return NewKnowExistPropStmt(existProp, tb.line), nil
}

func (p *TbParser) knowPropStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	namedUniFactStmt, err := p.namedUniFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	namedUniFact, ok := namedUniFactStmt.(*NamedUniFactStmt)
	if !ok {
		return nil, fmt.Errorf("expected NamedUniFactStmt")
	}

	return NewKnowPropStmt(namedUniFact.DefPropStmt, tb.line), nil
}

func (p *TbParser) knowFactStmt(tb *tokenBlock) (Stmt, error) {
	tb.header.skip(glob.KeywordKnow)

	if !tb.header.is(glob.KeySymbolColon) {
		var facts FactStmtSlice = FactStmtSlice{}
		var err error
		facts, err = p.inlineFacts_checkUniDepth0(tb, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		err = checkFactsUniDepth0(facts)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return NewKnowStmt(facts.ToCanBeKnownStmtSlice(), tb.line), nil
	}

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	var err error
	var facts FactStmtSlice = FactStmtSlice{}
	facts, err = p.bodyFacts(tb, UniFactDepth0)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return NewKnowStmt(facts.ToCanBeKnownStmtSlice(), tb.line), nil
}

func (p *TbParser) proveInEachCaseStmt(tb *tokenBlock) (Stmt, error) {
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

		orFact, err := p.orStmt(&tb.body[0])
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		thenFacts := []FactStmt{}
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

		proofs := []StmtSlice{}
		for i := 2; i < len(tb.body); i++ {
			proof := StmtSlice{}

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

		return NewProveInEachCaseStmt(orFact, thenFacts, proofs, tb.line), nil
	} else {
		orFact, err := p.inlineOrFact(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		thenFacts := []FactStmt{}
		for !tb.header.is(glob.KeySymbolColon) {
			fact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, []string{glob.KeySymbolColon})
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			thenFacts = append(thenFacts, fact)
		}

		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		proofs := []StmtSlice{}
		for i := range len(tb.body) {
			proof := StmtSlice{}

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

		return NewProveInEachCaseStmt(orFact, thenFacts, proofs, tb.line), nil
	}
}

func (p *TbParser) proveCaseByCaseStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skipKwAndColonCheckEOL(glob.KeywordProveCaseByCase)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	caseFacts := []*SpecFactStmt{}
	thenFacts := FactStmtSlice{}
	proofs := []StmtSlice{}
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
			proof := StmtSlice{}
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
					thenFacts = append(thenFacts, curStmt)
				}
			} else {
				// Parse inline fact
				curStmt, err := p.factStmt(&block, UniFactDepth0)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				thenFacts = append(thenFacts, curStmt)
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

	return NewProveCaseByCaseStmt(caseFacts, thenFacts, proofs, tb.line), nil
}

func (p *TbParser) proveByEnum(tb *tokenBlock) (Stmt, error) {
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
	domFacts, thenFacts, proofs, err := p.parseDomThenProve(tb.body)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	uniFact := NewUniFact(params, paramSets, domFacts, thenFacts, tb.line)
	return NewProveByEnumStmt(uniFact, proofs, tb.line), nil
}

func (p *TbParser) namedUniFactStmt(tb *tokenBlock) (Stmt, error) {
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
		}

		return NewNamedUniFactStmt(NewDefPropStmt(declHeader, []FactStmt{}, iffFacts, thenFacts, tb.line), tb.line), nil
	} else {
		iffFact, err := p.inlineDomFactInUniFactInterface(tb, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		thenFact, err := p.thenFacts_SkipEnd_Semicolon_or_EOL(tb, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		return NewNamedUniFactStmt(NewDefPropStmt(declHeader, []FactStmt{}, iffFact, thenFact, tb.line), tb.line), nil
	}
}

func (p *TbParser) fnTemplateStmt(tb *tokenBlock) (Stmt, error) {
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
		fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := p.fnInFnTemplateStmt(&tb.body[0])
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		newFnTStruct := NewFnTStruct(fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, tb.body[0].line)

		return NewFnTemplateStmt(defHeader, []FactStmt{}, newFnTStruct, tb.line), nil
	} else if len(tb.body) >= 2 {
		if tb.body[0].header.is(glob.KeywordDom) {
			err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeywordDom)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			templateDomFacts, err := p.bodyFacts(&tb.body[0], UniFactDepth1)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := p.fnInFnTemplateStmt(&tb.body[1])
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			newFnTStruct := NewFnTStruct(fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, tb.body[1].line)

			return NewFnTemplateStmt(defHeader, templateDomFacts, newFnTStruct, tb.line), nil
		} else {
			templateDomFacts := []FactStmt{}
			for i := range len(tb.body) - 1 {
				curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}
				templateDomFacts = append(templateDomFacts, curStmt)
			}

			fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := p.fnInFnTemplateStmt(&tb.body[len(tb.body)-1])
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			newFnTStruct := NewFnTStruct(fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, tb.body[len(tb.body)-1].line)

			return NewFnTemplateStmt(defHeader, templateDomFacts, newFnTStruct, tb.line), nil
		}
	} else {
		return nil, fmt.Errorf("expect one or two body blocks")
	}
}

func (p *TbParser) fnInFnTemplateStmt(tb *tokenBlock) ([]string, []Obj, Obj, []FactStmt, []FactStmt, error) {
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
		return fnParams, fnParamSets, fnRetSet, []FactStmt{}, []FactStmt{}, nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, nil, nil, nil, nil, parserErrAtTb(err, tb)
	}

	// domFacts, thenFacts, err := tb.dom_and_section(glob.KeywordThen, glob.KeywordIff)
	// domFacts, thenFacts, err := tb.dom_and_section(glob.KeySymbolEqualLarger, glob.KeywordIff)
	domFacts, thenFacts, err := p.dom_and_section(tb, glob.KeySymbolRightArrow, glob.KeySymbolEquivalent)
	if err != nil {
		return nil, nil, nil, nil, nil, parserErrAtTb(err, tb)
	}

	return fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, nil
}

func (p *TbParser) clearStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordClear)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return NewClearStmt(tb.line), nil
}

func (p *TbParser) proveInRangeStmt(tb *tokenBlock) (Stmt, error) {
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

	domFacts := []FactStmt{}
	thenFacts := []FactStmt{}
	proofs := []Stmt{}

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
			domFacts = append(domFacts, curStmt)
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
			thenFacts = append(thenFacts, curStmt)
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
				proofs = append(proofs, curStmt)
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
					thenFacts = append(thenFacts, curStmt)
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
				proofs = append(proofs, curStmt)
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

	return NewProveInRangeStmt(param, start, end, domFacts, thenFacts, proofs, tb.line), nil
}

func (p *TbParser) proveIsTransitivePropStmt(tb *tokenBlock) (Stmt, error) {
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
	propAtom, ok := prop.(Atom)
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

	proofs := []Stmt{}
	for _, block := range tb.body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
	}
	return NewProveIsTransitivePropStmt(propAtom, params, proofs, tb.line), nil
}

func (p *TbParser) proveCommutativePropStmt(tb *tokenBlock) (Stmt, error) {
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

	proofs := []Stmt{}
	err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for _, block := range tb.body[0].body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	proofsRightToLeft := []Stmt{}
	err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for _, block := range tb.body[1].body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proofsRightToLeft = append(proofsRightToLeft, curStmt)
	}

	return NewProveIsCommutativePropStmt(specFact, proofs, proofsRightToLeft, tb.line), nil
}

func (p *TbParser) algoDefStmt(tb *tokenBlock) (Stmt, error) {
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

	stmts := []AlgoStmt{}
	for _, block := range tb.body {
		curStmt, err := p.algoStmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		stmts = append(stmts, curStmt)
	}

	return NewAlgoDefStmt(funcName, params, stmts, tb.line), nil
}

func (p *TbParser) evalStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordEval)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	objsToEval, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return NewEvalStmt(objsToEval, tb.line), nil
}

func (p *TbParser) defProveAlgoStmt(tb *tokenBlock) (Stmt, error) {
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

	stmts := []ProveAlgoStmt{}
	for _, block := range tb.body {
		curStmt, err := p.proveAlgoStmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		stmts = append(stmts, curStmt)
	}
	return NewDefProveAlgoStmt(funcName, params, stmts, tb.line), nil
}

func (p *TbParser) byStmt(tb *tokenBlock) (Stmt, error) {
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

	proveAlgoParams := []Obj{}
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
	return NewByStmt(proveAlgoName, proveAlgoParams, tb.line), nil
}

func (p *TbParser) proveByContradictionStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveByContradiction)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	toCheck, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, []string{glob.KeySymbolColon})
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	proofs := []Stmt{}
	for _, block := range tb.body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
	}
	return NewClaimProveByContradictionStmt(NewClaimProveStmt(toCheck, proofs, tb.line), tb.line), nil
}

func (p *TbParser) printStmt(tb *tokenBlock) (Stmt, error) {
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

	return NewPrintStmt(isFString, value, tb.line), nil
}

func (p *TbParser) helpStmt(tb *tokenBlock) (Stmt, error) {
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

	return NewHelpStmt(keyword, tb.line), nil
}

func (p *TbParser) doNothingStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordDoNothing)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return NewDoNothingStmt(tb.line), nil
}

func (p *TbParser) importDirStmt(tb *tokenBlock) (Stmt, error) {
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
		return NewImportFileStmt(path, tb.line), nil
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

	return NewImportStmt(path, asPkgName, tb.line), nil
}

func (p *TbParser) haveCartWithDimStmt(tb *tokenBlock) (Stmt, error) {
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
	facts := []FactStmt{}

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
		facts = append(facts, curStmt)
	}

	// 分类：如果下面body[1]是case开头的，那就说明是case-by-case结构；否则是普通结构
	if len(tb.body) != 3 {
		return nil, fmt.Errorf("expect 3 blocks of %s when not defining case-by-case, but got %d", glob.KeywordHaveCartWithDim, len(tb.body))
	}

	proofs := []Stmt{}
	err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	for _, stmt := range tb.body[1].body {
		curStmt, err := p.Stmt(&stmt)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
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

	return NewHaveCartWithDimStmt(name, cartDim, param, facts, proofs, equalTo, tb.line), nil
}

func (p *TbParser) factsStmt(tb *tokenBlock) (Stmt, error) {
	if tb.GetEnd() != glob.KeySymbolColon { // 因为可能是 forall : 这样的
		facts, err := p.inlineFacts_checkUniDepth0(tb, []string{})
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if len(facts) == 1 {
			return facts[0], nil
		}

		return NewInlineFactsStmt(facts, tb.line), nil
	} else {
		return p.factStmt(tb, UniFactDepth0)
	}
}

func (p *TbParser) proveByInductionStmt(tb *tokenBlock) (Stmt, error) {
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
		}
		return NewProveByInductionStmt(fact, param, Atom("1"), tb.line), nil
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

		return NewProveByInductionStmt(fact, param, start, tb.line), nil
	}
}

// ============================================================================
// Fact statement parsing methods (first 10 methods from parser_statements.go)
// ============================================================================

func (p *TbParser) factStmt(tb *tokenBlock, uniFactDepth uniFactEnum) (FactStmt, error) {
	if !tb.EndWith(glob.KeySymbolColon) {
		return p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, []string{})
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
			return uniFact.(FactStmt), nil
		} else {
			uniFact, err := p.inlineUniInterfaceSkipTerminator(tb, []string{})
			if err != nil {
				return nil, err
			}
			return uniFact.(FactStmt), nil
		}
	case glob.KeywordOr:
		return p.orStmt(tb)
	case glob.KeySymbolEqual:
		return p.equalsFactStmt(tb)
	default:
		return p.fact(tb)
	}
}

func (p *TbParser) orStmt(tb *tokenBlock) (*OrStmt, error) {
	if tb.GetEnd() != glob.KeySymbolColon {
		return p.inlineOrFact(tb)
	}

	orFacts := []*SpecFactStmt{}
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

	return NewOrStmt(orFacts, tb.line), nil
}

func (p *TbParser) SpecFactOrOrStmt(tb *tokenBlock) (FactStmt, error) {
	if tb.header.is(glob.KeywordOr) {
		return p.orStmt(tb)
	} else if tb.header.is(glob.KeySymbolEqual) {
		return p.equalsFactStmt(tb)
	} else {
		return p.specFactStmt(tb)
	}
}

func (p *TbParser) specFactStmt_ExceedEnd(tb *tokenBlock) (*SpecFactStmt, error) {
	ret, err := p.specFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ret, nil
}

func (p *TbParser) specFactStmt(tb *tokenBlock) (*SpecFactStmt, error) {
	stmt, err := p.specFactStmt_OrOneLineEqualsFact(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	switch astStmt := stmt.(type) {
	case *SpecFactStmt:
		return astStmt, nil
	default:
		return nil, fmt.Errorf("expect specific fact, get %s", astStmt.String())
	}
}

func (p *TbParser) specFactStmt_OrOneLineEqualsFact(tb *tokenBlock) (FactStmt, error) {
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

func (p *TbParser) specFactWithoutExist_WithoutNot(tb *tokenBlock) (*SpecFactStmt, error) {
	stmt, err := p.specFactWithoutExist_WithoutNot_Or_EqualsFact(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	switch astStmt := stmt.(type) {
	case *SpecFactStmt:
		return astStmt, nil
	default:
		return nil, fmt.Errorf("expect specific fact, get %s", astStmt.String())
	}
}

func (p *TbParser) specFactWithoutExist_WithoutNot_Or_EqualsFact(tb *tokenBlock) (FactStmt, error) {
	if tb.header.is(glob.FuncFactPrefix) {
		ret, err := p.pureFuncSpecFact(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return ret, nil
	} else {
		ret, err := p.relaFactStmt_orRelaEquals(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return ret, nil
	}
}

func (p *TbParser) uniFactInterface(tb *tokenBlock, uniFactDepth uniFactEnum) (UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	params, setParams, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolColon, false)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(uniFactDepth.addDepth(), glob.KeywordThen)
	domainFacts, thenFacts, iffFacts, err := p.uniFactBodyFacts(tb, uniFactDepth.addDepth(), glob.KeySymbolRightArrow)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if len(iffFacts) == 0 {
		if len(thenFacts) == 0 {
			return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeySymbolRightArrow, NewUniFact(params, setParams, domainFacts, thenFacts, tb.line))
		}

		return NewUniFact(params, setParams, domainFacts, thenFacts, tb.line), nil
	} else {
		ret := NewUniFactWithIff(NewUniFact(params, setParams, domainFacts, thenFacts, tb.line), iffFacts, tb.line)

		if len(thenFacts) == 0 {
			// return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeywordThen, ret)
			return nil, fmt.Errorf("expect %s section to have at least one fact in %s", glob.KeySymbolRightArrow, ret)
		}

		return ret, nil
	}
}

func (p *TbParser) bodyFacts(tb *tokenBlock, uniFactDepth uniFactEnum) ([]FactStmt, error) {
	facts := []FactStmt{}
	for _, f := range tb.body {
		fact, err := p.factStmt(&f, uniFactDepth)
		if err != nil {
			return nil, err
		}
		facts = append(facts, fact)
	}

	return facts, nil
}

// Placeholder methods - to be implemented later
func (p *TbParser) equalsFactStmt(tb *tokenBlock) (*EqualsFactStmt, error) {
	tb.header.skip(glob.KeySymbolEqual)

	if tb.header.is(glob.KeySymbolColon) {
		err := tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		if tb.header.ExceedEnd() {
			params := make(ObjSlice, 0, len(tb.body))
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

			return NewEqualsFactStmt(params, tb.line), nil
		} else {
			params := []Obj{}
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

			return NewEqualsFactStmt(params, tb.line), nil
		}
	} else {
		err := tb.header.skip(glob.KeySymbolLeftBrace)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		params := []Obj{}
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

		return NewEqualsFactStmt(params, tb.line), nil
	}
}

func (p *TbParser) fact(tb *tokenBlock) (FactStmt, error) {
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
		}
		return ret, nil
	} else {
		ret, err := p.relaFact_intensionalSetFact_enumStmt_equals(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		return ret, nil
	}
}

func (p *TbParser) existFactStmt(tb *tokenBlock, isTrue bool) (*SpecFactStmt, error) {
	err := tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	existParams := []Obj{}

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

	factParams := MakeExistFactParamsSlice(existParams, pureSpecFact.Params)

	if isTrue {
		return NewSpecFactStmt(TrueExist_St, pureSpecFact.PropName, factParams, tb.line), nil
	} else {
		return NewSpecFactStmt(FalseExist_St, pureSpecFact.PropName, factParams, tb.line), nil
	}
}

func (p *TbParser) pureFuncSpecFact(tb *tokenBlock) (*SpecFactStmt, error) {
	if tb.header.is(glob.FuncFactPrefix) {
		tb.header.skip(glob.FuncFactPrefix)
	}

	propName, err := p.notNumberAtom(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	params := []Obj{}
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

	ret := NewSpecFactStmt(TruePure, propName, params, tb.line)

	return ret, nil
}

func (p *TbParser) relaFactStmt_orRelaEquals(tb *tokenBlock) (FactStmt, error) {
	var ret *SpecFactStmt

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
			ret = NewSpecFactStmt(TruePure, propName, []Obj{obj}, tb.line)
		} else {
			obj2, err := p.Obj(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			params := []Obj{obj, obj2}

			ret = NewSpecFactStmt(TruePure, propName, params, tb.line)
		}
	} else if !glob.IsBuiltinInfixRelaPropSymbol(opt) {
		return nil, fmt.Errorf("expect relation prop")
	} else {
		obj2, err := p.Obj(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		params := []Obj{obj, obj2}

		if opt != glob.KeySymbolEqual {
			ret = NewSpecFactStmt(TruePure, Atom(opt), params, tb.line)
		} else {
			// 循环地看下面一位是不是 = ，直到不是
			if tb.header.is(glob.KeySymbolEqual) {
				return p.relaEqualsFactStmt(tb, obj, obj2)
			} else {
				ret = NewSpecFactStmt(TruePure, Atom(opt), params, tb.line)
			}
		}
	}

	// 这里加入语法糖：!= 等价于 not =，好处是我 = 有 commutative的性质，我不用额外处理 != 了
	if ret.NameIs(glob.KeySymbolNotEqual) {
		ret.TypeEnum = FalsePure
		ret.PropName = Atom(glob.KeySymbolEqual)
	}

	return ret, nil
}

func (p *TbParser) param_paramSet_paramInSetFacts(tb *tokenBlock, endWith string, allowExceedEnd bool) ([]string, []Obj, error) {
	params := []string{}
	setParams := []Obj{}
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
		atomsInSetParam := GetAtomsInObj(setParam)
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

func (p *TbParser) defHeaderWithoutParsingColonAtEnd(tb *tokenBlock) (*DefHeader, error) {
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

	return NewDefHeader(Atom(name), params, setParams), nil
}

func (p *TbParser) uniFactBodyFacts(tb *tokenBlock, uniFactDepth uniFactEnum, defaultSectionName string) ([]FactStmt, []FactStmt, []FactStmt, error) {
	domFacts := []FactStmt{}
	thenFacts := []FactStmt{}
	iffFacts := []FactStmt{}
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
		thenFacts, err = p.bodyBlockFacts(&tb.body[len(tb.body)-1], uniFactDepth, len(tb.body[len(tb.body)-1].body))
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
			domFacts, err = p.bodyBlockFacts(&tb.body[0], uniFactDepth, len(tb.body[0].body))
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
			thenFacts, err = p.bodyBlockFacts(&tb.body[len(tb.body)-2], uniFactDepth, len(tb.body[len(tb.body)-2].body))
			if err != nil {
				return nil, nil, nil, err
			}

		} else if tb.body[0].header.is(glob.KeySymbolRightArrow) {
			err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
			if err != nil {
				return nil, nil, nil, err
			}
			thenFacts, err = p.bodyBlockFacts(&tb.body[0], uniFactDepth, len(tb.body[0].body))
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
				thenFacts, err = p.bodyBlockFacts(&tb.body[len(tb.body)-2], uniFactDepth, len(tb.body[len(tb.body)-2].body))
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

		// thenFacts, err = tb.bodyBlockFacts(uniFactDepth, len(tb.body)-1)
		// if err != nil {
		// 	return nil, nil, nil, err
		// }

		// err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordIff)
		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, nil, nil, err
		}
		iffFacts, err = p.bodyBlockFacts(&tb.body[len(tb.body)-1], uniFactDepth, len(tb.body[len(tb.body)-1].body))
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

func (p *TbParser) parseFactBodyWithHeaderNameAndUniFactDepth(tb *tokenBlock, headerName string, uniFactDepth uniFactEnum) ([]FactStmt, error) {
	err := tb.header.skipKwAndColonCheckEOL(headerName)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	facts := []FactStmt{}
	for _, stmt := range tb.body {
		curStmt, err := p.factStmt(&stmt, uniFactDepth)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		facts = append(facts, curStmt)
	}
	return facts, nil
}

func (p *TbParser) getStringInDoubleQuotes(tb *tokenBlock) (string, error) {
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

// Placeholder methods for functions that will be implemented later
func (p *TbParser) dom_and_section(tb *tokenBlock, kw string, kw_should_not_exist_in_body string) ([]FactStmt, []FactStmt, error) {
	if len(tb.body) == 0 {
		return nil, nil, fmt.Errorf("expect dom or section")
	}

	var err error
	domFacts, sectionFacts := []FactStmt{}, []FactStmt{}

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
			sectionFacts = append(sectionFacts, curStmt)
		}
		return domFacts, sectionFacts, nil
	} else if !tb.body[0].header.is(glob.KeywordDom) && tb.body[len(tb.body)-1].header.is(kw) {
		for i := range len(tb.body) - 1 {
			curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
			if err != nil {
				return nil, nil, parserErrAtTb(err, tb)
			}
			domFacts = append(domFacts, curStmt)
		}
		sectionFacts, err = p.parseFactBodyWithHeaderNameAndUniFactDepth(&tb.body[len(tb.body)-1], kw, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else if len(tb.body) == 2 && tb.body[0].header.is(glob.KeywordDom) && tb.body[1].header.is(kw) {
		domFacts, err = p.parseFactBodyWithHeaderNameAndUniFactDepth(&tb.body[0], glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		}
		sectionFacts, err = p.parseFactBodyWithHeaderNameAndUniFactDepth(&tb.body[1], kw, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else if len(tb.body) == 1 && tb.body[0].header.is(glob.KeywordDom) {
		domFacts, err = p.parseFactBodyWithHeaderNameAndUniFactDepth(&tb.body[0], glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, parserErrAtTb(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else {
		return nil, nil, fmt.Errorf("unexpected body structure in dom_and_section")
	}
}

func (p *TbParser) claimNamedUniFactInline(tb *tokenBlock) (Stmt, error) {
	var namedUniFact *NamedUniFactStmt

	if tb.header.is(glob.KeySymbolAt) {
		// 有点小问题，最好必须要规定是named inline
		namedUniFactResult, err := p.namedUniFactStmt(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		namedUniFact = namedUniFactResult.(*NamedUniFactStmt)
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
		// return NewClaimProveStmt(fact, []Stmt{}, tb.line), nil
		return nil, fmt.Errorf("expect proof after claim")
	}

	proof := []Stmt{}
	for _, block := range tb.body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proof = append(proof, curStmt)
	}

	if len(proof) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	return NewClaimPropStmt(namedUniFact.DefPropStmt, proof, tb.line), nil
}

func (p *TbParser) claimExistPropStmt(tb *tokenBlock) (Stmt, error) {
	if len(tb.body) != 3 {
		return nil, fmt.Errorf("expect 3 body blocks")
	}

	existProp, err := p.atExistPropDefStmt(&tb.body[0])
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	proofs := []Stmt{}
	for _, stmt := range tb.body[1].body {
		curStmt, err := p.Stmt(&stmt)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	err = tb.body[2].header.skip(glob.KeywordHave)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	haveObj := []Obj{}
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

	return NewClaimExistPropStmt(existProp, proofs, haveObj, tb.line), nil
}

func (p *TbParser) claimPropStmt(tb *tokenBlock) (Stmt, error) {
	namedUniFactStmt, err := p.namedUniFactStmt(&tb.body[0])
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	namedUniFact, ok := namedUniFactStmt.(*NamedUniFactStmt)
	if !ok {
		return nil, fmt.Errorf("expected NamedUniFactStmt")
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

	proofs := []Stmt{}
	for _, stmt := range tb.body[1].body {
		curStmt, err := p.Stmt(&stmt)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	if len(proofs) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	// return NewClaimPropStmt(NewDefPropStmt(declHeader, []FactStmt{}, iffFacts, thenFacts), proofs, isProve), nil
	return NewClaimPropStmt(NewDefPropStmt(namedUniFact.DefPropStmt.DefHeader, namedUniFact.DefPropStmt.DomFacts, namedUniFact.DefPropStmt.IffFacts, namedUniFact.DefPropStmt.ThenFacts, tb.line), proofs, tb.line), nil
}

func (p *TbParser) relaEqualsFactStmt(tb *tokenBlock, obj, obj2 Obj) (*EqualsFactStmt, error) {
	params := []Obj{obj, obj2}
	for tb.header.is(glob.KeySymbolEqual) {
		tb.header.skip(glob.KeySymbolEqual)
		nextObj, err := p.Obj(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		params = append(params, nextObj)
	}

	return NewEqualsFactStmt(params, tb.line), nil
}

func (p *TbParser) relaFact_intensionalSetFact_enumStmt_equals(tb *tokenBlock) (FactStmt, error) {
	var ret *SpecFactStmt

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
			ret = NewSpecFactStmt(TruePure, propName, []Obj{obj}, tb.line)
		} else {
			obj2, err := p.Obj(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}

			params := []Obj{obj, obj2}

			ret = NewSpecFactStmt(TruePure, propName, params, tb.line)
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
				return p.relaEqualsFactStmt(tb, obj, obj2)
			}
		}

		// 必须到底了
		if !tb.header.ExceedEnd() {
			// or 的情况
			if tb.header.is(glob.KeywordOr) {
				ret = NewSpecFactStmt(TruePure, Atom(opt), []Obj{obj, obj2}, tb.line)
				return p.inlineOrFactWithFirstFact(tb, ret)
			}

			return nil, fmt.Errorf("expect end of line")
		}

		params := []Obj{obj, obj2}

		ret = NewSpecFactStmt(TruePure, Atom(opt), params, tb.line)
	} else {
		return nil, fmt.Errorf("expect relation prop")
	}

	// 这里加入语法糖：!= 等价于 not =，好处是我 = 有 commutative的性质，我不用额外处理 != 了
	if ret.NameIs(glob.KeySymbolNotEqual) {
		ret.TypeEnum = FalsePure
		ret.PropName = Atom(glob.KeySymbolEqual)
	}

	return ret, nil
}

func (p *TbParser) intentionalSetBody(tb *tokenBlock) (string, Obj, []*SpecFactStmt, error) {
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

	proofs := []*SpecFactStmt{}
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

	return param, parentSet, proofs, nil
}

func (p *TbParser) bodyOfKnowProp(tb *tokenBlock) ([]FactStmt, []FactStmt, error) {
	var err error
	iffFacts := []FactStmt{}
	thenFacts := []FactStmt{}

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

func (p *TbParser) atExistPropDefStmt(tb *tokenBlock) (*DefExistPropStmt, error) {
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

	iffFacts := []FactStmt{}
	thenFacts := []FactStmt{}
	if tb.body[len(tb.body)-1].header.is(glob.KeySymbolRightArrow) {
		for i := range len(tb.body) - 1 {
			block := &tb.body[i]
			curStmt, err := p.factStmt(block, UniFactDepth1)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			iffFacts = append(iffFacts, curStmt)
		}

		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		for i := range tb.body[len(tb.body)-1].body {
			curStmt, err := p.factStmt(&tb.body[len(tb.body)-1].body[i], UniFactDepth1)
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
			thenFacts = append(thenFacts, curStmt)
		}
	}

	defBody := NewExistPropDef(header, []FactStmt{}, iffFacts, thenFacts, tb.line)
	return NewDefExistPropStmt(defBody, existParams, existParamSets, tb.line), nil
}

func (p *TbParser) parseDomThenProve(body []tokenBlock) ([]FactStmt, []FactStmt, []Stmt, error) {
	domFacts := []FactStmt{}
	thenFacts := []FactStmt{}
	proofs := []Stmt{}

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
			domFacts = append(domFacts, curStmt)
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
			thenFacts = append(thenFacts, curStmt)
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
				proofs = append(proofs, curStmt)
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
				thenFacts = append(thenFacts, curStmt)
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
			proofs = append(proofs, curStmt)
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
					thenFacts = append(thenFacts, curStmt)
				}
			} else {
				// It's a direct fact statement (no => needed)
				curStmt, err := p.factStmt(&body[i], UniFactDepth1)
				if err != nil {
					return nil, nil, nil, err
				}
				thenFacts = append(thenFacts, curStmt)
			}
		}
		// prove remains empty, dom remains empty
		return domFacts, thenFacts, proofs, nil
	}
}
