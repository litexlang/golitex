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
		return nil, ErrInLine(err, tb)
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
		if tb.header.strAtCurIndexPlus(1) == glob.KeywordFn {
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
			if tb.TokenAtHeaderIndexIs(1, glob.KeywordImplication) {
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
	case glob.KeywordFnTemplate:
		ret, err = p.fnTemplateStmt(tb)
	case glob.KeywordClear:
		ret, err = p.clearStmt(tb)
	case glob.KeywordProveByInduction:
		ret, err = p.proveByInductionStmt(tb)
	case glob.KeywordProveFor:
		ret, err = p.proveForStmt(tb)
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
	case glob.KeywordDoNothing:
		ret, err = p.doNothingStmt(tb)
	case glob.KeywordImport:
		ret, err = p.importStmt(tb)
	case glob.KeywordProveImplication:
		ret, err = p.proveImplicationStmt(tb)
	case glob.KeywordImplication:
		ret, err = p.implicationStmt(tb)
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

func (p *TbParser) defPropStmt(tb *tokenBlock) (*DefPropStmt, error) {
	body, err := p.defPropStmtWithoutSelfReferCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = NoSelfReferenceInPropDef(string(body.DefHeader.Name), append(append(body.DomFactsOrNil, body.IffFactsOrNil...), body.ImplicationFactsOrNil...))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = p.NewDefinedNameInCurrentParseEnv(string(body.DefHeader.Name))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	return body, nil
}

func (p *TbParser) defPropStmtWithoutSelfReferCheck(tb *tokenBlock) (*DefPropStmt, error) {
	err := tb.header.skip(glob.KeywordProp)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	declHeader, err := p.defHeaderWithoutParsingColonAtEnd_MustFollowWithFreeParamCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Add prop params to FreeParams
	for _, param := range declHeader.Params {
		if _, ok := p.FreeParams[param]; ok {
			return nil, ErrInLine(fmt.Errorf("parameter %s in prop definition conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}
	}

	// Defer: remove the params we added when leaving this prop scope
	defer func() {
		for _, param := range declHeader.Params {
			delete(p.FreeParams, param)
		}
	}()

	if !tb.header.is(glob.KeySymbolColon) {
		if tb.header.ExceedEnd() {
			return NewDefPropStmt(declHeader, nil, nil, nil, tb.line), nil
		} else if tb.header.is(glob.KeySymbolEquivalent) {
			err = tb.header.skip(glob.KeySymbolEquivalent)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			iffFacts, err := p.inlineFacts_checkUniDepth1(tb, []string{})
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			return NewDefPropStmt(declHeader, nil, iffFacts, nil, tb.line), nil
		} else {
			return nil, fmt.Errorf("expect ':' or end of block")
		}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.header.ExceedEnd() {
		// domFacts, iffFacts, err := tb.dom_and_section(glob.KeywordIff, glob.KeywordThen)
		// domFacts, iffFacts, err := tb.dom_and_section(glob.KeywordIff, glob.KeySymbolEqualLarger)
		domFacts, iffFacts, err := p.dom_and_section(tb, glob.KeySymbolEquivalent, glob.KeySymbolRightArrow)
		if err != nil {
			return nil, ErrInLine(err, tb)
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

		return NewDefPropStmt(declHeader, domFacts, iffFacts, nil, tb.line), nil
	} else {
		domFacts, iffFacts, err := p.bodyOfInlineDomAndThen(tb, glob.KeySymbolEquivalent, []string{})
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		return NewDefPropStmt(declHeader, domFacts, iffFacts, nil, tb.line), nil
	}
}

func (p *TbParser) defExistPropStmt(tb *tokenBlock, keyword string) (Stmt, error) {
	body, err := p.defExistPropStmtBodyWithoutSelfReferCheck(tb, keyword)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = NoSelfReferenceInPropDef(string(body.DefBody.DefHeader.Name), append(append(body.DefBody.DomFactsOrNil, body.DefBody.IffFactsOrNil...), body.DefBody.ImplicationFactsOrNil...))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	return body, nil
}

func (p *TbParser) defExistPropStmtBodyWithoutSelfReferCheck(tb *tokenBlock, head string) (*DefExistPropStmt, error) {
	var err error

	err = tb.header.skip(head)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	existParams, existParamSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeywordSt, false)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Add exist prop params to FreeParams
	for _, param := range existParams {
		if _, exists := p.FreeParams[param]; exists {
			return nil, ErrInLine(fmt.Errorf("parameter %s in exist prop definition conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}
	}

	defer func() {
		for _, param := range existParams {
			delete(p.FreeParams, param)
		}
	}()

	if len(existParams) == 0 {
		return nil, fmt.Errorf("expect at least one parameter in exist prop definition")
	}

	def, err := p.defExistPropStmtBody(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Also add params from defHeader (the main prop definition)
	for _, param := range def.DefHeader.Params {
		p.FreeParams[param] = struct{}{}
	}

	// Defer: remove the params we added when leaving this exist prop scope
	defer func() {
		// Remove existParams
		for _, param := range existParams {
			delete(p.FreeParams, param)
		}
		// Remove defHeader params
		for _, param := range def.DefHeader.Params {
			delete(p.FreeParams, param)
		}
	}()

	return NewDefExistPropStmt(def, existParams, existParamSets, tb.line), nil
}

func (p *TbParser) defFnStmt(tb *tokenBlock, skipFn bool) (Stmt, error) {
	if skipFn {
		err := tb.header.skip(glob.KeywordFn)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	}

	decl, err := p.defHeaderWithoutParsingColonAtEnd_MustFollowWithFreeParamCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = p.NewDefinedNameInCurrentParseEnv(string(decl.Name))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Add fn params to FreeParams
	for _, param := range decl.Params {
		if _, exists := p.FreeParams[param]; exists {
			return nil, ErrInLine(fmt.Errorf("parameter %s in fn definition conflicts with a free parameter in the outer scope", param), tb)
		}

		p.FreeParams[param] = struct{}{}
	}

	// Defer: remove the params we added when leaving this fn scope
	defer func() {
		for _, param := range decl.Params {
			delete(p.FreeParams, param)
		}
	}()

	retSet, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
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
				return nil, ErrInLine(err, tb)
			}
		} else {
			domFacts, err = p.inlineFacts_untilWord_or_exceedEnd_notSkipWord(tb, glob.KeySymbolRightArrow, []string{})
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			if !tb.header.is(glob.KeySymbolRightArrow) {
				return NewDefFnStmt(string(decl.Name), NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts, tb.line), tb.line), nil
			}

			err = tb.header.skip(glob.KeySymbolRightArrow)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			thenFacts, err = p.inlineFacts_untilEndOfInline(tb, []string{})
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
		}
	} else if tb.header.is(glob.KeySymbolRightArrow) {
		err = tb.header.skip(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		unitFacts, err := p.inlineFacts_checkUniDepth1(tb, []string{})
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		thenFacts = append(thenFacts, unitFacts...)
	}

	return NewDefFnStmt(string(decl.Name), NewFnTStruct(decl.Params, decl.ParamSets, retSet, domFacts, thenFacts, tb.line), tb.line), nil
}

func (p *TbParser) defObjStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip("")
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	objNames, objSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolColon, true)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if len(objNames) == 0 {
		return nil, fmt.Errorf("expect at least one object")
	}

	for _, objName := range objNames {
		err = p.NewDefinedNameInCurrentParseEnv(string(objName))
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	}

	if tb.header.ExceedEnd() && len(tb.body) == 0 {
		return NewDefLetStmt(objNames, objSets, []FactStmt{}, tb.line), nil
	} else if tb.header.ExceedEnd() && len(tb.body) != 0 {
		facts, err := p.bodyFacts(tb, UniFactDepth0)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		return NewDefLetStmt(objNames, objSets, facts, tb.line), nil
	} else {
		facts, err := p.inlineFacts_checkUniDepth0(tb, []string{})
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		err = checkFactsUniDepth0(facts)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		return NewDefLetStmt(objNames, objSets, facts, tb.line), nil
	}
}

func (p *TbParser) haveFnStmt(tb *tokenBlock) (Stmt, error) {
	var err error

	err = tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if len(tb.body) < 1 {
		return nil, fmt.Errorf("expect at least 1 body block")
	}

	defFnStmt, err := p.defFnStmt(&tb.body[0], false)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Note: defFnStmt already adds the function name to the environment, so we don't need to add it again here

	// Check if it's prove or case-by-case
	if len(tb.body) >= 2 && tb.body[1].header.is(glob.KeywordProve) {
		if len(tb.body) != 3 {
			return nil, fmt.Errorf("expect 3 body blocks for have fn with prove")
		}
		err = tb.body[1].header.skip(glob.KeywordProve)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		// Use parseTbBodyAndGetStmts to create a new parse env for proof, so have statements in proof don't leak to outer scope
		proof, err := p.parseTbBodyAndGetStmts(tb.body[1].body)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		err = tb.body[2].header.skip(glob.KeySymbolEqual)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		haveObjSatisfyFn, err := p.Obj(&tb.body[2])
		if err != nil {
			return nil, ErrInLine(err, tb)
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
					return nil, ErrInLine(err, tb)
				}
				curStmt, err := p.specFactStmt(&tb.body[i])
				if err != nil {
					return nil, ErrInLine(err, tb)
				}
				cases = append(cases, curStmt)
				err = tb.body[i].header.skip(glob.KeySymbolColon)
				if err != nil {
					return nil, ErrInLine(err, tb)
				}
				// Use parseTbBodyAndGetStmts to create a new parse env for proof, so have statements in proof don't leak to outer scope
				curProof, err := p.parseTbBodyAndGetStmts(tb.body[i].body)
				if err != nil {
					return nil, ErrInLine(err, tb)
				}
				proofs = append(proofs, curProof)
			} else {
				// Equal block
				err := tb.body[i].header.skip(glob.KeySymbolEqual)
				if err != nil {
					return nil, ErrInLine(err, tb)
				}
				curHaveObj, err := p.Obj(&tb.body[i])
				if err != nil {
					return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeywordFn)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	defHeader, err := p.defHeaderWithoutParsingColonAtEnd_MustFollowWithFreeParamCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = p.NewDefinedNameInCurrentParseEnv(string(defHeader.Name))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	for _, param := range defHeader.Params {
		if _, ok := p.FreeParams[param]; ok {
			return nil, fmt.Errorf("parameter %s is already defined", param)
		}
		p.FreeParams[param] = struct{}{}
	}

	defer func() {
		for _, param := range defHeader.Params {
			delete(p.FreeParams, param)
		}
	}()

	retSet, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if !tb.header.is(glob.KeySymbolColon) {
		equalTo, err := p.Obj(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		return NewHaveFnEqualStmt(defHeader, retSet, equalTo, tb.line), nil
	} else {
		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		caseByCaseFacts := []*SpecFactStmt{}
		caseByCaseEqualTo := []Obj{}
		for _, block := range tb.body {
			err := block.header.skip(glob.KeywordCase)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			curStmt, err := p.specFactStmt(&block)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			err = block.header.skip(glob.KeySymbolColon)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			obj, err := p.Obj(&block)
			if err != nil {
				return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	objNames := []string{}

	// there is at least one object name
	for {
		objName, err := tb.header.next()
		if err != nil {
			return nil, ErrInLine(err, tb)
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

	for _, objName := range objNames {
		err = p.NewDefinedNameInCurrentParseEnv(string(objName))
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	}

	err = tb.header.skip(glob.KeywordSt)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	fact, err := p.specFactStmt(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
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
				return nil, ErrInLine(err, tb)
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
					return nil, ErrInLine(err, tb)
				}
			}
			facts = append(facts, fact)
		}
	}

	return facts, nil
}

func (p *TbParser) defExistPropStmtBody(tb *tokenBlock) (*DefExistPropStmtBody, error) {
	declHeader, err := p.defHeaderWithoutParsingColonAtEnd_MustFollowWithFreeParamCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	for _, param := range declHeader.Params {
		if _, ok := p.FreeParams[param]; ok {
			return nil, fmt.Errorf("parameter %s in prop definition conflicts with a free parameter in the outer scope", param)
		}
		p.FreeParams[param] = struct{}{}
	}

	defer func() {
		for _, param := range declHeader.Params {
			delete(p.FreeParams, param)
		}
	}()

	err = p.NewDefinedNameInCurrentParseEnv(string(declHeader.Name))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.header.ExceedEnd() {
		return NewExistPropDef(declHeader, []FactStmt{}, []FactStmt{}, []FactStmt{}, tb.line), nil
	}

	if tb.header.is(glob.KeySymbolEquivalent) {
		err = tb.header.skip(glob.KeySymbolEquivalent)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		unitFacts, err := p.inlineFacts_checkUniDepth1(tb, []string{})
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		return NewExistPropDef(declHeader, []FactStmt{}, unitFacts, []FactStmt{}, tb.line), nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.header.ExceedEnd() {

		// domFacts, iffFactsAsFactStatements, err := tb.dom_and_section(glob.KeywordIff, glob.KeywordThen)
		// domFacts, iffFactsAsFactStatements, err := tb.dom_and_section(glob.KeywordIff, glob.KeySymbolEqualLarger)
		domFacts, iffFactsAsFactStatements, err := p.dom_and_section(tb, glob.KeySymbolEquivalent, glob.KeySymbolRightArrow)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		if len(iffFactsAsFactStatements) == 0 {
			return nil, fmt.Errorf("expect 'iff' section in proposition definition has at least one fact")
		}

		return NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements, []FactStmt{}, tb.line), nil
	} else {
		domFacts, iffFactsAsFactStatements, err := p.bodyOfInlineDomAndThen(tb, glob.KeySymbolEquivalent, []string{})
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		return NewExistPropDef(declHeader, domFacts, iffFactsAsFactStatements, []FactStmt{}, tb.line), nil
	}
}

func (p *TbParser) haveObjFromCartSetStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Parse object name
	objName, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = p.NewDefinedNameInCurrentParseEnv(string(objName))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Parse cart(...)
	cartSetObj, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	cartSet, ok := cartSetObj.(*FnObj)
	if !ok {
		return nil, ErrInLine(fmt.Errorf("expected cart to be FnObj"), tb)
	}

	if !IsFn_WithHeadName(cartSetObj, glob.KeywordCart) {
		return nil, ErrInLine(fmt.Errorf("expected cart function call"), tb)
	}

	// Parse = ...
	err = tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	equalTo, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Check end of line
	if !tb.header.ExceedEnd() {
		return nil, ErrInLine(fmt.Errorf("expect end of line"), tb)
	}

	return NewHaveObjFromCartSetStmt(objName, cartSet, equalTo, tb.line), nil
}

func (p *TbParser) haveObjEqualStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordHave)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	objectEqualTos := []Obj{}

	objectNames, setSlice, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolEqual, false)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	for _, objName := range objectNames {
		err = p.NewDefinedNameInCurrentParseEnv(string(objName))
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	}

	for !tb.header.ExceedEnd() {
		objectEqualTo, err := p.Obj(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	objNames, objSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolColon, true)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	for _, objName := range objNames {
		err = p.NewDefinedNameInCurrentParseEnv(string(objName))
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	}

	if len(objNames) == 0 {
		return nil, fmt.Errorf("expect at least one object")
	}

	return NewHaveObjInNonEmptySetStmt(objNames, objSets, tb.line), nil
}

func (p *TbParser) claimStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordClaim)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.body[0].header.is(glob.KeywordImplication) {
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
		return nil, ErrInLine(err, tb)
	}

	isProve := true

	if tb.body[1].header.is(glob.KeywordProveByContradiction) {
		isProve = false
		err := tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProveByContradiction)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	} else if tb.body[1].header.is(glob.KeywordProve) {
		err := tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	} else {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction' after claim")
	}

	proof, err := p.parseTbBodyAndGetStmts(tb.body[1].body)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if asUniFactWithIffStmt, ok := toCheck.(*UniFactWithIffStmt); ok {
		if !isProve {
			return nil, fmt.Errorf("prove_by_contradiction is not supported for iff statement")
		} else {
			err := tb.body[2].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			proof2, err := p.parseTbBodyAndGetStmts(tb.body[2].body)
			if err != nil {
				return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	if len(tb.body) == 0 {
		return nil, fmt.Errorf("expect proof")
	}

	if tb.header.is(glob.KeySymbolColon) {
		tb.header.skip(glob.KeySymbolColon)
		proof, err := p.parseTbBodyAndGetStmts(tb.body)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		return NewProveStmt(proof, tb.line), nil
	} else {
		factToCheck, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, []string{glob.KeySymbolColon})
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		proofs, err := p.parseTbBodyAndGetStmts(tb.body)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		return NewClaimProveStmt(factToCheck, proofs, tb.line), nil
	}
}

// ###############################################################

func (p *TbParser) knowExistPropStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	existProp, err := p.atExistPropDefStmt(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = p.NewDefinedNameInCurrentParseEnv(string(existProp.DefBody.DefHeader.Name))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	return NewKnowExistPropStmt(existProp, tb.line), nil
}

func (p *TbParser) knowPropStmt(tb *tokenBlock) (*KnowPropStmt, error) {
	err := tb.header.skip(glob.KeywordKnow)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.header.is(glob.KeywordImplication) {
		implicationStmt, err := p.implicationStmt(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		return NewKnowPropStmt(implicationStmt.ToProp(), tb.line), nil
	} else {
		prop, err := p.defPropStmt(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		return NewKnowPropStmt(prop, tb.line), nil
	}
}

func (p *TbParser) knowFactStmt(tb *tokenBlock) (Stmt, error) {
	tb.header.skip(glob.KeywordKnow)

	if !tb.header.is(glob.KeySymbolColon) {
		var facts FactStmtSlice = FactStmtSlice{}
		var err error
		facts, err = p.inlineFacts_checkUniDepth0(tb, []string{})
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		err = checkFactsUniDepth0(facts)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		return NewKnowStmt(facts.ToCanBeKnownStmtSlice(), tb.line), nil
	}

	if err := tb.header.testAndSkip(glob.KeySymbolColon); err != nil {
		return nil, ErrInLine(err, tb)
	}

	var err error
	var facts FactStmtSlice = FactStmtSlice{}
	facts, err = p.bodyFacts(tb, UniFactDepth0)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	return NewKnowStmt(facts.ToCanBeKnownStmtSlice(), tb.line), nil
}

func (p *TbParser) proveInEachCaseStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveInEachCase)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.header.is(glob.KeySymbolColon) {
		err := tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		if !tb.header.ExceedEnd() {
			return nil, fmt.Errorf("expect end of line")
		}

		orFact, err := p.orStmt(&tb.body[0])
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		thenFacts := []FactStmt{}
		// err = tb.body[1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
		err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		for _, stmt := range tb.body[1].body {
			curStmt, err := p.factStmt(&stmt, UniFactDepth0)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			thenFacts = append(thenFacts, curStmt)
		}

		proofs := []StmtSlice{}
		for i := 2; i < len(tb.body); i++ {
			err = tb.body[i].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			proof, err := p.parseTbBodyAndGetStmts(tb.body[i].body)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			proofs = append(proofs, proof)
		}

		if len(proofs) != len(orFact.Facts) {
			return nil, ErrInLine(fmt.Errorf("prove in each case: expect %d proofs, but got %d. expect the number of proofs to be the same as the number of facts in the or fact", len(orFact.Facts), len(proofs)), tb)
		}

		return NewProveInEachCaseStmt(orFact, thenFacts, proofs, tb.line), nil
	} else {
		orFact, err := p.inlineOrFact(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		thenFacts := []FactStmt{}
		for !tb.header.is(glob.KeySymbolColon) {
			fact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, []string{glob.KeySymbolColon})
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			thenFacts = append(thenFacts, fact)
		}

		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		proofs := []StmtSlice{}
		for i := range len(tb.body) {
			err = tb.body[i].header.skipKwAndColonCheckEOL(glob.KeywordProve)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			proof, err := p.parseTbBodyAndGetStmts(tb.body[i].body)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			proofs = append(proofs, proof)
		}

		if len(proofs) != len(orFact.Facts) {
			return nil, ErrInLine(fmt.Errorf("prove in each case: expect %d proofs, but got %d. expect the number of proofs to be the same as the number of facts in the or fact", len(orFact.Facts), len(proofs)), tb)
		}

		return NewProveInEachCaseStmt(orFact, thenFacts, proofs, tb.line), nil
	}
}

func (p *TbParser) proveCaseByCaseStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skipKwAndColonCheckEOL(glob.KeywordProveCaseByCase)
	if err != nil {
		return nil, ErrInLine(err, tb)
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
				return nil, ErrInLine(err, tb)
			}

			// Parse the specFact (condition)
			curStmt, err := p.specFactStmt(&block)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			// Skip the colon after specFact
			err = block.header.skip(glob.KeySymbolColon)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			caseFacts = append(caseFacts, curStmt)

			// Parse proof statements in the case block body
			proof, err := p.parseTbBodyAndGetStmts(block.body)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			proofs = append(proofs, proof)
		} else {
			// This is a thenFacts block
			if hasEncounteredCase {
				return nil, ErrInLine(fmt.Errorf("prove_case_by_case: thenFacts can only appear before case blocks"), tb)
			}

			// Parse thenFacts (could be =>: section or inline facts)
			if block.header.is(glob.KeySymbolRightArrow) {
				err = block.header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
				if err != nil {
					return nil, ErrInLine(err, tb)
				}

				curThenFacts, err := p.bodyBlockFacts(&block, UniFactDepth0, len(block.body))
				if err != nil {
					return nil, ErrInLine(err, tb)
				}
				thenFacts = append(thenFacts, curThenFacts...)
			} else {
				// Parse inline fact
				curStmt, err := p.factStmt(&block, UniFactDepth0)
				if err != nil {
					return nil, ErrInLine(err, tb)
				}
				thenFacts = append(thenFacts, curStmt)
			}
		}
	}

	if len(caseFacts) == 0 {
		return nil, ErrInLine(fmt.Errorf("prove_case_by_case: at least one case block is required"), tb)
	}

	// Verify that the number of proofs matches the number of cases
	if len(proofs) != len(caseFacts) {
		return nil, ErrInLine(fmt.Errorf("prove_case_by_case: expect %d proofs, but got %d. expect the number of proofs to be the same as the number of case facts", len(caseFacts), len(proofs)), tb)
	}

	return NewProveCaseByCaseStmt(caseFacts, thenFacts, proofs, tb.line), nil
}

func (p *TbParser) proveByEnum(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveByEnum)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// param paramSet pairs
	params, paramSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolRightBrace, false)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	for _, param := range params {
		if _, ok := p.FreeParams[param]; ok {
			return nil, ErrInLine(fmt.Errorf("parameter %s in proveByEnum conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}
	}
	defer func() {
		for _, param := range params {
			delete(p.FreeParams, param)
		}
	}()

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Use the new parseDomThenProve function to handle all three cases:
	// 1. dom:, =>:, prove: (all three sections)
	// 2. =>:, prove: (no dom section)
	// 3. =>: (only then section, no dom and no prove)
	domFacts, thenFacts, proofs, err := p.parseDomThenProve(tb.body)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	uniFact := NewUniFact(params, paramSets, domFacts, thenFacts, tb.line)
	return NewProveByEnumStmt(uniFact, proofs, tb.line), nil
}

func (p *TbParser) fnTemplateStmt(tb *tokenBlock) (Stmt, error) {
	tb.header.skipNext()

	defHeader, err := p.defHeaderWithoutParsingColonAtEnd_MustFollowWithFreeParamCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Add fn template params to FreeParams
	for _, param := range defHeader.Params {
		if _, exists := p.FreeParams[param]; exists {
			return nil, ErrInLine(fmt.Errorf("parameter %s in fn template definition conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}
	}

	// Defer: remove the params we added when leaving this fn template scope
	defer func() {
		for _, param := range defHeader.Params {
			delete(p.FreeParams, param)
		}
	}()

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	if len(tb.body) == 1 {
		fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := p.fnInFnTemplateStmt(&tb.body[0])
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		newFnTStruct := NewFnTStruct(fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, tb.body[0].line)

		return NewFnTemplateStmt(defHeader, []FactStmt{}, newFnTStruct, tb.line), nil
	} else if len(tb.body) >= 2 {
		if tb.body[0].header.is(glob.KeywordDom) {
			err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeywordDom)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			templateDomFacts, err := p.bodyFacts(&tb.body[0], UniFactDepth1)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := p.fnInFnTemplateStmt(&tb.body[1])
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			newFnTStruct := NewFnTStruct(fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, tb.body[1].line)

			return NewFnTemplateStmt(defHeader, templateDomFacts, newFnTStruct, tb.line), nil
		} else {
			templateDomFacts := []FactStmt{}
			for i := range len(tb.body) - 1 {
				curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
				if err != nil {
					return nil, ErrInLine(err, tb)
				}
				templateDomFacts = append(templateDomFacts, curStmt)
			}

			fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, err := p.fnInFnTemplateStmt(&tb.body[len(tb.body)-1])
			if err != nil {
				return nil, ErrInLine(err, tb)
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
		return nil, nil, nil, nil, nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, nil, nil, nil, nil, ErrInLine(err, tb)
	}

	fnParams, fnParamSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolRightBrace, false)
	if err != nil {
		return nil, nil, nil, nil, nil, ErrInLine(err, tb)
	}

	for _, param := range fnParams {
		if _, ok := p.FreeParams[param]; ok {
			return nil, nil, nil, nil, nil, ErrInLine(fmt.Errorf("parameter %s in fn template conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}
	}
	defer func() {
		for _, param := range fnParams {
			delete(p.FreeParams, param)
		}
	}()

	fnRetSet, err := p.Obj(tb)
	if err != nil {
		return nil, nil, nil, nil, nil, ErrInLine(err, tb)
	}

	if tb.header.ExceedEnd() {
		return fnParams, fnParamSets, fnRetSet, []FactStmt{}, []FactStmt{}, nil
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, nil, nil, nil, nil, ErrInLine(err, tb)
	}

	// domFacts, thenFacts, err := tb.dom_and_section(glob.KeywordThen, glob.KeywordIff)
	// domFacts, thenFacts, err := tb.dom_and_section(glob.KeySymbolEqualLarger, glob.KeywordIff)
	domFacts, thenFacts, err := p.dom_and_section(tb, glob.KeySymbolRightArrow, glob.KeySymbolEquivalent)
	if err != nil {
		return nil, nil, nil, nil, nil, ErrInLine(err, tb)
	}

	return fnParams, fnParamSets, fnRetSet, domFacts, thenFacts, nil
}

func (p *TbParser) clearStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordClear)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	// 把当前的 parser 里的名字都删了
	p.FreeParams = make(map[string]struct{})
	p.DefinedNamesAtEachParseEnv = NewDefinedNameAtEachParseEnv()
	p.AllDefinedNamesExceptPkgNames = make(map[string]struct{})

	return NewClearStmt(tb.line), nil
}

func (p *TbParser) proveForStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveFor)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Parse parameter name
	param, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Skip $in (FuncFactPrefix + KeywordIn)
	if tb.header.is(glob.FuncFactPrefix) {
		err = tb.header.skip(glob.FuncFactPrefix)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	}

	if !tb.header.is(glob.KeywordIn) {
		return nil, ErrInLine(fmt.Errorf("expect 'in' after '$'"), tb)
	}
	err = tb.header.skip(glob.KeywordIn)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Parse RangeOrClosedRange object (e.g., range(1, 10) or closed_range(1, 10))
	rangeOrClosedRange, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if !ObjIsRangeOrClosedRangeWith2Params(rangeOrClosedRange) {
		return nil, ErrInLine(fmt.Errorf("expect range or closed range, but got %s", rangeOrClosedRange.String()), tb)
	}

	fnObj := rangeOrClosedRange.(*FnObj)
	left := fnObj.Params[0]
	right := fnObj.Params[1]
	isProveIRange := fnObj.FnHead.String() == glob.KeywordRange

	// Skip colon
	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Use parseDomThenProve to handle all three cases:
	// 1. dom:, =>:, prove: (all three sections)
	// 2. =>:, prove: (no dom section)
	// 3. =>: (only then section, no dom and no prove)
	domFacts, thenFacts, proofs, err := p.parseDomThenProve(tb.body)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	return NewProveForStmt(param, left, right, isProveIRange, domFacts, thenFacts, proofs, tb.line), nil
}

func (p *TbParser) proveIsTransitivePropStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveIsTransitiveProp)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	prop, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}
	propAtom, ok := prop.(Atom)
	if !ok {
		return nil, ErrInLine(fmt.Errorf("expect obj atom, but got %T", prop), tb)
	}

	if tb.header.skip(glob.KeySymbolComma) != nil {
		return nil, ErrInLine(err, tb)
	}

	params := []string{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.next()
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		params = append(params, param)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	if len(params) != 3 {
		return nil, ErrInLine(fmt.Errorf("expect 3 params, but got %d", len(params)), tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	proofs := []Stmt{}
	for _, block := range tb.body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		proofs = append(proofs, curStmt)
	}
	return NewProveIsTransitivePropStmt(propAtom, params, proofs, tb.line), nil
}

func (p *TbParser) proveCommutativePropStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveIsCommutativeProp)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	specFact, err := p.specFactStmt(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if len(specFact.Params) != 2 {
		return nil, ErrInLine(fmt.Errorf("expect 2 params, but got %d", len(specFact.Params)), tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if len(tb.body) != 2 {
		return nil, ErrInLine(fmt.Errorf("expect 2 body blocks, but got %d", len(tb.body)), tb)
	}

	proofs := []Stmt{}
	err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	for _, block := range tb.body[0].body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	proofsRightToLeft := []Stmt{}
	err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	for _, block := range tb.body[1].body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		proofsRightToLeft = append(proofsRightToLeft, curStmt)
	}

	return NewProveIsCommutativePropStmt(specFact, proofs, proofsRightToLeft, tb.line), nil
}

func (p *TbParser) algoDefStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordAlgo)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	funcName, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	params := []string{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.next()
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		params = append(params, param)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	stmts := []AlgoStmt{}
	for _, block := range tb.body {
		curStmt, err := p.algoStmt(&block)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		stmts = append(stmts, curStmt)
	}

	return NewAlgoDefStmt(funcName, params, stmts, tb.line), nil
}

func (p *TbParser) evalStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordEval)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	objsToEval, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	return NewEvalStmt(objsToEval, tb.line), nil
}

func (p *TbParser) defProveAlgoStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveAlgo)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	funcName, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	params := []string{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := tb.header.next()
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		params = append(params, param)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	stmts := []ProveAlgoStmt{}
	for _, block := range tb.body {
		curStmt, err := p.proveAlgoStmt(&block)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		stmts = append(stmts, curStmt)
	}
	return NewDefProveAlgoStmt(funcName, params, stmts, tb.line), nil
}

func (p *TbParser) byStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordBy)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	proveAlgoName, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	proveAlgoParams := []Obj{}
	for !tb.header.is(glob.KeySymbolRightBrace) {
		param, err := p.Obj(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		proveAlgoParams = append(proveAlgoParams, param)
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// by statement no longer has then facts - facts are returned from prove_algo
	return NewByStmt(proveAlgoName, proveAlgoParams, tb.line), nil
}

func (p *TbParser) proveByContradictionStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveByContradiction)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	toCheck, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, []string{glob.KeySymbolColon})
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	proofs := []Stmt{}
	for _, block := range tb.body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		proofs = append(proofs, curStmt)
	}
	return NewClaimProveByContradictionStmt(NewClaimProveStmt(toCheck, proofs, tb.line), tb.line), nil
}

func (p *TbParser) doNothingStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordDoNothing)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return NewDoNothingStmt(tb.line), nil
}

func (p *TbParser) importStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordImport)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.header.is(glob.KeySymbolDoubleQuote) {
		// Parse the path in double quotes
		path, err := p.getStringInDoubleQuotes(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		// Check if path ends with .lit - if so, it's an ImportFileStmt
		if strings.HasSuffix(path, glob.LitexFileSuffix) {
			if !tb.header.ExceedEnd() {
				return nil, fmt.Errorf("expect end of line")
			}
			return NewImportFileStmt(path, tb.line), nil
		} else {
			err := tb.header.skip(glob.KeywordAs)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			asPkgName, err := tb.header.next()
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			return NewImportStmt(path, asPkgName, tb.line), nil
		}
	}

	pkgName, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}
	asPkgName := pkgName

	if tb.header.is(glob.KeywordAs) {
		err = tb.header.skip(glob.KeywordAs)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		asPkgName, err = tb.header.next()
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	}

	path, err := glob.ResolveSystemPackagePath(pkgName)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}
	return NewImportStmt(path, asPkgName, tb.line), nil
}

func (p *TbParser) proveImplicationStmt(tb *tokenBlock) (Stmt, error) {
	err := tb.header.skip(glob.KeywordProveImplication)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Parse implication name (e.g., "p")
	implicationName, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Parse parameters (e.g., "(x)")
	var params StrSlice
	if tb.header.is(glob.KeySymbolLeftBrace) {
		err = tb.header.skip(glob.KeySymbolLeftBrace)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		// Parse parameters without param sets (just parameter names)
		for !tb.header.is(glob.KeySymbolRightBrace) {
			param, err := tb.header.next()
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			params = append(params, param)

			if tb.header.is(glob.KeySymbolComma) {
				err = tb.header.skip(glob.KeySymbolComma)
				if err != nil {
					return nil, ErrInLine(err, tb)
				}
			}
		}

		err = tb.header.skip(glob.KeySymbolRightBrace)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
	}

	// Skip colon
	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Parse body - two cases:
	// Case 1: First line is =>:, then has prove: section
	// Case 2: No =>:, all are implications (no prove section)
	if len(tb.body) == 0 {
		return nil, ErrInLine(fmt.Errorf("expect body after prove_implication"), tb)
	}

	var implicationFacts FactStmtSlice
	var proofs StmtSlice

	// Check if first block is =>
	if tb.body[0].header.is(glob.KeySymbolRightArrow) {
		// Case 1: =>:, prove: format
		if len(tb.body) < 2 {
			return nil, ErrInLine(fmt.Errorf("expect 'prove:' section after '=>:'"), tb)
		}

		// Parse => section
		err = tb.body[0].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		for _, stmt := range tb.body[0].body {
			curStmt, err := p.factStmt(&stmt, UniFactDepth0)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			implicationFacts = append(implicationFacts, curStmt)
		}

		// Parse prove section
		if !tb.body[1].header.is(glob.KeywordProve) {
			return nil, ErrInLine(fmt.Errorf("expect 'prove:' section after '=>:'"), tb)
		}

		err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		proofs, err = p.parseTbBodyAndGetStmts(tb.body[1].body)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		if len(tb.body) > 2 {
			return nil, ErrInLine(fmt.Errorf("unexpected extra sections after 'prove:'"), tb)
		}
	} else {
		// Case 2: All are implications, no prove section
		// Parse all body blocks as fact statements
		for i := range len(tb.body) {
			curStmt, err := p.factStmt(&tb.body[i], UniFactDepth0)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			implicationFacts = append(implicationFacts, curStmt)
		}
	}

	return NewProveImplicationStmt(implicationName, params, implicationFacts, proofs, tb.line), nil
}

func (p *TbParser) implicationStmt(tb *tokenBlock) (*ImplicationStmt, error) {
	body, err := p.implicationStmtWithoutSelfReferCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = NoSelfReferenceInPropDef(string(body.DefHeader.Name), append(body.DomFacts, body.ImplicationFacts...))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = p.NewDefinedNameInCurrentParseEnv(string(body.DefHeader.Name))
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	return body, nil
}

func (p *TbParser) implicationStmtWithoutSelfReferCheck(tb *tokenBlock) (*ImplicationStmt, error) {
	err := tb.header.skip(glob.KeywordImplication)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	declHeader, err := p.defHeaderWithoutParsingColonAtEnd_MustFollowWithFreeParamCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Add implication params to FreeParams
	for _, param := range declHeader.Params {
		if _, ok := p.FreeParams[param]; ok {
			return nil, ErrInLine(fmt.Errorf("parameter %s in implication definition conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}
	}

	// Defer: remove the params we added when leaving this implication scope
	defer func() {
		for _, param := range declHeader.Params {
			delete(p.FreeParams, param)
		}
	}()

	if !tb.header.is(glob.KeySymbolColon) {
		if tb.header.ExceedEnd() {
			return NewImplicationStmt(declHeader, nil, nil, tb.line), nil
		} else {
			return nil, fmt.Errorf("expect ':' or end of block")
		}
	}

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.header.ExceedEnd() {
		// Parse dom and implication sections (no iff)
		// Third parameter is empty string because => can appear at the end (when there's no dom section)
		domFacts, implicationFacts, err := p.dom_and_section(tb, glob.KeySymbolRightArrow, "")
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		// Check that dom and implication facts don't reference the same prop name
		for _, fact := range domFacts {
			if factAsSpecFact, ok := fact.(*SpecFactStmt); ok {
				if string(factAsSpecFact.PropName) == string(declHeader.Name) {
					return nil, fmt.Errorf("dom fact cannot be the same as the implication being defined")
				}
			}
		}

		for _, fact := range implicationFacts {
			if factAsSpecFact, ok := fact.(*SpecFactStmt); ok {
				if string(factAsSpecFact.PropName) == string(declHeader.Name) {
					return nil, fmt.Errorf("implication fact cannot be the same as the implication being defined")
				}
			}
		}

		return NewImplicationStmt(declHeader, domFacts, implicationFacts, tb.line), nil
	} else {
		// Inline format: parse dom and implication facts
		domFacts, implicationFacts, err := p.bodyOfInlineDomAndThen(tb, glob.KeySymbolRightArrow, []string{})
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		return NewImplicationStmt(declHeader, domFacts, implicationFacts, tb.line), nil
	}
}

func (p *TbParser) factsStmt(tb *tokenBlock) (Stmt, error) {
	if tb.GetEnd() != glob.KeySymbolColon { // 因为可能是 forall : 这样的
		facts, err := p.inlineFacts_checkUniDepth0(tb, []string{})
		if err != nil {
			return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	fact, err := p.specFactStmt(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolComma)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	param, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if !tb.header.is(glob.KeySymbolComma) {
		err = tb.header.skip(glob.KeySymbolRightBrace)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		return NewProveByInductionStmt(fact, param, Atom("1"), tb.line), nil
	} else {
		err = tb.header.skip(glob.KeySymbolComma)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		start, err := p.Obj(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolRightBrace)
		if err != nil {
			return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	for _, factToParse := range tb.body {
		fact, err := p.specFactStmt_ExceedEnd(&factToParse)
		if err != nil {
			return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	if !tb.header.ExceedEnd() {
		return nil, fmt.Errorf("expect end of line")
	}

	return ret, nil
}

func (p *TbParser) specFactStmt(tb *tokenBlock) (*SpecFactStmt, error) {
	stmt, err := p.specFactStmt_OrOneLineEqualsFact(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
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
			return nil, ErrInLine(err, tb)
		}
		return ret, nil
	} else {
		ret, err := p.relaFactStmt_orRelaEquals(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		return ret, nil
	}
}

func (p *TbParser) uniFactInterface(tb *tokenBlock, uniFactDepth uniFactEnum) (FactStmt, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	params, setParams, err := p.param_paramSet_paramInSetFacts(tb, glob.KeySymbolColon, false)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Add uniFact params to FreeParams
	for _, param := range params {
		if _, exists := p.FreeParams[param]; exists {
			return nil, ErrInLine(fmt.Errorf("parameter %s conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}
	}

	// Defer: remove the params we added when leaving this uniFact scope
	defer func() {
		for _, param := range params {
			delete(p.FreeParams, param)
		}
	}()

	// domainFacts, thenFacts, iffFacts, err := tb.uniFactBodyFacts(uniFactDepth.addDepth(), glob.KeywordThen)
	domainFacts, thenFacts, iffFacts, err := p.uniFactBodyFacts(tb, uniFactDepth.addDepth(), glob.KeySymbolRightArrow)
	if err != nil {
		return nil, ErrInLine(err, tb)
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
			return nil, ErrInLine(err, tb)
		}

		if tb.header.ExceedEnd() {
			params := make(ObjSlice, 0, len(tb.body))
			for _, param := range tb.body {
				param, err := p.Obj(&param)
				if err != nil {
					return nil, ErrInLine(err, tb)
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
					return nil, ErrInLine(err, tb)
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
			return nil, ErrInLine(err, tb)
		}

		params := []Obj{}
		for {
			curObj, err := p.Obj(tb)
			if err != nil {
				return nil, ErrInLine(err, tb)
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
			return nil, ErrInLine(err, tb)
		}
		return ret, nil
	} else {
		ret, err := p.relationalSpecFactOrEqualsFact(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		return ret, nil
	}
}

func (p *TbParser) existFactStmt(tb *tokenBlock, isTrue bool) (*SpecFactStmt, error) {
	err := tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	existParams := []Obj{}

	for !tb.header.is(glob.KeywordSt) {
		param, err := p.Obj(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		existParams = append(existParams, param)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		}
	}

	err = tb.header.skip(glob.KeywordSt)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	pureSpecFact, err := p.specFactWithoutExist_WithoutNot(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	params := []Obj{}
	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if !tb.header.is(glob.KeySymbolRightBrace) {
		for {
			param, err := p.Obj(tb)
			if err != nil {
				return nil, ErrInLine(err, tb)
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
		return nil, ErrInLine(err, tb)
	}

	ret := NewSpecFactStmt(TruePure, propName, params, tb.line)

	return ret, nil
}

func (p *TbParser) relaFactStmt_orRelaEquals(tb *tokenBlock) (FactStmt, error) {
	var ret *SpecFactStmt

	obj, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	opt, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if opt == glob.FuncFactPrefix {
		propName, err := p.notNumberAtom(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		if tb.header.ExceedEnd() {
			ret = NewSpecFactStmt(TruePure, propName, []Obj{obj}, tb.line)
		} else {
			obj2, err := p.Obj(tb)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			params := []Obj{obj, obj2}

			ret = NewSpecFactStmt(TruePure, propName, params, tb.line)
		}
	} else if !glob.IsBuiltinInfixRelaPropSymbol(opt) {
		return nil, fmt.Errorf("expect relation prop")
	} else {
		obj2, err := p.Obj(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
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
	// for i, setParam := range setParams {
	// 	// 这里需要考虑极端情况： forall a {x R: x > 0}, x R 这样的极端情况，此时自由变量里有x，但是这个x出现在了setParam，而且此setParam出现在了自由变量x的前面，所以没被警告，所以需要特殊处理
	// 	atomsInSetParam := GetAtomsInObjIncludingParamInSetBuilder(setParam)
	// 	atomsInSetParamAsStr := make([]string, len(atomsInSetParam))
	// 	for i, atom := range atomsInSetParam {
	// 		atomsInSetParamAsStr[i] = string(atom)
	// 	}

	// 	for j := i; j < len(params); j++ {
	// 		if slices.Contains(atomsInSetParamAsStr, params[j]) {
	// 			return nil, nil, fmt.Errorf("the set %s of the parameter at index %d cannot include any parameters from index %d to the last one (found parameter %s)", setParam, i, j, params[j])
	// 		}
	// 	}
	// }

	return params, setParams, nil
}

func (p *TbParser) defHeaderWithoutParsingColonAtEnd_MustFollowWithFreeParamCheck(tb *tokenBlock) (*DefHeader, error) {
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

	return NewDefHeader(name, params, setParams), nil
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
		return nil, ErrInLine(err, tb)
	}

	facts := []FactStmt{}
	for _, stmt := range tb.body {
		curStmt, err := p.factStmt(&stmt, uniFactDepth)
		if err != nil {
			return nil, ErrInLine(err, tb)
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
				return nil, nil, ErrInLine(err, tb)
			}
			sectionFacts = append(sectionFacts, curStmt)
		}
		return domFacts, sectionFacts, nil
	} else if !tb.body[0].header.is(glob.KeywordDom) && tb.body[len(tb.body)-1].header.is(kw) {
		for i := range len(tb.body) - 1 {
			curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
			if err != nil {
				return nil, nil, ErrInLine(err, tb)
			}
			domFacts = append(domFacts, curStmt)
		}
		sectionFacts, err = p.parseFactBodyWithHeaderNameAndUniFactDepth(&tb.body[len(tb.body)-1], kw, UniFactDepth1)
		if err != nil {
			return nil, nil, ErrInLine(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else if len(tb.body) == 2 && tb.body[0].header.is(glob.KeywordDom) && tb.body[1].header.is(kw) {
		domFacts, err = p.parseFactBodyWithHeaderNameAndUniFactDepth(&tb.body[0], glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, ErrInLine(err, tb)
		}
		sectionFacts, err = p.parseFactBodyWithHeaderNameAndUniFactDepth(&tb.body[1], kw, UniFactDepth1)
		if err != nil {
			return nil, nil, ErrInLine(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else if len(tb.body) == 1 && tb.body[0].header.is(glob.KeywordDom) {
		domFacts, err = p.parseFactBodyWithHeaderNameAndUniFactDepth(&tb.body[0], glob.KeywordDom, UniFactDepth1)
		if err != nil {
			return nil, nil, ErrInLine(err, tb)
		}
		return domFacts, sectionFacts, nil
	} else {
		return nil, nil, fmt.Errorf("unexpected body structure in dom_and_section")
	}
}

// func (p *TbParser) claimNamedUniFactInline(tb *tokenBlock) (Stmt, error) {
// 	var implicationStmt *ImplicationStmt

// 	if tb.header.is(glob.KeySymbolRightArrow) {
// 		// 有点小问题，最好必须要规定是named inline
// 		namedUniFactResult, err := p.namedUniFactStmt(tb)
// 		if err != nil {
// 			return nil, ErrInLine(err, tb)
// 		}
// 		namedUniFact = namedUniFactResult.(*NamedUniFactStmt)
// 	}

// 	if tb.header.is(glob.KeySymbolColon) {
// 		err := tb.header.skip(glob.KeySymbolColon)
// 		if err != nil {
// 			return nil, ErrInLine(err, tb)
// 		}
// 		if !tb.header.ExceedEnd() {
// 			return nil, fmt.Errorf("expect end of line")
// 		}

// 	} else {
// 		// return NewClaimProveStmt(fact, []Stmt{}, tb.line), nil
// 		return nil, fmt.Errorf("expect proof after claim")
// 	}

// 	proof := []Stmt{}
// 	for _, block := range tb.body {
// 		curStmt, err := p.Stmt(&block)
// 		if err != nil {
// 			return nil, ErrInLine(err, tb)
// 		}
// 		proof = append(proof, curStmt)
// 	}

// 	if len(proof) == 0 {
// 		return nil, fmt.Errorf("expect proof after claim")
// 	}

// 	return NewClaimPropStmt(namedUniFact.DefPropStmt, proof, tb.line), nil
// }

func (p *TbParser) claimExistPropStmt(tb *tokenBlock) (Stmt, error) {
	if len(tb.body) != 3 {
		return nil, fmt.Errorf("expect 3 body blocks")
	}

	existProp, err := p.atExistPropDefStmt(&tb.body[0])
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	proofs := []Stmt{}
	for _, stmt := range tb.body[1].body {
		curStmt, err := p.Stmt(&stmt)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	err = tb.body[2].header.skip(glob.KeywordHave)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	haveObj := []Obj{}
	for !tb.body[2].header.ExceedEnd() {
		curObj, err := p.Obj(&tb.body[2])
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		haveObj = append(haveObj, curObj)
	}

	if len(proofs) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	return NewClaimExistPropStmt(existProp, proofs, haveObj, tb.line), nil
}

func (p *TbParser) claimPropStmt(tb *tokenBlock) (Stmt, error) {
	implicationStmt, err := p.implicationStmt(&tb.body[0])
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if tb.body[1].header.is(glob.KeywordProve) {
		err = tb.body[1].header.skipKwAndColonCheckEOL(glob.KeywordProve)
	} else if tb.body[1].header.is(glob.KeywordProveByContradiction) {
		panic("prove_by_contradiction is not supported for prop statement")
	} else {
		return nil, fmt.Errorf("expect 'prove' or 'prove_by_contradiction'")
	}

	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	proofs := []Stmt{}
	for _, stmt := range tb.body[1].body {
		curStmt, err := p.Stmt(&stmt)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		proofs = append(proofs, curStmt)
	}

	if len(proofs) == 0 {
		return nil, fmt.Errorf("expect proof after claim")
	}

	// return NewClaimPropStmt(NewDefPropStmt(declHeader, []FactStmt{}, iffFacts, thenFacts), proofs, isProve), nil
	return NewClaimPropStmt(implicationStmt, proofs, tb.line), nil
}

func (p *TbParser) relaEqualsFactStmt(tb *tokenBlock, obj, obj2 Obj) (*EqualsFactStmt, error) {
	params := []Obj{obj, obj2}
	for tb.header.is(glob.KeySymbolEqual) {
		tb.header.skip(glob.KeySymbolEqual)
		nextObj, err := p.Obj(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}
		params = append(params, nextObj)
	}

	return NewEqualsFactStmt(params, tb.line), nil
}

func (p *TbParser) relationalSpecFactOrEqualsFact(tb *tokenBlock) (FactStmt, error) {
	var ret *SpecFactStmt

	obj, err := p.Obj(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	opt, err := tb.header.next()
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	if opt == glob.FuncFactPrefix {
		propName, err := p.notNumberAtom(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		if tb.header.ExceedEnd() {
			ret = NewSpecFactStmt(TruePure, propName, []Obj{obj}, tb.line)
		} else {
			obj2, err := p.Obj(tb)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}

			params := []Obj{obj, obj2}

			ret = NewSpecFactStmt(TruePure, propName, params, tb.line)
		}
	} else if glob.IsBuiltinInfixRelaPropSymbol(opt) {
		obj2, err := p.Obj(tb)
		if err != nil {
			return nil, ErrInLine(err, tb)
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

// func (p *TbParser) intentionalSetBody(tb *tokenBlock) (string, Obj, []*SpecFactStmt, error) {
// 	err := tb.header.skip(glob.KeySymbolLeftCurly)
// 	if err != nil {
// 		return "", nil, nil, parserErrAtTb(err, tb)
// 	}

// 	param, err := tb.header.next()
// 	if err != nil {
// 		return "", nil, nil, parserErrAtTb(err, tb)
// 	}

// 	parentSet, err := p.Obj(tb)
// 	if err != nil {
// 		return "", nil, nil, parserErrAtTb(err, tb)
// 	}

// 	err = tb.header.skip(glob.KeySymbolColon)
// 	if err != nil {
// 		return "", nil, nil, parserErrAtTb(err, tb)
// 	}

// 	proofs := []*SpecFactStmt{}
// 	for !tb.header.is(glob.KeySymbolRightCurly) {
// 		curStmt, err := p.specFactStmt(tb)
// 		if err != nil {
// 			return "", nil, nil, parserErrAtTb(err, tb)
// 		}
// 		proofs = append(proofs, curStmt)
// 		tb.header.skipIfIs(glob.KeySymbolComma)
// 	}

// 	err = tb.header.skip(glob.KeySymbolRightCurly)
// 	if err != nil {
// 		return "", nil, nil, parserErrAtTb(err, tb)
// 	}

// 	return param, parentSet, proofs, nil
// }

// func (p *TbParser) bodyOfKnowProp(tb *tokenBlock) ([]FactStmt, []FactStmt, error) {
// 	var err error
// 	iffFacts := []FactStmt{}
// 	thenFacts := []FactStmt{}

// 	// if tb.body[len(tb.body)-1].header.is(glob.KeywordThen) {
// 	if tb.body[len(tb.body)-1].header.is(glob.KeySymbolRightArrow) {
// 		for i := range len(tb.body) - 1 {
// 			iffFact, err := p.factStmt(&tb.body[i], UniFactDepth1)
// 			if err != nil {
// 				return nil, nil, ErrInLine(err, tb)
// 			}
// 			iffFacts = append(iffFacts, iffFact)
// 		}

// 		// err = tb.body[len(tb.body)-1].header.skipKwAndColon_ExceedEnd(glob.KeywordThen)
// 		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
// 		if err != nil {
// 			return nil, nil, ErrInLine(err, tb)
// 		}

// 		for _, stmt := range tb.body[len(tb.body)-1].body {
// 			curStmt, err := p.factStmt(&stmt, UniFactDepth1)
// 			if err != nil {
// 				return nil, nil, ErrInLine(err, tb)
// 			}
// 			thenFacts = append(thenFacts, curStmt)
// 		}

// 		return iffFacts, thenFacts, nil
// 	} else {
// 		for i := range len(tb.body) {
// 			thenFact, err := p.factStmt(&tb.body[i], UniFactDepth1)
// 			if err != nil {
// 				return nil, nil, ErrInLine(err, tb)
// 			}
// 			thenFacts = append(thenFacts, thenFact)
// 		}

// 		return iffFacts, thenFacts, nil
// 	}
// }

func (p *TbParser) atExistPropDefStmt(tb *tokenBlock) (*DefExistPropStmt, error) {
	err := tb.header.skip(glob.KeywordImplication)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	err = tb.header.skip(glob.KeywordExist)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	existParams, existParamSets, err := p.param_paramSet_paramInSetFacts(tb, glob.KeywordSt, false)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Add exist prop params to FreeParams
	for _, param := range existParams {
		if _, exists := p.FreeParams[param]; exists {
			return nil, ErrInLine(fmt.Errorf("parameter %s in exist prop definition conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}
	}

	defer func() {
		for _, param := range existParams {
			delete(p.FreeParams, param)
		}
	}()

	header, err := p.defHeaderWithoutParsingColonAtEnd_MustFollowWithFreeParamCheck(tb)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	// Also add params from defHeader (the main prop definition)
	for _, param := range header.Params {
		if _, exists := p.FreeParams[param]; exists {
			return nil, ErrInLine(fmt.Errorf("parameter %s in exist prop definition conflicts with a free parameter in the outer scope", param), tb)
		}
		p.FreeParams[param] = struct{}{}

	}

	// Defer: remove the params we added when leaving this exist prop scope
	defer func() {
		// Remove existParams
		for _, param := range existParams {
			delete(p.FreeParams, param)
		}
		// Remove defHeader params
		for _, param := range header.Params {
			delete(p.FreeParams, param)
		}
	}()

	err = tb.header.skip(glob.KeySymbolColon)
	if err != nil {
		return nil, ErrInLine(err, tb)
	}

	iffFacts := []FactStmt{}
	thenFacts := []FactStmt{}
	if tb.body[len(tb.body)-1].header.is(glob.KeySymbolRightArrow) {
		for i := range len(tb.body) - 1 {
			block := &tb.body[i]
			curStmt, err := p.factStmt(block, UniFactDepth1)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			iffFacts = append(iffFacts, curStmt)
		}

		err = tb.body[len(tb.body)-1].header.skipKwAndColonCheckEOL(glob.KeySymbolRightArrow)
		if err != nil {
			return nil, ErrInLine(err, tb)
		}

		for i := range tb.body[len(tb.body)-1].body {
			curStmt, err := p.factStmt(&tb.body[len(tb.body)-1].body[i], UniFactDepth1)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			thenFacts = append(thenFacts, curStmt)
		}
	} else {
		for i := range len(tb.body) {
			curStmt, err := p.factStmt(&tb.body[i], UniFactDepth1)
			if err != nil {
				return nil, ErrInLine(err, tb)
			}
			thenFacts = append(thenFacts, curStmt)
		}
	}

	defBody := NewExistPropDef(header, []FactStmt{}, iffFacts, thenFacts, tb.line)
	return NewDefExistPropStmt(defBody, existParams, existParamSets, tb.line), nil
}

// 三种情况
// 1. dom:, =>:, prove: (all three sections)
// 2. =>:, prove: (no dom section)
// 3. =>: (only then section, no dom and no prove)
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
			proofs, err = p.parseTbBodyAndGetStmts(body[2].body)
			if err != nil {
				return nil, nil, nil, err
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
		proofs, err = p.parseTbBodyAndGetStmts(body[lastIdx].body)
		if err != nil {
			return nil, nil, nil, err
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

func (p *TbParser) parseTbBodyAndGetStmts(body []tokenBlock) ([]Stmt, error) {
	stmts := []Stmt{}
	p.NewParseEnv()
	for _, block := range body {
		curStmt, err := p.Stmt(&block)
		if err != nil {
			return nil, ErrInLine(err, &block)
		}
		stmts = append(stmts, curStmt)
	}
	p.DeleteCurrentParseEnv()
	return stmts, nil
}
