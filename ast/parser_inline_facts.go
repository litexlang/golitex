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
	glob "golitex/glob"
	"slices"
)

func (p *TbParser) IsEnding(tb *tokenBlock, ends []string) bool {
	if tb.header.ExceedEnd() {
		return true
	}

	for _, end := range ends {
		if tb.header.is(end) {
			return true
		}
	}

	return false
}

func (p *TbParser) inlineFacts_untilEndOfInline(tb *tokenBlock, ends []string) ([]FactStmt, error) {
	facts := []FactStmt{}
	for {
		fact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, ends)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		facts = append(facts, fact)

		if p.IsEnding(tb, ends) {
			break
		}
	}

	return facts, nil
}

// fact, isEnd, err
func (p *TbParser) inlineFactThenSkipStmtTerminatorUntilEndSignals(tb *tokenBlock, ends []string) (FactStmt, error) {
	curToken, err := tb.header.currentToken()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	switch curToken {
	case glob.KeywordForall:
		uniFact, err := p.inlineUniInterfaceSkipTerminator(tb, ends)
		if err != nil {
			return nil, err
		}
		return uniFact.(FactStmt), nil
	default:
		return p.inline_spec_or_enum_intensional_Equals_fact_skip_terminator(tb)
	}
}

// inlineSpecFactStmt_skip_terminator parses a spec fact and skips statement terminator (comma) if present
func (p *TbParser) inlineSpecFactStmt_skip_terminator(tb *tokenBlock) (*SpecFactStmt, error) {
	stmt, err := p.specFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	p.skipStmtComma(tb)
	return stmt, nil
}

func (p *TbParser) bodyOfInlineDomAndThen(tb *tokenBlock, word string, ends []string) ([]FactStmt, []FactStmt, error) {
	domFacts, err := p.inlineFacts_untilWord(tb, word, ends)
	if err != nil {
		return nil, nil, parserErrAtTb(err, tb)
	}

	thenFacts, err := p.inlineFacts_untilEndOfInline(tb, ends)
	if err != nil {
		return nil, nil, parserErrAtTb(err, tb)
	}

	return domFacts, thenFacts, nil
}

func (p *TbParser) inlineFacts_untilWord(tb *tokenBlock, word string, ends []string) ([]FactStmt, error) {
	facts := []FactStmt{}
	for {
		fact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, ends)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		facts = append(facts, fact)

		if tb.header.is(word) {
			tb.header.skip(word)
			break
		}
	}

	return facts, nil
}

func (p *TbParser) inlineFacts_untilWord_or_exceedEnd_notSkipWord(tb *tokenBlock, word string, ends []string) ([]FactStmt, error) {
	facts := []FactStmt{}
	for {
		fact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, ends)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		facts = append(facts, fact)

		if tb.header.is(word) {
			break
		}

		if p.IsEnding(tb, ends) {
			break
		}
	}

	return facts, nil
}

func (p *TbParser) inlineUniFact_Param_ParamSet_ParamInSetFacts(tb *tokenBlock) ([]string, []Obj, error) {
	params := []string{}
	setParams := []Obj{}
	paramWithoutSetCount := 0

	if tb.header.is(glob.KeySymbolColon) {
		return params, setParams, nil
	}

	if !tb.header.is(glob.KeySymbolRightArrow) || !tb.header.is(glob.KeySymbolColon) {
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

			// Expect either '=>' or ':'
			if tb.header.is(glob.KeySymbolRightArrow) || tb.header.is(glob.KeySymbolColon) {
				break
			}

			return nil, nil, fmt.Errorf("expected ',' or '=>' but got '%s'", tb.header.strAtCurIndexPlus(0))
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

func (p *TbParser) inlineUniInterfaceSkipTerminator(tb *tokenBlock, ends []string) (UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	params := []string{}
	setParams := []Obj{}
	domFact := []FactStmt{}

	if !tb.header.is(glob.KeySymbolRightArrow) { // 没有 参数
		params, setParams, err = p.inlineUniFact_Param_ParamSet_ParamInSetFacts(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}

		// Check for conflicts with existing FreeParams
		for _, param := range params {
			if _, exists := p.FreeParams[param]; exists {
				return nil, parserErrAtTb(fmt.Errorf("parameter %s conflicts with a free parameter in the outer scope", param), tb)
			}
		}

		// Add uniFact params to FreeParams
		for _, param := range params {
			p.FreeParams[param] = struct{}{}
		}
	}

	// Defer: remove the params we added when leaving this uniFact scope
	defer func() {
		for _, param := range params {
			delete(p.FreeParams, param)
		}
	}()

	if !tb.header.is(glob.KeySymbolRightArrow) {
		if tb.header.is(glob.KeySymbolColon) {
			tb.header.skip(glob.KeySymbolColon)
			domFact, err = p.inlineDomFactInUniFactInterface_WithoutSkippingEnd(tb, ends)
			if err != nil {
				return nil, err
			}

			if tb.header.is(glob.KeySymbolSemiColon) {
				tb.header.skip(glob.KeySymbolSemiColon)
				return NewUniFact(params, setParams, []FactStmt{}, domFact, tb.line), nil
			} else if p.IsEnding(tb, ends) {
				return NewUniFact(params, setParams, []FactStmt{}, domFact, tb.line), nil
			} else if tb.header.is(glob.KeySymbolEquivalent) {
				err = tb.header.skip(glob.KeySymbolEquivalent)
				if err != nil {
					return nil, parserErrAtTb(err, tb)
				}

				iffFacts, err := p.thenFacts_SkipEnd_Semicolon_or_EOL(tb, ends)
				if err != nil {
					return nil, err
				}

				return NewUniFactWithIff(NewUniFact(params, setParams, []FactStmt{}, domFact, tb.line), iffFacts, tb.line), nil
			}
		}
	}

	tb.header.skip(glob.KeySymbolRightArrow)
	thenFact, isEnd, err := p.thenFactsInUniFactInterface(tb, ends)
	if err != nil {
		return nil, err
	}

	if isEnd {
		return NewUniFact(params, setParams, domFact, thenFact, tb.line), nil
	}

	err = tb.header.skip(glob.KeySymbolEquivalent)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	iffFacts, err := p.thenFacts_SkipEnd_Semicolon_or_EOL(tb, ends)
	if err != nil {
		return nil, err
	}
	return NewUniFactWithIff(NewUniFact(params, setParams, domFact, thenFact, tb.line), iffFacts, tb.line), nil
}

func (p *TbParser) thenFactsInUniFactInterface(tb *tokenBlock, ends []string) ([]FactStmt, bool, error) {
	facts := []FactStmt{}
	for {
		specFact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, ends)
		if err != nil {
			return nil, false, parserErrAtTb(err, tb)
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolEquivalent) {
			return facts, false, nil
		}

		if p.IsEnding(tb, ends) {
			return facts, true, nil
		}

		if tb.header.is(glob.KeySymbolSemiColon) {
			tb.header.skip(glob.KeySymbolSemiColon)
			return facts, true, nil
		}

	}
}

func (p *TbParser) thenFacts_SkipEnd_Semicolon_or_EOL(tb *tokenBlock, ends []string) ([]FactStmt, error) {
	facts := []FactStmt{}
	for {
		specFact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, ends)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		facts = append(facts, specFact)

		if p.IsEnding(tb, ends) {
			return facts, nil
		}

		if tb.header.is(glob.KeySymbolSemiColon) {
			tb.header.skip(glob.KeySymbolSemiColon)
			return facts, nil
		}

	}
}

func (p *TbParser) inlineDomFactInUniFactInterface(tb *tokenBlock, ends []string) ([]FactStmt, error) {
	facts := []FactStmt{}
	for {
		specFact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, ends)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolRightArrow) {
			tb.header.skip(glob.KeySymbolRightArrow)
			return facts, nil
		}
	}
}

func (p *TbParser) inlineDomFactInUniFactInterface_WithoutSkippingEnd(tb *tokenBlock, ends []string) ([]FactStmt, error) {
	facts := []FactStmt{}
	for {
		specFact, err := p.inlineFactThenSkipStmtTerminatorUntilEndSignals(tb, ends)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolRightArrow) || tb.header.is(glob.KeySymbolSemiColon) || tb.header.is(glob.KeySymbolEquivalent) {
			return facts, nil
		}
		if p.IsEnding(tb, ends) {
			return facts, nil
		}
	}
}

// inline_spec_or_fact_skip_terminator parses spec fact or or-fact and skips statement terminator
func (p *TbParser) inline_spec_or_fact_skip_terminator(tb *tokenBlock) (FactStmt, error) {
	specFact, err := p.inlineSpecFactStmt_skip_terminator(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	if tb.header.is(glob.KeywordOr) {
		orFacts := []*SpecFactStmt{specFact}
		for tb.header.is(glob.KeywordOr) {
			tb.header.skip(glob.KeywordOr)
			specFact, err := p.inlineSpecFactStmt_skip_terminator(tb)
			if err != nil {
				return nil, parserErrAtTb(err, tb)
			}
			orFacts = append(orFacts, specFact)
		}
		return NewOrStmt(orFacts, tb.line), nil
	} else {
		return specFact, nil
	}
}

func (p *TbParser) inlineOrFact(tb *tokenBlock) (*OrStmt, error) {
	firstFact, err := p.specFactStmt(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}
	return p.inlineOrFactWithFirstFact(tb, firstFact)
}

func (p *TbParser) inlineOrFactWithFirstFact(tb *tokenBlock, firstFact *SpecFactStmt) (*OrStmt, error) {
	orFacts := []*SpecFactStmt{firstFact}
	for tb.header.is(glob.KeywordOr) {
		tb.header.skip(glob.KeywordOr)
		specFact, err := p.inlineSpecFactStmt_skip_terminator(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		orFacts = append(orFacts, specFact)
	}
	return NewOrStmt(orFacts, tb.line), nil
}

// inline_spec_or_enum_intensional_Equals_fact_skip_terminator is the main entry point for parsing inline facts.
// It handles four main cases:
// 1. Facts starting with special prefixes ($, not, exist)
// 2. Facts with function-like properties (x $prop y)
// 3. Facts with infix relational operators (x = y, x > y, etc.)
// 4. Enum intensional facts (x := {y | ...})
// After parsing, it skips the statement terminator (comma) if present.
func (p *TbParser) inline_spec_or_enum_intensional_Equals_fact_skip_terminator(tb *tokenBlock) (FactStmt, error) {
	// Case 1: Handle facts starting with special prefixes
	if p.isCurTokenSpecFactPrefix(tb) {
		return p.parseSpecialPrefixFact(tb)
	}

	// Case 2-4: Handle facts starting with a first-class citizen (obj)
	return p.parseFactStartWithObj(tb)
}

// isCurTokenSpecFactPrefix checks if the fact starts with a special prefix
func (p *TbParser) isCurTokenSpecFactPrefix(tb *tokenBlock) bool {
	return tb.header.is(glob.FuncFactPrefix) ||
		tb.header.is(glob.KeywordNot) ||
		tb.header.is(glob.KeywordExist)
}

// parseSpecialPrefixFact parses facts that start with special prefixes ($, not, exist)
func (p *TbParser) parseSpecialPrefixFact(tb *tokenBlock) (FactStmt, error) {
	fact, err := p.inline_spec_or_fact_skip_terminator(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	p.skipStmtComma(tb)
	return fact, nil
}

// parseFactStartWithObj parses facts that start with a first-class citizen
func (p *TbParser) parseFactStartWithObj(tb *tokenBlock) (FactStmt, error) {
	// Parse the first obj
	obj, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Get the operator/delimiter
	operator, err := tb.header.next()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Dispatch based on operator type
	var fact FactStmt
	if operator == glob.FuncFactPrefix {
		fact, err = p.parseFunctionPropertyFact(tb, obj)
		// } else if operator == glob.KeySymbolColonEqual {
	} else {
		fact, err = p.parseInfixRelationalFact(tb, obj, operator)
	}

	if err != nil {
		return nil, err
	}

	p.skipStmtComma(tb)
	return fact, nil
}

// parseFunctionPropertyFact parses facts like "x $prop y" or "x $prop"
func (p *TbParser) parseFunctionPropertyFact(tb *tokenBlock, leftObj Obj) (FactStmt, error) {
	propName, err := p.notNumberAtom(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Determine parameters: one or two
	params := []Obj{leftObj}
	if !tb.header.ExceedEnd() {
		rightObj, err := p.Obj(tb)
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		params = append(params, rightObj)
	}

	curFact := NewSpecFactStmt(TruePure, propName, params, tb.line)
	return p.handleOrFactIfPresent(tb, curFact)
}

// parseInfixRelationalFact parses facts like "x = y", "x > y", "x != y", etc.
func (p *TbParser) parseInfixRelationalFact(tb *tokenBlock, leftObj Obj, operator string) (FactStmt, error) {
	if !glob.IsBuiltinInfixRelaPropSymbol(operator) {
		return nil, fmt.Errorf("expect relation prop, got: %s", operator)
	}

	rightObj, err := p.Obj(tb)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	// Handle special case: double equals (==)
	if operator == glob.KeySymbolEqual && tb.header.is(glob.KeySymbolEqual) {
		return p.relaEqualsFactStmt(tb, leftObj, rightObj)
	}

	// Create the fact
	params := []Obj{leftObj, rightObj}
	curFact := NewSpecFactStmt(TruePure, Atom(operator), params, tb.line)

	// Handle syntactic sugar: != is equivalent to "not ="
	curFact = p.normalizeNotEqualFact(curFact)

	return p.handleOrFactIfPresent(tb, curFact)
}

// normalizeNotEqualFact converts != to "not =" for easier processing
// This allows us to reuse the commutative property of =
func (p *TbParser) normalizeNotEqualFact(fact *SpecFactStmt) *SpecFactStmt {
	if fact != nil && fact.NameIs(glob.KeySymbolNotEqual) {
		fact.TypeEnum = FalsePure
		fact.PropName = Atom(glob.KeySymbolEqual)
	}
	return fact
}

// handleOrFactIfPresent checks if there's an "or" keyword and handles it
func (p *TbParser) handleOrFactIfPresent(tb *tokenBlock, curFact *SpecFactStmt) (FactStmt, error) {
	if tb.header.is(glob.KeywordOr) {
		return p.inlineOrFactWithFirstFact(tb, curFact)
	}
	return curFact, nil
}

// skipStmtComma skips statement terminator (comma) if present
func (p *TbParser) skipStmtComma(tb *tokenBlock) {
	if tb.header.is(glob.KeySymbolComma) {
		tb.header.skip("")
	}
}

// inline_enum_intensional_fact_skip_terminator parses enum intensional fact (x := {items} or x := {y | ...})
// and skips statement terminator (comma)
// func (p *tbParser) inline_enum_intensional_fact_skip_terminator(tb *tokenBlock, left Obj) (FactStmt, error) {
// 	defer func() {
// 		p.skipStmtComma(tb)
// 	}()

// 	err := tb.header.skip(glob.KeySymbolLeftCurly)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	firstObj, err := p.Obj(tb)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	if tb.header.is(glob.KeySymbolComma) || tb.header.is(glob.KeySymbolRightCurly) {
// 		if tb.header.is(glob.KeySymbolComma) {
// 			tb.header.skip(glob.KeySymbolComma)
// 		} else {
// 			return NewSpecFactStmt(TruePure, Atom(glob.KeySymbolEqual), []Obj{left, MakeEnumSetObj([]Obj{firstObj})}, tb.line), nil
// 		}

// 		enumItems := []Obj{firstObj}
// 		for !tb.header.is(glob.KeySymbolRightCurly) {
// 			obj, err := p.Obj(tb)
// 			if err != nil {
// 				return nil, parserErrAtTb(err, tb)
// 			}
// 			enumItems = append(enumItems, obj)
// 			if tb.header.is(glob.KeySymbolComma) {
// 				tb.header.skip(glob.KeySymbolComma)
// 			}
// 		}

// 		err = tb.header.skip(glob.KeySymbolRightCurly)
// 		if err != nil {
// 			return nil, parserErrAtTb(err, tb)
// 		}

// 		return NewSpecFactStmt(TruePure, Atom(glob.KeySymbolEqual), []Obj{left, MakeEnumSetObj(enumItems)}, tb.line), nil
// 	} else {

// firstObjAsAtom := firstObj.(Atom)
// // 必须是纯的，不能是复合的
// if glob.IsValidUseDefinedFcAtom(string(firstObjAsAtom)) != nil {
// 	return nil, fmt.Errorf("the first item of enum must be an atom without package name, but got %s", firstObjAsAtom)
// }

// parentSet, err := p.Obj(tb)
// if err != nil {
// 	return nil, parserErrAtTb(err, tb)
// }

// err = tb.header.skip(glob.KeySymbolColon)
// if err != nil {
// 	return nil, parserErrAtTb(err, tb)
// }

// facts := []*SpecFactStmt{}
// for !tb.header.is(glob.KeySymbolRightCurly) {
// 	fact, err := p.inlineSpecFactStmt_skip_terminator(tb)
// 	if err != nil {
// 		return nil, parserErrAtTb(err, tb)
// 	}

// 	facts = append(facts, fact)
// }

// err = tb.header.skip(glob.KeySymbolRightCurly)
// if err != nil {
// 	return nil, parserErrAtTb(err, tb)
// }

// return NewIntensionalSetStmt(left, string(firstObjAsAtom), parentSet, facts, tb.line), nil
// 	}
// }

func (p *TbParser) inlineFacts_checkUniDepth0(tb *tokenBlock, ends []string) ([]FactStmt, error) {
	facts, err := p.inlineFacts_untilEndOfInline(tb, ends)
	if err != nil {
		return nil, err
	}

	err = checkFactsUniDepth0(facts)
	if err != nil {
		return nil, err
	}

	return facts, nil
}

func (p *TbParser) inlineFacts_checkUniDepth1(tb *tokenBlock, ends []string) ([]FactStmt, error) {
	facts, err := p.inlineFacts_untilEndOfInline(tb, ends)
	if err != nil {
		return nil, err
	}

	err = checkFactsUniDepth1(facts)
	if err != nil {
		return nil, err
	}

	return facts, nil
}
