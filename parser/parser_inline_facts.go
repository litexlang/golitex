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
	"strings"
)

func (tb *tokenBlock) IsEnding(ends []string) bool {
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

func (tb *tokenBlock) inlineFacts_untilEndOfInline(ends []string) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		fact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals(ends)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, fact)

		if tb.IsEnding(ends) {
			break
		}
	}

	return facts, nil
}

// fact, isEnd, err
func (tb *tokenBlock) inlineFactThenSkipStmtTerminatorUntilEndSignals(ends []string) (ast.FactStmt, error) {
	curToken, err := tb.header.currentToken()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	switch curToken {
	case glob.KeywordForall:
		uniFact, err := tb.inlineUniInterfaceSkipTerminator(ends)
		if err != nil {
			return nil, err
		}
		return uniFact.(ast.FactStmt), nil
	case glob.KeywordWhen:
		uniFact, err := tb.inlineWhenFactSkipTerminator(ends)
		if err != nil {
			return nil, err
		}
		return uniFact.(ast.FactStmt), nil
	default:
		return tb.inline_spec_or_enum_intensional_Equals_fact_skip_terminator()
	}
}

// inlineSpecFactStmt_skip_terminator parses a spec fact and skips statement terminator (comma) if present
func (tb *tokenBlock) inlineSpecFactStmt_skip_terminator() (*ast.SpecFactStmt, error) {
	stmt, err := tb.specFactStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	tb.skipStmtComma()
	return stmt, nil
}

func (tb *tokenBlock) bodyOfInlineDomAndThen(word string, ends []string) ([]ast.FactStmt, []ast.FactStmt, error) {
	domFacts, err := tb.inlineFacts_untilWord(word, ends)
	if err != nil {
		return nil, nil, tbErr(err, tb)
	}

	thenFacts, err := tb.inlineFacts_untilEndOfInline(ends)
	if err != nil {
		return nil, nil, tbErr(err, tb)
	}

	return domFacts, thenFacts, nil
}

func (tb *tokenBlock) inlineFacts_untilWord(word string, ends []string) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		fact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals(ends)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, fact)

		if tb.header.is(word) {
			tb.header.skip(word)
			break
		}
	}

	return facts, nil
}

func (tb *tokenBlock) inlineFacts_untilWord_or_exceedEnd_notSkipWord(word string, ends []string) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		fact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals(ends)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, fact)

		if tb.header.is(word) {
			break
		}

		if tb.IsEnding(ends) {
			break
		}
	}

	return facts, nil
}

func (tb *tokenBlock) inlineUniFact_Param_ParamSet_ParamInSetFacts() ([]string, []ast.Obj, error) {
	params := []string{}
	setParams := []ast.Obj{}
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

			setParam, err := tb.RawObj()
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

func (tb *tokenBlock) inlineUniInterfaceSkipTerminator(ends []string) (ast.UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	params := []string{}
	setParams := []ast.Obj{}
	domFact := []ast.FactStmt{}

	if !tb.header.is(glob.KeySymbolRightArrow) { // 没有 参数
		params, setParams, err = tb.inlineUniFact_Param_ParamSet_ParamInSetFacts()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if tb.header.is(glob.KeySymbolColon) {
			tb.header.skip(glob.KeySymbolColon)
			domFact, err = tb.inlineDomFactInUniFactInterface_WithoutSkippingEnd(ends)
			if err != nil {
				return nil, err
			}

			if tb.header.is(glob.KeySymbolSemiColon) {
				tb.header.skip(glob.KeySymbolSemiColon)
				return ast.NewUniFact(params, setParams, []ast.FactStmt{}, domFact, tb.line), nil
			} else if tb.IsEnding(ends) {
				return ast.NewUniFact(params, setParams, []ast.FactStmt{}, domFact, tb.line), nil
			} else if tb.header.is(glob.KeySymbolEquivalent) {
				err = tb.header.skip(glob.KeySymbolEquivalent)
				if err != nil {
					return nil, tbErr(err, tb)
				}

				iffFacts, err := tb.thenFacts_SkipEnd_Semicolon_or_EOL(ends)
				if err != nil {
					return nil, err
				}

				return ast.NewUniFactWithIff(ast.NewUniFact(params, setParams, []ast.FactStmt{}, domFact, tb.line), iffFacts, tb.line), nil
			}
		}
	}

	tb.header.skip(glob.KeySymbolRightArrow)
	thenFact, isEnd, err := tb.thenFactsInUniFactInterface(ends)
	if err != nil {
		return nil, err
	}

	if isEnd {
		return ast.NewUniFact(params, setParams, domFact, thenFact, tb.line), nil
	}

	err = tb.header.skip(glob.KeySymbolEquivalent)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	iffFacts, err := tb.thenFacts_SkipEnd_Semicolon_or_EOL(ends)
	if err != nil {
		return nil, err
	}
	return ast.NewUniFactWithIff(ast.NewUniFact(params, setParams, domFact, thenFact, tb.line), iffFacts, tb.line), nil
}

func (tb *tokenBlock) inlineWhenFactSkipTerminator(ends []string) (ast.UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordWhen)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// 可以写 : 也可以不写
	if tb.header.is(glob.KeySymbolColon) {
		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, tbErr(err, tb)
		}
	}

	domFact, err := tb.inlineDomFactInUniFactInterface(ends)
	if err != nil {
		return nil, err
	}

	tb.header.skip(glob.KeySymbolRightArrow)
	thenFact, isEnd, err := tb.thenFactsInUniFactInterface(ends)
	if err != nil {
		return nil, err
	}

	if isEnd {
		return ast.NewUniFact([]string{}, []ast.Obj{}, domFact, thenFact, tb.line), nil
	}

	err = tb.header.skip(glob.KeySymbolEquivalent)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	iffFacts, err := tb.thenFacts_SkipEnd_Semicolon_or_EOL(ends)
	if err != nil {
		return nil, err
	}
	return ast.NewUniFactWithIff(ast.NewUniFact([]string{}, []ast.Obj{}, domFact, thenFact, tb.line), iffFacts, tb.line), nil
}

func (tb *tokenBlock) thenFactsInUniFactInterface(ends []string) ([]ast.FactStmt, bool, error) {
	facts := []ast.FactStmt{}
	for {
		specFact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals(ends)
		if err != nil {
			return nil, false, tbErr(err, tb)
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolEquivalent) {
			return facts, false, nil
		}

		if tb.IsEnding(ends) {
			return facts, true, nil
		}

		if tb.header.is(glob.KeySymbolSemiColon) {
			tb.header.skip(glob.KeySymbolSemiColon)
			return facts, true, nil
		}

	}
}

func (tb *tokenBlock) thenFacts_SkipEnd_Semicolon_or_EOL(ends []string) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		specFact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals(ends)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, specFact)

		if tb.IsEnding(ends) {
			return facts, nil
		}

		if tb.header.is(glob.KeySymbolSemiColon) {
			tb.header.skip(glob.KeySymbolSemiColon)
			return facts, nil
		}

	}
}

func (tb *tokenBlock) inlineDomFactInUniFactInterface(ends []string) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		specFact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals(ends)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolRightArrow) {
			tb.header.skip(glob.KeySymbolRightArrow)
			return facts, nil
		}
	}
}

func (tb *tokenBlock) inlineDomFactInUniFactInterface_WithoutSkippingEnd(ends []string) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		specFact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals(ends)
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolRightArrow) || tb.header.is(glob.KeySymbolSemiColon) || tb.header.is(glob.KeySymbolEquivalent) {
			return facts, nil
		}
		if tb.IsEnding(ends) {
			return facts, nil
		}
	}
}

// inline_spec_or_fact_skip_terminator parses spec fact or or-fact and skips statement terminator
func (tb *tokenBlock) inline_spec_or_fact_skip_terminator() (ast.FactStmt, error) {
	specFact, err := tb.inlineSpecFactStmt_skip_terminator()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.header.is(glob.KeywordOr) {
		orFacts := []*ast.SpecFactStmt{specFact}
		for tb.header.is(glob.KeywordOr) {
			tb.header.skip(glob.KeywordOr)
			specFact, err := tb.inlineSpecFactStmt_skip_terminator()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			orFacts = append(orFacts, specFact)
		}
		return ast.NewOrStmt(orFacts, tb.line), nil
	} else {
		return specFact, nil
	}
}

func (tb *tokenBlock) inlineOrFact() (*ast.OrStmt, error) {
	firstFact, err := tb.specFactStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}
	return tb.inlineOrFactWithFirstFact(firstFact)
}

func (tb *tokenBlock) inlineOrFactWithFirstFact(firstFact *ast.SpecFactStmt) (*ast.OrStmt, error) {
	orFacts := []*ast.SpecFactStmt{firstFact}
	for tb.header.is(glob.KeywordOr) {
		tb.header.skip(glob.KeywordOr)
		specFact, err := tb.inlineSpecFactStmt_skip_terminator()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		orFacts = append(orFacts, specFact)
	}
	return ast.NewOrStmt(orFacts, tb.line), nil
}

// inline_spec_or_enum_intensional_Equals_fact_skip_terminator is the main entry point for parsing inline facts.
// It handles four main cases:
// 1. Facts starting with special prefixes ($, not, exist)
// 2. Facts with function-like properties (x $prop y)
// 3. Facts with infix relational operators (x = y, x > y, etc.)
// 4. Enum intensional facts (x := {y | ...})
// After parsing, it skips the statement terminator (comma) if present.
func (tb *tokenBlock) inline_spec_or_enum_intensional_Equals_fact_skip_terminator() (ast.FactStmt, error) {
	// Case 1: Handle facts starting with special prefixes
	if tb.isCurTokenSpecFactPrefix() {
		return tb.parseSpecialPrefixFact()
	}

	// Case 2-4: Handle facts starting with a first-class citizen (obj)
	return tb.parseFactStartWithObj()
}

// isCurTokenSpecFactPrefix checks if the fact starts with a special prefix
func (tb *tokenBlock) isCurTokenSpecFactPrefix() bool {
	return tb.header.is(glob.FuncFactPrefix) ||
		tb.header.is(glob.KeywordNot) ||
		tb.header.is(glob.KeywordExist)
}

// parseSpecialPrefixFact parses facts that start with special prefixes ($, not, exist)
func (tb *tokenBlock) parseSpecialPrefixFact() (ast.FactStmt, error) {
	fact, err := tb.inline_spec_or_fact_skip_terminator()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	tb.skipStmtComma()
	return fact, nil
}

// parseFactStartWithObj parses facts that start with a first-class citizen
func (tb *tokenBlock) parseFactStartWithObj() (ast.FactStmt, error) {
	// Parse the first obj
	obj, err := tb.RawObj()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// Get the operator/delimiter
	operator, err := tb.header.next()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// Dispatch based on operator type
	var fact ast.FactStmt
	if operator == glob.FuncFactPrefix {
		fact, err = tb.parseFunctionPropertyFact(obj)
		// } else if operator == glob.KeySymbolColonEqual {
	} else if operator == glob.KeySymbolEqual && tb.header.is(glob.KeySymbolLeftCurly) {
		fact, err = tb.inline_enum_intensional_fact_skip_terminator(obj)
	} else {
		fact, err = tb.parseInfixRelationalFact(obj, operator)
	}

	if err != nil {
		return nil, err
	}

	tb.skipStmtComma()
	return fact, nil
}

// parseFunctionPropertyFact parses facts like "x $prop y" or "x $prop"
func (tb *tokenBlock) parseFunctionPropertyFact(leftObj ast.Obj) (ast.FactStmt, error) {
	propName, err := tb.rawAtomObj()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// Determine parameters: one or two
	params := []ast.Obj{leftObj}
	if !tb.header.ExceedEnd() {
		rightObj, err := tb.RawObj()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		params = append(params, rightObj)
	}

	curFact := ast.NewSpecFactStmt(ast.TruePure, propName, params, tb.line)
	return tb.handleOrFactIfPresent(curFact)
}

// parseInfixRelationalFact parses facts like "x = y", "x > y", "x != y", etc.
func (tb *tokenBlock) parseInfixRelationalFact(leftObj ast.Obj, operator string) (ast.FactStmt, error) {
	if !glob.IsBuiltinInfixRelaPropSymbol(operator) {
		return nil, fmt.Errorf("expect relation prop, got: %s", operator)
	}

	rightObj, err := tb.RawObj()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// Handle special case: double equals (==)
	if operator == glob.KeySymbolEqual && tb.header.is(glob.KeySymbolEqual) {
		return tb.relaEqualsFactStmt(leftObj, rightObj)
	}

	// Create the fact
	params := []ast.Obj{leftObj, rightObj}
	curFact := ast.NewSpecFactStmt(ast.TruePure, ast.AtomObj(operator), params, tb.line)

	// Handle syntactic sugar: != is equivalent to "not ="
	curFact = tb.normalizeNotEqualFact(curFact)

	return tb.handleOrFactIfPresent(curFact)
}

// normalizeNotEqualFact converts != to "not =" for easier processing
// This allows us to reuse the commutative property of =
func (tb *tokenBlock) normalizeNotEqualFact(fact *ast.SpecFactStmt) *ast.SpecFactStmt {
	if fact != nil && fact.NameIs(glob.KeySymbolNotEqual) {
		fact.TypeEnum = ast.FalsePure
		fact.PropName = ast.AtomObj(glob.KeySymbolEqual)
	}
	return fact
}

// handleOrFactIfPresent checks if there's an "or" keyword and handles it
func (tb *tokenBlock) handleOrFactIfPresent(curFact *ast.SpecFactStmt) (ast.FactStmt, error) {
	if tb.header.is(glob.KeywordOr) {
		return tb.inlineOrFactWithFirstFact(curFact)
	}
	return curFact, nil
}

// skipStmtComma skips statement terminator (comma) if present
func (tb *tokenBlock) skipStmtComma() {
	if tb.header.is(glob.KeySymbolComma) {
		tb.header.skip("")
	}
}

// inline_enum_intensional_fact_skip_terminator parses enum intensional fact (x := {items} or x := {y | ...})
// and skips statement terminator (comma)
func (tb *tokenBlock) inline_enum_intensional_fact_skip_terminator(left ast.Obj) (ast.FactStmt, error) {
	defer func() {
		tb.skipStmtComma()
	}()

	err := tb.header.skip(glob.KeySymbolLeftCurly)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	firstObj, err := tb.RawObj()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.header.is(glob.KeySymbolComma) || tb.header.is(glob.KeySymbolRightCurly) {
		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		} else {
			return ast.NewEnumStmt(left, []ast.Obj{firstObj}, tb.line), nil
		}

		enumItems := []ast.Obj{firstObj}
		for !tb.header.is(glob.KeySymbolRightCurly) {
			obj, err := tb.RawObj()
			if err != nil {
				return nil, tbErr(err, tb)
			}
			enumItems = append(enumItems, obj)
			if tb.header.is(glob.KeySymbolComma) {
				tb.header.skip(glob.KeySymbolComma)
			}
		}

		err = tb.header.skip(glob.KeySymbolRightCurly)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewEnumStmt(left, enumItems, tb.line), nil
	} else {
		firstObjAsAtom := firstObj.(ast.AtomObj)
		// 必须是纯的，不能是复合的
		if strings.Contains(string(firstObjAsAtom), glob.KeySymbolColonColon) {
			return nil, fmt.Errorf("the first item of enum must be pure, but got %s", firstObjAsAtom)
		}

		parentSet, err := tb.RawObj()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		facts := []*ast.SpecFactStmt{}
		for !tb.header.is(glob.KeySymbolRightCurly) {
			fact, err := tb.inlineSpecFactStmt_skip_terminator()
			if err != nil {
				return nil, tbErr(err, tb)
			}

			facts = append(facts, fact)
		}

		err = tb.header.skip(glob.KeySymbolRightCurly)
		if err != nil {
			return nil, tbErr(err, tb)
		}

		return ast.NewIntensionalSetStmt(left, string(firstObjAsAtom), parentSet, facts, tb.line), nil
	}
}

func (tb *tokenBlock) inlineFacts_checkUniDepth0(ends []string) ([]ast.FactStmt, error) {
	facts, err := tb.inlineFacts_untilEndOfInline(ends)
	if err != nil {
		return nil, err
	}

	err = checkFactsUniDepth0(facts)
	if err != nil {
		return nil, err
	}

	return facts, nil
}

func (tb *tokenBlock) inlineFacts_checkUniDepth1(ends []string) ([]ast.FactStmt, error) {
	facts, err := tb.inlineFacts_untilEndOfInline(ends)
	if err != nil {
		return nil, err
	}

	err = checkFactsUniDepth1(facts)
	if err != nil {
		return nil, err
	}

	return facts, nil
}
