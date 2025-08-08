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
	"slices"
)

func (tb *tokenBlock) inlineFacts_untilEndOfInline() ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		fact, err := tb.inlineFact()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, fact)

		if tb.header.ExceedEnd() {
			break
		}
	}

	return facts, nil
}

func (tb *tokenBlock) inlineFacts_untilWord_SkipWord(word string) ([]*ast.SpecFactStmt, error) {
	facts := []*ast.SpecFactStmt{}
	for {
		stmt, err := tb.specFactStmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, stmt)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		} else if tb.header.is(word) {
			break
		} else {
			return nil, fmt.Errorf("expect ',' or %s", word)
		}
	}

	err := tb.header.skip(word)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return facts, nil
}

// fact, isEnd, err
func (tb *tokenBlock) inlineFact() (ast.FactStmt, error) {
	curToken, err := tb.header.currentToken()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	switch curToken {
	case glob.KeywordForall:
		return tb.inlineUniInterface()
	case glob.KeywordOr:
		return tb.inlineOrStmt()
	case glob.KeySymbolEqual:
		return tb.inlineEqualsFactStmt()
	default:
		return tb.inlineSpecFactStmt()
	}
}

func (tb *tokenBlock) inlineSpecFactStmt() (*ast.SpecFactStmt, error) {
	stmt, err := tb.specFactStmt()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.header.is(glob.KeySymbolComma) {
		tb.header.skip("")
	}

	return stmt, nil
}

func (tb *tokenBlock) inlineOrStmt() (*ast.OrStmt, error) {
	err := tb.header.skip(glob.KeywordOr)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	facts, err := tb.inlineFacts_untilWord_SkipWord(glob.KeySymbolRightBrace)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	if tb.header.is(glob.KeySymbolComma) {
		tb.header.skip("")
	}

	return ast.NewOrStmt(facts), nil
}

func (tb *tokenBlock) bodyOfInlineDomAndThen(word string) ([]ast.FactStmt, []ast.FactStmt, error) {
	domFacts, err := tb.inlineFacts_untilWord(word)
	if err != nil {
		return nil, nil, tbErr(err, tb)
	}

	thenFacts, err := tb.inlineFacts_untilEndOfInline()
	if err != nil {
		return nil, nil, tbErr(err, tb)
	}

	return domFacts, thenFacts, nil
}

func (tb *tokenBlock) inlineFacts_untilWord(word string) ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		fact, err := tb.inlineFact()
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

func (tb *tokenBlock) inlineUniFact_Param_ParamSet_ParamInSetFacts() ([]string, []ast.Fc, error) {
	params := []string{}
	setParams := []ast.Fc{}
	paramWithoutSetCount := 0

	if tb.header.is(glob.KeySymbolColon) {
		return params, setParams, nil
	}

	if !tb.header.is(glob.KeySymbolEqualLarger) || !tb.header.is(glob.KeySymbolColon) {
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

			if tb.header.is(glob.KeySymbolEqualLarger) || tb.header.is(glob.KeySymbolColon) {
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

func (tb *tokenBlock) inlineUniInterface() (ast.UniFactInterface, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	params := []string{}
	setParams := []ast.Fc{}
	domFact := []ast.FactStmt{}

	if !tb.header.is(glob.KeySymbolEqualLarger) {
		params, setParams, err = tb.inlineUniFact_Param_ParamSet_ParamInSetFacts()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		if tb.header.is(glob.KeySymbolColon) {
			tb.header.skip(glob.KeySymbolColon)
			domFact, err = tb.domFactInUniFactInterface()
			if err != nil {
				return nil, err
			}
		}
	}

	tb.header.skip(glob.KeySymbolEqualLarger)
	thenFact, isEnd, err := tb.thenFactsInUniFactInterface()
	if err != nil {
		return nil, err
	}

	if isEnd {
		return ast.NewUniFact(params, setParams, domFact, thenFact), nil
	}

	err = tb.header.skip(glob.KeySymbolEquivalent)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	iffFacts, err := tb.thenFacts_SkipEnd_Semicolon_or_EOL()
	if err != nil {
		return nil, err
	}
	return ast.NewUniFactWithIff(ast.NewUniFact(params, setParams, domFact, thenFact), iffFacts), nil
}

func (tb *tokenBlock) thenFactsInUniFactInterface() ([]ast.FactStmt, bool, error) {
	facts := []ast.FactStmt{}
	for {
		specFact, err := tb.inlineFact()
		if err != nil {
			return nil, false, tbErr(err, tb)
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolEquivalent) {
			return facts, false, nil
		}

		if tb.header.ExceedEnd() {
			return facts, true, nil
		}

		if tb.header.is(glob.KeySymbolSemiColon) {
			tb.header.skip(glob.KeySymbolSemiColon)
			return facts, true, nil
		}

	}
}

func (tb *tokenBlock) thenFacts_SkipEnd_Semicolon_or_EOL() ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		specFact, err := tb.inlineFact()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, specFact)

		if tb.header.ExceedEnd() {
			return facts, nil
		}

		if tb.header.is(glob.KeySymbolSemiColon) {
			tb.header.skip(glob.KeySymbolSemiColon)
			return facts, nil
		}

	}
}

func (tb *tokenBlock) domFactInUniFactInterface() ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		specFact, err := tb.inlineFact()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, specFact)
		if tb.header.is(glob.KeySymbolEqualLarger) {
			tb.header.skip(glob.KeySymbolEqualLarger)
			return facts, nil
		}
	}
}

func (tb *tokenBlock) inlineEqualsFactStmt() (*ast.EqualsFactStmt, error) {
	err := tb.header.skip(glob.KeySymbolEqual)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftBrace)
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

	if tb.header.is(glob.KeySymbolComma) {
		tb.header.skip("")
	}

	return ast.NewEqualsFactStmt(params), nil
}

func (tb *tokenBlock) inline_specFact_enum_intensional_fact() (ast.FactStmt, error) {
	if tb.header.is(glob.FuncFactPrefix) || tb.header.is(glob.KeywordNot) || tb.header.is(glob.KeywordExist) {
		return tb.specFactStmt()
	}

	var ret ast.FactStmt

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
	} else if opt == glob.KeySymbolColonEqual {
		return tb.inline_enum_intensional_fact()
	} else {
		fc2, err := tb.RawFc()
		if err != nil {
			return nil, tbErr(err, tb)
		}

		params := []ast.Fc{fc, fc2}

		ret = ast.NewSpecFactStmt(ast.TruePure, ast.FcAtom(opt), params)
	}

	// 这里加入语法糖：!= 等价于 not =，好处是我 = 有 commutative的性质，我不用额外处理 != 了
	if asSpec, ok := ret.(*ast.SpecFactStmt); ok {
		if asSpec.NameIs(glob.KeySymbolNotEqual) {
			asSpec.TypeEnum = ast.FalsePure
			asSpec.PropName = ast.FcAtom(glob.KeySymbolEqual)
		}
	}

	return ret, nil
}

func (tb *tokenBlock) inline_enum_intensional_fact() (ast.FactStmt, error) {
	err := tb.header.skip(glob.KeySymbolColonEqual)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	err = tb.header.skip(glob.KeySymbolLeftCurly)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	firstFc, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}
	_ = firstFc

	if tb.header.is(glob.KeySymbolComma) || tb.header.is(glob.KeySymbolRightCurly) {
		panic("not implemented")
	} else {
		panic("not implemented")
	}
}
