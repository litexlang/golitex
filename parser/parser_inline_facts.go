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
)

func (tb *tokenBlock) inlineFacts_untilEOL() ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		fact, err := tb.specFactStmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, fact)

		if tb.header.is(glob.KeySymbolComma) {
			tb.header.skip(glob.KeySymbolComma)
		} else if tb.header.ExceedEnd() {
			break
		} else {
			return nil, fmt.Errorf("expect ',' or end of line")
		}
	}

	return facts, nil
}

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
		return tb.inlineUniFact()
	case glob.KeywordOr:
		return tb.inlineOrStmt()
	default:
		return tb.inlineSpecFactStmt()
	}
}

func (tb *tokenBlock) inlineFacts_InInlineUniFactThenFacts() ([]ast.FactStmt, error) {
	facts := []ast.FactStmt{}
	for {
		fact, err := tb.inlineFact()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		facts = append(facts, fact)

		if tb.header.is(glob.EndOfInlineForall) {
			tb.header.skip(glob.EndOfInlineForall)
			break
		}

		if tb.header.ExceedEnd() {
			break
		}
	}

	return facts, nil
}

func (tb *tokenBlock) inlineFacts_InInlineUniFactThenFacts_UntilEndOfInline() ([]ast.FactStmt, error) {
	cur, err := tb.header.currentToken()
	if err != nil {
		return nil, tbErr(err, tb)
	}
	if cur == glob.KeySymbolEqualLarger {
		tb.header.skip(glob.KeySymbolEqualLarger)
		return []ast.FactStmt{}, nil
	}

	if cur == glob.KeySymbolColon {
		tb.header.skip(glob.KeySymbolColon)
	}

	dom := []ast.FactStmt{}
	for {
		specFact, err := tb.inlineFact()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		dom = append(dom, specFact)
		if tb.header.is(glob.KeySymbolEqualLarger) {
			tb.header.skip(glob.KeySymbolEqualLarger)
			break
		}

	}

	return dom, nil
}

func (tb *tokenBlock) inlineUniFact() (*ast.UniFactStmt, error) {
	err := tb.header.skip(glob.KeywordForall)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	params, setParams, err := tb.inlineUniFact_Param_ParamSet_ParamInSetFacts()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	// domFact, err := tb.inlineUniFactDomFact()
	domFact, err := tb.inlineFacts_InInlineUniFactThenFacts_UntilEndOfInline()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	thenFacts, err := tb.inlineFacts_InInlineUniFactThenFacts()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewUniFact(params, setParams, domFact, thenFacts), nil
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

// func (tb *tokenBlock) inlineUniFact() (*ast.UniFactStmt, bool, error) {
// 	panic("")
// }
