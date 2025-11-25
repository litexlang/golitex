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
	ast "golitex/ast"
	glob "golitex/glob"
)

func (tb *tokenBlock) algoStmt() (ast.AlgoStmt, error) {
	if tb.header.is(glob.KeywordIf) {
		return tb.algoIfStmt()
	}

	if tb.header.is(glob.KeywordReturn) {
		// Check if return is followed by colon (multi-line facts) or looks like a fact
		nextToken := tb.header.strAtCurIndexPlus(1)
		if nextToken == glob.KeySymbolColon || nextToken == glob.FuncFactPrefix || nextToken == glob.KeywordNot || nextToken == glob.KeywordExist || nextToken == "" {
			return tb.proveAlgoReturnStmt()
		} else {
			// Check if it looks like a fact (has relational operators) vs an object
			// For now, we'll try to parse as prove_algo return first, fallback to algo return
			// This is a heuristic - if return is followed by =, !=, etc., it's likely a fact
			if glob.IsBuiltinInfixRelaPropSymbol(nextToken) || tb.EndWith(glob.KeySymbolColon) {
				return tb.proveAlgoReturnStmt()
			}
			return tb.algoReturnStmt()
		}
	}

	return tb.Stmt()
	// panic("not implemented")
}

func (tb *tokenBlock) algoIfStmt() (*ast.AlgoIfStmt, error) {
	err := tb.header.skip(glob.KeywordIf)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	condition, err := tb.inlineFacts_checkUniDepth0([]string{glob.KeySymbolColon})
	if err != nil {
		return nil, tbErr(err, tb)
	}

	thenFacts := []ast.AlgoStmt{}
	for _, bodyStmt := range tb.body {
		stmt, err := bodyStmt.algoStmt()
		if err != nil {
			return nil, tbErr(err, tb)
		}
		thenFacts = append(thenFacts, stmt)
	}

	return ast.NewAlgoIfStmt(condition, thenFacts, tb.line), nil
}

func (tb *tokenBlock) algoReturnStmt() (*ast.AlgoReturnStmt, error) {
	err := tb.header.skip(glob.KeywordReturn)
	if err != nil {
		return nil, tbErr(err, tb)
	}

	obj, err := tb.RawObj()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewAlgoReturnStmt(obj, tb.line), nil
}

func (tb *tokenBlock) proveAlgoReturnStmt() (*ast.ProveAlgoReturnStmt, error) {
	err := tb.header.skip(glob.KeywordReturn)
	if err != nil {
		return nil, err
	}

	// Check if there's a colon after return
	hasColon := tb.EndWith(glob.KeySymbolColon)

	if hasColon {
		// return: with colon - parse facts from body
		facts, err := tb.bodyFacts(UniFactDepth0)
		if err != nil {
			return nil, err
		}
		return ast.NewProveAlgoReturnStmt(facts, tb.line), nil
	} else {
		// return without colon - parse a single inline fact
		if tb.header.ExceedEnd() {
			return ast.NewProveAlgoReturnStmt(nil, tb.line), nil
		}
		
		fact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals([]string{})
		if err != nil {
			return nil, err
		}
		return ast.NewProveAlgoReturnStmt([]ast.FactStmt{fact}, tb.line), nil
	}
}
