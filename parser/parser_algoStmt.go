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
)

func (tb *tokenBlock) algoStmt() (ast.AlgoStmt, error) {
	if tb.header.is(glob.KeywordIf) {
		return tb.algoIfStmt()
	}

	if tb.header.is(glob.KeywordReturn) {
		return tb.algoReturnStmt()
	}

	return tb.Stmt()
	// panic("not implemented")
}

func (tb *tokenBlock) proveAlgoStmt() (ast.ProveAlgoStmt, error) {
	if tb.header.is(glob.KeywordIf) {
		return tb.proveAlgoIfStmt()
	}

	if tb.header.is(glob.KeywordReturn) {
		return tb.proveAlgoReturnStmt()
	}

	// In prove_algo, only if and return statements are allowed at the top level
	// Other statements like facts should be part of return or if blocks
	return nil, fmt.Errorf("unexpected statement in prove_algo, only 'if' and 'return' are allowed")
}

func (tb *tokenBlock) proveAlgoIfStmt() (*ast.ProveAlgoIfStmt, error) {
	err := tb.header.skip(glob.KeywordIf)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	condition, err := tb.inlineFacts_checkUniDepth0([]string{glob.KeySymbolColon})
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	thenFacts := []ast.ProveAlgoStmt{}
	for _, bodyStmt := range tb.body {
		stmt, err := bodyStmt.proveAlgoStmt()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		thenFacts = append(thenFacts, stmt)
	}

	return ast.NewProveAlgoIfStmt(condition, thenFacts, tb.line), nil
}

func (tb *tokenBlock) algoIfStmt() (*ast.AlgoIfStmt, error) {
	err := tb.header.skip(glob.KeywordIf)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	condition, err := tb.inlineFacts_checkUniDepth0([]string{glob.KeySymbolColon})
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	thenFacts := []ast.AlgoStmt{}
	for _, bodyStmt := range tb.body {
		stmt, err := bodyStmt.algoStmt()
		if err != nil {
			return nil, parserErrAtTb(err, tb)
		}
		thenFacts = append(thenFacts, stmt)
	}

	return ast.NewAlgoIfStmt(condition, thenFacts, tb.line), nil
}

func (tb *tokenBlock) algoReturnStmt() (*ast.AlgoReturnStmt, error) {
	err := tb.header.skip(glob.KeywordReturn)
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	obj, err := tb.RawObj()
	if err != nil {
		return nil, parserErrAtTb(err, tb)
	}

	return ast.NewAlgoReturnStmt(obj, tb.line), nil
}

func (tb *tokenBlock) proveAlgoReturnStmt() (*ast.ProveAlgoReturnStmt, error) {
	err := tb.header.skip(glob.KeywordReturn)
	if err != nil {
		return nil, err
	}

	// 首先检查是否到达末尾 - 如果到达，说明没有相关的 fact or by
	if tb.header.ExceedEnd() {
		return ast.NewProveAlgoReturnStmt([]ast.FactOrByStmt{}, tb.line), nil
	}

	// 没到最后，检查是否是 colon
	curToken, err := tb.header.currentToken()
	if err != nil {
		return nil, err
	}

	if curToken == glob.KeySymbolColon {
		// 是 colon，跳过它然后取 body
		err = tb.header.skip(glob.KeySymbolColon)
		if err != nil {
			return nil, err
		}

		// return: with colon - parse body which may contain facts or by statements
		factOrBySlice := []ast.FactOrByStmt{}
		for _, bodyBlock := range tb.body {
			// Check if it's a by statement
			if bodyBlock.header.is(glob.KeywordBy) {
				byStmt, err := bodyBlock.byStmt()
				if err != nil {
					return nil, err
				}
				factOrBySlice = append(factOrBySlice, byStmt)
			} else {
				// Otherwise parse as fact
				fact, err := bodyBlock.factStmt(UniFactDepth0)
				if err != nil {
					return nil, err
				}
				factOrBySlice = append(factOrBySlice, fact)
			}
		}
		return ast.NewProveAlgoReturnStmt(factOrBySlice, tb.line), nil
	}

	// 不是 colon，说明是单行的结果
	// Check if it's a by statement
	if tb.header.is(glob.KeywordBy) {
		byStmt, err := tb.byStmt()
		if err != nil {
			return nil, err
		}
		return ast.NewProveAlgoReturnStmt([]ast.FactOrByStmt{byStmt}, tb.line), nil
	}

	// Otherwise parse as fact
	fact, err := tb.inlineFactThenSkipStmtTerminatorUntilEndSignals([]string{})
	if err != nil {
		return nil, err
	}
	return ast.NewProveAlgoReturnStmt([]ast.FactOrByStmt{fact}, tb.line), nil
}
