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
		if tb.header.strAtCurIndexPlus(1) == glob.KeywordBy || tb.header.strAtCurIndexPlus(1) == "" {
			return tb.proveAlgoReturnStmt()
		} else {
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

	fc, err := tb.RawFc()
	if err != nil {
		return nil, tbErr(err, tb)
	}

	return ast.NewAlgoReturnStmt(fc, tb.line), nil
}

func (tb *tokenBlock) proveAlgoReturnStmt() (*ast.ProveAlgoReturnStmt, error) {
	err := tb.header.skip(glob.KeywordReturn)
	if err != nil {
		return nil, err
	}

	if tb.header.ExceedEnd() {
		return ast.NewProveAlgoReturnStmt(nil, tb.line), nil
	}

	by, err := tb.byStmt()
	if err != nil {
		return nil, err
	}

	return ast.NewProveAlgoReturnStmt(by, tb.line), nil
}
